use std::collections::{BTreeSet, HashMap, HashSet};

use oxc_ast::{AstKind, AstType};
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use serde::{Deserialize, Serialize};

use crate::analysis::Analysis;
use crate::cost::{Cost, Part, Reading};
use crate::declarations::FunctionId;
use crate::project::FileId;
use crate::report::report_rows_of;
use crate::summaries::Substitutions;
use crate::syntax::is_iteration_kind;
use crate::unknowns::{SourceSpan, UnknownId};

pub const SCHEMA: u32 = 1;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKey {
    pub path: String,
    pub start: u32,
    pub end: u32,
    pub kind: String,
}

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeState {
    Known,
    Partial,
    Unknown,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NodeRow {
    pub key: NodeKey,
    pub state: NodeState,
    pub bound: Option<String>,
    pub floor: Option<String>,
    pub contributions: Vec<(NodeKey, String)>,
    pub asserted: bool,
    pub unknowns: Vec<(NodeKey, String)>,
    pub rules: Vec<String>,
    pub certificate: Option<String>,
}

pub(crate) type RecordKey = (SourceSpan, AstType);

#[derive(Clone, Debug)]
pub(crate) struct NodeRecord {
    node: NodeId,
    function: FunctionId,
    part: Part,
    asserted: bool,
}

struct Entry {
    key: NodeKey,
    file: FileId,
    node: NodeId,
    cost: Cost,
    unknowns: Option<UnknownId>,
    absent: bool,
    asserted: bool,
    function: bool,
    iteration: bool,
    children: Vec<usize>,
}

impl Entry {
    fn state(&self) -> NodeState {
        match (self.unknowns, self.absent) {
            (None, _) => NodeState::Known,
            (Some(_), true) => NodeState::Unknown,
            (Some(_), false) => NodeState::Partial,
        }
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn record_node(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
        function: FunctionId,
        reading: &Reading,
        asserted: bool,
    ) {
        let part = reading.total(&mut self.unknowns, &mut self.traces);
        let origin = self.source_span(file, kind.span());

        self.node_records.insert(
            (origin, kind.ty()),
            NodeRecord {
                node: kind.node_id(),
                function,
                part,
                asserted,
            },
        );
    }
}

fn node_key_of(analysis: &Analysis<'_, '_>, origin: SourceSpan, kind: AstType) -> NodeKey {
    NodeKey {
        path: analysis.project.file(origin.file).relative.clone(),
        start: origin.start,
        end: origin.end,
        kind: format!("{kind:?}"),
    }
}

fn origin_kind_of(
    analysis: &Analysis<'_, '_>,
    kinds: &mut HashMap<FileId, HashMap<(u32, u32), AstType>>,
    origin: SourceSpan,
) -> Option<AstType> {
    kinds
        .entry(origin.file)
        .or_insert_with(|| {
            let mut found = HashMap::new();

            for node in analysis.project.file(origin.file).semantic.nodes().iter() {
                let span = node.kind().span();

                found
                    .entry((span.start, span.end))
                    .or_insert(node.kind().ty());
            }

            found
        })
        .get(&(origin.start, origin.end))
        .copied()
}

fn unknown_origins_of(
    analysis: &Analysis<'_, '_>,
    kinds: &mut HashMap<FileId, HashMap<(u32, u32), AstType>>,
    root: Option<UnknownId>,
) -> Vec<(NodeKey, String)> {
    let mut found = BTreeSet::new();

    for unknown in analysis.unknowns.origins(root) {
        let key = match origin_kind_of(analysis, kinds, unknown.origin) {
            Some(kind) => node_key_of(analysis, unknown.origin, kind),
            None => NodeKey {
                path: analysis.project.file(unknown.origin.file).relative.clone(),
                start: unknown.origin.start,
                end: unknown.origin.end,
                kind: String::new(),
            },
        };

        found.insert((key, unknown.reason.text().to_owned()));
    }

    found.into_iter().collect()
}

pub fn snapshot_rows(analysis: &mut Analysis<'_, '_>) -> Vec<NodeRow> {
    let functions = analysis.reportable();
    let mut entries = Vec::new();
    let mut located: HashMap<(FileId, NodeId), usize> = HashMap::new();
    let mut reportable = HashSet::with_capacity(functions.len());

    for (file, function) in functions {
        let assertions = analysis.assertions;
        let row = report_rows_of(analysis, &[(file, function)])
            .pop()
            .expect("one report row per function");
        let asserted = row.mark.is_some() || analysis.assertions != assertions;
        let reading = match row.mark {
            Some(_) => analysis.summarize_with(file, function, Substitutions::new(), true),
            None => analysis.summarize(file, function),
        };
        let absent = reading
            .total(&mut analysis.unknowns, &mut analysis.traces)
            .is_absent();
        let kind = analysis.kind_of_node(file, function.node_id());
        let key = node_key_of(analysis, analysis.source_span(file, kind.span()), kind.ty());

        reportable.insert(FunctionId {
            file,
            node: function.node_id(),
        });
        located.insert((file, function.node_id()), entries.len());
        entries.push(Entry {
            key,
            file,
            node: function.node_id(),
            cost: row.cost,
            unknowns: row.unknowns,
            absent,
            asserted,
            function: true,
            iteration: false,
            children: Vec::new(),
        });
    }

    let functions = entries.len();
    let mut records: Vec<_> = analysis
        .node_records
        .iter()
        .filter(|(_, record)| reportable.contains(&record.function))
        .map(|(key, record)| (*key, record.clone()))
        .collect();

    records.sort_by_key(|((origin, _), record)| (*origin, record.node));

    for ((origin, kind), record) in records {
        if located.contains_key(&(origin.file, record.node)) {
            continue;
        }

        located.insert((origin.file, record.node), entries.len());
        entries.push(Entry {
            key: node_key_of(analysis, origin, kind),
            file: origin.file,
            node: record.node,
            absent: record.part.is_absent(),
            cost: record.part.cost,
            unknowns: record.part.unknowns,
            asserted: record.asserted,
            function: false,
            iteration: is_iteration_kind(&analysis.kind_of_node(origin.file, record.node)),
            children: Vec::new(),
        });
    }

    for index in functions..entries.len() {
        let nodes = analysis.project.file(entries[index].file).semantic.nodes();
        let parent = nodes
            .ancestor_ids(entries[index].node)
            .take_while(|ancestor| {
                located.contains_key(&(entries[index].file, *ancestor))
                    || !matches!(
                        nodes.kind(*ancestor),
                        AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
                    )
            })
            .find_map(|ancestor| located.get(&(entries[index].file, ancestor)).copied());

        if let Some(parent) = parent {
            entries[parent].children.push(index);
        }
    }

    let mut kinds = HashMap::new();
    let mut rows: Vec<NodeRow> = entries
        .iter()
        .map(|entry| {
            let state = entry.state();
            let text = entry.cost.text_with(&|id| analysis.values.label(id));
            let mut contributions: Vec<(NodeKey, String)> = match (state, entry.iteration) {
                (NodeState::Partial, false) => entry
                    .children
                    .iter()
                    .map(|child| &entries[*child])
                    .filter(|child| !child.function && child.state() == NodeState::Known)
                    .map(|child| {
                        (
                            child.key.clone(),
                            child.cost.text_with(&|id| analysis.values.label(id)),
                        )
                    })
                    .collect(),
                _ => Vec::new(),
            };

            contributions.sort();

            NodeRow {
                key: entry.key.clone(),
                state,
                bound: (state == NodeState::Known).then(|| text.clone()),
                floor: (state == NodeState::Partial).then_some(text),
                contributions,
                asserted: entry.asserted,
                unknowns: unknown_origins_of(analysis, &mut kinds, entry.unknowns),
                rules: Vec::new(),
                certificate: None,
            }
        })
        .collect();

    rows.sort_by(|left, right| left.key.cmp(&right.key));

    rows
}

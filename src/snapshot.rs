use std::collections::{BTreeSet, HashMap, HashSet};

use oxc_ast::{AstKind, AstType};
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use serde::{Deserialize, Serialize};

use crate::analysis::Analysis;
use crate::cost::{state_of, Cost, Part, Reading, State};
use crate::declarations::FunctionId;
use crate::flow::loop_phases_of;
use crate::project::FileId;
use crate::report::report_rows_of;
use crate::summaries::Substitutions;
use crate::unknowns::{SourceSpan, UnknownId};
use crate::values::{SizeQuantity, RECURRENCE_BASE, RECURRENCE_FLOOR};

/// Row schema. Version 2 renders each size dimension with a label unique to it (`Labels`), where version 1 used the
/// report's labels, which can name different dimensions with the same text.
pub const SCHEMA: u32 = 2;

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

impl From<State> for NodeState {
    fn from(state: State) -> Self {
        match state {
            State::Known => NodeState::Known,
            State::Partial => NodeState::Partial,
            State::Unknown => NodeState::Unknown,
        }
    }
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
    /// For a loop, the children its visits do not repeat (the initializer and the iterable), whose contributions
    /// carry multiplicity one; `None` for any other node, whose children all do.
    once: Option<Vec<NodeId>>,
    children: Vec<usize>,
}

impl Entry {
    fn state(&self) -> NodeState {
        state_of(self.unknowns, self.absent).into()
    }

    fn contributes(&self, child: &Entry) -> bool {
        !child.function
            && child.state() == NodeState::Known
            && self
                .once
                .as_ref()
                .is_none_or(|once| once.contains(&child.node))
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

/// Snapshot cost labels: each size dimension renders as a name unique to it and stable across runs, so identical
/// text always names the same dimension. A quantity's name is its report label, with characters outside
/// `[A-Za-z0-9_]` replaced by `_`, then `$`, the quantity (`l` length, `k` keys, `v` value), the measured value's
/// source span `<start>_<end>` and a hash of its file's project-relative path. The envelope stays `N`, and recurrence
/// markers render as `recursion$r<index>`. The report keeps its own labels.
pub struct Labels {
    names: HashMap<u64, String>,
}

impl Labels {
    pub fn of(analysis: &Analysis<'_, '_>) -> Labels {
        let names = analysis
            .values
            .quantity_dimensions()
            .map(|(id, value, quantity)| {
                let mut name: String = analysis
                    .values
                    .label(id)
                    .chars()
                    .map(|character| match character.is_ascii_alphanumeric() {
                        true => character,
                        false => '_',
                    })
                    .collect();

                if !name.starts_with(|character: char| character.is_ascii_alphabetic()) {
                    name.insert(0, '_');
                }

                let quantity = match quantity {
                    SizeQuantity::Length => 'l',
                    SizeQuantity::Keys => 'k',
                    SizeQuantity::Value => 'v',
                };
                let origin = match analysis.values.origin_of_value(value) {
                    Some(origin) => format!(
                        "{}_{}_{:08x}",
                        origin.start,
                        origin.end,
                        path_hash(&analysis.project.file(origin.file).relative)
                    ),
                    None => format!("d{id}"),
                };

                (id, format!("{name}${quantity}{origin}"))
            })
            .collect();

        Labels { names }
    }

    pub fn name(&self, id: u64) -> String {
        match id {
            u64::MAX => "N".to_string(),
            id if id >= RECURRENCE_FLOOR => format!("recursion$r{}", RECURRENCE_BASE - id),
            id => self
                .names
                .get(&id)
                .cloned()
                .unwrap_or_else(|| format!("size$d{id}")),
        }
    }

    pub fn text(&self, cost: &Cost) -> String {
        cost.text_with(&|id| self.name(id))
    }
}

/// FNV-1a over the path's bytes: a fixed hash, so labels are identical across runs and platforms.
fn path_hash(path: &str) -> u32 {
    path.bytes().fold(0x811c_9dc5, |hash, byte| {
        (hash ^ u32::from(byte)).wrapping_mul(0x0100_0193)
    })
}

pub fn snapshot_rows(analysis: &mut Analysis<'_, '_>) -> Vec<NodeRow> {
    let functions = analysis.reportable();

    // Under `record_nodes`, every reportable function's nodes are recorded once, from the evaluation of its root
    // summary key: summaries left from earlier summarization are dropped so each root key evaluates in this pass, and
    // the root keys are registered before any evaluation, so a root first reached as another root's callee records
    // there.
    if analysis.options.record_nodes {
        if analysis.has_summary_state() {
            analysis.reset_between_passes();
        }

        analysis.register_recorded_roots(&functions);
    }

    let mut entries = Vec::new();
    let mut located: HashMap<(FileId, NodeId), usize> = HashMap::new();
    let mut reportable = HashSet::with_capacity(functions.len());

    for (file, function) in functions {
        let row = report_rows_of(analysis, &[(file, function)])
            .pop()
            .expect("one report row per function");

        // A function whose cost a directive sets reads that cost (§3.3); its body's nodes record in the raw
        // summarization only.
        if row.mark.is_some() {
            analysis.summarize_with(file, function, Substitutions::new(), true);
        }

        let absent = row.state == State::Unknown;
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
            asserted: row.asserted,
            function: true,
            once: None,
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

        let once = loop_phases_of(analysis.kind_of_node(origin.file, record.node)).map(|phases| {
            phases
                .initialize
                .into_iter()
                .chain(phases.iterable)
                .collect()
        });

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
            once,
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
    let labels = Labels::of(analysis);
    let mut rows: Vec<NodeRow> = entries
        .iter()
        .map(|entry| {
            let state = entry.state();
            let text = labels.text(&entry.cost);
            let mut contributions: Vec<(NodeKey, String)> = match state {
                NodeState::Partial => entry
                    .children
                    .iter()
                    .map(|child| &entries[*child])
                    .filter(|child| entry.contributes(child))
                    .map(|child| (child.key.clone(), labels.text(&child.cost)))
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

use std::collections::{HashMap, HashSet};

use indexmap::IndexMap;
use oxc_semantic::NodeId;

use crate::budgets::BudgetContext;
use crate::cost::{Part, Reading};
use crate::declarations::{Binding, Declarations};
use crate::directives::PerfTag;
use crate::project::{FileId, Project};
use crate::summaries::{Substitutions, SummaryKey};
use crate::tsc::{Query, TscAnswer};
use crate::types::{QueryKind, TscPass};

#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum TypeMode {
    Auto,
    Tsc,
    Syntactic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    pub minimum_exponent: u32,
    pub types: TypeMode,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats(IndexMap<String, u32>);

impl Stats {
    pub fn count(&mut self, label: &str) {
        *self.0.entry(label.to_string()).or_insert(0) += 1;
    }

    pub fn lines(&self) -> Vec<String> {
        let mut entries: Vec<(&String, &u32)> = self.0.iter().collect();

        entries.sort_by_key(|(_, count)| std::cmp::Reverse(**count));

        entries
            .into_iter()
            .map(|(label, count)| format!("{count:>5}  {label}"))
            .collect()
    }
}

pub struct Analysis<'p, 'a> {
    pub project: &'p Project<'a>,
    pub declarations: Declarations<'a>,
    pub options: Options,
    pub stats: Stats,
    pub(crate) tag_cache: HashMap<(FileId, NodeId), Vec<PerfTag>>,
    pub(crate) pass: TscPass,
    pub(crate) needed: IndexMap<(FileId, u32, u32, QueryKind), Query>,
    pub(crate) answers: HashMap<(FileId, u32, u32, QueryKind), Option<TscAnswer>>,
    pub tsc_info: String,
    pub(crate) summaries: HashMap<SummaryKey, Reading>,
    pub(crate) stack: Vec<SummaryKey>,
    pub(crate) minimum_hit: usize,
    pub(crate) pending_cycle: Vec<SummaryKey>,
    pub(crate) current_substitutions: Substitutions,
    pub budget_context: Option<BudgetContext>,
    pub share_bindings: Vec<Binding>,
    pub(crate) pending_scoped: HashMap<(FileId, NodeId), Part>,
    pub(crate) bound_seen: HashSet<(FileId, NodeId)>,
    pub(crate) children: HashMap<FileId, Vec<Vec<NodeId>>>,
    pub(crate) replays_type_answers: bool,
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn new(project: &'p Project<'a>, options: Options) -> Self {
        Analysis {
            project,
            declarations: Declarations::new(project),
            options,
            stats: Stats::default(),
            tag_cache: HashMap::new(),
            pass: TscPass::Off,
            needed: IndexMap::new(),
            answers: HashMap::new(),
            tsc_info: String::new(),
            summaries: HashMap::new(),
            stack: Vec::new(),
            minimum_hit: usize::MAX,
            pending_cycle: Vec::new(),
            current_substitutions: Substitutions::new(),
            budget_context: None,
            share_bindings: Vec::new(),
            pending_scoped: HashMap::new(),
            bound_seen: HashSet::new(),
            children: HashMap::new(),
            replays_type_answers: false,
        }
    }
}

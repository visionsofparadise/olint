use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};
use oxc_semantic::NodeId;

use crate::budgets::BudgetContext;
use crate::cost::Part;
use crate::declarations::{Binding, Declarations, FunctionId};
use crate::directives::PerfTag;
use crate::effects::{Effects, Storage};
use crate::project::{FileId, Project};
use crate::summaries::{Scheduler, Substitutions, SummaryId, SummaryKey, SummaryRecord};
use crate::tsc::{Query, TscAnswer};
use crate::types::{QueryKind, TscPass};
use crate::unknowns::Unknowns;
use crate::values::Values;

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
        let count = self.0.entry(label.to_string()).or_insert(0);
        *count = count.saturating_add(1);
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

#[path = "analysis_work.rs"]
pub mod work;

pub struct Analysis<'p, 'a> {
    pub project: &'p Project<'a>,
    pub declarations: Declarations<'a>,
    pub options: Options,
    pub stats: Stats,
    pub warnings: IndexSet<String>,
    pub errors: IndexSet<String>,
    pub(crate) tag_cache: HashMap<(FileId, NodeId), Vec<PerfTag>>,
    pub(crate) pass: TscPass,
    pub(crate) needed: IndexMap<(FileId, u32, u32, QueryKind), Query>,
    pub(crate) answers: HashMap<(FileId, u32, u32, QueryKind), Option<TscAnswer>>,
    pub tsc_info: String,
    pub(crate) summaries: HashMap<SummaryKey, SummaryId>,
    pub summaries_arena: Vec<SummaryRecord>,
    pub unknowns: Unknowns,
    pub traces: crate::trace::TraceArena,
    pub values: Values,
    pub(crate) root_sizes: Option<Vec<crate::cost::Cost>>,
    pub current_effects: Effects,
    pub(crate) scheduler: Scheduler,
    pub(crate) current_substitutions: Substitutions,
    pub budget_context: Option<BudgetContext>,
    pub share_bindings: Vec<Binding>,
    pub(crate) pending_scoped: HashMap<(FileId, NodeId), Part>,
    pub(crate) bound_seen: HashSet<(FileId, NodeId)>,
    pub(crate) children: HashMap<FileId, Vec<Vec<NodeId>>>,
    pub(crate) isolated_bindings: HashMap<(Binding, NodeId), bool>,
    pub(crate) budget_storage: HashMap<FunctionId, Storage>,
    pub(crate) dynamic_scopes: HashMap<(FileId, NodeId), (bool, bool)>,
    pub(crate) unclassified_writes: HashMap<(Binding, Option<NodeId>), bool>,
    pub(crate) prototype_members: crate::values::PrototypeMembers<'a>,
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn new(project: &'p Project<'a>, options: Options) -> Self {
        Analysis {
            project,
            declarations: Declarations::new(project),
            options,
            stats: Stats::default(),
            warnings: IndexSet::new(),
            errors: IndexSet::new(),
            tag_cache: HashMap::new(),
            pass: TscPass::Off,
            needed: IndexMap::new(),
            answers: HashMap::new(),
            tsc_info: String::new(),
            summaries: HashMap::new(),
            summaries_arena: Vec::new(),
            unknowns: Unknowns::default(),
            traces: crate::trace::TraceArena::default(),
            values: Values::default(),
            root_sizes: None,
            current_effects: Effects::default(),
            scheduler: Scheduler::default(),
            current_substitutions: Substitutions::new(),
            budget_context: None,
            share_bindings: Vec::new(),
            pending_scoped: HashMap::new(),
            bound_seen: HashSet::new(),
            children: HashMap::new(),
            isolated_bindings: HashMap::new(),
            budget_storage: HashMap::new(),
            dynamic_scopes: HashMap::new(),
            unclassified_writes: HashMap::new(),
            prototype_members: HashMap::new(),
        }
    }
}

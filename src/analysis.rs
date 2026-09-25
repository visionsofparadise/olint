use std::collections::{HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};
use oxc_semantic::NodeId;

use crate::budgets::BudgetContext;
use crate::cost::{Part, Reading};
use crate::declarations::{Binding, Declarations, FunctionId};
use crate::directives::PerfTag;
use crate::effects::{BudgetStorage, Effects};
use crate::flow::Completion;
use crate::project::{FileId, Project};
use crate::summaries::{Scheduler, Substitutions, SummaryId, SummaryKey, SummaryRecord};
use crate::tsc::{Query, TscAnswer};
use crate::types::{QueryKind, TscPass};
use crate::unknowns::Unknowns;
use crate::values::Values;
use crate::walker::FinalizerReplacements;

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
    pub(crate) enclosing_factors: Vec<(FileId, NodeId, crate::cost::Cost, bool)>,
    pub(crate) produced: Option<crate::summaries::Produced>,
    pub(crate) deferred_reading: Option<Reading>,
    pub(crate) deferred_storage: Option<crate::effects::Storage>,
    pub(crate) latent_storage: HashMap<crate::summaries::SummaryId, crate::effects::Storage>,
    pub(crate) latent_readings: HashMap<crate::summaries::SummaryId, Reading>,
    pub(crate) suspensions: HashMap<(FileId, NodeId), bool>,
    pub(crate) latent_returns: HashMap<(FunctionId, u64), crate::summaries::LatentSources>,
    pub(crate) pending_scoped: HashMap<(FileId, NodeId, crate::cost::ExecutionPhase), Part>,
    pub(crate) pending_effects:
        HashMap<SummaryKey, Option<Vec<(crate::unknowns::SourceSpan, Effects)>>>,
    pub(crate) interference: Effects,
    pub(crate) pending_enabled: Option<bool>,
    pub(crate) storage_arguments: Vec<(Binding, crate::values::ValueId)>,
    pub(crate) collecting_pending: bool,
    pub(crate) scheduling: HashMap<SummaryKey, bool>,
    pub(crate) bound_seen: HashSet<(FileId, NodeId)>,
    pub(crate) active_bounds: HashSet<(FileId, NodeId)>,
    pub(crate) repeating_bodies: HashMap<(FileId, NodeId), bool>,
    pub(crate) children: HashMap<FileId, Vec<Vec<NodeId>>>,
    pub(crate) finalizer_replacements: FinalizerReplacements,
    pub(crate) completion_escapes:
        HashMap<(FileId, NodeId, Completion, NodeId), Option<Completion>>,
    pub(crate) escape_depth_exhausted: bool,
    pub(crate) isolated_bindings: HashMap<(Binding, NodeId), bool>,
    pub(crate) budget_storage: HashMap<FunctionId, BudgetStorage>,
    pub(crate) dynamic_scopes: HashMap<(FileId, NodeId), (bool, bool)>,
    pub(crate) unclassified_writes: HashMap<(Binding, Option<NodeId>), bool>,
    pub(crate) prototype_members: crate::values::PrototypeMembers<'a>,
    pub regex_answers: HashMap<crate::regex::RegexRequest, crate::regex::RegexAnswer>,
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
            enclosing_factors: Vec::new(),
            produced: None,
            deferred_reading: None,
            deferred_storage: None,
            latent_storage: HashMap::new(),
            latent_readings: HashMap::new(),
            suspensions: HashMap::new(),
            latent_returns: HashMap::new(),
            pending_scoped: HashMap::new(),
            pending_effects: HashMap::new(),
            interference: Effects::default(),
            pending_enabled: None,
            storage_arguments: Vec::new(),
            collecting_pending: false,
            scheduling: HashMap::new(),
            bound_seen: HashSet::new(),
            active_bounds: HashSet::new(),
            repeating_bodies: HashMap::new(),
            children: HashMap::new(),
            finalizer_replacements: FinalizerReplacements::new(),
            completion_escapes: HashMap::new(),
            escape_depth_exhausted: false,
            isolated_bindings: HashMap::new(),
            budget_storage: HashMap::new(),
            dynamic_scopes: HashMap::new(),
            unclassified_writes: HashMap::new(),
            prototype_members: HashMap::new(),
            regex_answers: HashMap::new(),
        }
    }
}

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, FormalParameter, MethodDefinitionKind,
    PropertyKind,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::analysis::work::{Charges, Event, FallbackCredit, Limits, Snapshot, WorkBudget};
use crate::analysis::{Analysis, Stats};
use crate::cost::{Cost, CostError, Part, Preference, Reading};
use crate::declarations::{
    parameters_of, Binding, Declaration, FunctionId, FunctionNode, ParameterNode, TargetSet,
};
use crate::directives::{cost_tag_of, PerfTag};
use crate::effects::Effects;
use crate::flow::Completion;
use crate::project::{FileId, Site};
use crate::recurrences::{
    solution_of, weaker_relation_of, ArgumentBounds, ArgumentRelation, CallStep, RecurrenceEdge,
    RecurrenceEquation, RecurrenceSolution, MAXIMUM_RECURRENCE_MEMBERS,
};
use crate::syntax::unwrap;
use crate::tsc::{Query, TscError, TscReply};
use crate::types::TscPass;
use crate::unknowns::UnknownReason;
use crate::values::{
    ArgumentFacts, ConstructionPlan, Definedness, SizeQuantity, ValueFacts, ValueId,
    RECURRENCE_BASE,
};
use crate::walker::tagged_reading_of;

const MAXIMUM_PATTERN_ALIASES: usize = 8;
const MAXIMUM_LATENT_DEPTH: usize = 6;
const RESUMPTIONS: [&str; 3] = ["next", "return", "throw"];
const MAXIMUM_RECURRENCE_ROUNDS: usize = 4;

#[cfg(test)]
#[path = "summaries.test.rs"]
mod tests;

pub type Substitutions = HashMap<Binding, ArgumentFacts>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SummaryId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryRecord {
    pub reading: Reading,
    pub result: ValueFacts,
    pub effects: Effects,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Latent {
    pub work: Part,
    pub yields: Option<Cost>,
    pub effects: Effects,
    pub record: Option<SummaryId>,
    deferred: Option<Reading>,
}

impl Latent {
    fn unresolved(work: Part) -> Latent {
        Latent {
            work,
            yields: None,
            effects: Effects::unknown(),
            record: None,
            deferred: None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Deferral {
    Excluded,
    Consumed,
    Escaped,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Produced {
    pub count: Option<Cost>,
    pub yielded: bool,
}

impl Produced {
    pub fn joined(self, count: Option<Cost>) -> Produced {
        let count = match (self.yielded, self.count, count) {
            (false, _, count) => count,
            (true, Some(held), Some(count)) => Cost::maximum(vec![held, count]).ok(),
            _ => None,
        };

        Produced {
            count,
            yielded: true,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LatentSources {
    pub direct: bool,
    pub parameters: Vec<usize>,
}

impl LatentSources {
    fn join(&mut self, other: LatentSources) {
        self.direct |= other.direct;

        for index in other.parameters {
            if !self.parameters.contains(&index) {
                self.parameters.push(index);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LatentKey {
    pub work: Cost,
    pub cost_error: Option<CostError>,
    pub unknowns: crate::unknowns::SemanticKeyId,
    pub yields: Option<Cost>,
    pub channels: Vec<LatentChannelKey>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LatentChannelKey {
    pub phase: crate::cost::ExecutionPhase,
    pub completion: Completion,
    pub cost: Cost,
    pub cost_error: Option<CostError>,
    pub preference: Preference,
    pub unknowns: crate::unknowns::SemanticKeyId,
    pub retained: crate::unknowns::SemanticKeyId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArgumentKey {
    pub binding: Binding,
    pub value: ValueFacts,
    pub cost: Option<Cost>,
    pub cost_error: Option<CostError>,
    pub unknowns: crate::unknowns::SemanticKeyId,
    pub preference: Preference,
    pub definedness: Definedness,
    pub latent_effects: Option<Effects>,
    pub latent: Option<LatentKey>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SummaryKey {
    pub generation: u64,
    pub raw: bool,
    pub root_sizes: Vec<Cost>,
    pub function: FunctionId,
    pub substitutions: Vec<ArgumentKey>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ConstructionKey {
    class: (FileId, NodeId),
    inherited: bool,
    root_sizes: Vec<Cost>,
    captures: Vec<ArgumentKey>,
}

const MAXIMUM_CONSTRUCTION_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TscRounds {
    pub sites: usize,
    pub rounds: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TaskId(usize);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RecurrenceKey {
    task: TaskId,
    active: Vec<TaskId>,
}

struct RecurrenceFrame {
    key: RecurrenceKey,
    children: Vec<RecurrenceKey>,
    next: usize,
}

struct RecurrenceMarkers {
    members: Vec<TaskId>,
    effects: Effects,
    solved: Option<Vec<Cost>>,
    provenance: Vec<Option<crate::unknowns::UnknownId>>,
    unresolved: bool,
    steps: HashMap<(TaskId, TaskId, crate::unknowns::SourceSpan), Vec<CallStep>>,
    bounds: HashMap<(TaskId, TaskId, crate::unknowns::SourceSpan), ArgumentBounds>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TaskState {
    Queued,
    Evaluating,
    Waiting,
    Ready(SummaryId),
}

struct SummaryTask {
    key: SummaryKey,
    root_id: usize,
    inputs: Substitutions,
    state: TaskState,
    dependencies: HashSet<TaskId>,
    pending_children: usize,
    recurrence_members: Arc<HashSet<FunctionId>>,
    stable_loops: HashMap<(FileId, NodeId), (Reading, Effects)>,
    invocations: HashMap<(crate::unknowns::SourceSpan, FunctionId), (Vec<TaskId>, bool)>,
    waiters: HashSet<TaskId>,
    credit: Option<FallbackCredit>,
    fallback: bool,
    passes: u64,
    produced: Option<Produced>,
    deferred_reading: Option<Reading>,
}

#[derive(Clone)]
enum CallbackDescriptor {
    Source {
        function: FunctionId,
        captured: Substitutions,
        generation: u64,
    },
    PromiseResolve {
        generation: u64,
    },
}

impl CallbackDescriptor {
    fn generation(&self) -> u64 {
        match self {
            Self::Source { generation, .. } | Self::PromiseResolve { generation } => *generation,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SchedulerLimits {
    pub work: Limits,
    pub specializations_per_function: usize,
}

impl Default for SchedulerLimits {
    fn default() -> Self {
        Self {
            work: Limits::uniform(4_000_000)
                .with(Event::TaskKey, 20_000)
                .with(Event::BodyPass, 100_000)
                .with(Event::CallbackDescriptor, 20_000)
                .with(Event::RecurrenceContext, 4096)
                .with(Event::CaptureEdge, 200_000),
            specializations_per_function: 32,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SchedulerStats {
    pub generation: u64,
    pub work: Snapshot,
    pub tasks: usize,
    pub ready: usize,
    pub waiting: usize,
    pub queued: usize,
    pub maximum_body_passes: u64,
}

pub(crate) struct Scheduler {
    generation: u64,
    limits: SchedulerLimits,
    work: WorkBudget,
    tasks: Vec<SummaryTask>,
    keys: HashMap<SummaryKey, TaskId>,
    root_ids: HashMap<Vec<Cost>, usize>,
    closed_ready: HashMap<(FunctionId, bool, usize), TaskId>,
    queue: VecDeque<TaskId>,
    waiting: HashSet<TaskId>,
    active: Option<TaskId>,
    missing: HashSet<TaskId>,
    pending_serial: u64,
    component: HashSet<TaskId>,
    recurrence_context: Option<RecurrenceKey>,
    recurrence_admitted: HashSet<RecurrenceKey>,
    recurrence_records: HashMap<RecurrenceKey, (Reading, Effects)>,
    recurrence_missing: HashSet<RecurrenceKey>,
    recurrence_fallbacks: HashMap<TaskId, (Reading, Effects)>,
    recurrence_markers: Option<RecurrenceMarkers>,
    runtime: HashSet<(FunctionId, FunctionId)>,
    sites: HashSet<(FunctionId, crate::unknowns::SourceSpan, FunctionId)>,
    function_counts: HashMap<(FunctionId, bool, Vec<Cost>), usize>,
    exhausted: bool,
    fallback_active: bool,
    active_credit: Option<FallbackCredit>,
    callbacks: Vec<CallbackDescriptor>,
    promise_resolver: Option<usize>,
    assimilating: HashSet<(FileId, NodeId)>,
    callback_keys: HashMap<SummaryKey, usize>,
    callback_values: HashMap<ValueId, usize>,
    local_records: HashMap<TaskId, SummaryRecord>,
    body_sizes: HashMap<FunctionId, u64>,
    constructions: HashMap<ConstructionKey, (Reading, Effects)>,
    initializing: HashSet<((FileId, NodeId), bool)>,
    constructing: Vec<(FileId, NodeId)>,
}

impl Default for Scheduler {
    fn default() -> Self {
        Self::new(SchedulerLimits::default(), 0)
    }
}

impl Scheduler {
    fn new(limits: SchedulerLimits, generation: u64) -> Self {
        Self {
            generation,
            limits,
            work: WorkBudget::new(limits.work),
            tasks: Vec::new(),
            keys: HashMap::new(),
            root_ids: HashMap::new(),
            closed_ready: HashMap::new(),
            queue: VecDeque::new(),
            waiting: HashSet::new(),
            active: None,
            missing: HashSet::new(),
            pending_serial: 0,
            component: HashSet::new(),
            recurrence_context: None,
            recurrence_admitted: HashSet::new(),
            recurrence_records: HashMap::new(),
            recurrence_missing: HashSet::new(),
            recurrence_fallbacks: HashMap::new(),
            recurrence_markers: None,
            runtime: HashSet::new(),
            sites: HashSet::new(),
            function_counts: HashMap::new(),
            exhausted: false,
            fallback_active: false,
            active_credit: None,
            callbacks: Vec::new(),
            promise_resolver: None,
            assimilating: HashSet::new(),
            callback_keys: HashMap::new(),
            callback_values: HashMap::new(),
            local_records: HashMap::new(),
            body_sizes: HashMap::new(),
            constructions: HashMap::new(),
            initializing: HashSet::new(),
            constructing: Vec::new(),
        }
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn function_inputs(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        mut substitutions: Substitutions,
    ) -> Substitutions {
        let mut scopes = vec![function];

        scopes.extend(self.enclosing_functions_of(file, function.node_id()));

        for scope in scopes {
            let Some(parameters) = parameters_of(scope) else {
                continue;
            };

            let patterns = parameters
                .items
                .iter()
                .map(|parameter| {
                    (
                        &parameter.pattern,
                        matches!(parameter.pattern, BindingPattern::BindingIdentifier(_)),
                    )
                })
                .chain(
                    parameters
                        .rest
                        .iter()
                        .map(|rest| (&rest.rest.argument, false)),
                );

            for (pattern, plain) in patterns {
                for identifier in pattern.get_binding_identifiers() {
                    let Some(symbol) = identifier.symbol_id.get() else {
                        continue;
                    };
                    let binding = Binding::Symbol { file, symbol };

                    if let std::collections::hash_map::Entry::Vacant(entry) =
                        substitutions.entry(binding)
                    {
                        let origin = self.source_span(file, identifier.span);
                        let mut value = self.values.at(origin);

                        if plain {
                            value.size = self
                                .values
                                .quantity(
                                    value.value,
                                    SizeQuantity::Value,
                                    identifier.name.to_string(),
                                )
                                .ok();
                        }

                        entry.insert(ArgumentFacts {
                            value,
                            callback: None,
                            preference: Preference::Absent,
                            definedness: Definedness::Unknown,
                        });
                    }
                }
            }
        }

        substitutions
    }

    pub fn bind_function_cost(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        cost: &Cost,
    ) -> Result<Cost, CostError> {
        let inputs = self.function_inputs(file, function, Substitutions::new());
        let saved = self.root_sizes.take();
        let result = self.bind_cost_in(cost, &inputs);
        self.root_sizes = saved;

        result
    }

    pub(crate) fn bind_cost_in(
        &mut self,
        cost: &Cost,
        inputs: &Substitutions,
    ) -> Result<Cost, CostError> {
        let mut names = HashMap::new();
        let mut available = std::collections::HashSet::new();
        let referenced = cost.names();
        let mut roots = Vec::new();
        let mut inputs: Vec<_> = inputs.iter().collect();

        inputs.sort_by_key(|(binding, _)| {
            let depth = match self.declarations.of_binding(self.project, **binding) {
                Some(Declaration::Parameter { file, function, .. }) => self
                    .project
                    .file(file)
                    .semantic
                    .nodes()
                    .ancestor_ids(function.node_id())
                    .count(),
                _ => 0,
            };

            (depth, self.binding_name_of(**binding))
        });

        for (binding, facts) in inputs {
            let name = self.binding_name_of(*binding);

            names.remove(&name);
            names.remove(&format!("{name}.length"));

            let length_alias = self
                .declarations
                .of_binding(self.project, *binding)
                .is_some_and(|declaration| {
                    matches!(declaration, Declaration::Parameter { parameter: crate::declarations::ParameterNode::Formal(parameter), .. } if !matches!(parameter.pattern, BindingPattern::BindingIdentifier(_)))
                        || matches!(self.declared_type_of_binding(declaration, 0).kind, crate::declared_types::Kind::String | crate::declared_types::Kind::Array)
                });

            available.insert(name.clone());

            if length_alias {
                available.insert(format!("{name}.length"));
            } else {
                available.remove(&format!("{name}.length"));
            }

            if let Some(size) = &facts.value.size {
                names.insert(name.clone(), size.clone());

                if length_alias {
                    names.insert(format!("{name}.length"), size.clone());
                }

                if length_alias && referenced.contains(&format!("{name}.length")) {
                    self.values.prefer_length_label(facts.value.value);
                }

                roots.push(size.clone());
            }
        }

        if let Some(active) = &self.root_sizes {
            roots = active.clone();
        }

        if roots.is_empty() {
            roots.push(Cost::dimension(u64::MAX, crate::cost::Domain::Size));
        }

        if let Some(name) = referenced.iter().find(|name| !available.contains(*name)) {
            return Err(CostError::UnknownName(name.clone()));
        }

        cost.bind(
            &|_| Some(Cost::dimension(u64::MAX, crate::cost::Domain::Size)),
            &[Cost::dimension(u64::MAX, crate::cost::Domain::Size)],
        )?;

        cost.bind(&|name| names.get(name).cloned(), &roots)
            .map_err(|error| match error {
                CostError::UnknownName(name) if available.contains(&name) => {
                    CostError::UnresolvedQuantity(name)
                }
                error => error,
            })
    }

    pub(crate) fn bind_current_cost(&mut self, cost: &Cost) -> Result<Cost, CostError> {
        self.bind_cost_in(cost, &self.current_substitutions.clone())
    }

    fn finish_reading(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        mut reading: Reading,
        inputs: &Substitutions,
    ) -> Reading {
        let origin = self.source_span(file, self.kind_of_node(file, function.node_id()).span());

        reading.set(
            crate::cost::ExecutionPhase::Immediate,
            Completion::Normal,
            Part {
                origin: Some(origin),
                ..reading.main()
            },
        );

        for (_, _, part) in &mut reading.completions {
            part.origin = part.origin.or(Some(origin));

            match self.bind_cost_in(&part.cost, inputs) {
                Ok(cost) => part.cost = cost,
                Err(error) => part.cost_error = Some(error),
            }

            if part.cost_error.is_some() {
                let failure = self
                    .unknowns
                    .origin(origin, UnknownReason::ResourceExhaustion);
                part.unknowns = self.unknowns.join(part.unknowns, Some(failure));
            }
        }

        reading
    }
    fn key_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: &Substitutions,
    ) -> Result<SummaryKey, crate::unknowns::SemanticError> {
        let mut facts: Vec<_> = substitutions
            .iter()
            .map(|(binding, facts)| {
                let mut value = facts.value.clone();

                value
                    .targets
                    .known
                    .sort_by_key(|target| (target.file.0, target.node.index()));
                value.targets.known.dedup();

                let latent_effects = value
                    .latent
                    .and_then(|id| self.summaries_arena.get(id.0 as usize))
                    .map(|record| {
                        let mut effects = record.effects.clone();

                        effects.binding_writes.sort_by_key(|binding| match binding {
                            Binding::Symbol { file, symbol } => (file.0, symbol.index()),
                        });
                        effects.binding_writes.dedup();
                        effects.member_writes.sort();
                        effects.member_writes.dedup();
                        effects.escapes.sort();
                        effects.escapes.dedup();
                        effects.unknown_reachable.sort();
                        effects.unknown_reachable.dedup();

                        effects
                    });
                let latent = match value
                    .latent
                    .and_then(|id| self.summaries_arena.get(id.0 as usize))
                    .map(|record| (record.reading.clone(), record.result.size.clone()))
                {
                    Some((reading, yields)) => {
                        let work = reading.latent(&mut self.unknowns, &mut self.traces);
                        let deferred = value
                            .latent
                            .and_then(|id| self.latent_readings.get(&id))
                            .cloned()
                            .unwrap_or_else(|| Reading::of_part(work.clone()));
                        let mut channels = Vec::new();

                        for (phase, completion, part) in deferred.completions {
                            let unknowns =
                                self.unknowns.semantic_key(part.unknowns, &mut || {
                                    self.scheduler
                                        .work
                                        .admit(Charges::one(Event::SemanticIdentity, 1))
                                        .is_ok()
                                })?;
                            let retained =
                                self.unknowns.semantic_key(part.retained, &mut || {
                                    self.scheduler
                                        .work
                                        .admit(Charges::one(Event::SemanticIdentity, 1))
                                        .is_ok()
                                })?;

                            channels.push(LatentChannelKey {
                                phase,
                                completion,
                                cost: part.cost,
                                cost_error: part.cost_error,
                                preference: part.preference,
                                unknowns,
                                retained,
                            });
                        }

                        Some(LatentKey {
                            work: work.cost,
                            cost_error: work.cost_error,
                            unknowns: self.unknowns.semantic_key(work.unknowns, &mut || {
                                self.scheduler
                                    .work
                                    .admit(Charges::one(Event::SemanticIdentity, 1))
                                    .is_ok()
                            })?,
                            yields,
                            channels,
                        })
                    }
                    None => None,
                };
                value.latent = None;

                Ok(ArgumentKey {
                    binding: *binding,
                    value,
                    cost: facts.callback.as_ref().map(|part| part.cost.clone()),
                    cost_error: facts
                        .callback
                        .as_ref()
                        .and_then(|part| part.cost_error.clone()),
                    unknowns: self.unknowns.semantic_key(
                        facts.callback.as_ref().and_then(|part| part.unknowns),
                        &mut || {
                            self.scheduler
                                .work
                                .admit(Charges::one(Event::SemanticIdentity, 1))
                                .is_ok()
                        },
                    )?,
                    preference: facts.preference,
                    definedness: facts.definedness,
                    latent_effects,
                    latent,
                })
            })
            .collect::<Result<Vec<_>, crate::unknowns::SemanticError>>()?;

        facts.sort_by_key(|facts| match facts.binding {
            Binding::Symbol { file, symbol } => (file.0, symbol.index()),
        });

        Ok(SummaryKey {
            generation: self.scheduler.generation,
            raw: false,
            root_sizes: self.root_sizes.clone().unwrap_or_default(),
            function: FunctionId {
                file,
                node: function.node_id(),
            },
            substitutions: facts,
        })
    }

    fn store_summary(
        &mut self,
        key: SummaryKey,
        reading: Reading,
        mut effects: Effects,
        produced: Option<Produced>,
        deferred_reading: Option<Reading>,
    ) -> SummaryId {
        effects
            .binding_writes
            .retain(|binding| !self.is_declared_within(*binding, key.function));

        let span = self
            .kind_of_node(key.function.file, key.function.node)
            .span();
        let origin = self.source_span(key.function.file, span);
        let mut result = self.values.at(origin);
        let id =
            SummaryId(u32::try_from(self.summaries_arena.len()).expect("summary arena fits u32"));

        if let Some(produced) = produced {
            result.latent = Some(id);
            result.size = produced.count;
        }

        self.summaries_arena.push(SummaryRecord {
            reading,
            result,
            effects,
        });

        if let Some(deferred) = deferred_reading {
            self.latent_readings.insert(id, deferred);
        }

        self.summaries.insert(key, id);

        id
    }

    fn binding_name_of(&self, binding: Binding) -> String {
        match binding {
            Binding::Symbol { file, symbol } => self
                .project
                .file(file)
                .semantic
                .scoping()
                .symbol_name(symbol)
                .to_string(),
        }
    }

    pub fn summarize(&mut self, file: FileId, function: FunctionNode<'a>) -> Reading {
        self.summarize_with(file, function, Substitutions::new(), false)
    }

    pub fn summarize_with(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: Substitutions,
        raw: bool,
    ) -> Reading {
        let substitutions = self.function_inputs(file, function, substitutions);
        let is_root = self.root_sizes.is_none();

        if is_root {
            let mut roots: Vec<_> = substitutions
                .values()
                .filter_map(|facts| facts.value.size.clone())
                .collect();

            roots.sort_by_key(Cost::structural_key);
            roots.dedup();

            if roots.is_empty() {
                roots.push(Cost::dimension(u64::MAX, crate::cost::Domain::Size));
            }

            self.root_sizes = Some(roots);
        }

        let reading = self.summarize_in(file, function, substitutions, raw);

        if is_root {
            self.root_sizes = None;
        }

        reading
    }

    pub fn summary_records_for(&self, function: FunctionId) -> Vec<&SummaryRecord> {
        self.summaries
            .iter()
            .filter(|(key, _)| key.function == function)
            .map(|(_, id)| &self.summaries_arena[id.0 as usize])
            .collect()
    }
    pub fn member_local_records_for(&self, function: FunctionId) -> Vec<&SummaryRecord> {
        self.scheduler
            .local_records
            .iter()
            .filter(|(id, _)| self.scheduler.tasks[id.0].key.function == function)
            .map(|(_, record)| record)
            .collect()
    }
    pub fn scheduler_stats(&self) -> SchedulerStats {
        SchedulerStats {
            generation: self.scheduler.generation,
            work: self.scheduler.work.snapshot(),
            tasks: self.scheduler.tasks.len(),
            ready: self
                .scheduler
                .tasks
                .iter()
                .filter(|task| matches!(task.state, TaskState::Ready(_)))
                .count(),
            waiting: self.scheduler.waiting.len(),
            queued: self.scheduler.queue.len(),
            maximum_body_passes: self
                .scheduler
                .tasks
                .iter()
                .map(|task| task.passes)
                .max()
                .unwrap_or(0),
        }
    }

    pub fn set_scheduler_limits(&mut self, limits: SchedulerLimits) -> Result<(), &'static str> {
        if !self.scheduler.tasks.is_empty() {
            return Err("scheduler limits require an unused generation");
        }

        self.scheduler = Scheduler::new(limits, self.scheduler.generation);

        Ok(())
    }

    pub(crate) fn charge_work(&mut self, event: Event, amount: u64) -> bool {
        self.charge_work_set(Charges::one(event, amount))
    }

    pub(crate) fn fallback_active(&self) -> bool {
        self.scheduler.fallback_active
    }

    pub(crate) fn work_exhausted(&self) -> bool {
        self.scheduler.exhausted
    }

    pub(crate) fn contribution_serial(&self) -> u64 {
        self.scheduler.pending_serial
    }

    pub(crate) fn stable_loop(&mut self, file: FileId, node: NodeId) -> Option<Reading> {
        if !self.fallback_active() {
            return None;
        }

        let active = self.scheduler.active?;
        let (reading, effects) = self.scheduler.tasks[active.0]
            .stable_loops
            .get(&(file, node))?
            .clone();

        self.current_effects.join(&effects);

        Some(reading)
    }

    pub(crate) fn retain_stable_loop(
        &mut self,
        file: FileId,
        node: NodeId,
        serial: u64,
        diagnostics: (usize, usize),
        reading: &Reading,
    ) {
        if self.fallback_active()
            || self.work_exhausted()
            || !self.scheduler.component.is_empty()
            || serial != self.scheduler.pending_serial
            || !self.pending_scoped.is_empty()
            || !self.share_bindings.is_empty()
            || diagnostics != (self.warnings.len(), self.errors.len())
        {
            return;
        }

        if let Some(active) = self.scheduler.active {
            self.scheduler.tasks[active.0].stable_loops.insert(
                (file, node),
                (reading.clone(), self.current_effects.clone()),
            );
        }
    }

    fn charge_work_set(&mut self, charges: Charges) -> bool {
        let result = if self.scheduler.fallback_active {
            match self.scheduler.active_credit.as_mut() {
                Some(credit) => self.scheduler.work.admit_fallback(credit, charges),
                None => return false,
            }
        } else {
            self.scheduler.work.admit(charges)
        };

        if result.is_err() {
            self.scheduler.exhausted = true;

            false
        } else {
            true
        }
    }

    pub(crate) fn function_at(&self, id: FunctionId) -> FunctionNode<'a> {
        match self.kind_of_node(id.file, id.node) {
            AstKind::Function(function) => FunctionNode::Function(function),
            AstKind::ArrowFunctionExpression(function) => FunctionNode::Arrow(function),
            AstKind::Class(class) => FunctionNode::Construction(class),
            _ => unreachable!("summary target is a function"),
        }
    }

    pub(crate) fn deferred_unknown(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
        reason: UnknownReason,
    ) -> Part {
        let part = self.unknown_part(file, span, reason);
        self.current_effects.unknown_global = true;

        part
    }

    fn body_size(&mut self, function: FunctionId) -> Option<u64> {
        if let Some(size) = self.scheduler.body_sizes.get(&function) {
            return Some(*size);
        }

        let mut pending = self.children_of(function.file, function.node);

        if self.scheduler.exhausted {
            return None;
        }

        let mut size = 1u64;

        while let Some(node) = pending.pop() {
            if !self.charge_work(Event::BudgetPrepassNode, 1) {
                return None;
            }

            size = size.saturating_add(1);

            if matches!(
                self.kind_of_node(function.file, node),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                continue;
            }

            pending.extend(self.children_of(function.file, node));
        }

        if self.scheduler.exhausted {
            return None;
        }

        self.scheduler.body_sizes.insert(function, size);

        Some(size)
    }

    fn request_task(&mut self, key: SummaryKey, inputs: Substitutions) -> Option<TaskId> {
        if let Some(id) = self.scheduler.keys.get(&key) {
            return Some(*id);
        }

        let count_key = (key.function, key.raw, key.root_sizes.clone());

        if self.scheduler.fallback_active
            || self
                .scheduler
                .function_counts
                .get(&count_key)
                .copied()
                .unwrap_or(0)
                >= self.scheduler.limits.specializations_per_function
        {
            return None;
        }

        let size = self.body_size(key.function)?;
        let reserved = Charges::one(Event::BodyPass, 1)
            .plus(Event::Publication, 1)
            .ok()?
            .plus(Event::WalkerNode, size.saturating_mul(2))
            .ok()?
            .plus(Event::BudgetPrepassNode, size)
            .ok()?
            .plus(Event::InvocationEvaluation, size)
            .ok()?
            .plus(Event::LatentStep, size.saturating_mul(2))
            .ok()?
            .plus(Event::TraversalEdge, size.saturating_mul(2))
            .ok()?
            .plus(Event::QueuePush, 2)
            .ok()?;
        let ordinary = Charges::one(Event::TaskKey, 1)
            .plus(Event::GraphNode, key.root_sizes.len() as u64)
            .ok()?
            .plus(Event::Specialization, 1)
            .ok()?
            .plus(Event::QueuePush, 1)
            .ok()?;
        let credit = self
            .scheduler
            .work
            .admit_and_reserve(ordinary, reserved)
            .ok()?;
        let id = TaskId(self.scheduler.tasks.len());
        let next_root = self.scheduler.root_ids.len();
        let root_id = *self
            .scheduler
            .root_ids
            .entry(key.root_sizes.clone())
            .or_insert(next_root);

        self.scheduler.tasks.push(SummaryTask {
            key: key.clone(),
            root_id,
            inputs,
            state: TaskState::Queued,
            dependencies: HashSet::new(),
            pending_children: 0,
            recurrence_members: Arc::default(),
            stable_loops: HashMap::new(),
            invocations: HashMap::new(),
            waiters: HashSet::new(),
            credit: Some(credit),
            fallback: false,
            passes: 0,
            produced: None,
            deferred_reading: None,
        });
        self.scheduler.keys.insert(key, id);

        *self.scheduler.function_counts.entry(count_key).or_default() += 1;

        self.scheduler.queue.push_back(id);

        Some(id)
    }

    fn request_reading(&mut self, key: SummaryKey, inputs: Substitutions) -> (Reading, bool) {
        if self.scheduler.active.is_none() {
            if let Some(id) = self.summaries.get(&key) {
                return (self.summaries_arena[id.0 as usize].reading.clone(), false);
            }
        }

        let function = key.function;
        let parent = self.scheduler.active;
        let existing = self.scheduler.keys.get(&key).copied();
        let new_dependency = !self.fallback_active()
            && parent.is_some_and(|parent| {
                existing.is_none_or(|id| !self.scheduler.tasks[parent.0].dependencies.contains(&id))
            });

        if new_dependency
            && !self.charge_work_set(
                Charges::one(Event::DependencyPair, 1)
                    .plus(Event::DependencyWake, 1)
                    .expect("fixed charges fit"),
            )
        {
            return (
                Reading::of_part(self.deferred_unknown(
                    function.file,
                    self.kind_of_node(function.file, function.node).span(),
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        }

        let Some(id) = self.request_task(key, inputs) else {
            return (
                Reading::of_part(self.deferred_unknown(
                    function.file,
                    self.kind_of_node(function.file, function.node).span(),
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        };

        if new_dependency {
            if let Some(parent) = parent {
                self.scheduler.tasks[parent.0].dependencies.insert(id);

                if !matches!(self.scheduler.tasks[id.0].state, TaskState::Ready(_)) {
                    self.scheduler.tasks[parent.0].pending_children += 1;

                    self.scheduler.tasks[id.0].waiters.insert(parent);
                }
            }
        }

        if self.scheduler.component.contains(&id) {
            if let Some(part) = self.marker_part_of(id) {
                return (Reading::of_part(part), true);
            }

            self.current_effects.unknown_global = true;

            return (self.recurrence_reading(id), true);
        }

        if let TaskState::Ready(record) = self.scheduler.tasks[id.0].state {
            let reading = self.summaries_arena[record.0 as usize].reading.clone();
            let recurrence = Arc::clone(&self.scheduler.tasks[id.0].recurrence_members);
            let cyclic = self.scheduler.active.is_some_and(|parent| {
                let cyclic = recurrence.contains(&self.scheduler.tasks[parent.0].key.function);

                self.merge_recurrence_members(parent, recurrence);

                cyclic
            });

            return (reading, cyclic);
        }

        if self.scheduler.fallback_active {
            return (
                Reading::of_part(self.deferred_unknown(
                    function.file,
                    self.kind_of_node(function.file, function.node).span(),
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        }

        if let Some(parent) = self.scheduler.active {
            let _ = parent;

            self.scheduler.missing.insert(id);

            self.scheduler.pending_serial = self.scheduler.pending_serial.saturating_add(1);
            self.current_effects.unknown_global = true;

            return (Reading::empty(), false);
        }

        self.drive_summaries();

        match self.scheduler.tasks[id.0].state {
            TaskState::Ready(record) => (
                self.summaries_arena[record.0 as usize].reading.clone(),
                false,
            ),
            _ => unreachable!("summary driver drains admitted roots"),
        }
    }

    fn summarize_in(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: Substitutions,
        raw: bool,
    ) -> Reading {
        let substitutions = self.function_inputs(file, function, substitutions);
        let Ok(mut key) = self.key_of(file, function, &substitutions) else {
            self.scheduler.exhausted = true;

            return self.unknown_reading(
                file,
                self.kind_of_node(file, function.node_id()).span(),
                UnknownReason::ResourceExhaustion,
            );
        };
        key.raw = raw;

        self.request_reading(key, substitutions).0
    }

    fn publish_task(&mut self, id: TaskId, reading: Reading, effects: Effects) {
        let key = self.scheduler.tasks[id.0].key.clone();
        let mut credit = self.scheduler.tasks[id.0]
            .credit
            .take()
            .expect("task owns publication credit");

        self.scheduler
            .work
            .admit_fallback(&mut credit, Charges::one(Event::Publication, 1))
            .expect("publication reserved at admission");
        self.scheduler
            .work
            .release(&mut credit)
            .expect("task credit is owned");

        let produced = self.scheduler.tasks[id.0].produced.take();
        let deferred = self.scheduler.tasks[id.0].deferred_reading.take();
        let record = self.store_summary(key, reading, effects, produced, deferred);
        self.scheduler.tasks[id.0].state = TaskState::Ready(record);

        let task = &self.scheduler.tasks[id.0];

        if task.key.substitutions.is_empty() && self.closed_function(task.key.function) {
            self.scheduler
                .closed_ready
                .insert((task.key.function, task.key.raw, task.root_id), id);
        }

        self.scheduler.waiting.remove(&id);

        let waiters = std::mem::take(&mut self.scheduler.tasks[id.0].waiters);

        for parent in waiters {
            self.scheduler.tasks[parent.0].pending_children -= 1;

            if self.scheduler.tasks[parent.0].state == TaskState::Waiting
                && self.scheduler.tasks[parent.0].pending_children == 0
            {
                self.enqueue_task(parent);
            }
        }
    }

    fn enqueue_task(&mut self, id: TaskId) {
        if matches!(
            self.scheduler.tasks[id.0].state,
            TaskState::Queued | TaskState::Ready(_)
        ) {
            return;
        }

        if !self.charge_work(Event::QueuePush, 1) {
            self.scheduler.tasks[id.0].fallback = true;
            let task = &mut self.scheduler.tasks[id.0];

            if let Some(credit) = task.credit.as_mut() {
                self.scheduler
                    .work
                    .admit_fallback(credit, Charges::one(Event::QueuePush, 1))
                    .expect("fallback retry credit reserved");
            }
        }

        self.scheduler.waiting.remove(&id);

        self.scheduler.tasks[id.0].state = TaskState::Queued;

        self.scheduler.queue.push_back(id);
    }

    fn evaluate_task(&mut self, id: TaskId) -> (Reading, Effects, HashSet<TaskId>, bool) {
        let key = self.scheduler.tasks[id.0].key.clone();
        let inputs = self.scheduler.tasks[id.0].inputs.clone();
        let function = self.function_at(key.function);
        let saved_effects = std::mem::take(&mut self.current_effects);
        let saved_inputs = std::mem::replace(&mut self.current_substitutions, inputs.clone());
        let saved_roots = self.root_sizes.replace(key.root_sizes.clone());
        let saved_budget = self.budget_context.take();
        let saved_shares = std::mem::take(&mut self.share_bindings);
        let saved_factors = std::mem::take(&mut self.enclosing_factors);
        let saved_produced = self.produced.take();
        let saved_deferred = self.deferred_reading.take();
        let saved_scoped = std::mem::take(&mut self.pending_scoped);
        let saved_bounds = std::mem::take(&mut self.bound_seen);
        let saved_warnings = std::mem::take(&mut self.warnings);
        let saved_errors = std::mem::take(&mut self.errors);
        self.scheduler.active = Some(id);

        self.scheduler.missing.clear();

        self.scheduler.exhausted = false;
        self.scheduler.fallback_active = self.scheduler.tasks[id.0].fallback;
        self.scheduler.active_credit = self.scheduler.tasks[id.0].credit.take();
        self.scheduler.tasks[id.0].state = TaskState::Evaluating;

        if !self.fallback_active() && self.scheduler.component.is_empty() {
            self.scheduler.tasks[id.0].stable_loops.clear();
        }

        let reading = if self.charge_work(Event::BodyPass, 1) {
            self.scheduler.tasks[id.0].passes += 1;

            self.evaluate_body(key.function.file, function, &inputs, key.raw)
        } else {
            Reading::of_part(
                self.deferred_unknown(
                    key.function.file,
                    self.kind_of_node(key.function.file, key.function.node)
                        .span(),
                    UnknownReason::ResourceExhaustion,
                ),
            )
        };
        let reading = self.finish_reading(key.function.file, function, reading, &inputs);
        let produced =
            std::mem::replace(&mut self.produced, saved_produced).map(|produced| Produced {
                count: produced
                    .count
                    .and_then(|count| self.bind_cost_in(&count, &inputs).ok()),
                yielded: produced.yielded,
            });

        self.scheduler.tasks[id.0].produced = produced;

        let deferred = std::mem::replace(&mut self.deferred_reading, saved_deferred);
        let deferred = deferred
            .map(|reading| self.finish_reading(key.function.file, function, reading, &inputs));

        self.scheduler.tasks[id.0].deferred_reading = deferred;

        let effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.current_substitutions = saved_inputs;
        self.root_sizes = saved_roots;
        self.budget_context = saved_budget;
        self.share_bindings = saved_shares;
        self.enclosing_factors = saved_factors;
        self.pending_scoped = saved_scoped;
        self.bound_seen = saved_bounds;
        let pending = std::mem::take(&mut self.scheduler.missing);
        let exhausted = self.scheduler.exhausted;
        let warnings = std::mem::replace(&mut self.warnings, saved_warnings);
        let errors = std::mem::replace(&mut self.errors, saved_errors);

        if pending.is_empty() && self.scheduler.recurrence_missing.is_empty() {
            self.warnings.extend(warnings);
            self.errors.extend(errors);
        }

        self.scheduler.tasks[id.0].credit = self.scheduler.active_credit.take();
        self.scheduler.active = None;
        self.scheduler.fallback_active = false;

        (reading, effects, pending, exhausted)
    }

    fn drive_summaries(&mut self) {
        loop {
            while let Some(id) = self.scheduler.queue.pop_front() {
                if matches!(self.scheduler.tasks[id.0].state, TaskState::Ready(_)) {
                    continue;
                }

                if self.scheduler.tasks[id.0].fallback {
                    if let Some((reading, effects)) =
                        self.scheduler.recurrence_fallbacks.get(&id).cloned()
                    {
                        self.publish_task(id, reading, effects);

                        continue;
                    }
                }

                let ran_fallback = self.scheduler.tasks[id.0].fallback;
                let (reading, effects, pending, exhausted) = self.evaluate_task(id);

                if !pending.is_empty() {
                    self.scheduler.tasks[id.0].state = TaskState::Waiting;
                    self.scheduler.tasks[id.0].fallback |= exhausted;

                    self.scheduler.waiting.insert(id);

                    if !self.charge_work(Event::DiscoveryWave, 1) {
                        self.scheduler.tasks[id.0].fallback = true;
                    }
                } else if exhausted && !ran_fallback {
                    self.scheduler.tasks[id.0].fallback = true;

                    self.enqueue_task(id);
                } else {
                    self.publish_task(id, reading, effects);
                }
            }

            if self.scheduler.waiting.is_empty() {
                break;
            }

            self.finish_components();
        }
    }

    fn finish_components(&mut self) {
        use petgraph::{algo::kosaraju_scc, graph::DiGraph};

        let mut tasks: Vec<_> = self.scheduler.waiting.iter().copied().collect();

        tasks.sort_by_key(|id| id.0);

        let mut graph = DiGraph::<TaskId, ()>::new();
        let mut nodes = HashMap::new();
        let mut resource = false;

        for id in &tasks {
            if !self.charge_work(Event::GraphNode, 1) {
                resource = true;

                break;
            }

            nodes.insert(*id, graph.add_node(*id));
        }

        if !resource {
            for id in &tasks {
                let dependencies: Vec<_> = self.scheduler.tasks[id.0]
                    .dependencies
                    .iter()
                    .copied()
                    .collect();

                for child in dependencies {
                    if let Some(target) = nodes.get(&child) {
                        if !self.charge_work(Event::GraphEdge, 1) {
                            resource = true;

                            break;
                        }

                        graph.add_edge(nodes[id], *target, ());
                    }
                }

                if resource {
                    break;
                }
            }
        }

        if resource {
            for id in tasks {
                self.scheduler.tasks[id.0].fallback = true;

                self.enqueue_task(id);
            }

            return;
        }

        if !self.charge_work(
            Event::GraphNode,
            (graph.node_count() as u64).saturating_mul(2),
        ) || !self.charge_work(
            Event::GraphEdge,
            (graph.edge_count() as u64).saturating_mul(2),
        ) {
            for id in tasks {
                self.scheduler.tasks[id.0].fallback = true;

                self.enqueue_task(id);
            }

            return;
        }

        let components = kosaraju_scc(&graph);

        for component in components {
            let members: Vec<_> = component.into_iter().map(|index| graph[index]).collect();
            let set: HashSet<_> = members.iter().copied().collect();

            if !members.iter().all(|id| {
                self.scheduler.tasks[id.0].dependencies.iter().all(|child| {
                    set.contains(child)
                        || matches!(self.scheduler.tasks[child.0].state, TaskState::Ready(_))
                })
            }) {
                continue;
            }

            let cyclic = members.len() > 1
                || members
                    .iter()
                    .any(|id| self.scheduler.tasks[id.0].dependencies.contains(id));

            if !cyclic {
                for id in members {
                    self.enqueue_task(id);
                }

                continue;
            }

            if members.iter().any(|id| self.scheduler.tasks[id.0].fallback) {
                for id in members {
                    self.scheduler.tasks[id.0].fallback = true;

                    self.enqueue_task(id);
                }

                continue;
            }

            self.scheduler.component = set;
            let recurrence: Arc<HashSet<_>> = Arc::new(
                members
                    .iter()
                    .map(|id| self.scheduler.tasks[id.0].key.function)
                    .collect(),
            );

            for id in &members {
                self.merge_recurrence_members(*id, Arc::clone(&recurrence));
            }

            if members.iter().any(|id| self.scheduler.tasks[id.0].fallback) {
                self.fallback_component(members);

                continue;
            }

            for id in &members {
                self.scheduler.local_records.remove(id);
            }

            let mut results = Vec::new();
            let mut pending = false;

            for id in &members {
                let (reading, effects, missing, exhausted) = self.evaluate_task(*id);

                if !missing.is_empty() {
                    pending = true;
                }

                if exhausted {
                    self.scheduler.tasks[id.0].fallback = true;
                }

                let key = &self.scheduler.tasks[id.0].key;
                let result = self.values.at(self.source_span(
                    key.function.file,
                    self.kind_of_node(key.function.file, key.function.node)
                        .span(),
                ));

                results.push((*id, reading, effects, result));
            }

            for (id, reading, effects, result) in &results {
                self.scheduler.local_records.insert(
                    *id,
                    SummaryRecord {
                        reading: reading.clone(),
                        result: result.clone(),
                        effects: effects.clone(),
                    },
                );
            }

            if members.iter().any(|id| self.scheduler.tasks[id.0].fallback) {
                self.fallback_component(members);

                continue;
            }

            if pending {
                self.scheduler.component.clear();

                for id in members {
                    self.scheduler.tasks[id.0].state = TaskState::Waiting;
                }

                continue;
            }

            self.scheduler.recurrence_records.clear();
            self.scheduler.recurrence_admitted.clear();

            for id in &members {
                if self.scheduler.recurrence_fallbacks.contains_key(id) {
                    continue;
                }

                self.scheduler.tasks[id.0].fallback = true;
                let (reading, effects, missing, _) = self.evaluate_task(*id);

                assert!(missing.is_empty(), "fallback creates no dependency");

                self.scheduler.tasks[id.0].fallback = false;

                self.scheduler
                    .recurrence_fallbacks
                    .insert(*id, (reading, effects));
            }

            if let Some(solved) = self.solve_component_recurrence(&members) {
                self.scheduler.component.clear();

                let mut effects = Effects::unknown();

                for id in &members {
                    let local = self
                        .scheduler
                        .local_records
                        .get(id)
                        .map(|record| record.effects.clone());

                    if let Some(local) = local {
                        effects.join(&local);
                    }
                }

                for (id, reading) in solved {
                    self.publish_task(id, reading, effects.clone());
                }

                continue;
            }

            let mut completed = Vec::new();

            for id in &members {
                match self.complete_recurrence(*id) {
                    Some((reading, effects)) => completed.push((*id, reading, effects)),
                    None => {
                        pending = true;

                        break;
                    }
                }
            }

            self.scheduler.component.clear();

            if pending {
                for id in members {
                    self.scheduler.tasks[id.0].state = TaskState::Waiting;
                }

                continue;
            }

            let mut effects = Effects::unknown();

            for (_, _, local_effects) in &completed {
                effects.join(local_effects);
            }

            for (id, reading, _) in completed {
                self.publish_task(id, reading, effects.clone());
            }
        }
    }

    fn merge_recurrence_members(&mut self, id: TaskId, incoming: Arc<HashSet<FunctionId>>) {
        if incoming.is_empty()
            || Arc::ptr_eq(&incoming, &self.scheduler.tasks[id.0].recurrence_members)
        {
            return;
        }

        if self.scheduler.tasks[id.0].recurrence_members.is_empty() {
            self.scheduler.tasks[id.0].recurrence_members = incoming;

            return;
        }

        let amount = incoming
            .len()
            .saturating_add(self.scheduler.tasks[id.0].recurrence_members.len())
            as u64;

        if !self.charge_work(Event::GraphNode, amount) {
            self.scheduler.tasks[id.0].fallback = true;

            return;
        }

        Arc::make_mut(&mut self.scheduler.tasks[id.0].recurrence_members)
            .extend(incoming.iter().copied());
    }

    fn local_resource_reading(&mut self, id: TaskId) -> Reading {
        let function = self.scheduler.tasks[id.0].key.function;
        let mut reading = self
            .scheduler
            .local_records
            .get(&id)
            .map(|record| record.reading.clone())
            .unwrap_or_else(Reading::empty);
        let origin = self.source_span(
            function.file,
            self.kind_of_node(function.file, function.node).span(),
        );
        let unknown = self
            .unknowns
            .origin(origin, UnknownReason::ResourceExhaustion);
        let part = reading
            .total(&mut self.unknowns, &mut self.traces)
            .retaining(Some(unknown), &mut self.unknowns);

        reading = Reading::of_part(part);

        reading
    }

    pub(crate) fn forget_recurrence_multiplicity(&mut self) {
        if let Some(markers) = self.scheduler.recurrence_markers.as_mut() {
            markers.unresolved = true;
        }
    }

    fn marker_of(&self, id: TaskId) -> Option<Cost> {
        let markers = self.scheduler.recurrence_markers.as_ref()?;
        let index = markers.members.iter().position(|member| *member == id)?;

        match &markers.solved {
            Some(solved) => solved.get(index).cloned(),
            None => Some(marker_cost_of(index)),
        }
    }

    fn marker_part_of(&mut self, id: TaskId) -> Option<Part> {
        let cost = self.marker_of(id)?;
        let (effects, members, owned) =
            self.scheduler.recurrence_markers.as_ref().map(|markers| {
                (
                    markers.effects.clone(),
                    markers.members.clone(),
                    markers.provenance.clone(),
                )
            })?;
        let caller = self.scheduler.active;
        let mut provenance = None;

        for (member, unknowns) in members.iter().zip(owned) {
            if caller != Some(*member) {
                provenance = self.unknowns.join(provenance, unknowns);
            }
        }

        self.current_effects.join(&effects);

        Some(Part::unmarked(cost, None).retaining(provenance, &mut self.unknowns))
    }

    fn cyclic_effects_of(&mut self, key: &SummaryKey) -> Effects {
        let Some(id) = self.scheduler.keys.get(key).copied() else {
            return Effects::unknown();
        };

        match self
            .scheduler
            .recurrence_markers
            .as_ref()
            .filter(|markers| markers.members.contains(&id))
        {
            Some(markers) => markers.effects.clone(),
            None => Effects::unknown(),
        }
    }

    fn record_recurrence_steps(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments, span): (FileId, &'a [Argument<'a>], oxc_span::Span),
        key: &SummaryKey,
    ) {
        let Some(callee) = self.scheduler.keys.get(key).copied() else {
            return;
        };
        let Some(caller) = self.scheduler.active else {
            return;
        };

        if self
            .scheduler
            .recurrence_markers
            .as_ref()
            .is_none_or(|markers| !markers.members.contains(&callee))
        {
            return;
        }

        let site = self.source_span(call_file, span);

        if self
            .scheduler
            .recurrence_markers
            .as_ref()
            .is_some_and(|markers| markers.steps.contains_key(&(caller, callee, site)))
        {
            return;
        }

        let caller_function = self.scheduler.tasks[caller.0].key.function;
        let caller_node = self.function_at(caller_function);
        let steps = self.call_steps_of(
            (file, function),
            (caller_function.file, caller_node),
            (call_file, arguments),
        );
        let bounds = self.argument_bounds_of(
            function,
            (caller_function.file, caller_node),
            (call_file, arguments),
            &steps,
        );

        if let Some(markers) = self.scheduler.recurrence_markers.as_mut() {
            markers.steps.insert((caller, callee, site), steps);
            markers.bounds.insert((caller, callee, site), bounds);
        }
    }

    fn evaluate_marked_members(&mut self, members: &[TaskId]) -> Option<Vec<(Reading, Effects)>> {
        let mut results = Vec::new();

        for id in members {
            let (reading, effects, missing, exhausted) = self.evaluate_task(*id);

            if !missing.is_empty() || exhausted || self.scheduler.tasks[id.0].fallback {
                return None;
            }

            results.push((reading, effects));
        }

        Some(results)
    }

    fn activation_effects_of(&mut self, members: &[TaskId], mut shared: Effects) -> Effects {
        let functions: Vec<FunctionId> = members
            .iter()
            .map(|id| self.scheduler.tasks[id.0].key.function)
            .collect();
        let mut retained = Vec::new();

        for binding in std::mem::take(&mut shared.binding_writes) {
            let activation = functions.iter().any(|function| {
                self.is_isolated_binding(function.file, Some(function.node), binding)
            });

            if !activation {
                retained.push(binding);
            }
        }

        shared.binding_writes = retained;

        shared
    }

    fn solve_component_recurrence(&mut self, members: &[TaskId]) -> Option<Vec<(TaskId, Reading)>> {
        if members.len() > MAXIMUM_RECURRENCE_MEMBERS
            || !self.charge_work(Event::RecurrenceStep, members.len() as u64)
        {
            return None;
        }

        let mut shared = Effects::default();
        let mut settled = None;

        for _ in 0..MAXIMUM_RECURRENCE_ROUNDS {
            self.scheduler.recurrence_markers = Some(RecurrenceMarkers {
                members: members.to_vec(),
                effects: shared.clone(),
                solved: None,
                provenance: Vec::new(),
                unresolved: false,
                steps: HashMap::new(),
                bounds: HashMap::new(),
            });

            let Some(round) = self.evaluate_marked_members(members) else {
                self.scheduler.recurrence_markers = None;

                return None;
            };
            let mut observed = Effects::default();

            for (_, effects) in &round {
                observed.join(effects);
            }

            let observed = self.activation_effects_of(members, observed);
            let mut widened = shared.clone();

            widened.join(&observed);

            if widened == shared {
                settled = Some(round);

                break;
            }

            shared = widened;
        }

        let Some(results) = settled else {
            self.scheduler.recurrence_markers = None;

            return None;
        };
        let markers = self.scheduler.recurrence_markers.take()?;

        if markers.unresolved {
            return None;
        }

        let readings: Vec<Reading> = results.into_iter().map(|(reading, _)| reading).collect();
        let member_totals: Vec<Part> = readings
            .iter()
            .map(|reading| {
                let total = reading.total(&mut self.unknowns, &mut self.traces);
                let latent = reading.latent(&mut self.unknowns, &mut self.traces);

                total.max(latent, &mut self.unknowns, &mut self.traces)
            })
            .collect();
        let equations = self.recurrence_equations_of(members, &member_totals, &markers)?;
        let RecurrenceSolution::Solved { factors, proof } = solution_of(&equations) else {
            return None;
        };
        let local = Cost::maximum(
            equations
                .iter()
                .map(|equation| equation.local.clone())
                .collect(),
        )
        .ok()?;
        let provenance = member_totals.iter().map(|total| total.unknowns).collect();
        let mut totals = Vec::new();

        for factor in &factors {
            totals.push(factor.multiply(&local).ok()?);
        }

        self.scheduler.recurrence_markers = Some(RecurrenceMarkers {
            members: members.to_vec(),
            effects: markers.effects.clone(),
            solved: Some(totals),
            provenance,
            unresolved: false,
            steps: HashMap::new(),
            bounds: HashMap::new(),
        });

        let explained = self.evaluate_marked_members(members);

        self.scheduler.recurrence_markers = None;

        let explained = explained?;
        let mut solved = Vec::new();

        for (index, id) in members.iter().enumerate() {
            let mut reading = explained[index].0.clone();

            for (phase, completion, part) in &mut reading.completions {
                if part.holds_no_work() {
                    continue;
                }

                let main = *phase == crate::cost::ExecutionPhase::Immediate
                    && *completion == Completion::Normal;
                let source = readings[index].part_of(*phase, *completion);
                let (channel, _) = stripped_cost_of(&source.cost, members.len())?;
                let channel = match main {
                    true => Cost::maximum(vec![channel, local.clone()]).ok()?,
                    false => channel,
                };

                part.cost = factors[index].multiply(&channel).ok()?;
            }

            solved.push((*id, reading));
        }

        self.stats.count(&format!("recurrence solved: {proof}"));

        Some(solved)
    }

    fn recurrence_equations_of(
        &mut self,
        members: &[TaskId],
        totals: &[Part],
        markers: &RecurrenceMarkers,
    ) -> Option<Vec<RecurrenceEquation>> {
        let mut locals = Vec::new();
        let mut multiplicities = Vec::new();

        for total in totals {
            let (local, factors) = stripped_cost_of(&total.cost, members.len())?;

            locals.push(local);
            multiplicities.push(factors);
        }

        let slots = self.recurrence_slots_of(members, &multiplicities, markers)?;
        let mut equations = Vec::new();

        for (index, id) in members.iter().enumerate() {
            let function = self.scheduler.tasks[id.0].key.function;
            let inputs = self.scheduler.tasks[id.0].inputs.clone();
            let node = self.function_at(function);
            let measure = self.recurrence_measure_of(function.file, node, slots[index], &inputs)?;
            let mut edges = Vec::new();

            for (callee, multiplicity) in multiplicities[index].iter().enumerate() {
                let sites = site_count_of((members[index], members[callee]), markers);
                let Some(multiplicity) = multiplicity else {
                    if sites > 0 {
                        return None;
                    }

                    continue;
                };

                if sites == 0
                    || !arguments_bounded_of(
                        (members[index], members[callee]),
                        slots[callee],
                        markers,
                    )
                {
                    return None;
                }

                let multiplicity = multiplicity.multiply(&Cost::constant(sites)).ok()?;
                let (relation, lower_bound) = recurrence_relation_of(
                    (members[index], members[callee]),
                    (slots[index], slots[callee]),
                    markers,
                )?;

                edges.push(RecurrenceEdge {
                    callee,
                    multiplicity,
                    relation,
                    lower_bound,
                });
            }

            equations.push(RecurrenceEquation {
                local: locals[index].clone(),
                measure,
                edges,
            });
        }

        Some(equations)
    }

    fn recurrence_slots_of(
        &mut self,
        members: &[TaskId],
        multiplicities: &[Vec<Option<Cost>>],
        markers: &RecurrenceMarkers,
    ) -> Option<Vec<usize>> {
        let function = self.scheduler.tasks[members[0].0].key.function;
        let node = self.function_at(function);
        let positions = parameters_of(node).map_or(0, |parameters| parameters.items.len());

        for candidate in 0..positions {
            if !self.charge_work(Event::RecurrenceStep, 1) {
                return None;
            }

            if let Some(slots) = slots_from(members, multiplicities, markers, candidate) {
                return Some(slots);
            }
        }

        None
    }

    fn recurrence_reading(&mut self, id: TaskId) -> Reading {
        if self.fallback_active() {
            return self.local_resource_reading(id);
        }

        let Some(context) = self.scheduler.recurrence_context.as_ref() else {
            self.scheduler.pending_serial = self.scheduler.pending_serial.saturating_add(1);

            return Reading::empty();
        };
        let function = self.scheduler.tasks[id.0].key.function;

        if context.active.contains(&id) {
            return Reading::of_part(self.deferred_unknown(
                function.file,
                self.kind_of_node(function.file, function.node).span(),
                UnknownReason::Recurrence,
            ));
        }

        let count = context.active.len() as u64;

        if !self.charge_work(Event::GraphNode, count + 1) || !self.charge_work(Event::GraphEdge, 1)
        {
            return self.scheduler.recurrence_fallbacks[&id].0.clone();
        }

        let mut active = self
            .scheduler
            .recurrence_context
            .as_ref()
            .unwrap()
            .active
            .clone();

        active.push(id);
        active.sort_by_key(|id| id.0);

        let key = RecurrenceKey { task: id, active };

        if let Some((reading, _)) = self.scheduler.recurrence_records.get(&key) {
            return reading.clone();
        }

        if !self.scheduler.recurrence_admitted.contains(&key) {
            if !self.charge_work(Event::RecurrenceContext, 1) {
                return self.scheduler.recurrence_fallbacks[&id].0.clone();
            }

            self.scheduler.recurrence_admitted.insert(key.clone());
        }

        self.scheduler.recurrence_missing.insert(key);

        self.scheduler.pending_serial = self.scheduler.pending_serial.saturating_add(1);

        Reading::empty()
    }

    fn complete_recurrence(&mut self, id: TaskId) -> Option<(Reading, Effects)> {
        let root = RecurrenceKey {
            task: id,
            active: vec![id],
        };

        if !self.charge_work(Event::RecurrenceContext, 1) || !self.charge_work(Event::QueuePush, 1)
        {
            return self.scheduler.recurrence_fallbacks.get(&id).cloned();
        }

        self.scheduler.recurrence_admitted.insert(root.clone());

        let mut stack = vec![RecurrenceFrame {
            key: root.clone(),
            children: Vec::new(),
            next: 0,
        }];

        while let Some(frame) = stack.last_mut() {
            if frame.next < frame.children.len() {
                let child = frame.children[frame.next].clone();
                frame.next += 1;

                if self.scheduler.recurrence_records.contains_key(&child) {
                    continue;
                }

                if !self.charge_work(Event::QueuePush, 1) {
                    self.scheduler.recurrence_records.insert(
                        child.clone(),
                        self.scheduler.recurrence_fallbacks[&child.task].clone(),
                    );

                    continue;
                }

                stack.push(RecurrenceFrame {
                    key: child,
                    children: Vec::new(),
                    next: 0,
                });

                continue;
            }

            let key = frame.key.clone();

            if self.scheduler.tasks[key.task.0].fallback {
                self.scheduler.recurrence_records.insert(
                    key.clone(),
                    self.scheduler.recurrence_fallbacks[&key.task].clone(),
                );
                stack.pop();

                continue;
            }

            self.scheduler.recurrence_context = Some(key.clone());

            self.scheduler.recurrence_missing.clear();

            let (reading, effects, missing, exhausted) = self.evaluate_task(key.task);
            self.scheduler.recurrence_context = None;

            if !missing.is_empty() {
                self.scheduler.recurrence_missing.clear();

                return None;
            }

            if exhausted {
                self.scheduler.recurrence_missing.clear();
                self.scheduler.recurrence_records.insert(
                    key.clone(),
                    self.scheduler.recurrence_fallbacks[&key.task].clone(),
                );
                stack.pop();

                continue;
            }

            let mut children: Vec<_> = self.scheduler.recurrence_missing.drain().collect();

            children.sort_by_key(|child| child.task.0);

            if !children.is_empty() {
                frame.children = children;
                frame.next = 0;

                continue;
            }

            assert!(
                self.scheduler.recurrence_missing.is_empty(),
                "only terminal recurrence contexts publish"
            );

            self.scheduler
                .recurrence_records
                .insert(key, (reading, effects));
            stack.pop();
        }

        self.scheduler.recurrence_records.get(&root).cloned()
    }

    fn evaluate_body(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: &Substitutions,
        raw: bool,
    ) -> Reading {
        if !raw {
            let tags = self.function_tags(file, function);

            if tags.contains(&PerfTag::Ignore) {
                self.stats.count("@perf ignore: function");

                self.current_effects = Effects::unknown();

                return Reading::empty();
            }

            if let Some((cost, text)) = cost_tag_of(&tags) {
                self.stats.count("@perf O(...): function");

                let (cost, unresolved) =
                    match cost.bind_known(&mut |cost| self.bind_cost_in(cost, substitutions)) {
                        Ok(bound) => bound,
                        Err(CostError::Resource | CostError::Overflow) => {
                            let reading = self.unknown_reading(
                                file,
                                self.kind_of_node(file, function.node_id()).span(),
                                UnknownReason::ResourceExhaustion,
                            );

                            self.current_effects = Effects::unknown();

                            return reading;
                        }
                        Err(error) => {
                            self.errors.insert(format!(
                                "invalid {text} at {}:{}: {error:?}",
                                self.project.file(file).relative,
                                self.function_site_of(file, function).line
                            ));

                            return self.unknown_reading(
                                file,
                                self.kind_of_node(file, function.node_id()).span(),
                                UnknownReason::UnsupportedModel,
                            );
                        }
                    };
                let mut reading = tagged_reading_of(
                    cost.unwrap_or(Cost::ONE),
                    &text,
                    self.function_site_of(file, function),
                    self.source_span(file, self.kind_of_node(file, function.node_id()).span()),
                    &mut self.traces,
                    &mut self.unknowns,
                );

                if unresolved {
                    let unknown = self.unknown_reading(
                        file,
                        self.kind_of_node(file, function.node_id()).span(),
                        UnknownReason::SizeRelation,
                    );
                    let mut main = reading.main();
                    main.unknowns = self.unknowns.join(main.unknowns, unknown.main().unknowns);
                    reading = reading.with_main(main);
                }

                let reading = self.finish_reading(file, function, reading, substitutions);

                self.current_effects = Effects::unknown();

                return reading;
            }
        }

        if let FunctionNode::Construction(class) = function {
            if self.fallback_active() {
                self.current_effects = Effects::unknown();
            }

            return Reading::of_part(
                self.construction_part_of((file, &[], class.span), (file, class)),
            );
        }

        let has_body = match function {
            FunctionNode::Function(inner) => inner.body.is_some(),
            FunctionNode::Arrow(_) => true,
            FunctionNode::Construction(_) => unreachable!("construction returns above"),
        };

        if has_body {
            let mut parameters = self.cost_of_parameters(file, function);

            if let Some(class) = self
                .constructed_class_of(file, function)
                .filter(|class| class.heritage.is_none())
            {
                let fields = Reading::of_part(self.instance_fields_part_of(file, class));

                parameters = Some(match parameters {
                    Some(parameters) => {
                        parameters.merge(fields, &mut self.unknowns, &mut self.traces)
                    }
                    None => fields,
                });
            }

            if self.fallback_active() {
                self.current_effects = Effects::unknown();
            } else {
                let budgets = self.collect_budgets(file, function);

                if !self.work_exhausted() {
                    self.budget_context = Some(budgets);
                }
            }

            let generator = matches!(function, FunctionNode::Function(inner) if inner.generator);

            if generator {
                self.produced = Some(Produced {
                    count: Some(Cost::ONE),
                    yielded: false,
                });
            }

            let body = self.cost_of_function_body(file, function);
            let body = match generator {
                true => {
                    self.deferred_reading = Some(body.clone());

                    body.in_phase(
                        crate::cost::ExecutionPhase::Lazy,
                        &mut self.unknowns,
                        &mut self.traces,
                    )
                }
                false => self.returned_latent_reading_of(file, function, body),
            };

            match parameters {
                Some(parameters) => parameters.merge(body, &mut self.unknowns, &mut self.traces),
                None => body,
            }
        } else {
            self.unknown_reading(
                file,
                self.kind_of_node(file, function.node_id()).span(),
                UnknownReason::Target,
            )
        }
    }

    pub(crate) fn enter_construction(
        &mut self,
        class: (FileId, NodeId),
    ) -> Result<(), UnknownReason> {
        let constructing = &mut self.scheduler.constructing;

        if constructing.contains(&class) {
            return Err(UnknownReason::Recurrence);
        }

        if constructing.len() >= MAXIMUM_CONSTRUCTION_DEPTH {
            return Err(UnknownReason::ResourceExhaustion);
        }

        constructing.push(class);

        Ok(())
    }

    pub(crate) fn leave_construction(&mut self, class: (FileId, NodeId)) {
        if let Some(position) = self
            .scheduler
            .constructing
            .iter()
            .rposition(|known| *known == class)
        {
            self.scheduler.constructing.remove(position);
        }
    }

    pub(crate) fn instance_fields_part_of(
        &mut self,
        file: FileId,
        class: &'a oxc_ast::ast::Class<'a>,
    ) -> Reading {
        let site = (file, class.node_id());
        let owners = self.owners_of(file, site.1);

        self.initializers_part_of((site, false), &[site], &owners)
    }

    pub(crate) fn inherited_fields_part_of(
        &mut self,
        file: FileId,
        class: &'a oxc_ast::ast::Class<'a>,
        plan: &ConstructionPlan,
    ) -> Reading {
        if plan.initializers.is_empty() {
            return Reading::empty();
        }

        self.initializers_part_of(
            ((file, class.node_id()), true),
            &plan.initializers,
            &plan.owners,
        )
    }

    pub(crate) fn owners_of(&self, file: FileId, node: NodeId) -> HashSet<(FileId, NodeId)> {
        self.enclosing_functions_of(file, node)
            .iter()
            .map(|function| (file, function.node_id()))
            .collect()
    }

    fn initializers_part_of(
        &mut self,
        (site, inherited): ((FileId, NodeId), bool),
        initializers: &[(FileId, NodeId)],
        owners: &HashSet<(FileId, NodeId)>,
    ) -> Reading {
        let key = self.construction_key_of((site, inherited), owners);

        if let Some((part, effects)) = key
            .as_ref()
            .and_then(|key| self.scheduler.constructions.get(key))
            .cloned()
        {
            self.current_effects.join(&effects);

            return part;
        }

        let span = self.kind_of_node(site.0, site.1).span();

        if !self.scheduler.initializing.insert((site, inherited)) {
            return Reading::of_part(self.deferred_unknown(
                site.0,
                span,
                UnknownReason::Recurrence,
            ));
        }

        let serial = self.scheduler.pending_serial;
        let diagnostics = (self.warnings.len(), self.errors.len());
        let members = self.active_recurrence_members();
        let outer = std::mem::take(&mut self.current_effects);
        let mut part = Reading::empty();

        for (file, node) in initializers {
            if !self.charge_work(Event::DispatchStep, 1) {
                let exhausted =
                    self.deferred_unknown(site.0, span, UnknownReason::ResourceExhaustion);

                part = part.merge(exhausted, &mut self.unknowns, &mut self.traces);

                break;
            }

            let AstKind::Class(class) = self.kind_of_node(*file, *node) else {
                continue;
            };
            let fields = self.cost_of_instance_fields(*file, class);

            part = part.merge(fields, &mut self.unknowns, &mut self.traces);
        }

        let effects = std::mem::replace(&mut self.current_effects, outer);

        self.current_effects.join(&effects);
        self.scheduler.initializing.remove(&(site, inherited));

        let stable = !self.fallback_active()
            && !self.work_exhausted()
            && self.scheduler.component.is_empty()
            && serial == self.scheduler.pending_serial
            && self.pending_scoped.is_empty()
            && self.share_bindings.is_empty()
            && diagnostics == (self.warnings.len(), self.errors.len())
            && members == self.active_recurrence_members();

        if let (Some(key), true) = (key, stable) {
            self.scheduler
                .constructions
                .insert(key, (part.clone(), effects));
        }

        part
    }

    pub(crate) fn forget_constructions(&mut self) {
        self.scheduler.constructions.clear();
    }

    fn enclosing_functions_of(&self, file: FileId, node: NodeId) -> Vec<FunctionNode<'a>> {
        let nodes = self.project.file(file).semantic.nodes();

        nodes
            .ancestor_ids(node)
            .filter_map(|node| match nodes.kind(node) {
                AstKind::Function(function) => Some(FunctionNode::Function(function)),
                AstKind::ArrowFunctionExpression(function) => Some(FunctionNode::Arrow(function)),
                _ => None,
            })
            .collect()
    }

    fn active_recurrence_members(&self) -> Option<usize> {
        self.scheduler
            .active
            .map(|active| self.scheduler.tasks[active.0].recurrence_members.len())
    }

    fn construction_key_of(
        &mut self,
        (class, inherited): ((FileId, NodeId), bool),
        owners: &HashSet<(FileId, NodeId)>,
    ) -> Option<ConstructionKey> {
        let function = owners
            .iter()
            .min_by_key(|(file, node)| (file.0, node.index()))
            .and_then(|(file, node)| match self.kind_of_node(*file, *node) {
                AstKind::Function(function) => Some((*file, FunctionNode::Function(function))),
                AstKind::ArrowFunctionExpression(function) => {
                    Some((*file, FunctionNode::Arrow(function)))
                }
                _ => None,
            });
        let captures = match function {
            None => Vec::new(),
            Some((file, function)) => {
                if !self.charge_work(Event::CaptureEdge, self.current_substitutions.len() as u64) {
                    return None;
                }

                let captured: Substitutions = self
                    .current_substitutions
                    .iter()
                    .filter(|(binding, _)| {
                        matches!(
                            self.declarations.of_binding(self.project, **binding),
                            Some(Declaration::Parameter { file: declared, function: owner, .. })
                                if owners.contains(&(declared, owner.node_id()))
                        )
                    })
                    .map(|(binding, facts)| (*binding, facts.clone()))
                    .collect();

                self.key_of(file, function, &captured).ok()?.substitutions
            }
        };

        Some(ConstructionKey {
            class,
            inherited,
            root_sizes: self.root_sizes.clone().unwrap_or_default(),
            captures,
        })
    }

    fn inherited_substitutions_of(
        &mut self,
        target: FileId,
        function: FunctionNode<'a>,
    ) -> Option<Substitutions> {
        let source = std::mem::take(&mut self.current_substitutions);
        let captured = self.captured_substitutions_of(&source, target, function);

        self.current_substitutions = source;

        captured
    }

    fn captured_substitutions_of(
        &mut self,
        source: &Substitutions,
        target: FileId,
        function: FunctionNode<'a>,
    ) -> Option<Substitutions> {
        if !self.charge_work(Event::BudgetPrepassNode, source.len() as u64) {
            return None;
        }

        let ancestors: HashSet<_> = self
            .project
            .file(target)
            .semantic
            .nodes()
            .ancestor_ids(function.node_id())
            .collect();
        let captured = |binding: &Binding| matches!(self.declarations.of_binding(self.project,*binding),Some(Declaration::Parameter {file,function:owner,..}) if file==target && owner!=function && ancestors.contains(&owner.node_id()));
        let count = source.keys().filter(|binding| captured(binding)).count();

        if !self.charge_work(Event::CaptureEdge, count as u64) {
            return None;
        }

        let captured = |binding: &Binding| matches!(self.declarations.of_binding(self.project,*binding),Some(Declaration::Parameter {file,function:owner,..}) if file==target && owner!=function && ancestors.contains(&owner.node_id()));

        Some(
            source
                .iter()
                .filter(|(binding, _)| captured(binding))
                .map(|(binding, facts)| (*binding, facts.clone()))
                .collect(),
        )
    }

    pub(crate) fn argument_facts_of(
        &mut self,
        file: FileId,
        argument: &'a Argument<'a>,
    ) -> ArgumentFacts {
        self.expression_facts_of(file, argument.span(), argument.as_expression())
    }

    pub(crate) fn expression_facts_of(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
        expression: Option<&'a Expression<'a>>,
    ) -> ArgumentFacts {
        let definedness = match expression {
            Some(expression) => self.definedness_of(file, expression),
            None => Definedness::Unknown,
        };

        ArgumentFacts {
            definedness,
            ..self.expression_value_facts_of(file, span, expression)
        }
    }

    fn expression_value_facts_of(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
        expression: Option<&'a Expression<'a>>,
    ) -> ArgumentFacts {
        let origin = self.source_span(file, span);
        let mut value = self.values.at(origin);
        let expression = expression.map(unwrap);

        if let Some(Expression::NumericLiteral(number)) = expression {
            if number.value.is_finite()
                && number.value >= 0.0
                && number.value <= 9_007_199_254_740_991.0
                && number.value.fract() == 0.0
            {
                value.size = Some(Cost::constant((number.value as u64).max(1)));
            }
        }

        if let Some(expression) = expression.filter(|expression| {
            !matches!(
                expression,
                Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_)
            )
        }) {
            if value.size.is_none() {
                value.size = self.size_of_value(file, expression);
            }
        }

        let mut callback_open = false;
        let declaration = expression.and_then(|expression| match expression {
            Expression::Identifier(reference) => {
                let (declaration, closed) =
                    self.declarations
                        .callable_reference(self.project, file, reference);

                callback_open = !closed;

                declaration
            }
            _ => expression.as_member_expression().and_then(|member| {
                callback_open = true;

                self.resolved_member_of(file, member)
                    .declaration
                    .map(|declaration| {
                        self.declarations
                            .executable_declaration(self.project, declaration)
                    })
            }),
        });

        if let Some(binding) =
            declaration.and_then(|declaration| self.parameter_binding_of(declaration))
        {
            if let Some(facts) = self
                .current_substitutions
                .get(&binding)
                .cloned()
                .filter(|_| self.is_parameter_unwritten(binding))
            {
                return facts;
            }
        }

        if let Some(Expression::StaticMemberExpression(member)) = expression {
            if member.property.name == "length" {
                if let Expression::Identifier(reference) = unwrap(&member.object) {
                    let admitted = matches!(
                        self.declared_type_of_identifier(file, reference).kind,
                        crate::declared_types::Kind::String | crate::declared_types::Kind::Array
                    );

                    if let Some(binding) = self.binding_of_identifier(file, reference) {
                        if let Some(facts) = self
                            .current_substitutions
                            .get(&binding)
                            .filter(|_| admitted)
                        {
                            value.size = facts.value.size.clone();

                            self.values.prefer_length_label(facts.value.value);
                        }
                    }
                }
            }
        }

        let function = match expression {
            Some(Expression::FunctionExpression(function)) => {
                Some((file, FunctionNode::Function(function)))
            }
            Some(Expression::ArrowFunctionExpression(arrow)) => {
                Some((file, FunctionNode::Arrow(arrow)))
            }
            _ => declaration.and_then(|declaration| self.declarations.function_of(declaration)),
        };

        if let (None, Some(Expression::Identifier(reference))) = (function, expression) {
            if let Some(facts) = self.pattern_argument_facts_of(file, reference, !callback_open) {
                return facts;
            }

            if self.is_pattern_reference(file, reference) {
                let targets = self.callable_targets_of(file, expression.unwrap());

                if let [known] = targets.known[..] {
                    let function = self.function_at(known);

                    return self.callback_facts_of(
                        (file, span),
                        value,
                        (known.file, function),
                        targets.open,
                    );
                }
            }
        }

        if let Some(expression) = expression.filter(|expression| {
            matches!(
                expression,
                Expression::CallExpression(_)
                    | Expression::Identifier(_)
                    | Expression::ConditionalExpression(_)
                    | Expression::LogicalExpression(_)
                    | Expression::SequenceExpression(_)
            )
        }) {
            if let Some(latent) = self.latent_of(file, expression) {
                value.latent = self.latent_record_of(latent, origin);

                if value.latent.is_none() {
                    self.scheduler.exhausted = true;
                }
            }
        }

        match function {
            Some((target, function)) => {
                self.callback_facts_of((file, span), value, (target, function), callback_open)
            }
            None => ArgumentFacts {
                value,
                callback: None,
                preference: Preference::Absent,
                definedness: Definedness::Unknown,
            },
        }
    }

    pub(crate) fn callback_facts_of(
        &mut self,
        origin: (FileId, oxc_span::Span),
        value: ValueFacts,
        (target, function): (FileId, FunctionNode<'a>),
        callback_open: bool,
    ) -> ArgumentFacts {
        let Some(captured) = self.inherited_substitutions_of(target, function) else {
            return self.exhausted_callback_facts_of(origin, value);
        };

        self.captured_callback_facts_of(origin, value, (target, function), callback_open, captured)
    }

    fn captured_callback_facts_of(
        &mut self,
        origin: (FileId, oxc_span::Span),
        value: ValueFacts,
        (target, function): (FileId, FunctionNode<'a>),
        callback_open: bool,
        captured: Substitutions,
    ) -> ArgumentFacts {
        let Ok(key) = self.key_of(target, function, &captured) else {
            self.scheduler.exhausted = true;

            return self.exhausted_callback_facts_of(origin, value);
        };
        let descriptor = match self.scheduler.callback_keys.get(&key).copied() {
            Some(id) => id,
            None if self.charge_work(Event::CallbackDescriptor, 1) => {
                let id = self.scheduler.callbacks.len();

                self.scheduler.callbacks.push(CallbackDescriptor::Source {
                    function: key.function,
                    captured,
                    generation: self.scheduler.generation,
                });
                self.scheduler.callback_keys.insert(key, id);

                id
            }
            None => return self.exhausted_callback_facts_of(origin, value),
        };
        let mut value = self.values.callback(descriptor);

        value.targets = TargetSet {
            known: vec![FunctionId {
                file: target,
                node: function.node_id(),
            }],
            open: callback_open,
        };

        self.scheduler
            .callback_values
            .insert(value.value, descriptor);

        ArgumentFacts {
            value,
            callback: None,
            preference: self
                .function_preference_of(target, function)
                .unwrap_or(Preference::Unmarked),
            definedness: Definedness::Unknown,
        }
    }

    fn exhausted_callback_facts_of(
        &mut self,
        (file, span): (FileId, oxc_span::Span),
        value: ValueFacts,
    ) -> ArgumentFacts {
        ArgumentFacts {
            value,
            callback: Some(self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion)),
            preference: Preference::Unmarked,
            definedness: Definedness::Unknown,
        }
    }

    pub(crate) fn pattern_argument_facts_of(
        &self,
        file: FileId,
        reference: &'a oxc_ast::ast::IdentifierReference<'a>,
        closed: bool,
    ) -> Option<ArgumentFacts> {
        if !closed {
            return None;
        }

        let (mut file, mut reference) = (file, reference);

        for _ in 0..MAXIMUM_PATTERN_ALIASES {
            let binding = self
                .declarations
                .binding_of_reference(self.project, file, reference)?;

            if let Some(facts) = self.pattern_callback_of(binding) {
                return Some(facts);
            }

            let Some(Declaration::Variable {
                file: target,
                declarator,
                constant: true,
            }) = self.declarations.of_binding(self.project, binding)
            else {
                return None;
            };
            let Some(Expression::Identifier(next)) = declarator.init.as_ref().map(unwrap) else {
                return None;
            };

            (file, reference) = (target, next);
        }

        None
    }

    fn is_pattern_reference(
        &self,
        file: FileId,
        reference: &'a oxc_ast::ast::IdentifierReference<'a>,
    ) -> bool {
        match self
            .declarations
            .of_reference(self.project, file, reference)
        {
            Some(Declaration::Variable { declarator, .. }) => {
                !matches!(declarator.id, BindingPattern::BindingIdentifier(_))
            }
            Some(Declaration::Parameter {
                parameter: crate::declarations::ParameterNode::Formal(parameter),
                ..
            }) => !matches!(parameter.pattern, BindingPattern::BindingIdentifier(_)),
            _ => false,
        }
    }

    fn pattern_callback_of(&self, binding: Binding) -> Option<ArgumentFacts> {
        self.current_substitutions
            .get(&binding)
            .filter(|facts| {
                self.scheduler
                    .callback_values
                    .contains_key(&facts.value.value)
            })
            .cloned()
    }

    fn substitute_pattern_callbacks(
        &mut self,
        file: FileId,
        parameter: &'a oxc_ast::ast::FormalParameter<'a>,
        (call_file, argument): (FileId, &'a Expression<'a>),
        substitutions: &mut Substitutions,
    ) {
        let mut sources = vec![(call_file, argument)];

        sources.extend(
            parameter
                .initializer
                .iter()
                .map(|initializer| (file, &**initializer)),
        );

        for identifier in parameter.pattern.get_binding_identifiers() {
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            let targets =
                self.pattern_argument_targets_of(file, &parameter.pattern, symbol, sources.clone());
            let [known] = targets.known[..] else {
                continue;
            };
            let function = self.function_at(known);
            let value = self.values.at(self.source_span(file, identifier.span));
            let facts = self.callback_facts_of(
                (call_file, argument.span()),
                value,
                (known.file, function),
                targets.open,
            );

            substitutions.insert(Binding::Symbol { file, symbol }, facts);
        }
    }

    pub(crate) fn reading_of_argument(
        &mut self,
        file: FileId,
        argument: Option<&'a Argument<'a>>,
    ) -> Option<Reading> {
        let argument = argument?;
        let facts = self.argument_facts_of(file, argument);

        Some(self.invoke_argument_with(&facts, file, argument.span(), &[], (true, &[])))
    }

    pub(crate) fn invoke_callback(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        supplied: &[Part],
    ) -> Reading {
        self.invoke_argument_with(facts, file, span, &[], (true, supplied))
    }

    pub(crate) fn apply_argument_effects(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        arguments: &'a [Argument<'a>],
    ) {
        match facts
            .value
            .latent
            .and_then(|id| self.summaries_arena.get(id.0 as usize))
            .map(|record| record.effects.clone())
        {
            Some(effects) => self.current_effects.join(&effects),
            None => self.record_unknown_reach(file, None, arguments, span),
        }
    }

    pub(crate) fn invoke_argument(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        arguments: &'a [Argument<'a>],
    ) -> Reading {
        self.invoke_argument_with(facts, file, span, arguments, (false, &[]))
    }

    fn invoke_argument_with(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        arguments: &'a [Argument<'a>],
        (implicit, supplied): (bool, &[Part]),
    ) -> Reading {
        if let Some(id) = self
            .scheduler
            .callback_values
            .get(&facts.value.value)
            .copied()
        {
            let descriptor = self.scheduler.callbacks[id].clone();

            if descriptor.generation() != self.scheduler.generation {
                return Reading::of_part(self.deferred_unknown(file, span, UnknownReason::Target));
            }

            let (target, captured) = match descriptor {
                CallbackDescriptor::PromiseResolve { .. } => {
                    return match implicit {
                        true => {
                            Reading::of_part(self.unknown_part(file, span, UnknownReason::Target))
                        }
                        false => self.resolved_promise_reading_of(file, span, arguments),
                    };
                }
                CallbackDescriptor::Source {
                    function, captured, ..
                } => (function, captured),
            };
            let function = self.function_at(target);

            let (mut part, cyclic) = if self.fallback_active() {
                self.fallback_invocation(
                    target,
                    file,
                    span,
                    if implicit {
                        Deferral::Excluded
                    } else {
                        Deferral::Escaped
                    },
                )
            } else {
                let captured =
                    self.supplied_substitutions_of((target.file, function), captured, supplied);

                self.call_with_captures(
                    (target.file, function),
                    (file, arguments, span),
                    (
                        implicit,
                        if implicit {
                            Deferral::Excluded
                        } else {
                            Deferral::Escaped
                        },
                    ),
                    captured,
                )
            };

            if facts.value.targets.open {
                let unknown = self.unknown_invocation(file, span, arguments, UnknownReason::Target);

                part = part.retaining(unknown.main().unknowns, &mut self.unknowns);
            }

            return self.called_reading_of(target.file, function, part, cyclic);
        }

        self.apply_argument_effects(facts, file, span, arguments);

        Reading::of_part(
            facts
                .callback
                .clone()
                .unwrap_or_else(|| self.unknown_part(file, span, UnknownReason::Target)),
        )
    }

    fn supplied_substitutions_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        mut substitutions: Substitutions,
        supplied: &[Part],
    ) -> Substitutions {
        let Some(parameters) = parameters_of(function) else {
            return substitutions;
        };

        for (parameter, part) in parameters.items.iter().zip(supplied) {
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };

            substitutions.insert(
                Binding::Symbol { file, symbol },
                ArgumentFacts {
                    value: self.values.at(self.source_span(file, identifier.span)),
                    callback: Some(part.clone()),
                    preference: Preference::Absent,
                    definedness: Definedness::Defined,
                },
            );
        }

        substitutions
    }

    pub(crate) fn called_part_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        part: Part,
        cyclic: bool,
    ) -> Part {
        let mark = if cyclic {
            None
        } else {
            self.function_preference_of(file, function)
        };

        match mark {
            Some(mark) => part.preferred(mark),
            None if part.holds_no_work() => part.preferred(Preference::Absent),
            None => part.preferred(Preference::Unmarked),
        }
    }

    pub(crate) fn called_reading_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        reading: Reading,
        cyclic: bool,
    ) -> Reading {
        if reading.completions.is_empty() {
            return Reading::of_part(self.called_part_of(file, function, Part::none(), cyclic));
        }

        reading.map_parts(|part| self.called_part_of(file, function, part, cyclic))
    }

    pub fn call_user(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        call_file: FileId,
        arguments: &'a [Argument<'a>],
        span: oxc_span::Span,
    ) -> (Part, bool) {
        let (reading, cyclic) = self.call_user_reading(file, function, call_file, arguments, span);

        (reading.total(&mut self.unknowns, &mut self.traces), cyclic)
    }

    pub(crate) fn call_user_reading(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        call_file: FileId,
        arguments: &'a [Argument<'a>],
        span: oxc_span::Span,
    ) -> (Reading, bool) {
        self.call_user_with(
            (file, function),
            (call_file, arguments, span),
            Deferral::Excluded,
        )
    }

    pub(crate) fn call_user_with(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments, span): (FileId, &'a [Argument<'a>], oxc_span::Span),
        deferral: Deferral,
    ) -> (Reading, bool) {
        if self.fallback_active() {
            return self.fallback_invocation(
                FunctionId {
                    file,
                    node: function.node_id(),
                },
                call_file,
                span,
                deferral,
            );
        }

        let Some(captured) = self.inherited_substitutions_of(file, function) else {
            return (
                Reading::of_part(self.deferred_unknown(
                    call_file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        };

        self.call_with_captures(
            (file, function),
            (call_file, arguments, span),
            (false, deferral),
            captured,
        )
    }

    pub(crate) fn call_implicit(
        &mut self,
        target: FunctionId,
        call_file: FileId,
        span: oxc_span::Span,
    ) -> (Reading, bool) {
        if self.fallback_active() {
            return self.fallback_invocation(target, call_file, span, Deferral::Consumed);
        }

        let function = self.function_at(target);
        let Some(captured) = self.inherited_substitutions_of(target.file, function) else {
            return (
                Reading::of_part(self.deferred_unknown(
                    call_file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        };

        self.call_with_captures(
            (target.file, function),
            (call_file, &[], span),
            (true, Deferral::Consumed),
            captured,
        )
    }

    pub(crate) fn call_supplied(
        &mut self,
        target: FunctionId,
        (call_file, span): (FileId, oxc_span::Span),
        (supplied, rest): (Vec<Option<ArgumentFacts>>, Option<ArgumentFacts>),
    ) -> (Reading, bool) {
        if self.fallback_active() {
            return self.fallback_invocation(target, call_file, span, Deferral::Excluded);
        }

        let function = self.function_at(target);
        let Some(mut captured) = self.inherited_substitutions_of(target.file, function) else {
            return (
                Reading::of_part(self.deferred_unknown(
                    call_file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        };

        if let Some(parameters) = parameters_of(function) {
            let rest = parameters
                .rest
                .as_ref()
                .map(|parameter| (&parameter.rest.argument, rest));
            let items = parameters
                .items
                .iter()
                .map(|parameter| &parameter.pattern)
                .zip(supplied)
                .chain(rest);

            for (pattern, facts) in items {
                let (BindingPattern::BindingIdentifier(identifier), Some(facts)) = (pattern, facts)
                else {
                    continue;
                };

                if let Some(symbol) = identifier.symbol_id.get() {
                    captured.insert(
                        Binding::Symbol {
                            file: target.file,
                            symbol,
                        },
                        facts,
                    );
                }
            }
        }

        self.call_with_captures(
            (target.file, function),
            (call_file, &[], span),
            (true, Deferral::Excluded),
            captured,
        )
    }

    fn call_with_captures(
        &mut self,
        function: (FileId, FunctionNode<'a>),
        call: (FileId, &'a [Argument<'a>], oxc_span::Span),
        (implicit, deferral): (bool, Deferral),
        substitutions: Substitutions,
    ) -> (Reading, bool) {
        let (reading, cyclic) = self.invocation_reading_of(
            function,
            call,
            implicit,
            substitutions,
            deferral == Deferral::Consumed,
        );

        (
            self.called_phases_of(reading, deferral, call.0, call.2),
            cyclic,
        )
    }

    fn called_phases_of(
        &mut self,
        reading: Reading,
        deferral: Deferral,
        file: FileId,
        span: oxc_span::Span,
    ) -> Reading {
        let mut result = Reading::empty();

        for (phase, _, part) in reading.completions {
            let (phase, part) = match (phase, deferral) {
                (crate::cost::ExecutionPhase::Lazy, Deferral::Excluded) => continue,
                (crate::cost::ExecutionPhase::Lazy, Deferral::Escaped) => {
                    let unknown = self
                        .unknowns
                        .origin(self.source_span(file, span), UnknownReason::Multiplicity);

                    (
                        crate::cost::ExecutionPhase::Immediate,
                        part.retaining(Some(unknown), &mut self.unknowns),
                    )
                }
                (crate::cost::ExecutionPhase::Lazy, Deferral::Consumed) => {
                    (crate::cost::ExecutionPhase::Immediate, part)
                }
                (phase, _) => (phase, part),
            };

            result.join(
                phase,
                crate::flow::Completion::Normal,
                part,
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        result
    }

    fn invocation_reading_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments, span): (FileId, &'a [Argument<'a>], oxc_span::Span),
        implicit: bool,
        substitutions: Substitutions,
        consume: bool,
    ) -> (Reading, bool) {
        let target = FunctionId {
            file,
            node: function.node_id(),
        };

        if self.fallback_active() {
            let (part, cyclic) = self.fallback_invocation(
                target,
                call_file,
                span,
                if consume {
                    Deferral::Consumed
                } else {
                    Deferral::Excluded
                },
            );

            return (Reading::of_part(part), cyclic);
        }

        if !self.charge_work(Event::InvocationEvaluation, 1) {
            return (
                Reading::of_part(self.deferred_unknown(
                    call_file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        }

        if let Some(parent) = self.scheduler.active.filter(|_| !self.fallback_active()) {
            let caller = self.scheduler.tasks[parent.0].key.function;

            if !self.scheduler.runtime.contains(&(caller, target)) {
                if !self.charge_work(Event::RuntimePair, 1) {
                    return (
                        Reading::of_part(self.deferred_unknown(
                            call_file,
                            span,
                            UnknownReason::ResourceExhaustion,
                        )),
                        false,
                    );
                }

                self.scheduler.runtime.insert((caller, target));
            }

            let site = (caller, self.source_span(call_file, span), target);

            if !self.scheduler.sites.contains(&site) {
                if !self.charge_work(Event::InvocationSite, 1) {
                    return (
                        Reading::of_part(self.deferred_unknown(
                            call_file,
                            span,
                            UnknownReason::ResourceExhaustion,
                        )),
                        false,
                    );
                }

                self.scheduler.sites.insert(site);
            }
        }

        let substitutions = self.invocation_substitutions_of(
            (file, function),
            (call_file, arguments),
            implicit,
            substitutions,
        );
        let substitutions = self.function_inputs(file, function, substitutions);
        let Ok(key) = self.key_of(file, function, &substitutions) else {
            self.scheduler.exhausted = true;

            return (
                Reading::of_part(self.deferred_unknown(
                    call_file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        };

        self.observe_invocation(&key, call_file, span);

        let (reading, cyclic) = self.request_reading(key.clone(), substitutions);

        self.observe_invocation(&key, call_file, span);

        if cyclic {
            self.record_recurrence_steps((file, function), (call_file, arguments, span), &key);
        }

        let mut effects = match self.summaries.get(&key) {
            Some(id) => self.summaries_arena[id.0 as usize].effects.clone(),
            None => self.cyclic_effects_of(&key),
        };

        self.substitute_parameter_values(file, function, call_file, arguments, &mut effects);
        self.current_effects.join(&effects);

        let reading = match self
            .summaries
            .get(&key)
            .and_then(|id| self.latent_readings.get(id))
            .filter(|_| consume)
            .cloned()
        {
            Some(deferred) => {
                let mut immediate = reading;

                immediate
                    .completions
                    .retain(|channel| channel.0 != crate::cost::ExecutionPhase::Lazy);

                immediate.merge(deferred, &mut self.unknowns, &mut self.traces)
            }
            None => reading,
        };

        (reading, cyclic)
    }

    fn invocation_substitutions_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments): (FileId, &'a [Argument<'a>]),
        implicit: bool,
        mut substitutions: Substitutions,
    ) -> Substitutions {
        let Some(parameters) = parameters_of(function) else {
            return substitutions;
        };
        let spread_at = arguments
            .iter()
            .position(|argument| matches!(argument, Argument::SpreadElement(_)));

        for (index, parameter) in parameters.items.iter().enumerate() {
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                let argument = arguments
                    .get(index)
                    .and_then(Argument::as_expression)
                    .filter(|_| {
                        !arguments[..index]
                            .iter()
                            .any(|argument| matches!(argument, Argument::SpreadElement(_)))
                    });

                if let Some(argument) = argument {
                    self.substitute_pattern_callbacks(
                        file,
                        parameter,
                        (call_file, argument),
                        &mut substitutions,
                    );
                }

                continue;
            };
            let supplied = identifier
                .symbol_id
                .get()
                .filter(|_| implicit && arguments.get(index).is_none())
                .is_some_and(|symbol| {
                    substitutions.contains_key(&Binding::Symbol { file, symbol })
                });

            if supplied {
                continue;
            }

            let positional = spread_at.is_none_or(|spread| spread > index);
            let undefined = match arguments.get(index).and_then(Argument::as_expression) {
                Some(expression) => {
                    positional
                        && self.definedness_of(call_file, expression) == Definedness::Undefined
                }
                None => !implicit && spread_at.is_none(),
            };
            let facts = match arguments.get(index) {
                _ if undefined => ArgumentFacts {
                    value: self.values.undefined(),
                    callback: None,
                    preference: Preference::Unmarked,
                    definedness: Definedness::Undefined,
                },
                Some(argument) if positional => self.argument_facts_of(call_file, argument),
                _ => ArgumentFacts {
                    value: self.values.at(self.source_span(file, identifier.span)),
                    callback: None,
                    preference: Preference::Unmarked,
                    definedness: Definedness::Unknown,
                },
            };

            let mut facts = facts;

            if facts.value.size.is_none() && positional && !undefined {
                if let Some(argument) = arguments.get(index).and_then(Argument::as_expression) {
                    facts.value.size = self.reduced_measure_size_of(call_file, argument);
                }
            }

            if let Some(symbol) = identifier.symbol_id.get() {
                substitutions.insert(Binding::Symbol { file, symbol }, facts);
            }
        }

        if let Some(rest) = parameters.rest.as_ref() {
            if let BindingPattern::BindingIdentifier(identifier) = &rest.rest.argument {
                if let Some(symbol) = identifier.symbol_id.get().filter(|symbol| {
                    !(implicit
                        && substitutions.contains_key(&Binding::Symbol {
                            file,
                            symbol: *symbol,
                        }))
                }) {
                    let origin = self.source_span(file, identifier.span);
                    let mut value = self.values.at(origin);

                    let constant = self.collects_constant_arguments(
                        (call_file, arguments),
                        parameters.items.len(),
                        implicit,
                    );

                    value.size = constant.then_some(Cost::ONE);

                    substitutions.insert(
                        Binding::Symbol { file, symbol },
                        ArgumentFacts {
                            value,
                            callback: None,
                            preference: Preference::Unmarked,
                            definedness: Definedness::Defined,
                        },
                    );
                }
            }
        }

        substitutions
    }

    fn collects_constant_arguments(
        &mut self,
        (call_file, arguments): (FileId, &'a [Argument<'a>]),
        collected_from: usize,
        implicit: bool,
    ) -> bool {
        if implicit {
            return false;
        }

        if arguments[..collected_from.min(arguments.len())]
            .iter()
            .any(|argument| matches!(argument, Argument::SpreadElement(_)))
        {
            return false;
        }

        arguments
            .iter()
            .skip(collected_from)
            .all(|argument| match argument {
                Argument::SpreadElement(spread) => {
                    self.is_constant_sized(call_file, &spread.argument)
                }
                _ => true,
            })
    }

    pub(crate) fn is_parameter_unwritten(&mut self, binding: Binding) -> bool {
        if !self.declarations.is_write_free(self.project, binding) {
            return false;
        }

        match self.declarations.of_binding(self.project, binding) {
            Some(Declaration::Parameter { file, function, .. }) => {
                self.dynamic_scope_of(file, function.node_id()) == (false, false)
            }
            _ => true,
        }
    }

    pub(crate) fn parameter_definedness_of(
        &self,
        file: FileId,
        parameter: &'a FormalParameter<'a>,
    ) -> Definedness {
        let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
            return Definedness::Unknown;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            return Definedness::Unknown;
        };

        match self
            .current_substitutions
            .get(&Binding::Symbol { file, symbol })
        {
            Some(facts) => facts.definedness,
            None => Definedness::Unknown,
        }
    }

    pub(crate) fn bind_parameter_default(
        &mut self,
        file: FileId,
        parameter: &'a FormalParameter<'a>,
    ) {
        let (BindingPattern::BindingIdentifier(identifier), Some(initializer)) =
            (&parameter.pattern, &parameter.initializer)
        else {
            return;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            return;
        };
        let facts = self.expression_facts_of(file, initializer.span(), Some(initializer));

        self.current_substitutions
            .insert(Binding::Symbol { file, symbol }, facts);
    }

    fn defaulted_substitutions_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        substitutions: Substitutions,
    ) -> Substitutions {
        let Some(parameters) = parameters_of(function) else {
            return substitutions;
        };
        let saved = std::mem::replace(&mut self.current_substitutions, substitutions);

        for parameter in &parameters.items {
            if parameter.initializer.is_some()
                && self.parameter_definedness_of(file, parameter) == Definedness::Undefined
            {
                self.bind_parameter_default(file, parameter);
            }
        }

        std::mem::replace(&mut self.current_substitutions, saved)
    }

    pub(crate) fn returned_facts_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<(Vec<ArgumentFacts>, bool)> {
        let targets = self.resolved_callee_of(file, call).targets;

        if targets.known.is_empty() {
            return None;
        }

        let mut open = targets.open;
        let mut found: Vec<ArgumentFacts> = Vec::new();

        for target in targets.known {
            let function = self.function_at(target);
            let deferred = match function {
                FunctionNode::Function(inner) => inner.r#async || inner.generator,
                FunctionNode::Arrow(arrow) => arrow.r#async,
                FunctionNode::Construction(_) => false,
            };

            if deferred {
                open = true;

                continue;
            }

            let captured = self.inherited_substitutions_of(target.file, function)?;
            let substitutions = self.invocation_substitutions_of(
                (target.file, function),
                (file, &call.arguments),
                false,
                captured,
            );
            let substitutions =
                self.defaulted_substitutions_of((target.file, function), substitutions);
            let substitutions = self.function_inputs(target.file, function, substitutions);

            for returned in self.returned_expressions_of(target) {
                let (facts, unresolved) =
                    self.returned_value_facts_of((target.file, returned), &substitutions)?;

                open |= unresolved;

                for facts in facts {
                    if !found.contains(&facts) {
                        found.push(facts);
                    }
                }
            }
        }

        Some((found, open))
    }

    fn returned_value_facts_of(
        &mut self,
        (file, returned): (FileId, &'a Expression<'a>),
        substitutions: &Substitutions,
    ) -> Option<(Vec<ArgumentFacts>, bool)> {
        let returned = unwrap(returned);

        if let Expression::Identifier(reference) = returned {
            let binding = self
                .declarations
                .of_reference(self.project, file, reference)
                .and_then(|declaration| self.parameter_binding_of(declaration));

            if let Some(binding) = binding {
                let unwritten = self.is_parameter_unwritten(binding);
                let facts = substitutions.get(&binding).filter(|facts| {
                    self.scheduler
                        .callback_values
                        .contains_key(&facts.value.value)
                });

                return Some(match (facts, unwritten) {
                    (Some(facts), true) => (vec![facts.clone()], false),
                    _ => (Vec::new(), true),
                });
            }
        }

        let targets = self.callable_targets_of(file, returned);
        let mut found = Vec::new();

        for known in targets.known {
            let function = self.function_at(known);
            let captured = self.captured_substitutions_of(substitutions, known.file, function)?;
            let value = self.values.at(self.source_span(file, returned.span()));

            found.push(self.captured_callback_facts_of(
                (file, returned.span()),
                value,
                (known.file, function),
                false,
                captured,
            ));
        }

        Some((found, targets.open))
    }

    fn substitute_parameter_values(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        call_file: FileId,
        arguments: &'a [Argument<'a>],
        effects: &mut Effects,
    ) {
        if effects.unknown_global {
            return;
        }

        let Some(parameters) = parameters_of(function) else {
            return;
        };

        for (parameter, argument) in parameters.items.iter().zip(arguments) {
            let (BindingPattern::BindingIdentifier(identifier), Some(expression)) =
                (&parameter.pattern, argument.as_expression())
            else {
                break;
            };
            let rebound = identifier.symbol_id.get().is_none_or(|symbol| {
                !self.is_parameter_unwritten(Binding::Symbol { file, symbol })
            });

            if rebound {
                continue;
            }

            let parameter = self
                .values
                .at(self.source_span(file, parameter.pattern.span()))
                .value;
            let argument = self.storage_value_of(call_file, expression);

            effects.substitute(parameter, argument);
        }
    }

    fn observe_invocation(&mut self, key: &SummaryKey, file: FileId, span: oxc_span::Span) {
        let Some(parent) = self.scheduler.active else {
            return;
        };
        let Some(target) = self.scheduler.keys.get(key).copied() else {
            return;
        };
        let site = (self.source_span(file, span), key.function);

        if self.scheduler.tasks[parent.0]
            .invocations
            .get(&site)
            .is_some_and(|(observed, _)| observed.contains(&target))
        {
            return;
        }

        let charged = self.charge_work(Event::InvocationObservation, 1);
        let (observed, incomplete) = self.scheduler.tasks[parent.0]
            .invocations
            .entry(site)
            .or_default();

        match charged {
            true => observed.push(target),
            false => *incomplete = true,
        }
    }

    fn fallback_component(&mut self, members: Vec<TaskId>) {
        self.scheduler.component.clear();

        for id in members {
            self.scheduler.tasks[id.0].fallback = true;

            self.enqueue_task(id);
        }
    }

    fn fallback_invocation(
        &mut self,
        target: FunctionId,
        file: FileId,
        span: oxc_span::Span,
        deferral: Deferral,
    ) -> (Reading, bool) {
        if !self.charge_work(Event::InvocationEvaluation, 1) {
            return (
                Reading::of_part(self.deferred_unknown(
                    file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            );
        }

        let (observed, incomplete): (Vec<TaskId>, bool) = self
            .scheduler
            .active
            .map(|parent| {
                let task = &self.scheduler.tasks[parent.0];
                let (observed, incomplete) = task
                    .invocations
                    .get(&(self.source_span(file, span), target))
                    .cloned()
                    .unwrap_or_default();

                match observed.is_empty() {
                    false => (observed, incomplete),
                    true => (
                        self.scheduler
                            .closed_ready
                            .get(&(target, false, task.root_id))
                            .copied()
                            .into_iter()
                            .collect(),
                        incomplete,
                    ),
                }
            })
            .unwrap_or_default();
        let mut joined: Option<(Reading, bool)> = None;

        for id in observed {
            let (part, cyclic) =
                self.observed_invocation_of(id, file, span, deferral == Deferral::Consumed);

            joined = Some(match joined {
                Some((known, was_cyclic)) => (
                    known.merge(part, &mut self.unknowns, &mut self.traces),
                    was_cyclic || cyclic,
                ),
                None => (part, cyclic),
            });
        }

        let (reading, cyclic) = match joined {
            Some((part, cyclic)) if incomplete => {
                let unknown = self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion);
                let part = part.retaining(unknown.unknowns, &mut self.unknowns);

                (part, cyclic)
            }
            Some(joined) => joined,
            None => (
                Reading::of_part(self.deferred_unknown(
                    file,
                    span,
                    UnknownReason::ResourceExhaustion,
                )),
                false,
            ),
        };

        (self.called_phases_of(reading, deferral, file, span), cyclic)
    }

    fn observed_invocation_of(
        &mut self,
        id: TaskId,
        file: FileId,
        span: oxc_span::Span,
        consume: bool,
    ) -> (Reading, bool) {
        if self.scheduler.component.contains(&id) {
            self.current_effects.unknown_global = true;

            let reading = self.local_resource_reading(id);
            let deferred = self.scheduler.tasks[id.0]
                .deferred_reading
                .clone()
                .filter(|_| consume);

            return (self.restored_latent_reading(reading, deferred), true);
        }

        if let TaskState::Ready(record) = self.scheduler.tasks[id.0].state {
            let deferred = self
                .latent_readings
                .get(&record)
                .cloned()
                .filter(|_| consume);
            let record = self.summaries_arena[record.0 as usize].clone();

            self.current_effects.join(&record.effects);

            let cyclic = self.scheduler.active.is_some_and(|parent| {
                self.scheduler.tasks[id.0]
                    .recurrence_members
                    .contains(&self.scheduler.tasks[parent.0].key.function)
            });

            return (
                self.restored_latent_reading(record.reading, deferred),
                cyclic,
            );
        }

        (
            Reading::of_part(self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion)),
            false,
        )
    }

    fn restored_latent_reading(
        &mut self,
        mut reading: Reading,
        deferred: Option<Reading>,
    ) -> Reading {
        if let Some(deferred) = deferred {
            reading
                .completions
                .retain(|channel| channel.0 != crate::cost::ExecutionPhase::Lazy);

            reading = reading.merge(deferred, &mut self.unknowns, &mut self.traces);
        }

        reading
    }

    fn closed_function(&self, target: FunctionId) -> bool {
        let nodes = self.project.file(target.file).semantic.nodes();
        let AstKind::Function(function) = nodes.kind(target.node) else {
            return false;
        };

        if !function.params.items.is_empty()
            || function.params.rest.is_some()
            || function.this_param.is_some()
        {
            return false;
        }

        let parent = nodes.parent_id(target.node);

        matches!(nodes.kind(parent), AstKind::Program(_))
            || (matches!(
                nodes.kind(parent),
                AstKind::ExportNamedDeclaration(_) | AstKind::ExportDefaultDeclaration(_)
            ) && matches!(nodes.parent_kind(parent), AstKind::Program(_)))
    }

    pub(crate) fn trace_name_of(
        &self,
        file: FileId,
        function: FunctionNode<'a>,
    ) -> Result<String, std::fmt::Error> {
        let mut out = crate::trace::BoundedText {
            text: String::new(),
            limit: self.traces.label_limit(),
            exhausted: false,
        };

        self.write_name_of(file, function, &mut out)?;

        Ok(out.text)
    }

    pub fn name_of(&self, file: FileId, function: FunctionNode<'a>) -> String {
        let mut out = String::new();

        self.write_name_of(file, function, &mut out)
            .expect("String writer");

        out
    }

    fn write_name_of(
        &self,
        file: FileId,
        function: FunctionNode<'a>,
        out: &mut dyn std::fmt::Write,
    ) -> std::fmt::Result {
        let nodes = self.project.file(file).semantic.nodes();
        let parent = nodes.parent_id(function.node_id());
        let owner = |out: &mut dyn std::fmt::Write| {
            let body = nodes.parent_id(parent);

            if let (AstKind::ClassBody(_), AstKind::Class(class)) =
                (nodes.kind(body), nodes.parent_kind(body))
            {
                out.write_str(class.id.as_ref().map_or("<class>", |id| id.name.as_str()))?;
                out.write_char('.')?;
            }

            Ok(())
        };
        let key = |property: &oxc_ast::ast::PropertyKey<'a>,
                   computed: bool,
                   out: &mut dyn std::fmt::Write| {
            let span = property.span();

            if !computed {
                return out.write_str(self.text_of(file, span));
            }

            let source = self.project.file(file).text;
            let open = source[..span.start as usize]
                .trim_end()
                .strip_suffix('[')
                .map(str::len);
            let after = &source[span.end as usize..];
            let close = after
                .find(|character: char| !character.is_whitespace())
                .filter(|index| after[*index..].starts_with(']'));

            match (open, close) {
                (Some(open), Some(close)) => {
                    out.write_str(&source[open..span.end as usize + close + 1])
                }
                _ => {
                    out.write_char('[')?;
                    out.write_str(self.text_of(file, span))?;

                    out.write_char(']')
                }
            }
        };

        if let FunctionNode::Construction(class) = function {
            out.write_str("new ")?;

            match &class.id {
                Some(id) => out.write_str(id.name.as_str())?,
                None => match nodes.kind(parent) {
                    AstKind::VariableDeclarator(declaration) => {
                        out.write_str(self.text_of(file, declaration.id.span()))?
                    }
                    AstKind::ExportDefaultDeclaration(_) => out.write_str("<default>")?,
                    _ => out.write_str("<class>")?,
                },
            }

            return out.write_str("()");
        }

        if let FunctionNode::Function(inner) = function {
            if inner.is_declaration() {
                return out.write_str(inner.id.as_ref().map_or("<default>", |id| id.name.as_str()));
            }

            if let AstKind::MethodDefinition(method) = nodes.kind(parent) {
                owner(out)?;

                return if method.kind == MethodDefinitionKind::Constructor {
                    out.write_str("constructor")
                } else {
                    key(&method.key, method.computed, out)
                };
            }
        }

        match nodes.kind(parent) {
            AstKind::VariableDeclarator(declaration) => {
                return out.write_str(self.text_of(file, declaration.id.span()))
            }
            AstKind::ObjectProperty(property) => return key(&property.key, property.computed, out),
            AstKind::PropertyDefinition(property) => {
                owner(out)?;

                return key(&property.key, property.computed, out);
            }
            AstKind::AccessorProperty(property) => {
                owner(out)?;

                return key(&property.key, property.computed, out);
            }
            _ => {}
        }

        if let FunctionNode::Function(inner) = function {
            if let Some(id) = &inner.id {
                return out.write_str(id.name.as_str());
            }
        }

        out.write_str(match nodes.kind(parent) {
            AstKind::CallExpression(_) | AstKind::NewExpression(_) => "<callback>",
            AstKind::ReturnStatement(_) => "<returned fn>",
            _ => "<anonymous>",
        })
    }

    pub(crate) fn function_start_of(&self, file: FileId, function: FunctionNode<'a>) -> u32 {
        let nodes = self.project.file(file).semantic.nodes();
        let node = function.node_id();

        if let FunctionNode::Function(_) = function {
            match nodes.parent_kind(node) {
                AstKind::MethodDefinition(method) => return method.span.start,
                AstKind::ObjectProperty(property)
                    if property.method || property.kind != PropertyKind::Init =>
                {
                    return property.span.start
                }
                _ => {}
            }
        }

        nodes.kind(node).span().start
    }

    pub fn function_site_of(&self, file: FileId, function: FunctionNode<'a>) -> Site {
        Site {
            file,
            line: self
                .project
                .line_of(file, self.function_start_of(file, function)),
        }
    }

    pub fn reportable(&mut self) -> Vec<(FileId, FunctionNode<'a>)> {
        let project = self.project;
        let mut found = Vec::new();

        for source in &project.files {
            let file = source.id;

            if !project.is_project_file(file)
                || project.is_test_path(file)
                || source.relative.starts_with("..")
            {
                continue;
            }

            let nodes = source.semantic.nodes();
            let mut functions: Vec<FunctionNode<'a>> = nodes
                .iter()
                .filter_map(|node| {
                    let parent = nodes.parent_kind(node.id());
                    let inline = matches!(
                        parent,
                        AstKind::CallExpression(_) | AstKind::NewExpression(_)
                    );

                    match node.kind() {
                        AstKind::Function(function) if function.body.is_some() => (!(inline
                            && function.is_expression()))
                        .then_some(FunctionNode::Function(function)),
                        AstKind::ArrowFunctionExpression(arrow) => {
                            (!inline).then_some(FunctionNode::Arrow(arrow))
                        }
                        AstKind::Class(class) => {
                            self.declarations.construction_of(project, file, class)
                        }
                        _ => None,
                    }
                })
                .collect();

            functions.sort_by_key(|function| {
                let end = nodes.kind(function.node_id()).span().end;

                (
                    self.function_start_of(file, *function),
                    std::cmp::Reverse(end),
                )
            });

            for function in functions {
                if !self
                    .function_tags(file, function)
                    .contains(&PerfTag::Ignore)
                {
                    found.push((file, function));
                }
            }
        }

        found
    }

    pub fn reset_between_passes(&mut self) {
        self.summaries.clear();

        let generation = self
            .scheduler
            .generation
            .checked_add(1)
            .expect("analysis generation fits u64");
        let limits = self.scheduler.limits;
        let callbacks = std::mem::take(&mut self.scheduler.callbacks);
        let callback_values = std::mem::take(&mut self.scheduler.callback_values);
        let body_sizes = std::mem::take(&mut self.scheduler.body_sizes);
        self.scheduler = Scheduler::new(limits, generation);
        self.scheduler.callbacks = callbacks;
        self.scheduler.callback_values = callback_values;
        self.scheduler.body_sizes = body_sizes;

        self.bound_seen.clear();
        self.pending_scoped.clear();

        self.current_effects = Effects::default();
        self.stats = Stats::default();
    }

    pub fn summarize_reportable(&mut self, functions: &[(FileId, FunctionNode<'a>)]) {
        for (file, function) in functions {
            self.summarize(*file, *function);

            let tags = self.function_tags(*file, *function);

            if cost_tag_of(&tags).is_some() {
                self.summarize_with(*file, *function, Substitutions::new(), true);
            }
        }
    }

    pub fn gather_answers(
        &mut self,
        functions: &[(FileId, FunctionNode<'a>)],
        mut ask: impl FnMut(&[Query]) -> Result<TscReply, TscError>,
    ) -> Result<TscRounds, TscError> {
        let mut rounds = TscRounds::default();

        self.set_pass(TscPass::Recording);

        loop {
            self.summarize_reportable(functions);

            let queries = self.needed_queries();
            let asked_nothing = queries.is_empty();

            if !asked_nothing || rounds.rounds == 0 {
                let reply = ask(&queries)?;

                rounds.sites += queries.len();
                rounds.rounds += 1;

                self.take_answers(reply)?;
            }

            self.reset_between_passes();

            if asked_nothing {
                break;
            }
        }

        self.set_pass(TscPass::Answering);

        Ok(rounds)
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    fn returned_latent_reading_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        reading: Reading,
    ) -> Reading {
        let target = FunctionId {
            file,
            node: function.node_id(),
        };

        if self.is_asynchronous_target(target) || !self.may_return_latent(target, 0) {
            return reading;
        }

        let mut found: Option<Latent> = None;
        let mut mixed = false;

        for returned in self.returned_expressions_of(target) {
            match self.latent_of(file, returned) {
                Some(latent) => {
                    found = Some(self.joined_latent_of(
                        found,
                        latent,
                        self.source_span(file, returned.span()),
                    ))
                }
                None => mixed = true,
            }
        }

        let Some(mut latent) = found else {
            return reading;
        };

        if mixed {
            latent.yields = None;
        }

        self.deferred_reading = Some(self.reading_of_latent(&latent));
        self.produced = Some(Produced {
            count: latent.yields,
            yielded: true,
        });

        let mut reading = reading;

        reading.join(
            crate::cost::ExecutionPhase::Lazy,
            Completion::Normal,
            latent.work,
            &mut self.unknowns,
            &mut self.traces,
        );

        reading
    }

    fn is_generator_target(&self, target: FunctionId) -> bool {
        matches!(self.function_at(target), FunctionNode::Function(function) if function.generator)
    }

    fn is_asynchronous_target(&self, target: FunctionId) -> bool {
        match self.function_at(target) {
            FunctionNode::Function(function) => function.r#async,
            FunctionNode::Arrow(arrow) => arrow.r#async,
            FunctionNode::Construction(_) => false,
        }
    }

    fn joined_latent_of(
        &mut self,
        held: Option<Latent>,
        latent: Latent,
        origin: crate::unknowns::SourceSpan,
    ) -> Latent {
        let Some(held) = held else {
            return latent;
        };
        let deferred = self.reading_of_latent(&held).merge(
            self.reading_of_latent(&latent),
            &mut self.unknowns,
            &mut self.traces,
        );
        let mut effects = held.effects;

        effects.join(&latent.effects);

        let mut result = Latent {
            work: held
                .work
                .max(latent.work, &mut self.unknowns, &mut self.traces),
            yields: match (held.yields, latent.yields) {
                (Some(left), Some(right)) => Cost::maximum(vec![left, right]).ok(),
                _ => None,
            },
            effects,
            record: None,
            deferred: Some(deferred.clone()),
        };

        result.record = self.store_latent_record(result.clone(), deferred, origin);

        result
    }

    pub(crate) fn latent_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<Latent> {
        if !self.may_be_latent(file, expression, 0) {
            return None;
        }

        self.latent_at(file, expression, 0)
    }

    fn latent_at(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Option<Latent> {
        if depth > MAXIMUM_LATENT_DEPTH || !self.charge_work(Event::LatentStep, 1) {
            return Some(self.unresolved_latent_of(
                (file, expression.span()),
                UnknownReason::ResourceExhaustion,
            ));
        }

        match unwrap(expression) {
            Expression::CallExpression(call) => self.call_latent_of(file, call),
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference)?;

                if let Some(binding) = self.parameter_binding_of(declaration) {
                    let id = self
                        .current_substitutions
                        .get(&binding)
                        .and_then(|facts| facts.value.latent)?;

                    if !self.is_parameter_unwritten(binding) {
                        return None;
                    }

                    return Some(self.record_latent_of(id, false));
                }

                let (source, initializer) = crate::constants::constant_initializer_of(declaration)?;

                self.latent_at(source, initializer, depth + 1)
            }
            Expression::ConditionalExpression(conditional) => self.alternative_latent_of(
                file,
                [&conditional.consequent, &conditional.alternate],
                depth,
            ),
            Expression::LogicalExpression(logical) => {
                self.alternative_latent_of(file, [&logical.left, &logical.right], depth)
            }
            Expression::SequenceExpression(sequence) => {
                self.latent_at(file, sequence.expressions.last()?, depth + 1)
            }
            _ => None,
        }
    }

    fn alternative_latent_of(
        &mut self,
        file: FileId,
        alternatives: [&'a Expression<'a>; 2],
        depth: usize,
    ) -> Option<Latent> {
        let mut found: Option<Latent> = None;
        let mut mixed = false;

        for alternative in alternatives {
            let latent = match self.may_be_latent(file, alternative, depth + 1) {
                true => self.latent_at(file, alternative, depth + 1),
                false => None,
            };

            match latent {
                Some(latent) => {
                    found = Some(self.joined_latent_of(
                        found,
                        latent,
                        self.source_span(file, alternative.span()),
                    ))
                }
                None => mixed = true,
            }
        }

        found.map(|latent| match mixed {
            true => Latent {
                yields: None,
                ..latent
            },
            false => latent,
        })
    }

    pub(crate) fn call_latent_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<Latent> {
        let targets = self.resolved_callee_of(file, call).targets;

        self.targets_latent_of(file, call, targets)
    }

    fn targets_latent_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        targets: TargetSet,
    ) -> Option<Latent> {
        let mut found: Option<Latent> = None;
        let mut missing = targets.open;

        for target in targets.known {
            match self.invocation_latent_of(target, file, call) {
                Some(latent) => {
                    found = Some(self.joined_latent_of(
                        found,
                        latent,
                        self.source_span(file, call.span),
                    ))
                }
                None => missing = true,
            }
        }

        found.map(|latent| match missing {
            true => Latent {
                yields: None,
                ..latent
            },
            false => latent,
        })
    }

    fn invocation_latent_of(
        &mut self,
        target: FunctionId,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<Latent> {
        let generator = self.is_generator_target(target);

        if !generator && (self.is_asynchronous_target(target) || !self.may_return_latent(target, 0))
        {
            return None;
        }

        let function = self.function_at(target);
        let origin = (file, call.span);
        let Some(captured) = self.inherited_substitutions_of(target.file, function) else {
            return Some(self.unresolved_latent_of(origin, UnknownReason::ResourceExhaustion));
        };
        let substitutions = self.invocation_substitutions_of(
            (target.file, function),
            (file, &call.arguments),
            false,
            captured,
        );
        let substitutions = self.function_inputs(target.file, function, substitutions);
        let Ok(key) = self.key_of(target.file, function, &substitutions) else {
            self.scheduler.exhausted = true;

            return Some(self.unresolved_latent_of(origin, UnknownReason::ResourceExhaustion));
        };

        if !self.charge_work(Event::LatentStep, 1) {
            return Some(self.unresolved_latent_of(origin, UnknownReason::ResourceExhaustion));
        }

        let (reading, cyclic) = self.request_reading(key.clone(), substitutions);

        if cyclic {
            let total = reading.total(&mut self.unknowns, &mut self.traces);
            let latent = reading.latent(&mut self.unknowns, &mut self.traces);

            return Some(Latent::unresolved(total.max(
                latent,
                &mut self.unknowns,
                &mut self.traces,
            )));
        }

        let ready = self.summaries.get(&key).copied().or_else(|| {
            self.scheduler.keys.get(&key).and_then(|task| {
                match self.scheduler.tasks[task.0].state {
                    TaskState::Ready(id) => Some(id),
                    _ => None,
                }
            })
        });

        match ready {
            Some(id)
                if generator || self.summaries_arena[id.0 as usize].result.latent.is_some() =>
            {
                Some(self.record_latent_of(id, generator))
            }
            Some(_) => None,
            None => Some(Latent::unresolved(Part::none())),
        }
    }

    fn unresolved_latent_of(
        &mut self,
        (file, span): (FileId, oxc_span::Span),
        reason: UnknownReason,
    ) -> Latent {
        let unknown = self.unknown_part(file, span, reason);

        Latent::unresolved(unknown)
    }

    fn record_latent_of(&mut self, id: SummaryId, generator: bool) -> Latent {
        let record = &self.summaries_arena[id.0 as usize];
        let reading = record.reading.clone();
        let yields = match (record.result.latent.is_some(), generator) {
            (false, true) => None,
            _ => record.result.size.clone(),
        };
        let effects = record.effects.clone();

        Latent {
            work: reading.latent(&mut self.unknowns, &mut self.traces),
            yields,
            effects,
            record: Some(id),
            deferred: self.latent_readings.get(&id).cloned(),
        }
    }

    pub(crate) fn latent_record_of(
        &mut self,
        latent: Latent,
        origin: crate::unknowns::SourceSpan,
    ) -> Option<SummaryId> {
        if let Some(record) = latent.record {
            return Some(record);
        }

        let reading = self.reading_of_latent(&latent);

        self.store_latent_record(latent, reading, origin)
    }

    fn store_latent_record(
        &mut self,
        latent: Latent,
        deferred: Reading,
        origin: crate::unknowns::SourceSpan,
    ) -> Option<SummaryId> {
        if !self.charge_work(Event::LatentStep, 1) {
            return None;
        }

        let id =
            SummaryId(u32::try_from(self.summaries_arena.len()).expect("summary arena fits u32"));
        let mut result = self.values.at(origin);

        result.latent = Some(id);
        result.size = latent.yields;

        self.summaries_arena.push(SummaryRecord {
            reading: Reading::of_completion(
                crate::cost::ExecutionPhase::Lazy,
                Completion::Normal,
                latent.work,
            ),
            result,
            effects: latent.effects,
        });

        self.latent_readings.insert(id, deferred);

        Some(id)
    }

    pub(crate) fn latent_size_of(&self, latent: &Latent) -> crate::values::Size {
        let size = crate::values::Size {
            exceeds: true,
            element_resolved: false,
            ..crate::values::Size::sized(latent.yields.clone().unwrap_or(Cost::N))
        };

        match latent.yields {
            Some(_) => size,
            None => size.unresolved_length(),
        }
    }

    pub(crate) fn consumed_part_of(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
        latent: &Latent,
    ) -> Reading {
        let origin = self.source_span(file, span);

        self.current_effects.join(&latent.effects);

        let part = self
            .reading_of_latent(latent)
            .map_parts(|part| match part.cost.is_one() {
                true => part,
                false => part.explain(
                    format_args!(
                        "call {} [lazy]",
                        crate::bounds::short(self.text_of(file, span))
                    ),
                    self.project.site_of(file, span),
                    origin,
                    true,
                    &mut self.traces,
                    &mut self.unknowns,
                ),
            });

        part.called(origin, &mut self.unknowns)
            .normalized(&mut self.unknowns, &mut self.traces)
    }

    fn reading_of_latent(&self, latent: &Latent) -> Reading {
        latent
            .deferred
            .as_ref()
            .or_else(|| latent.record.and_then(|id| self.latent_readings.get(&id)))
            .cloned()
            .unwrap_or_else(|| Reading::of_part(latent.work.clone()))
    }

    pub(crate) fn untracked_latent_part_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        targets: &TargetSet,
    ) -> Option<Reading> {
        if !self.may_return_latent_targets(file, call, targets, 0)
            || self.is_tracked_consumption(file, call.node_id(), 0)
        {
            return None;
        }

        let latent = self.targets_latent_of(file, call, targets.clone())?;
        let part = self.consumed_part_of(file, call.span, &latent);
        let origin = self.source_span(file, call.span);
        let unknown = self.unknowns.origin(origin, UnknownReason::Multiplicity);

        Some(part.retaining(Some(unknown), &mut self.unknowns))
    }

    fn may_be_latent(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_LATENT_DEPTH {
            return true;
        }

        match unwrap(expression) {
            Expression::CallExpression(call) => self.may_return_latent_call(file, call, depth),
            Expression::Identifier(reference) => {
                let Some(declaration) =
                    self.declarations
                        .of_reference(self.project, file, reference)
                else {
                    return false;
                };

                if let Some(binding) = self.parameter_binding_of(declaration) {
                    return self
                        .current_substitutions
                        .get(&binding)
                        .is_some_and(|facts| facts.value.latent.is_some());
                }

                match crate::constants::constant_initializer_of(declaration) {
                    Some((source, initializer)) => {
                        self.may_be_latent(source, initializer, depth + 1)
                    }
                    None => false,
                }
            }
            Expression::ConditionalExpression(conditional) => {
                self.may_be_latent(file, &conditional.consequent, depth + 1)
                    || self.may_be_latent(file, &conditional.alternate, depth + 1)
            }
            Expression::LogicalExpression(logical) => {
                self.may_be_latent(file, &logical.left, depth + 1)
                    || self.may_be_latent(file, &logical.right, depth + 1)
            }
            Expression::SequenceExpression(sequence) => sequence
                .expressions
                .last()
                .is_some_and(|last| self.may_be_latent(file, last, depth + 1)),
            _ => false,
        }
    }

    fn may_return_latent_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        depth: usize,
    ) -> bool {
        let targets = self.resolved_callee_of(file, call).targets;

        self.may_return_latent_targets(file, call, &targets, depth)
    }

    fn may_return_latent_targets(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        targets: &TargetSet,
        depth: usize,
    ) -> bool {
        targets.known.iter().copied().any(|target| {
            if self.is_generator_target(target) {
                return true;
            }

            if self.is_asynchronous_target(target) {
                return false;
            }

            let sources = self.target_latent_sources_of(target, depth + 1);

            sources.direct
                || sources.parameters.into_iter().any(|index| {
                    call.arguments
                        .get(index)
                        .and_then(Argument::as_expression)
                        .is_some_and(|argument| self.may_be_latent(file, argument, depth + 1))
                })
        })
    }

    fn may_return_latent(&mut self, target: FunctionId, depth: usize) -> bool {
        if self.is_generator_target(target) {
            return true;
        }

        let sources = self.target_latent_sources_of(target, depth);

        sources.direct || !sources.parameters.is_empty()
    }

    fn target_latent_sources_of(&mut self, target: FunctionId, depth: usize) -> LatentSources {
        let everything = LatentSources {
            direct: true,
            parameters: Vec::new(),
        };

        if depth > MAXIMUM_LATENT_DEPTH {
            return everything;
        }

        let key = (target, self.scheduler.generation);

        if let Some(found) = self.latent_returns.get(&key) {
            return found.clone();
        }

        self.latent_returns.insert(key, LatentSources::default());

        let found = match self.charge_work(Event::LatentStep, 1) {
            true => {
                let mut found = LatentSources::default();

                for returned in self.returned_expressions_of(target) {
                    let sources = self.latent_sources_of(target, returned, depth + 1);

                    found.join(sources);
                }

                found
            }
            false => everything,
        };

        self.latent_returns.insert(key, found.clone());

        found
    }

    fn latent_sources_of(
        &mut self,
        owner: FunctionId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> LatentSources {
        let file = owner.file;
        let mut found = LatentSources::default();

        if depth > MAXIMUM_LATENT_DEPTH {
            found.direct = true;

            return found;
        }

        match unwrap(expression) {
            Expression::CallExpression(call) => {
                let targets = self.resolved_callee_of(file, call).targets;

                for target in targets.known {
                    if self.is_generator_target(target) {
                        found.direct = true;

                        continue;
                    }

                    if self.is_asynchronous_target(target) {
                        continue;
                    }

                    let sources = self.target_latent_sources_of(target, depth + 1);

                    found.direct |= sources.direct;

                    for index in sources.parameters {
                        if let Some(argument) =
                            call.arguments.get(index).and_then(Argument::as_expression)
                        {
                            let sources = self.latent_sources_of(owner, argument, depth + 1);

                            found.join(sources);
                        }
                    }
                }
            }
            Expression::Identifier(reference) => {
                match self
                    .declarations
                    .of_reference(self.project, file, reference)
                {
                    Some(Declaration::Parameter {
                        parameter: ParameterNode::Formal(parameter),
                        function,
                        ..
                    }) if function.node_id() == owner.node => {
                        let index = parameters_of(function).and_then(|parameters| {
                            parameters
                                .items
                                .iter()
                                .position(|item| item.span == parameter.span)
                        });

                        match index {
                            Some(index) => found.parameters.push(index),
                            None => found.direct = true,
                        }
                    }
                    Some(Declaration::Parameter { .. }) => found.direct = true,
                    Some(declaration) => {
                        if let Some((source, initializer)) =
                            crate::constants::constant_initializer_of(declaration)
                        {
                            let sources = self.latent_sources_of(
                                FunctionId {
                                    file: source,
                                    node: owner.node,
                                },
                                initializer,
                                depth + 1,
                            );

                            found.join(sources);
                        }
                    }
                    None => {}
                }
            }
            Expression::ConditionalExpression(conditional) => {
                for branch in [&conditional.consequent, &conditional.alternate] {
                    let sources = self.latent_sources_of(owner, branch, depth + 1);

                    found.join(sources);
                }
            }
            Expression::LogicalExpression(logical) => {
                for branch in [&logical.left, &logical.right] {
                    let sources = self.latent_sources_of(owner, branch, depth + 1);

                    found.join(sources);
                }
            }
            Expression::SequenceExpression(sequence) => {
                if let Some(last) = sequence.expressions.last() {
                    found = self.latent_sources_of(owner, last, depth + 1);
                }
            }
            _ => {}
        }

        found
    }

    pub(crate) fn is_tracked_consumption(
        &mut self,
        file: FileId,
        node: NodeId,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_LATENT_DEPTH || !self.charge_work(Event::LatentStep, 1) {
            return false;
        }

        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let mut current = node;

        loop {
            current = crate::values::outermost_of(nodes, current);

            let span = nodes.kind(current).span();
            let parent = nodes.parent_id(current);

            match nodes.kind(parent) {
                AstKind::ConditionalExpression(conditional) if conditional.test.span() == span => {
                    return true
                }
                AstKind::SequenceExpression(sequence)
                    if sequence
                        .expressions
                        .last()
                        .is_none_or(|last| last.span() != span) =>
                {
                    return true
                }
                AstKind::LogicalExpression(_)
                | AstKind::ConditionalExpression(_)
                | AstKind::SequenceExpression(_) => current = parent,
                AstKind::ExpressionStatement(_) => return true,
                AstKind::UnaryExpression(unary) => {
                    return unary.operator == oxc_syntax::operator::UnaryOperator::Void;
                }
                AstKind::ForOfStatement(statement) => return statement.right.span() == span,
                AstKind::SpreadElement(_) => return true,
                AstKind::YieldExpression(yielded) => return yielded.delegate,
                AstKind::ReturnStatement(_) => return self.returns_value(file, parent),
                AstKind::ArrowFunctionExpression(arrow) => {
                    return arrow.get_expression().is_some();
                }
                AstKind::StaticMemberExpression(member) => {
                    let AstKind::CallExpression(call) = nodes.parent_kind(parent) else {
                        return false;
                    };

                    return member.object.span() == span
                        && call.callee.span() == member.span
                        && RESUMPTIONS.contains(&member.property.name.as_str())
                        && self.resolved_callee_of(file, call).targets.known.is_empty();
                }
                AstKind::CallExpression(call) => {
                    return self.is_tracked_argument(file, call, span, depth);
                }
                AstKind::VariableDeclarator(declarator) => {
                    if matches!(declarator.id, BindingPattern::ArrayPattern(_)) {
                        return declarator
                            .init
                            .as_ref()
                            .is_some_and(|init| init.span() == span)
                            && !matches!(
                                nodes.parent_kind(nodes.parent_id(parent)),
                                AstKind::ForOfStatement(_) | AstKind::ForInStatement(_)
                            );
                    }

                    return self.is_tracked_holder(file, parent, declarator, depth);
                }
                AstKind::AssignmentExpression(assignment) => {
                    return assignment.right.span() == span
                        && matches!(
                            assignment.left,
                            oxc_ast::ast::AssignmentTarget::ArrayAssignmentTarget(_)
                        );
                }
                _ => return false,
            }
        }
    }

    fn returns_value(&self, file: FileId, statement: NodeId) -> bool {
        self.project
            .file(file)
            .semantic
            .nodes()
            .ancestors(statement)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(!function.generator),
                AstKind::ArrowFunctionExpression(_) => Some(true),
                _ => None,
            })
            .unwrap_or(false)
    }

    fn is_tracked_argument(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        span: oxc_span::Span,
        depth: usize,
    ) -> bool {
        if call.callee.span() == span {
            return false;
        }

        let Some(index) = call
            .arguments
            .iter()
            .position(|argument| argument.span() == span)
        else {
            return false;
        };

        if call.arguments[..index]
            .iter()
            .any(|argument| matches!(argument, Argument::SpreadElement(_)))
        {
            return false;
        }

        let targets = self.resolved_callee_of(file, call).targets;

        if targets.known.is_empty() {
            let member = self.callee_member_of(file, call);

            return match self.native_of(file, call, member, false) {
                crate::native::Native::Modelled(model) => {
                    self.call_site_of(file, call, member).iterates(model, index)
                }
                _ => false,
            };
        }

        if targets.open {
            return false;
        }

        targets.known.into_iter().all(|target| {
            let function = self.function_at(target);
            let Some(parameter) =
                parameters_of(function).and_then(|parameters| parameters.items.get(index))
            else {
                return false;
            };
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                return false;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                return false;
            };

            parameter.initializer.is_none()
                && self.is_parameter_unwritten(Binding::Symbol {
                    file: target.file,
                    symbol,
                })
                && self.are_references_tracked(target.file, symbol, depth)
        })
    }

    fn is_tracked_holder(
        &mut self,
        file: FileId,
        node: NodeId,
        declarator: &'a oxc_ast::ast::VariableDeclarator<'a>,
        depth: usize,
    ) -> bool {
        let project = self.project;
        let constant = matches!(
            project.file(file).semantic.nodes().parent_kind(node),
            AstKind::VariableDeclaration(declaration)
                if declaration.kind == oxc_ast::ast::VariableDeclarationKind::Const
                    && !declaration.declare
        );
        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
            return false;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            return false;
        };

        constant && self.are_references_tracked(file, symbol, depth)
    }

    fn are_references_tracked(
        &mut self,
        file: FileId,
        symbol: oxc_semantic::SymbolId,
        depth: usize,
    ) -> bool {
        let project = self.project;
        let references: Vec<NodeId> = project
            .file(file)
            .semantic
            .scoping()
            .get_resolved_references(symbol)
            .filter(|reference| !reference.flags().is_type())
            .map(oxc_semantic::Reference::node_id)
            .collect();

        references
            .into_iter()
            .all(|reference| self.is_tracked_consumption(file, reference, depth + 1))
    }
}

fn marker_cost_of(index: usize) -> Cost {
    Cost::dimension(RECURRENCE_BASE - index as u64, crate::cost::Domain::Size)
}

fn stripped_cost_of(cost: &Cost, members: usize) -> Option<(Cost, Vec<Option<Cost>>)> {
    let mut residue = cost.clone();
    let mut factors = Vec::new();

    for index in 0..members {
        let (local, factor) = residue.split_dimension(RECURRENCE_BASE - index as u64)?;

        residue = local;

        factors.push(factor);
    }

    Some((residue, factors))
}

fn site_count_of((caller, callee): (TaskId, TaskId), markers: &RecurrenceMarkers) -> u64 {
    markers
        .steps
        .keys()
        .filter(|(site_caller, site_callee, _)| *site_caller == caller && *site_callee == callee)
        .count() as u64
}

fn arguments_bounded_of(
    (caller, callee): (TaskId, TaskId),
    measure: usize,
    markers: &RecurrenceMarkers,
) -> bool {
    markers
        .bounds
        .iter()
        .filter(|((site_caller, site_callee, _), _)| {
            *site_caller == caller && *site_callee == callee
        })
        .all(|(_, bounds)| bounds.admits(measure))
}

fn recurrence_relation_of(
    (caller, callee): (TaskId, TaskId),
    (caller_position, callee_position): (usize, usize),
    markers: &RecurrenceMarkers,
) -> Option<(ArgumentRelation, Option<f64>)> {
    let mut relation: Option<ArgumentRelation> = None;
    let mut lower_bound: Option<f64> = None;
    let mut seen = false;

    for ((site_caller, site_callee, _), steps) in &markers.steps {
        if *site_caller != caller || *site_callee != callee {
            continue;
        }

        let step = steps.iter().find(|step| {
            step.caller_position == caller_position && step.callee_position == callee_position
        })?;

        relation = Some(match relation {
            None => step.relation,
            Some(found) => weaker_relation_of(found, step.relation),
        });
        lower_bound = match (seen, lower_bound, step.lower_bound) {
            (false, _, bound) => bound,
            (true, Some(found), Some(bound)) => Some(f64::min(found, bound)),
            _ => None,
        };
        seen = true;
    }

    relation.map(|relation| (relation, lower_bound))
}

fn slots_from(
    members: &[TaskId],
    multiplicities: &[Vec<Option<Cost>>],
    markers: &RecurrenceMarkers,
    candidate: usize,
) -> Option<Vec<usize>> {
    let mut slots: Vec<Option<usize>> = vec![None; members.len()];
    let mut pending = vec![0usize];

    slots[0] = Some(candidate);

    while let Some(index) = pending.pop() {
        let caller_position = slots[index]?;

        for (callee, multiplicity) in multiplicities[index].iter().enumerate() {
            if multiplicity.is_none() {
                continue;
            }

            let mut position = None;

            for ((site_caller, site_callee, _), steps) in &markers.steps {
                if *site_caller != members[index] || *site_callee != members[callee] {
                    continue;
                }

                let step = steps
                    .iter()
                    .find(|step| step.caller_position == caller_position)?;

                if position.is_some_and(|found| found != step.callee_position) {
                    return None;
                }

                position = Some(step.callee_position);
            }

            let position = position?;

            match slots[callee] {
                Some(found) if found != position => return None,
                Some(_) => {}
                None => {
                    slots[callee] = Some(position);

                    pending.push(callee);
                }
            }
        }
    }

    slots.into_iter().collect()
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn promise_settlers_of(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
    ) -> [ArgumentFacts; 2] {
        let descriptor = match self.scheduler.promise_resolver {
            Some(descriptor) => descriptor,
            None => {
                let descriptor = self.scheduler.callbacks.len();

                self.scheduler
                    .callbacks
                    .push(CallbackDescriptor::PromiseResolve {
                        generation: self.scheduler.generation,
                    });

                self.scheduler.promise_resolver = Some(descriptor);

                descriptor
            }
        };
        let resolve = self.values.callback(descriptor);

        self.scheduler
            .callback_values
            .insert(resolve.value, descriptor);

        [
            ArgumentFacts {
                value: resolve,
                callback: None,
                preference: Preference::Absent,
                definedness: Definedness::Defined,
            },
            ArgumentFacts {
                value: self.values.at(self.source_span(file, span)),
                callback: Some(Part::none()),
                preference: Preference::Absent,
                definedness: Definedness::Defined,
            },
        ]
    }

    pub(crate) fn enter_promise_assimilation(&mut self, file: FileId, node: NodeId) -> bool {
        self.charge_work(Event::CallbackDescriptor, 1)
            && self.scheduler.assimilating.len() < MAXIMUM_LATENT_DEPTH
            && self.scheduler.assimilating.insert((file, node))
    }

    pub(crate) fn leave_promise_assimilation(&mut self, file: FileId, node: NodeId) {
        self.scheduler.assimilating.remove(&(file, node));
    }

    pub(crate) fn invoke_promise_handler(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
    ) -> Reading {
        self.invoke_callback_with_facts(facts, file, span, &[], true)
    }

    pub(crate) fn invoke_callback_with_facts(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        supplied: &[ArgumentFacts],
        assimilate_result: bool,
    ) -> Reading {
        let Some(descriptor) = self
            .scheduler
            .callback_values
            .get(&facts.value.value)
            .copied()
        else {
            return self.invoke_callback(facts, file, span, &[]);
        };
        let descriptor = self.scheduler.callbacks[descriptor].clone();

        if descriptor.generation() != self.scheduler.generation {
            return Reading::of_part(self.deferred_unknown(file, span, UnknownReason::Target));
        }

        let CallbackDescriptor::Source {
            function: target,
            mut captured,
            ..
        } = descriptor
        else {
            return Reading::of_part(self.unknown_part(file, span, UnknownReason::Target));
        };
        let function = self.function_at(target);

        if let Some(parameters) = parameters_of(function) {
            for (parameter, facts) in parameters.items.iter().zip(supplied) {
                let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                    continue;
                };

                if let Some(symbol) = identifier.symbol_id.get() {
                    captured.insert(
                        Binding::Symbol {
                            file: target.file,
                            symbol,
                        },
                        facts.clone(),
                    );
                }
            }
        }

        let (mut reading, cyclic) = if self.fallback_active() {
            self.fallback_invocation(target, file, span, Deferral::Excluded)
        } else {
            self.call_with_captures(
                (target.file, function),
                (file, &[], span),
                (true, Deferral::Excluded),
                captured.clone(),
            )
        };

        if assimilate_result
            && !matches!(function, FunctionNode::Function(inner) if inner.r#async)
            && !matches!(function, FunctionNode::Arrow(inner) if inner.r#async)
        {
            let returned = self.assimilated_returns_of(target, captured, file, span);

            reading = reading.merge(returned, &mut self.unknowns, &mut self.traces);
        }

        if facts.value.targets.open {
            let unknown = self.unknown_part(file, span, UnknownReason::Target);

            reading = reading.merge(
                Reading::of_part(unknown),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        self.called_reading_of(target.file, function, reading, cyclic)
    }

    fn assimilated_returns_of(
        &mut self,
        target: FunctionId,
        captured: Substitutions,
        file: FileId,
        span: oxc_span::Span,
    ) -> Reading {
        if !self.charge_work(Event::CallbackDescriptor, 1) {
            return Reading::of_part(self.deferred_unknown(
                file,
                span,
                UnknownReason::ResourceExhaustion,
            ));
        }

        if self.is_generator_target(target) {
            return match self
                .may_implement_any(&[crate::values::MemberKey::Name("then".to_string())])
            {
                true => Reading::of_part(self.unknown_part(file, span, UnknownReason::Target)),
                false => Reading::empty(),
            };
        }

        let function = self.function_at(target);
        let substitutions =
            self.invocation_substitutions_of((target.file, function), (file, &[]), true, captured);
        let substitutions = self.defaulted_substitutions_of((target.file, function), substitutions);
        let substitutions = self.function_inputs(target.file, function, substitutions);
        let previous = std::mem::replace(&mut self.current_substitutions, substitutions);
        let mut reading = Reading::empty();

        for returned in self.returned_expressions_of(target) {
            let assimilated = self.assimilated_reading_of(target.file, returned);

            reading = reading.merge(assimilated, &mut self.unknowns, &mut self.traces);
        }

        self.current_substitutions = previous;

        reading
    }
}

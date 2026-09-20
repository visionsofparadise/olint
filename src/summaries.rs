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
use crate::declarations::{Binding, Declaration, FunctionId, FunctionNode, TargetSet};
use crate::directives::{cost_tag_of, PerfTag};
use crate::effects::Effects;
use crate::project::{FileId, Site};
use crate::syntax::unwrap;
use crate::tsc::{Query, TscError, TscReply};
use crate::types::TscPass;
use crate::unknowns::UnknownReason;
use crate::values::{
    ArgumentFacts, ConstructionPlan, Definedness, SizeQuantity, ValueFacts, ValueId,
};
use crate::walker::tagged_reading_of;

const MAXIMUM_PATTERN_ALIASES: usize = 8;

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
}

#[derive(Clone)]
struct CallbackDescriptor {
    function: FunctionId,
    captured: Substitutions,
    generation: u64,
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
    runtime: HashSet<(FunctionId, FunctionId)>,
    sites: HashSet<(FunctionId, crate::unknowns::SourceSpan, FunctionId)>,
    function_counts: HashMap<(FunctionId, bool, Vec<Cost>), usize>,
    exhausted: bool,
    fallback_active: bool,
    active_credit: Option<FallbackCredit>,
    callbacks: Vec<CallbackDescriptor>,
    callback_keys: HashMap<SummaryKey, usize>,
    callback_values: HashMap<ValueId, usize>,
    local_records: HashMap<TaskId, SummaryRecord>,
    body_sizes: HashMap<FunctionId, u64>,
    constructions: HashMap<ConstructionKey, (Part, Effects)>,
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
            runtime: HashSet::new(),
            sites: HashSet::new(),
            function_counts: HashMap::new(),
            exhausted: false,
            fallback_active: false,
            active_credit: None,
            callbacks: Vec::new(),
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
            let parameters = match scope {
                FunctionNode::Function(inner) => &inner.params,
                FunctionNode::Arrow(inner) => &inner.params,
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

        for part in [
            &mut reading.main,
            &mut reading.function_exit,
            &mut reading.loop_exit,
        ] {
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
    ) -> SummaryId {
        effects
            .binding_writes
            .retain(|binding| !self.is_declared_within(*binding, key.function));

        let span = self
            .kind_of_node(key.function.file, key.function.node)
            .span();
        let origin = self.source_span(key.function.file, span);
        let result = self.values.at(origin);
        let id =
            SummaryId(u32::try_from(self.summaries_arena.len()).expect("summary arena fits u32"));

        self.summaries_arena.push(SummaryRecord {
            reading,
            result,
            effects,
        });
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

        let record = self.store_summary(key, reading, effects);
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
        let effects = std::mem::replace(&mut self.current_effects, saved_effects);
        self.current_substitutions = saved_inputs;
        self.root_sizes = saved_roots;
        self.budget_context = saved_budget;
        self.share_bindings = saved_shares;
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
        let mut part = reading.total(&mut self.unknowns, &mut self.traces);
        part.unknowns = self.unknowns.join(part.unknowns, Some(unknown));

        if part.preference == Preference::Absent {
            part.preference = Preference::Unmarked;
        }

        reading = Reading::of_part(part);

        reading
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
                    reading.main.unknowns = self
                        .unknowns
                        .join(reading.main.unknowns, unknown.main.unknowns);
                }

                let reading = self.finish_reading(file, function, reading, substitutions);

                self.current_effects = Effects::unknown();

                return reading;
            }
        }

        let has_body = match function {
            FunctionNode::Function(inner) => inner.body.is_some(),
            FunctionNode::Arrow(_) => true,
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

            let body = self.cost_of_function_body(file, function);

            match parameters {
                Some(parameters) => {
                    let phases = body.phases;
                    let mut reading = parameters.merge(body, &mut self.unknowns, &mut self.traces);

                    reading.phases = phases;

                    reading
                }
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
    ) -> Part {
        let site = (file, class.node_id());
        let owners = self.owners_of(file, site.1);

        self.initializers_part_of((site, false), &[site], &owners)
    }

    pub(crate) fn inherited_fields_part_of(
        &mut self,
        file: FileId,
        class: &'a oxc_ast::ast::Class<'a>,
        plan: &ConstructionPlan,
    ) -> Part {
        if plan.initializers.is_empty() {
            return Part::none();
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
    ) -> Part {
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
            return self.deferred_unknown(site.0, span, UnknownReason::Recurrence);
        }

        let serial = self.scheduler.pending_serial;
        let diagnostics = (self.warnings.len(), self.errors.len());
        let members = self.active_recurrence_members();
        let outer = std::mem::take(&mut self.current_effects);
        let mut part = Part::none();

        for (file, node) in initializers {
            if !self.charge_work(Event::DispatchStep, 1) {
                let exhausted =
                    self.deferred_unknown(site.0, span, UnknownReason::ResourceExhaustion);

                part = part.max(exhausted, &mut self.unknowns, &mut self.traces);

                break;
            }

            let AstKind::Class(class) = self.kind_of_node(*file, *node) else {
                continue;
            };
            let fields = self
                .cost_of_instance_fields(*file, class)
                .total(&mut self.unknowns, &mut self.traces);

            part = part.max(fields, &mut self.unknowns, &mut self.traces);
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

    fn expression_facts_of(
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

    fn callback_facts_of(
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

                self.scheduler.callbacks.push(CallbackDescriptor {
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

    pub(crate) fn part_of_argument(
        &mut self,
        file: FileId,
        argument: Option<&'a Argument<'a>>,
    ) -> Option<Part> {
        let argument = argument?;
        let facts = self.argument_facts_of(file, argument);

        Some(self.invoke_argument_with(&facts, file, argument.span(), &[], true))
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
    ) -> Part {
        self.invoke_argument_with(facts, file, span, arguments, false)
    }

    fn invoke_argument_with(
        &mut self,
        facts: &ArgumentFacts,
        file: FileId,
        span: oxc_span::Span,
        arguments: &'a [Argument<'a>],
        implicit: bool,
    ) -> Part {
        if let Some(id) = self
            .scheduler
            .callback_values
            .get(&facts.value.value)
            .copied()
        {
            let descriptor = &self.scheduler.callbacks[id];

            if descriptor.generation != self.scheduler.generation {
                return self.deferred_unknown(file, span, UnknownReason::Target);
            }

            let function = self.function_at(descriptor.function);
            let target = descriptor.function;

            let (mut part, cyclic) = if self.fallback_active() {
                self.fallback_invocation(target, file, span)
            } else {
                let descriptor = descriptor.clone();

                self.call_with_captures(
                    (target.file, function),
                    (file, arguments, span),
                    implicit,
                    descriptor.captured,
                )
            };

            if facts.value.targets.open {
                let unknown = self.unknown_invocation(file, span, arguments, UnknownReason::Target);

                part.unknowns = self.unknowns.join(part.unknowns, unknown.main.unknowns);
            }

            return self.called_part_of(target.file, function, part, cyclic);
        }

        self.apply_argument_effects(facts, file, span, arguments);

        facts
            .callback
            .clone()
            .unwrap_or_else(|| self.unknown_part(file, span, UnknownReason::Target))
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
            None if part.cost.is_one() && part.unknowns.is_none() => {
                part.preferred(Preference::Absent)
            }
            None => part.preferred(Preference::Unmarked),
        }
    }

    pub fn call_user(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        call_file: FileId,
        arguments: &'a [Argument<'a>],
        span: oxc_span::Span,
    ) -> (Part, bool) {
        if self.fallback_active() {
            return self.fallback_invocation(
                FunctionId {
                    file,
                    node: function.node_id(),
                },
                call_file,
                span,
            );
        }

        let Some(captured) = self.inherited_substitutions_of(file, function) else {
            return (
                self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
                false,
            );
        };

        self.call_with_captures(
            (file, function),
            (call_file, arguments, span),
            false,
            captured,
        )
    }

    pub(crate) fn call_implicit(
        &mut self,
        target: FunctionId,
        call_file: FileId,
        span: oxc_span::Span,
    ) -> (Part, bool) {
        if self.fallback_active() {
            return self.fallback_invocation(target, call_file, span);
        }

        let function = self.function_at(target);
        let Some(captured) = self.inherited_substitutions_of(target.file, function) else {
            return (
                self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
                false,
            );
        };

        self.call_with_captures(
            (target.file, function),
            (call_file, &[], span),
            true,
            captured,
        )
    }

    fn call_with_captures(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments, span): (FileId, &'a [Argument<'a>], oxc_span::Span),
        implicit: bool,
        substitutions: Substitutions,
    ) -> (Part, bool) {
        let target = FunctionId {
            file,
            node: function.node_id(),
        };

        if self.fallback_active() {
            return self.fallback_invocation(target, call_file, span);
        }

        if !self.charge_work(Event::InvocationEvaluation, 1) {
            return (
                self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
                false,
            );
        }

        if let Some(parent) = self.scheduler.active.filter(|_| !self.fallback_active()) {
            let caller = self.scheduler.tasks[parent.0].key.function;

            if !self.scheduler.runtime.contains(&(caller, target)) {
                if !self.charge_work(Event::RuntimePair, 1) {
                    return (
                        self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
                        false,
                    );
                }

                self.scheduler.runtime.insert((caller, target));
            }

            let site = (caller, self.source_span(call_file, span), target);

            if !self.scheduler.sites.contains(&site) {
                if !self.charge_work(Event::InvocationSite, 1) {
                    return (
                        self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
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
                self.deferred_unknown(call_file, span, UnknownReason::ResourceExhaustion),
                false,
            );
        };

        self.observe_invocation(&key, call_file, span);

        let (reading, cyclic) = self.request_reading(key.clone(), substitutions);

        self.observe_invocation(&key, call_file, span);

        let mut effects = self
            .summaries
            .get(&key)
            .map(|id| self.summaries_arena[id.0 as usize].effects.clone())
            .unwrap_or_else(Effects::unknown);

        self.substitute_parameter_values(file, function, call_file, arguments, &mut effects);
        self.current_effects.join(&effects);

        (reading.total(&mut self.unknowns, &mut self.traces), cyclic)
    }

    fn invocation_substitutions_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (call_file, arguments): (FileId, &'a [Argument<'a>]),
        implicit: bool,
        mut substitutions: Substitutions,
    ) -> Substitutions {
        let parameters = match function {
            FunctionNode::Function(inner) => &inner.params,
            FunctionNode::Arrow(inner) => &inner.params,
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

            if let Some(symbol) = identifier.symbol_id.get() {
                substitutions.insert(Binding::Symbol { file, symbol }, facts);
            }
        }

        if let Some(rest) = parameters.rest.as_ref() {
            if let BindingPattern::BindingIdentifier(identifier) = &rest.rest.argument {
                if let Some(symbol) = identifier.symbol_id.get() {
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
        let parameters = match function {
            FunctionNode::Function(inner) => &inner.params,
            FunctionNode::Arrow(inner) => &inner.params,
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

        let parameters = match function {
            FunctionNode::Function(inner) => &inner.params,
            FunctionNode::Arrow(inner) => &inner.params,
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
    ) -> (Part, bool) {
        if !self.charge_work(Event::InvocationEvaluation, 1) {
            return (
                self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion),
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
        let mut joined: Option<(Part, bool)> = None;

        for id in observed {
            let (part, cyclic) = self.observed_invocation_of(id, file, span);

            joined = Some(match joined {
                Some((known, was_cyclic)) => (
                    known.max(part, &mut self.unknowns, &mut self.traces),
                    was_cyclic || cyclic,
                ),
                None => (part, cyclic),
            });
        }

        match joined {
            Some((mut part, cyclic)) if incomplete => {
                let unknown = self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion);

                part.unknowns = self.unknowns.join(part.unknowns, unknown.unknowns);

                (part, cyclic)
            }
            Some(joined) => joined,
            None => (
                self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion),
                false,
            ),
        }
    }

    fn observed_invocation_of(
        &mut self,
        id: TaskId,
        file: FileId,
        span: oxc_span::Span,
    ) -> (Part, bool) {
        if self.scheduler.component.contains(&id) {
            self.current_effects.unknown_global = true;

            return (
                self.local_resource_reading(id)
                    .total(&mut self.unknowns, &mut self.traces),
                true,
            );
        }

        if let TaskState::Ready(record) = self.scheduler.tasks[id.0].state {
            let record = self.summaries_arena[record.0 as usize].clone();

            self.current_effects.join(&record.effects);

            let cyclic = self.scheduler.active.is_some_and(|parent| {
                self.scheduler.tasks[id.0]
                    .recurrence_members
                    .contains(&self.scheduler.tasks[parent.0].key.function)
            });

            return (
                record.reading.total(&mut self.unknowns, &mut self.traces),
                cyclic,
            );
        }

        (
            self.deferred_unknown(file, span, UnknownReason::ResourceExhaustion),
            false,
        )
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

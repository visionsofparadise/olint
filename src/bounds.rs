use std::collections::{HashMap, HashSet};

use oxc_ast::ast::{
    AssignmentExpression, AssignmentTarget, BindingPattern, Expression, ForStatement,
    ForStatementInit, Statement,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId, SymbolId};
use oxc_span::GetSpan;
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, UpdateOperator};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::budgets::{
    comparison_pairs_of, conjuncts_of, is_less, Direction, Strictness, Subtree, Visits,
};
use crate::cost::{Cost, CostComparison};
use crate::declarations::{Binding, Declaration, ParameterNode};
use crate::derivation::{DerivationArena, DerivationId, Fact};
use crate::directives::PerfTag;
use crate::flow::{completion_of, control_target_of, Completion};
use crate::project::FileId;
use crate::syntax::{
    collapsed_text_of, identifier_of, is_identifier_pattern, is_iteration_kind, loop_body_of,
    member_expression_of, unwrap, Root,
};
use crate::unknowns::UnknownReason;
use crate::values::{Primitive, SizeQuantity};

const MAXIMUM_VALUE_DEPTH: usize = 4;

const LARGEST_CONTRACTION_RATIO: f64 = 0.5;

pub(crate) type CounterWriteSites = Vec<(u32, u32, NodeId)>;

fn quantity_maximum(left: Cost, right: Cost) -> Option<Cost> {
    if left.is_one() && left.compare(&right) == CostComparison::Within {
        return Some(right);
    }

    if right.is_one() && right.compare(&left) == CostComparison::Within {
        return Some(left);
    }

    Cost::maximum(vec![left, right]).ok()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum QuantityKey {
    Binding(Binding),
    Expression(NodeId),
}

#[derive(Default)]
struct QuantityProof {
    visiting: HashSet<QuantityKey>,
    settled: HashMap<QuantityKey, Option<(Cost, f64)>>,
}

/// A loop's iteration bound. A proven bound carries the derivation that proved its factor: the ledger rule, the loop
/// it concerns and the side condition the rule established, named in the loop's explanation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bound {
    Proven {
        factor: Cost,
        derivation: Option<DerivationId>,
    },
    Unresolved {
        reason: UnknownReason,
    },
}

impl Bound {
    pub fn factor(&self) -> Option<&Cost> {
        match self {
            Bound::Proven { factor, .. } => Some(factor),
            Bound::Unresolved { .. } => None,
        }
    }

    pub fn derivation(&self) -> Option<DerivationId> {
        match self {
            Bound::Proven { derivation, .. } => *derivation,
            Bound::Unresolved { .. } => None,
        }
    }

    /// The side condition the bound's derivation names, which the loop's explanation shows.
    pub fn proof<'d>(&self, derivations: &'d DerivationArena) -> Option<&'d str> {
        let derivation = derivations.get(self.derivation()?)?;

        derivation.facts.iter().find_map(|fact| match fact {
            Fact::Name(name) => Some(name.as_str()),
            _ => None,
        })
    }

    pub fn reason(&self) -> Option<UnknownReason> {
        match self {
            Bound::Proven { .. } => None,
            Bound::Unresolved { reason } => Some(*reason),
        }
    }

    pub fn is_unresolved(&self) -> bool {
        matches!(self, Bound::Unresolved { .. })
    }

    pub fn label<'d>(&self, derivations: &'d DerivationArena) -> &'d str {
        match (self, self.proof(derivations)) {
            (_, Some(proof)) => proof,
            (Bound::Unresolved { reason }, None) => reason.text(),
            (Bound::Proven { factor, .. }, None) => factor_label_of(factor),
        }
    }
}

fn factor_label_of(factor: &Cost) -> &'static str {
    match factor.is_logarithm() {
        true => "log",
        false => "N",
    }
}

/// A bound as the bound rules find it, before its derivation is recorded: a proven factor with the ledger rule that
/// proved it and the side condition the rule established, if the explanation names one.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    Proven {
        factor: Cost,
        rule: &'static str,
        condition: Option<&'static str>,
    },
    Unresolved {
        reason: UnknownReason,
    },
}

impl Verdict {
    fn label(&self) -> &'static str {
        match self {
            Verdict::Unresolved { reason } => reason.text(),
            Verdict::Proven {
                condition: Some(condition),
                ..
            } => condition,
            Verdict::Proven { factor, .. } => factor_label_of(factor),
        }
    }

    fn strength(&self) -> u8 {
        match self {
            Verdict::Proven { factor, .. } if factor.is_one() => 0,
            Verdict::Proven { factor, .. } if factor.is_logarithm() => 1,
            Verdict::Proven { .. } => 2,
            Verdict::Unresolved { .. } => 3,
        }
    }
}

pub fn loop_label(kind: AstKind<'_>) -> &'static str {
    match kind {
        AstKind::ForOfStatement(_) => "for-of",
        AstKind::ForInStatement(_) => "for-in",
        AstKind::ForStatement(_) => "for",
        AstKind::WhileStatement(_) => "while",
        _ => "do-while",
    }
}

pub fn short(text: &str) -> String {
    let collapsed = collapsed_text_of(text);

    if utf16_length_of(&collapsed) <= 40 {
        return collapsed;
    }

    let mut kept = String::new();
    let mut units = 0;

    for character in collapsed.chars() {
        units += character.len_utf16();

        if units > 37 {
            if units == 38 && character.len_utf16() == 2 {
                kept.push(char::REPLACEMENT_CHARACTER);
            }

            break;
        }

        kept.push(character);
    }

    kept.push_str("...");

    kept
}

pub(crate) fn utf16_length_of(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Step {
    Additive(Option<f64>),
    Geometric(Option<f64>),
    Replacing,
}

#[derive(Clone, Copy, Debug)]
struct CounterWrite {
    site: NodeId,
    step: Step,
    deferred: bool,
    updating: bool,
    within_update: bool,
}

struct Comparison<'a> {
    expression: &'a Expression<'a>,
    counter: Binding,
    endpoint: &'a Expression<'a>,
    direction: Direction,
    strictness: Strictness,
}

struct Repetition<'a> {
    node: NodeId,
    body: &'a Statement<'a>,
    update: Option<&'a Expression<'a>>,
    initial: Option<(Binding, &'a Expression<'a>)>,
    returns_to_head: bool,
    geometric_proof: &'static str,
}

struct Progression {
    writes: Vec<CounterWrite>,
    unconditional: Vec<CounterWrite>,
}

impl Progression {
    fn is_driven(&self) -> bool {
        self.writes
            .iter()
            .any(|write| write.within_update || !is_replacing(write))
    }

    fn advances(&self, toward: f64) -> Option<Vec<Option<f64>>> {
        self.writes
            .iter()
            .map(|write| match write.step {
                Step::Additive(delta) => Some(delta.map(|delta| delta * toward)),
                _ => None,
            })
            .collect()
    }

    fn guaranteed_advance(&self, toward: f64) -> Option<f64> {
        self.unconditional
            .iter()
            .map(|write| match write.step {
                Step::Additive(delta) => delta.map(|delta| delta * toward),
                _ => None,
            })
            .try_fold(0.0, |total, advance| advance.map(|advance| total + advance))
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn inside_loop(&self, file: FileId, node: NodeId) -> bool {
        let nodes = self.project.file(file).semantic.nodes();

        for ancestor in nodes.ancestors(node) {
            let kind = ancestor.kind();

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                return false;
            }

            if is_iteration_kind(&kind) {
                return true;
            }
        }

        false
    }

    /// The loop's iteration bound, a proven one with its derivation: a leaf of the bound rule that proved it,
    /// concerning the loop and naming the side condition the rule established.
    pub fn bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Bound {
        let key = (file, loop_kind.node_id());

        if !self.active_bounds.insert(key) {
            return Bound::Unresolved {
                reason: UnknownReason::Bound,
            };
        }

        let verdict = self.inner_bound_of(file, loop_kind);

        self.active_bounds.remove(&key);

        if self.bound_seen.insert((file, loop_kind.node_id())) {
            self.stats.count(&format!(
                "loop {}: {}",
                loop_label(loop_kind),
                verdict.label()
            ));
        }

        match verdict {
            Verdict::Proven {
                factor,
                rule,
                condition,
            } => {
                let syntax = self.source_span(file, loop_kind.span());
                let facts = condition
                    .map(|condition| vec![Fact::Name(condition.to_string())])
                    .unwrap_or_default();
                let derivation = self
                    .traces
                    .derivations
                    .leaf(rule, syntax, facts, factor.clone());

                Bound::Proven { factor, derivation }
            }
            Verdict::Unresolved { reason } => Bound::Unresolved { reason },
        }
    }

    fn inner_bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Verdict {
        if self.perf_tags(file, loop_kind).contains(&PerfTag::Bounded) {
            self.assertions += 1;

            return constant_bound_of("bound-directive", "@perf bounded");
        }

        let Some(body) = loop_body_of(loop_kind) else {
            return unresolved_bound_of();
        };

        if self.runs_at_most_once(file, loop_kind.node_id(), body) {
            return constant_bound_of("bound-single-iteration", "single iteration");
        }

        match loop_kind {
            AstKind::ForOfStatement(statement) => {
                let iteration = self.iteration_of(file, &statement.right, statement.r#await);
                let count = self.iteration_count_of(file, &statement.right, &iteration);
                let sized = self.is_sized_iteration(file, &statement.right, &iteration);

                if count.is_none()
                    && !sized
                    && !self.is_untracked_iteration(file, &statement.right, &iteration)
                {
                    return unresolved_bound_of();
                }

                if !iteration.native {
                    return match count {
                        Some(count) => Verdict::Proven {
                            factor: count,
                            rule: "bound-iterator-visits",
                            condition: Some("iterator visits"),
                        },
                        None if self.is_untracked_iteration(file, &statement.right, &iteration) => {
                            untracked_bound_of()
                        }
                        None => unresolved_bound_of(),
                    };
                }

                match self.live_iteration_of(file, statement) {
                    Some(Visits::Budgeted(budget)) => {
                        let initial =
                            self.initial_size_of(file, &statement.right, statement.node_id());

                        if !initial.length_resolved {
                            return untracked_bound_of();
                        }

                        return match Cost::maximum(vec![initial.length, budget.cost]) {
                            Ok(factor) => Verdict::Proven {
                                factor,
                                rule: "bound-live-visits",
                                condition: Some("visit budget"),
                            },
                            Err(_) => unresolved_bound_of(),
                        };
                    }
                    Some(Visits::Unresolved) => return unresolved_bound_of(),
                    _ => {}
                }

                if self.is_constant_sized(file, &statement.right) {
                    constant_bound_of("bound-constant-collection", "constant collection")
                } else if self.is_share_sized(file, &statement.right) {
                    constant_bound_of("bound-share", "share of budget")
                } else {
                    match count {
                        Some(count) => Verdict::Proven {
                            factor: count,
                            rule: "bound-for-of-native",
                            condition: None,
                        },
                        None => untracked_bound_of(),
                    }
                }
            }
            AstKind::ForInStatement(statement) => {
                if self.is_constant_sized(file, &statement.right)
                    || self.is_closed(file, &statement.right)
                {
                    constant_bound_of("bound-for-in", "closed object type")
                } else {
                    match self.tracked_length_of(file, &statement.right) {
                        Some(factor) => Verdict::Proven {
                            factor,
                            rule: "bound-for-in",
                            condition: None,
                        },
                        None => untracked_bound_of(),
                    }
                }
            }
            AstKind::ForStatement(statement) => self.bound_of_for(file, statement, body),
            AstKind::WhileStatement(statement) => {
                self.bound_of_while(file, loop_kind.node_id(), &statement.test, body)
            }
            AstKind::DoWhileStatement(statement) => {
                self.bound_of_while(file, loop_kind.node_id(), &statement.test, body)
            }
            _ => unresolved_bound_of(),
        }
    }

    fn bound_of_for(
        &mut self,
        file: FileId,
        statement: &'a ForStatement<'a>,
        body: &'a Statement<'a>,
    ) -> Verdict {
        let Some(test) = statement.test.as_ref() else {
            return unresolved_bound_of();
        };
        let variable = self.loop_variable_of(file, statement);
        let repetition = Repetition {
            node: statement.node_id(),
            body,
            update: statement.update.as_ref().map(unwrap),
            initial: variable,
            returns_to_head: self.returns_to_head(file, statement.node_id(), body),
            geometric_proof: "geometric step",
        };

        if let Some(bound) = self.share_bound_of(file, test, &repetition) {
            return bound;
        }

        self.bound_of_repetition(file, test, &repetition)
    }

    fn bound_of_while(
        &mut self,
        file: FileId,
        node: NodeId,
        test: &'a Expression<'a>,
        body: &'a Statement<'a>,
    ) -> Verdict {
        let repetition = Repetition {
            node,
            body,
            update: None,
            initial: None,
            returns_to_head: self.returns_to_head(file, node, body),
            geometric_proof: "halving",
        };

        self.bound_of_repetition(file, test, &repetition)
    }

    fn bound_of_repetition(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        repetition: &Repetition<'a>,
    ) -> Verdict {
        if matches!(unwrap(test), Expression::BooleanLiteral(literal) if !literal.value) {
            return constant_bound_of("bound-false-condition", "false condition");
        }

        let comparisons = self.comparisons_of(file, test);
        let mut best: Option<Verdict> = None;

        for comparison in comparisons {
            let Some(bound) = self.verdict_of(file, &comparison, repetition) else {
                continue;
            };

            if best
                .as_ref()
                .is_none_or(|found| bound.strength() < found.strength())
            {
                best = Some(bound);
            }
        }

        best.unwrap_or_else(unresolved_bound_of)
    }

    fn comparisons_of(&mut self, file: FileId, test: &'a Expression<'a>) -> Vec<Comparison<'a>> {
        let mut found = Vec::new();

        for conjunct in conjuncts_of(test) {
            let Some(pairs) = comparison_pairs_of(conjunct) else {
                continue;
            };

            for (counter, endpoint, direction, strictness) in pairs {
                let expression = counter;
                let Some(reference) = identifier_of(counter) else {
                    continue;
                };
                let Some(counter) = self.binding_of_identifier(file, reference) else {
                    continue;
                };

                found.push(Comparison {
                    expression,
                    counter,
                    endpoint,
                    direction,
                    strictness,
                });
            }
        }

        found
    }

    fn verdict_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        let progression = self.progression_of(file, comparison.counter, repetition)?;

        if let Some(bound) = self.bisection_bound_of(file, comparison, repetition) {
            return Some(bound);
        }

        if progression.is_driven() && progression.writes.iter().any(is_replacing) {
            return Some(unresolved_bound_of());
        }

        if let Some(bound) = self.geometric_bound_of(file, comparison, &progression, repetition) {
            return Some(bound);
        }

        self.additive_bound_of(file, comparison, &progression, repetition)
    }

    fn progression_of(
        &mut self,
        file: FileId,
        counter: Binding,
        repetition: &Repetition<'a>,
    ) -> Option<Progression> {
        let sites = self.write_sites_of(file, counter, repetition.node)?;
        let mut writes = Vec::new();

        for site in sites {
            writes.push(self.write_of(file, counter, site, repetition));
        }

        let mut unconditional = Vec::new();

        for write in &writes {
            let reached = write.updating
                || (!write.deferred
                    && !repetition.returns_to_head
                    && self.covers_every_path(file, repetition, &[write.site]));

            if reached {
                unconditional.push(*write);
            }
        }

        Some(Progression {
            writes,
            unconditional,
        })
    }

    fn write_sites_of(
        &mut self,
        file: FileId,
        counter: Binding,
        node: NodeId,
    ) -> Option<Vec<NodeId>> {
        let symbol = local_symbol_of(file, counter)?;

        if !self.charge_work(Event::BudgetPrepassNode, 1) {
            return None;
        }

        if !self.counter_writes.contains_key(&counter) {
            let writes = self.counter_write_index_of(file, symbol);

            self.counter_writes.insert(counter, writes);
        }

        let count = self.counter_writes.get(&counter)?.as_ref()?.len() as u64;
        let search = 2 * (64 - count.saturating_add(1).leading_zeros() as u64);

        if !self.charge_work(Event::BudgetPrepassNode, search) {
            return None;
        }

        let scope = self.kind_of_node(file, node).span();
        let writes = self.counter_writes.get(&counter)?.as_ref()?;
        let start = writes.partition_point(|write| write.0 < scope.start);
        let end = writes.partition_point(|write| write.0 <= scope.end);

        if !self.charge_work(Event::BudgetPrepassNode, 2 * (end - start) as u64) {
            return None;
        }

        let writes = self.counter_writes.get(&counter)?.as_ref()?;

        Some(
            writes[start..end]
                .iter()
                .filter(|write| write.1 <= scope.end)
                .map(|write| write.2)
                .collect(),
        )
    }

    fn counter_write_index_of(
        &mut self,
        file: FileId,
        symbol: SymbolId,
    ) -> Option<CounterWriteSites> {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let mut writes = Vec::new();
        let references = semantic.scoping().get_resolved_reference_ids(symbol).len() as u64;

        if !self.charge_work(Event::BudgetPrepassNode, references.saturating_mul(3)) {
            return None;
        }

        for reference in semantic.scoping().get_resolved_references(symbol) {
            if reference.is_write() {
                let node = reference.node_id();
                let span = semantic.nodes().kind(node).span();

                writes.push((span.start, span.end, node));
            }
        }

        let count = writes.len() as u64;
        let sorting = count.saturating_mul(64 - count.leading_zeros() as u64);

        if !self.charge_work(Event::BudgetPrepassNode, sorting) {
            return None;
        }

        writes.sort_unstable_by_key(|write| (write.0, write.1, write.2.index()));

        Some(writes)
    }

    fn write_of(
        &mut self,
        file: FileId,
        counter: Binding,
        site: NodeId,
        repetition: &Repetition<'a>,
    ) -> CounterWrite {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let span = nodes.kind(site).span();
        let parent = nodes.parent_id(site);
        let deferred = nodes
            .ancestor_ids(site)
            .take_while(|ancestor| *ancestor != repetition.node)
            .any(|ancestor| {
                matches!(
                    nodes.kind(ancestor),
                    AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
                )
            });
        let within_update = repetition
            .update
            .is_some_and(|update| is_within(nodes, site, update.node_id()));
        let (site, step) = match nodes.parent_kind(site) {
            AstKind::UpdateExpression(update) => (
                parent,
                Step::Additive(Some(match update.operator {
                    UpdateOperator::Increment => 1.0,
                    UpdateOperator::Decrement => -1.0,
                })),
            ),
            AstKind::AssignmentExpression(assignment) if assignment.left.span() == span => (
                parent,
                self.step_of_assignment(file, counter, assignment, repetition),
            ),
            _ => (site, Step::Replacing),
        };

        let updating = repetition
            .update
            .is_some_and(|update| covers_expression(update, &[site]));

        CounterWrite {
            site,
            step,
            deferred,
            updating,
            within_update,
        }
    }

    fn step_of_assignment(
        &mut self,
        file: FileId,
        counter: Binding,
        assignment: &'a AssignmentExpression<'a>,
        repetition: &Repetition<'a>,
    ) -> Step {
        let right = &assignment.right;

        match assignment.operator {
            AssignmentOperator::Addition => Step::Additive(self.numeric_value_of(file, right)),
            AssignmentOperator::Subtraction => {
                Step::Additive(self.numeric_value_of(file, right).map(|value| -value))
            }
            AssignmentOperator::Multiplication => {
                Step::Geometric(self.numeric_value_of(file, right))
            }
            AssignmentOperator::Division => Step::Geometric(self.inverse_value_of(file, right)),
            AssignmentOperator::ShiftLeft => {
                Step::Geometric(self.shift_ratio_of(file, right, true))
            }
            AssignmentOperator::ShiftRight | AssignmentOperator::ShiftRightZeroFill => {
                Step::Geometric(self.shift_ratio_of(file, right, false))
            }
            AssignmentOperator::Assign => self.step_of_value(file, counter, right, repetition, 0),
            _ => Step::Replacing,
        }
    }

    fn step_of_value(
        &mut self,
        file: FileId,
        counter: Binding,
        value: &'a Expression<'a>,
        repetition: &Repetition<'a>,
        depth: usize,
    ) -> Step {
        let value = unwrap(value);

        if depth < MAXIMUM_VALUE_DEPTH {
            if let Some(aliased) = self.repetition_constant_of(file, value, repetition) {
                return self.step_of_value(file, counter, aliased, repetition, depth + 1);
            }
        }

        if let Expression::BinaryExpression(binary) = value {
            let left = unwrap(&binary.left);
            let right = unwrap(&binary.right);
            let counted_left = self.is_counter_reference(file, counter, left);
            let counted_right = self.is_counter_reference(file, counter, right);

            match binary.operator {
                BinaryOperator::Addition if counted_left => {
                    return Step::Additive(self.numeric_value_of(file, right))
                }
                BinaryOperator::Addition if counted_right => {
                    return Step::Additive(self.numeric_value_of(file, left))
                }
                BinaryOperator::Subtraction if counted_left => {
                    return Step::Additive(self.numeric_value_of(file, right).map(|value| -value))
                }
                BinaryOperator::Multiplication if counted_left => {
                    return Step::Geometric(self.numeric_value_of(file, right))
                }
                BinaryOperator::Multiplication if counted_right => {
                    return Step::Geometric(self.numeric_value_of(file, left))
                }
                BinaryOperator::Division if counted_left => {
                    return Step::Geometric(self.inverse_value_of(file, right))
                }
                BinaryOperator::ShiftLeft if counted_left => {
                    return Step::Geometric(self.shift_ratio_of(file, right, true))
                }
                BinaryOperator::ShiftRight | BinaryOperator::ShiftRightZeroFill if counted_left => {
                    return Step::Geometric(self.shift_ratio_of(file, right, false))
                }
                _ => {}
            }
        }

        if depth < MAXIMUM_VALUE_DEPTH {
            if let Some(argument) = self.truncated_argument_of(file, value) {
                return match self.step_of_value(file, counter, argument, repetition, depth + 1) {
                    Step::Geometric(ratio) => Step::Geometric(ratio),
                    Step::Additive(_) => Step::Additive(None),
                    Step::Replacing => Step::Replacing,
                };
            }
        }

        match self.mentions_counter(file, counter, value) {
            true => Step::Additive(None),
            false => Step::Replacing,
        }
    }

    fn repetition_constant_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<&'a Expression<'a>> {
        let reference = identifier_of(value)?;
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference)?;
        let Declaration::Variable {
            file: owner,
            declarator,
            constant: true,
        } = declaration
        else {
            return None;
        };

        if owner != file || !is_identifier_pattern(&declarator.id) {
            return None;
        }

        let nodes = self.project.file(file).semantic.nodes();

        is_within(nodes, declarator.node_id(), repetition.node)
            .then_some(declarator.init.as_ref())
            .flatten()
    }

    fn truncated_argument_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
    ) -> Option<&'a Expression<'a>> {
        let Expression::CallExpression(call) = value else {
            return None;
        };
        let member = member_expression_of(&call.callee)?;
        let object = identifier_of(unwrap(member.object()))?;

        if object.name != "Math" || self.binding_of_identifier(file, object).is_some() {
            return None;
        }

        let name = member.static_property_name()?;

        if !matches!(name, "floor" | "trunc") || self.intrinsic_replaced_of(file, &call.callee) {
            return None;
        }

        call.arguments
            .first()
            .and_then(|argument| argument.as_expression())
            .map(unwrap)
    }

    fn is_counter_reference(
        &mut self,
        file: FileId,
        counter: Binding,
        value: &'a Expression<'a>,
    ) -> bool {
        identifier_of(value)
            .and_then(|reference| self.binding_of_identifier(file, reference))
            .is_some_and(|binding| binding == counter)
    }

    fn mentions_counter(
        &mut self,
        file: FileId,
        counter: Binding,
        value: &'a Expression<'a>,
    ) -> bool {
        let references: Vec<&'a oxc_ast::ast::IdentifierReference<'a>> =
            Subtree::of(Root::Expression(value), false, false)
                .into_iter()
                .filter_map(|kind| match kind {
                    AstKind::IdentifierReference(reference) => Some(reference),
                    _ => None,
                })
                .collect();

        references
            .into_iter()
            .any(|reference| self.binding_of_identifier(file, reference) == Some(counter))
    }

    pub(crate) fn numeric_value_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
    ) -> Option<f64> {
        match self.known_value(file, value).value.as_deref() {
            Ok(Primitive::Number(found)) if found.is_finite() => Some(*found),
            _ => None,
        }
    }

    fn inverse_value_of(&mut self, file: FileId, value: &'a Expression<'a>) -> Option<f64> {
        self.numeric_value_of(file, value)
            .map(|found| 1.0 / found)
            .filter(|ratio| ratio.is_finite())
    }

    fn shift_ratio_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        leftward: bool,
    ) -> Option<f64> {
        let places = self.numeric_value_of(file, value)? as i64 & 31;
        let ratio = (2.0_f64).powi(places as i32);

        match leftward {
            true => Some(ratio),
            false => Some(1.0 / ratio),
        }
    }

    fn geometric_bound_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        progression: &Progression,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        if progression.writes.is_empty() {
            return None;
        }

        let initial = self
            .initial_expression_of(file, comparison.counter, repetition)
            .or_else(|| {
                matches!(
                    self.declarations
                        .of_binding(self.project, comparison.counter),
                    Some(Declaration::Parameter { .. })
                )
                .then_some(comparison.expression)
            })?;

        self.bounded_quantity_of(file, initial, repetition, 0)?;
        self.bounded_quantity_of(file, comparison.endpoint, repetition, 0)?;

        let mut ratios = Vec::new();

        for write in &progression.writes {
            if let AstKind::AssignmentExpression(assignment) = self.kind_of_node(file, write.site) {
                if assignment.operator == AssignmentOperator::ShiftLeft
                    || Subtree::of(Root::Expression(&assignment.right), false, false).iter().any(|kind|
                        matches!(kind, AstKind::BinaryExpression(binary) if binary.operator == BinaryOperator::ShiftLeft))
                {
                    return Some(unresolved_bound_of());
                }
            }

            match write.step {
                Step::Geometric(Some(ratio)) if write.updating || !write.deferred => {
                    ratios.push(ratio)
                }
                _ => return None,
            }
        }

        if progression.unconditional.is_empty() {
            return None;
        }

        if !self.is_stable_endpoint(file, comparison.endpoint, repetition) {
            return None;
        }

        match comparison.direction {
            Direction::Up => {
                if !ratios.iter().all(|ratio| *ratio > 1.0) {
                    return None;
                }

                let initial = self.initial_expression_of(file, comparison.counter, repetition)?;

                if self.numeric_value_of(file, initial)? < 1.0 {
                    return None;
                }

                Some(
                    match self.bounded_quantity_of(file, comparison.endpoint, repetition, 0) {
                        Some((endpoint, _)) => logarithmic_bound_of(
                            "bound-geometric",
                            repetition.geometric_proof,
                            endpoint,
                        ),
                        None => untracked_bound_of(),
                    },
                )
            }
            Direction::Down => {
                if !ratios
                    .iter()
                    .all(|ratio| ratio.abs() <= LARGEST_CONTRACTION_RATIO)
                {
                    return None;
                }

                let endpoint = self.numeric_value_of(file, comparison.endpoint)?;
                let clears_the_endpoint = match comparison.strictness {
                    Strictness::Strict => endpoint >= 0.0,
                    Strictness::Inclusive => endpoint > 0.0,
                };

                if !clears_the_endpoint {
                    return None;
                }

                let initial = self
                    .initial_expression_of(file, comparison.counter, repetition)
                    .unwrap_or(comparison.expression);

                Some(
                    match self
                        .bounded_quantity_of(file, initial, repetition, 0)
                        .or_else(|| {
                            self.bounded_quantity_of(file, comparison.expression, repetition, 0)
                        }) {
                        Some((initial, _)) => logarithmic_bound_of(
                            "bound-geometric",
                            repetition.geometric_proof,
                            initial,
                        ),
                        None => untracked_bound_of(),
                    },
                )
            }
        }
    }

    fn additive_bound_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        progression: &Progression,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        if progression.writes.is_empty() {
            return None;
        }

        let toward = match comparison.direction {
            Direction::Up => 1.0,
            Direction::Down => -1.0,
        };
        let advances = progression.advances(toward)?;

        if advances.iter().any(Option::is_none) {
            return Some(unresolved_bound_of());
        }

        let guaranteed = progression.guaranteed_advance(toward);
        let sums_every_write = progression.unconditional.len() == progression.writes.len();

        if guaranteed.is_some_and(|guaranteed| guaranteed <= 0.0)
            && (sums_every_write
                || advances
                    .iter()
                    .all(|advance| advance.is_some_and(|advance| advance <= 0.0)))
        {
            return Some(unresolved_bound_of());
        }

        let guaranteed = guaranteed.filter(|guaranteed| *guaranteed > 0.0)?;

        if !advances
            .iter()
            .all(|advance| advance.is_some_and(|advance| advance >= 0.0))
        {
            return self.exact_additive_distance_of(file, comparison, progression, repetition);
        }

        if !self.is_stable_endpoint(file, comparison.endpoint, repetition) {
            return None;
        }

        let initial = self
            .initial_expression_of(file, comparison.counter, repetition)
            .unwrap_or(comparison.expression);
        let (initial_cost, initial_magnitude) = self
            .bounded_quantity_of(file, initial, repetition, 0)
            .or_else(|| self.bounded_quantity_of(file, comparison.expression, repetition, 0))?;
        let (endpoint_cost, endpoint_magnitude) =
            self.bounded_quantity_of(file, comparison.endpoint, repetition, 0)?;
        let magnitude = initial_magnitude.max(endpoint_magnitude);

        if !progression.unconditional.iter().any(|write| {
            matches!(write.step, Step::Additive(Some(delta))
                if delta * toward > 0.0 && magnitude + (delta * toward) / 2.0 > magnitude)
        }) {
            return Some(unresolved_bound_of());
        }

        if let Some((distance, proof)) = self.distance_of(file, comparison, repetition) {
            let repetitions = (distance / guaranteed).floor() + 1.0;

            return repetitions
                .is_finite()
                .then(|| constant_bound_of("bound-constant-distance", proof));
        }

        quantity_maximum(initial_cost, endpoint_cost).map(|factor| Verdict::Proven {
            factor,
            rule: "bound-additive",
            condition: None,
        })
    }

    fn exact_additive_distance_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        progression: &Progression,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        if progression.unconditional.len() != progression.writes.len()
            || progression.writes.iter().any(|write| write.deferred)
            || !self.is_stable_endpoint(file, comparison.endpoint, repetition)
        {
            return None;
        }

        let initial = self.initial_expression_of(file, comparison.counter, repetition)?;
        let initial = self.numeric_value_of(file, initial)?;
        let endpoint = self.numeric_value_of(file, comparison.endpoint)?;
        let mut magnitude = initial.abs().max(endpoint.abs());

        if [initial, endpoint]
            .iter()
            .any(|value| (value * 4.0).fract() != 0.0)
        {
            return None;
        }

        let nodes = self.project.file(file).semantic.nodes();

        for write in &progression.writes {
            if nodes
                .ancestor_ids(write.site)
                .take_while(|node| *node != repetition.node)
                .any(|node| is_iteration_kind(&nodes.kind(node)))
            {
                return None;
            }

            let Step::Additive(Some(delta)) = write.step else {
                return None;
            };

            if !delta.is_finite() || (delta * 4.0).fract() != 0.0 {
                return None;
            }

            magnitude += delta.abs();
        }

        (magnitude <= 281_474_976_710_656.0)
            .then(|| constant_bound_of("bound-exact-additive", "constant bound"))
    }

    fn bounded_quantity_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        repetition: &Repetition<'a>,
        depth: usize,
    ) -> Option<(Cost, f64)> {
        self.bounded_quantity_with(
            file,
            expression,
            repetition,
            depth,
            &mut QuantityProof::default(),
        )
    }

    fn bounded_quantity_with(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        repetition: &Repetition<'a>,
        depth: usize,
        proof: &mut QuantityProof,
    ) -> Option<(Cost, f64)> {
        if depth > MAXIMUM_VALUE_DEPTH || !self.charge_work(Event::BudgetPrepassNode, 1) {
            return None;
        }

        let test = match self.kind_of_node(file, repetition.node) {
            AstKind::ForStatement(statement) => statement.test.as_ref(),
            AstKind::WhileStatement(statement) => Some(&statement.test),
            AstKind::DoWhileStatement(statement) => Some(&statement.test),
            _ => None,
        };
        let current = test.is_some_and(|test| {
            is_within(
                self.project.file(file).semantic.nodes(),
                expression.node_id(),
                test.node_id(),
            )
        });
        let key = identifier_of(unwrap(expression))
            .filter(|_| current)
            .and_then(|reference| self.binding_of_identifier(file, reference))
            .map_or(
                QuantityKey::Expression(expression.node_id()),
                QuantityKey::Binding,
            );

        if let Some(found) = proof.settled.get(&key) {
            return found.clone();
        }

        if !proof.visiting.insert(key) {
            return None;
        }

        let found = self.bounded_quantity_inner(file, expression, repetition, depth, proof);

        proof.visiting.remove(&key);
        proof.settled.insert(key, found.clone());

        found
    }

    fn bounded_quantity_inner(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        repetition: &Repetition<'a>,
        depth: usize,
        proof: &mut QuantityProof,
    ) -> Option<(Cost, f64)> {
        if depth > MAXIMUM_VALUE_DEPTH {
            return None;
        }

        if let Some(value) = self.numeric_value_of(file, expression) {
            return Some((Cost::ONE, value.abs()));
        }

        let expression = unwrap(expression);

        if let Expression::BinaryExpression(binary) = expression {
            if matches!(
                binary.operator,
                BinaryOperator::Addition | BinaryOperator::Subtraction
            ) {
                let (left, left_magnitude) =
                    self.bounded_quantity_with(file, &binary.left, repetition, depth + 1, proof)?;
                let (right, right_magnitude) =
                    self.bounded_quantity_with(file, &binary.right, repetition, depth + 1, proof)?;
                let magnitude = left_magnitude + right_magnitude;

                if magnitude <= 9_007_199_254_740_991.0 {
                    return Some((quantity_maximum(left, right)?, magnitude));
                }
            }

            return None;
        }

        if let Expression::StaticMemberExpression(member) = expression {
            if member.property.name == "length" {
                let mut kind = self.proven_kind(file, &member.object);

                if kind == crate::declared_types::Kind::Unknown
                    && self.is_primitive_operand(file, &member.object)
                    && self.declared_type_of_expression(file, &member.object).kind
                        == crate::declared_types::Kind::String
                {
                    kind = crate::declared_types::Kind::String;
                }

                if matches!(
                    kind,
                    crate::declared_types::Kind::Array | crate::declared_types::Kind::String
                ) {
                    let size = self.collection_size_of(file, &member.object);

                    if size.length_resolved {
                        let magnitude = if kind == crate::declared_types::Kind::Array {
                            4_294_967_295.0
                        } else {
                            9_007_199_254_740_991.0
                        };

                        return Some((size.length, magnitude));
                    }
                }
            }
        }

        let binding = identifier_of(expression)
            .and_then(|reference| self.binding_of_identifier(file, reference));
        let declaration =
            binding.and_then(|binding| self.declarations.of_binding(self.project, binding));

        if let Some(Declaration::Variable {
            file: owner,
            declarator,
            constant: true,
        }) = declaration
        {
            if owner == file {
                if let Some(initial) = declarator.init.as_ref() {
                    if let Some(found) =
                        self.bounded_quantity_with(file, initial, repetition, depth + 1, proof)
                    {
                        return Some(found);
                    }
                }
            }
        }

        let test = match self.kind_of_node(file, repetition.node) {
            AstKind::ForStatement(statement) => statement.test.as_ref()?,
            AstKind::WhileStatement(statement) => &statement.test,
            AstKind::DoWhileStatement(statement) => &statement.test,
            _ => return None,
        };
        let mut tests = vec![test];
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();

        if !is_within(nodes, expression.node_id(), test.node_id()) {
            if member_expression_of(expression).is_some() {
                return None;
            }

            let fresh = repetition.initial.is_some_and(|(_, initial)| {
                is_within(nodes, expression.node_id(), initial.node_id())
            });
            let references = Subtree::of(Root::Expression(expression), false, false);

            for kind in references.iter() {
                if !self.charge_work(Event::BudgetPrepassNode, 1) {
                    return None;
                }

                let AstKind::IdentifierReference(reference) = kind else {
                    continue;
                };
                let binding = self.binding_of_identifier(file, reference)?;
                let symbol = local_symbol_of(file, binding)?;

                if project
                    .file(file)
                    .semantic
                    .scoping()
                    .get_resolved_references(symbol)
                    .any(|reference| {
                        reference.is_write()
                            && (!fresh || is_within(nodes, reference.node_id(), repetition.node))
                    })
                {
                    return None;
                }
            }
        }

        let guarded_binding = binding.or_else(|| {
            member_expression_of(expression)
                .and_then(|member| identifier_of(unwrap(member.object())))
                .and_then(|reference| self.binding_of_identifier(file, reference))
        });

        if let Some(guarded_binding) = guarded_binding {
            for ancestor in nodes.ancestor_ids(repetition.node) {
                if !self.charge_work(Event::BudgetPrepassNode, 1) {
                    return None;
                }

                let AstKind::IfStatement(statement) = nodes.kind(ancestor) else {
                    continue;
                };

                if is_within(nodes, repetition.node, statement.consequent.node_id())
                    && self
                        .write_sites_of(file, guarded_binding, ancestor)
                        .is_some_and(|writes| {
                            writes
                                .iter()
                                .all(|write| is_within(nodes, *write, repetition.node))
                        })
                {
                    tests.push(&statement.test);
                }
            }
        }

        let mut lower: Option<f64> = None;
        let mut upper: Option<(Cost, f64)> = None;

        for conjunct in tests.into_iter().flat_map(conjuncts_of) {
            if !self.charge_work(Event::BudgetPrepassNode, 1) {
                return None;
            }

            let Some(pairs) = comparison_pairs_of(conjunct) else {
                continue;
            };

            for (value, endpoint, direction, _) in pairs {
                if !self.is_same_reading(file, value, expression) {
                    continue;
                }

                match direction {
                    Direction::Up => {
                        if let Some(candidate) =
                            self.bounded_quantity_with(file, endpoint, repetition, depth + 1, proof)
                        {
                            if upper.as_ref().is_none_or(|held| candidate.1 < held.1) {
                                upper = Some(candidate);
                            }
                        }
                    }
                    Direction::Down => {
                        if let Some(endpoint) = self.numeric_value_of(file, endpoint) {
                            lower = Some(lower.map_or(endpoint, |held| held.max(endpoint)));
                        }
                    }
                }
            }
        }

        let (Some(lower), Some((upper_cost, upper))) = (lower, upper) else {
            return None;
        };

        if lower < 0.0 || upper < lower || upper > 9_007_199_254_740_991.0 {
            return None;
        }

        let stable_binding = binding.filter(|binding| {
            if !matches!(declaration, Some(Declaration::Parameter { .. }))
                || self.is_parameter_unwritten(*binding)
            {
                return true;
            }

            local_symbol_of(file, *binding).is_some_and(|symbol| {
                project
                    .file(file)
                    .semantic
                    .scoping()
                    .get_resolved_references(symbol)
                    .filter(|reference| reference.is_write())
                    .all(|reference| is_within(nodes, reference.node_id(), repetition.node))
            })
        });
        let cost = stable_binding
            .and_then(|binding| self.current_substitutions.get(&binding))
            .and_then(|facts| facts.value.size.clone())
            .or_else(|| {
                stable_binding
                    .and(declaration)
                    .and_then(|declaration| self.parameter_quantity_of(declaration))
            });
        let cost = match (cost, expression) {
            (Some(cost), _) => cost,
            (None, Expression::StaticMemberExpression(member))
                if member.property.name == "length" =>
            {
                self.collection_size_of(file, &member.object).length
            }
            (None, Expression::Identifier(_)) if !upper_cost.is_one() => upper_cost,
            (None, Expression::Identifier(_)) => {
                let supplied = self.guarded_quantity_cost(file, expression, 0).or_else(|| {
                    let binding = binding?;
                    let (_, initial) = repetition
                        .initial
                        .filter(|(found, _)| *found == binding)
                        .or_else(|| self.entry_value_of(file, binding, repetition))?;

                    self.guarded_quantity_cost(file, initial, 0)
                });

                match supplied {
                    Some(cost) => cost,
                    None if repetition.initial.is_some_and(|(_, initial)| {
                        self.is_same_reading(file, initial, expression)
                    }) =>
                    {
                        Cost::ONE
                    }
                    None => return None,
                }
            }
            _ => return None,
        };

        Some((cost, upper))
    }

    fn parameter_quantity_of(&mut self, declaration: Declaration<'a>) -> Option<Cost> {
        let Declaration::Parameter {
            file,
            parameter: ParameterNode::Formal(parameter),
            ..
        } = declaration
        else {
            return None;
        };
        let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
            return None;
        };
        let origin = self.source_span(file, identifier.span);
        let value = self.values.at(origin);

        self.values
            .quantity(
                value.value,
                SizeQuantity::Value,
                identifier.name.to_string(),
            )
            .ok()
    }

    fn guarded_quantity_cost(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Option<Cost> {
        if depth > MAXIMUM_VALUE_DEPTH || !self.charge_work(Event::BudgetPrepassNode, 1) {
            return None;
        }

        if self.numeric_value_of(file, expression).is_some() {
            return Some(Cost::ONE);
        }

        let expression = unwrap(expression);

        if let Expression::StaticMemberExpression(member) = expression {
            if member.property.name == "length" {
                let size = self.collection_size_of(file, &member.object);

                return size.length_resolved.then_some(size.length);
            }
        }

        let reference = identifier_of(expression)?;
        let binding = self.binding_of_identifier(file, reference)?;
        let declaration = self.declarations.of_binding(self.project, binding)?;
        let (mut cost, function) = match declaration {
            Declaration::Variable {
                file: owner,
                declarator,
                ..
            } if owner == file => (
                self.guarded_quantity_cost(file, declarator.init.as_ref()?, depth + 1)?,
                self.enclosing_function_of(file, declarator.node_id())?,
            ),
            Declaration::Parameter {
                file: owner,
                function,
                ..
            } if owner == file => {
                let cost = self
                    .current_substitutions
                    .get(&binding)
                    .and_then(|facts| facts.value.size.clone())
                    .or_else(|| self.parameter_quantity_of(declaration))?;

                if self.is_parameter_unwritten(binding) {
                    return Some(cost);
                }

                (cost, function.node_id())
            }
            _ => return None,
        };
        let writes = self.write_sites_of(file, binding, function)?;

        if matches!(declaration, Declaration::Parameter { .. }) && writes.is_empty() {
            return None;
        }

        for site in writes {
            if !self.charge_work(Event::BudgetPrepassNode, 1) {
                return None;
            }

            let AstKind::AssignmentExpression(assignment) =
                self.project.file(file).semantic.nodes().parent_kind(site)
            else {
                return None;
            };

            if assignment.operator != AssignmentOperator::Assign {
                return None;
            }

            let assigned = self.guarded_quantity_cost(file, &assignment.right, depth + 1)?;
            cost = quantity_maximum(cost, assigned)?;
        }

        Some(cost)
    }

    fn distance_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<(f64, &'static str)> {
        let initial = self.initial_expression_of(file, comparison.counter, repetition)?;
        let toward = match comparison.direction {
            Direction::Up => 1.0,
            Direction::Down => -1.0,
        };

        if let (Some(start), Some(end)) = (
            self.numeric_value_of(file, initial),
            self.numeric_value_of(file, comparison.endpoint),
        ) {
            return Some((((end - start) * toward).max(0.0), "constant bound"));
        }

        let offset = self.offset_of(file, initial, comparison.endpoint)? * toward;

        Some((offset.max(0.0), "constant offset from start"))
    }

    fn offset_of(
        &mut self,
        file: FileId,
        initial: &'a Expression<'a>,
        endpoint: &'a Expression<'a>,
    ) -> Option<f64> {
        let Expression::BinaryExpression(binary) = unwrap(endpoint) else {
            return None;
        };
        let left = unwrap(&binary.left);
        let right = unwrap(&binary.right);

        match binary.operator {
            BinaryOperator::Addition => {
                if self.is_same_reading(file, initial, left) {
                    return self.numeric_value_of(file, right);
                }

                self.is_same_reading(file, initial, right)
                    .then(|| self.numeric_value_of(file, left))
                    .flatten()
            }
            BinaryOperator::Subtraction => self
                .is_same_reading(file, initial, left)
                .then(|| self.numeric_value_of(file, right).map(|value| -value))
                .flatten(),
            _ => None,
        }
    }

    fn is_same_reading(
        &mut self,
        file: FileId,
        left: &'a Expression<'a>,
        right: &'a Expression<'a>,
    ) -> bool {
        let left = unwrap(left);
        let right = unwrap(right);

        if let (Some(left), Some(right)) = (identifier_of(left), identifier_of(right)) {
            let left = self.binding_of_identifier(file, left);

            return left.is_some() && left == self.binding_of_identifier(file, right);
        }

        let (Some(left), Some(right)) = (member_expression_of(left), member_expression_of(right))
        else {
            return false;
        };
        let (Some(left_name), Some(right_name)) =
            (left.static_property_name(), right.static_property_name())
        else {
            return false;
        };

        left_name == right_name
            && self.is_same_reading(file, unwrap(left.object()), unwrap(right.object()))
    }

    fn initial_expression_of(
        &mut self,
        file: FileId,
        counter: Binding,
        repetition: &Repetition<'a>,
    ) -> Option<&'a Expression<'a>> {
        repetition
            .initial
            .filter(|(binding, _)| *binding == counter)
            .or_else(|| self.entry_value_of(file, counter, repetition))
            .map(|(_, initial)| initial)
    }

    fn entry_value_of(
        &mut self,
        file: FileId,
        counter: Binding,
        repetition: &Repetition<'a>,
    ) -> Option<(Binding, &'a Expression<'a>)> {
        let symbol = local_symbol_of(file, counter)?;
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();
        let declaration = semantic.scoping().symbol_declaration(symbol);

        if is_within(nodes, declaration, repetition.node) {
            return None;
        }

        let local = self.write_sites_of(file, counter, repetition.node)?;
        let total = self.counter_writes.get(&counter)?.as_ref()?.len();
        let settled = local.len() == total;

        if !settled {
            return None;
        }

        if self.enclosing_function_of(file, declaration)
            != self.enclosing_function_of(file, repetition.node)
        {
            return None;
        }

        let AstKind::VariableDeclarator(declarator) = self.kind_of_node(file, declaration) else {
            return None;
        };

        if !is_identifier_pattern(&declarator.id) {
            return None;
        }

        declarator
            .init
            .as_ref()
            .map(|initial| (counter, unwrap(initial)))
    }

    fn is_stable_endpoint(
        &mut self,
        file: FileId,
        endpoint: &'a Expression<'a>,
        repetition: &Repetition<'a>,
    ) -> bool {
        if self.numeric_value_of(file, endpoint).is_some() {
            return true;
        }

        let kinds = Subtree::of(Root::Expression(endpoint), false, false);
        let mut references = Vec::new();

        for kind in kinds {
            match kind {
                AstKind::CallExpression(_)
                | AstKind::NewExpression(_)
                | AstKind::TaggedTemplateExpression(_)
                | AstKind::JSXElement(_)
                | AstKind::JSXFragment(_)
                | AstKind::AwaitExpression(_)
                | AstKind::YieldExpression(_)
                | AstKind::AssignmentExpression(_)
                | AstKind::UpdateExpression(_)
                | AstKind::Function(_)
                | AstKind::ArrowFunctionExpression(_) => return false,
                AstKind::IdentifierReference(reference) => references.push(reference),
                _ => {}
            }
        }

        for reference in references {
            let Some(binding) = self.binding_of_identifier(file, reference) else {
                return false;
            };

            match self.write_sites_of(file, binding, repetition.node) {
                Some(sites) if sites.is_empty() => {}
                _ => return false,
            }
        }

        true
    }

    fn bisection_bound_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        if comparison.direction != Direction::Up {
            return None;
        }

        let reference = identifier_of(unwrap(comparison.endpoint))?;
        let upper = self.binding_of_identifier(file, reference)?;
        let lower = comparison.counter;

        if upper == lower || repetition.returns_to_head {
            return None;
        }

        let mut range = Cost::ONE;

        for binding in [lower, upper] {
            let (_, initial) = repetition
                .initial
                .filter(|(found, _)| *found == binding)
                .or_else(|| self.entry_value_of(file, binding, repetition))?;

            if self
                .numeric_value_of(file, initial)
                .is_some_and(|value| value < 0.0)
            {
                return None;
            }

            let (quantity, magnitude) = self.bounded_quantity_of(file, initial, repetition, 0)?;

            if magnitude > 1_073_741_823.0 {
                return None;
            }

            range = quantity_maximum(range, quantity)?;
        }

        let mut sites = Vec::new();

        for (binding, rising) in [(lower, true), (upper, false)] {
            for site in self.write_sites_of(file, binding, repetition.node)? {
                let write = self.write_of(file, binding, site, repetition);

                if write.deferred || write.updating {
                    return None;
                }

                if !self.is_bisecting_write(
                    file,
                    (lower, upper),
                    rising,
                    write.site,
                    repetition,
                    comparison.strictness,
                ) {
                    return None;
                }

                sites.push(write.site);
            }
        }

        if sites.is_empty() {
            return None;
        }

        self.covers_every_path(file, repetition, &sites)
            .then(|| logarithmic_bound_of("bound-bisection", "halving", range))
    }

    fn is_bisecting_write(
        &mut self,
        file: FileId,
        interval: (Binding, Binding),
        rising: bool,
        site: NodeId,
        repetition: &Repetition<'a>,
        strictness: Strictness,
    ) -> bool {
        let AstKind::AssignmentExpression(assignment) = self.kind_of_node(file, site) else {
            return false;
        };

        if assignment.operator != AssignmentOperator::Assign {
            return false;
        }

        let value = unwrap(&assignment.right);
        let (middle, offset) = match value {
            Expression::BinaryExpression(binary)
                if matches!(
                    binary.operator,
                    BinaryOperator::Addition | BinaryOperator::Subtraction
                ) =>
            {
                let Some(offset) = self.numeric_value_of(file, &binary.right) else {
                    return false;
                };
                let signed = match binary.operator {
                    BinaryOperator::Subtraction => -offset,
                    _ => offset,
                };

                (unwrap(&binary.left), signed)
            }
            _ => (value, 0.0),
        };

        let largest_falling_offset = match strictness {
            Strictness::Strict => 0.0,
            Strictness::Inclusive => -1.0,
        };

        if rising && offset < 1.0 {
            return false;
        }

        if !rising && offset > largest_falling_offset {
            return false;
        }

        self.is_midpoint_of(file, interval, middle, repetition, 0)
    }

    fn is_midpoint_of(
        &mut self,
        file: FileId,
        interval: (Binding, Binding),
        value: &'a Expression<'a>,
        repetition: &Repetition<'a>,
        depth: usize,
    ) -> bool {
        let value = unwrap(value);

        if depth < MAXIMUM_VALUE_DEPTH {
            if let Some(aliased) = self.repetition_constant_of(file, value, repetition) {
                return self.is_midpoint_of(file, interval, aliased, repetition, depth + 1);
            }
        }

        let truncated = self.truncated_argument_of(file, value);
        let value = truncated.unwrap_or(value);
        let Expression::BinaryExpression(binary) = value else {
            return false;
        };
        let left = unwrap(&binary.left);
        let right = unwrap(&binary.right);

        match binary.operator {
            BinaryOperator::Division
            | BinaryOperator::ShiftRight
            | BinaryOperator::ShiftRightZeroFill => {
                (binary.operator != BinaryOperator::Division || truncated.is_some())
                    && self.is_halving_divisor(file, binary.operator, right)
                    && self.is_interval_sum(file, interval, left)
            }
            BinaryOperator::Addition => {
                (self.is_counter_reference(file, interval.0, left)
                    && self.is_half_width(file, interval, right))
                    || (self.is_counter_reference(file, interval.0, right)
                        && self.is_half_width(file, interval, left))
            }
            _ => false,
        }
    }

    fn is_halving_divisor(
        &mut self,
        file: FileId,
        operator: BinaryOperator,
        divisor: &'a Expression<'a>,
    ) -> bool {
        let expected = match operator {
            BinaryOperator::Division => 2.0,
            BinaryOperator::ShiftRight | BinaryOperator::ShiftRightZeroFill => 1.0,
            _ => return false,
        };

        self.numeric_value_of(file, divisor) == Some(expected)
    }

    fn is_interval_sum(
        &mut self,
        file: FileId,
        interval: (Binding, Binding),
        value: &'a Expression<'a>,
    ) -> bool {
        let Expression::BinaryExpression(binary) = unwrap(value) else {
            return false;
        };

        if binary.operator != BinaryOperator::Addition {
            return false;
        }

        let left = unwrap(&binary.left);
        let right = unwrap(&binary.right);

        (self.is_counter_reference(file, interval.0, left)
            && self.is_counter_reference(file, interval.1, right))
            || (self.is_counter_reference(file, interval.1, left)
                && self.is_counter_reference(file, interval.0, right))
    }

    fn is_half_width(
        &mut self,
        file: FileId,
        interval: (Binding, Binding),
        value: &'a Expression<'a>,
    ) -> bool {
        let value = unwrap(value);
        let truncated = self.truncated_argument_of(file, value);
        let value = truncated.unwrap_or(value);
        let Expression::BinaryExpression(binary) = value else {
            return false;
        };
        let halving = self.is_halving_divisor(file, binary.operator, &binary.right);

        if !halving || (binary.operator == BinaryOperator::Division && truncated.is_none()) {
            return false;
        }

        let Expression::BinaryExpression(width) = unwrap(&binary.left) else {
            return false;
        };

        width.operator == BinaryOperator::Subtraction
            && self.is_counter_reference(file, interval.1, unwrap(&width.left))
            && self.is_counter_reference(file, interval.0, unwrap(&width.right))
    }

    pub(crate) fn share_quantity_of(
        &mut self,
        file: FileId,
        loop_kind: AstKind<'a>,
        step: NodeId,
    ) -> Option<Cost> {
        let AstKind::AssignmentExpression(assignment) = self.kind_of_node(file, step) else {
            return None;
        };
        let body = loop_body_of(loop_kind)?;
        let node = loop_kind.node_id();
        let (update, initial) = match loop_kind {
            AstKind::ForStatement(statement) => (
                statement.update.as_ref().map(unwrap),
                self.loop_variable_of(file, statement),
            ),
            _ => (None, None),
        };
        let repetition = Repetition {
            node,
            body,
            update,
            initial,
            returns_to_head: self.returns_to_head(file, node, body),
            geometric_proof: "halving",
        };

        self.bounded_quantity_of(file, &assignment.right, &repetition, 0)
            .map(|(cost, _)| cost)
    }

    fn share_bound_of(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        for conjunct in conjuncts_of(test) {
            if let Some(bound) = self.share_conjunct_bound_of(file, conjunct, repetition) {
                return Some(bound);
            }
        }

        None
    }

    fn share_conjunct_bound_of(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<Verdict> {
        let Expression::BinaryExpression(binary) = unwrap(test) else {
            return None;
        };

        if !is_less(binary.operator) {
            return None;
        }

        let counter = identifier_of(unwrap(&binary.left))?;
        let counter = self.binding_of_identifier(file, counter)?;
        let (_, initial) = repetition
            .initial
            .filter(|(binding, _)| *binding == counter)?;
        let endpoint = unwrap(&binary.right);
        let (_, initial_magnitude) = self.bounded_quantity_of(file, initial, repetition, 0)?;
        let (_, endpoint_magnitude) = self.bounded_quantity_of(file, endpoint, repetition, 0)?;
        let magnitude = initial_magnitude.max(endpoint_magnitude);

        if magnitude + 0.5 <= magnitude {
            return None;
        }

        let shared =
            self.is_share_sized(file, endpoint) || self.is_share_offset_of(file, initial, endpoint);

        (shared && self.consumes_a_unit(file, counter, repetition))
            .then(|| constant_bound_of("bound-share", "share of budget"))
    }

    fn is_share_offset_of(
        &mut self,
        file: FileId,
        initial: &'a Expression<'a>,
        endpoint: &'a Expression<'a>,
    ) -> bool {
        let Expression::BinaryExpression(sum) = endpoint else {
            return false;
        };

        if sum.operator != BinaryOperator::Addition {
            return false;
        }

        (self.is_same_reading(file, initial, &sum.left) && self.is_share_sized(file, &sum.right))
            || (self.is_same_reading(file, initial, &sum.right)
                && self.is_share_sized(file, &sum.left))
    }

    fn consumes_a_unit(
        &mut self,
        file: FileId,
        counter: Binding,
        repetition: &Repetition<'a>,
    ) -> bool {
        let Some(progression) = self.progression_of(file, counter, repetition) else {
            return false;
        };
        let Some(advances) = progression.advances(1.0) else {
            return false;
        };

        if !advances
            .iter()
            .all(|advance| advance.is_some_and(|advance| advance >= 0.0))
        {
            return false;
        }

        progression
            .guaranteed_advance(1.0)
            .is_some_and(|guaranteed| guaranteed >= 1.0)
    }

    fn loop_variable_of(
        &mut self,
        file: FileId,
        statement: &'a ForStatement<'a>,
    ) -> Option<(Binding, &'a Expression<'a>)> {
        match statement.init.as_ref()? {
            ForStatementInit::VariableDeclaration(declaration) => {
                let [declarator] = declaration.declarations.as_slice() else {
                    return None;
                };
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    return None;
                };
                let symbol = identifier.symbol_id.get()?;
                let initial = declarator.init.as_ref()?;

                Some((Binding::Symbol { file, symbol }, unwrap(initial)))
            }
            init => {
                let Expression::AssignmentExpression(assignment) = init.as_expression()? else {
                    return None;
                };
                let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left else {
                    return None;
                };

                if assignment.operator != AssignmentOperator::Assign {
                    return None;
                }

                let binding = self.binding_of_identifier(file, target)?;

                Some((binding, unwrap(&assignment.right)))
            }
        }
    }

    fn runs_at_most_once(&mut self, file: FileId, node: NodeId, body: &'a Statement<'a>) -> bool {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let Some(completion) = completion_of(semantic, body.node_id()) else {
            return false;
        };

        if !leaves_iteration(semantic.nodes(), completion, node) {
            return false;
        }

        !self.returns_to_head(file, node, body)
    }

    fn returns_to_head(&mut self, file: FileId, node: NodeId, body: &'a Statement<'a>) -> bool {
        if let Some(found) = self.repeating_bodies.get(&(file, node)) {
            return *found;
        }

        let kinds = self.counted_subtree(file, Root::Statement(body), Event::BudgetPrepassNode);
        let exhausted = self.work_exhausted();
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let found = exhausted
            || kinds.into_iter().any(|kind| match kind {
                AstKind::ContinueStatement(statement) => {
                    let label = statement.label.as_ref().map(|label| label.name.as_str());

                    control_target_of(semantic, statement.node_id(), label, true) == Some(node)
                }
                _ => false,
            });

        self.repeating_bodies.insert((file, node), found);

        found
    }

    fn covers_every_path(
        &self,
        file: FileId,
        repetition: &Repetition<'a>,
        sites: &[NodeId],
    ) -> bool {
        self.covers_statement(file, repetition.node, repetition.body, sites)
    }

    fn covers_statement(
        &self,
        file: FileId,
        node: NodeId,
        statement: &'a Statement<'a>,
        sites: &[NodeId],
    ) -> bool {
        let project = self.project;
        let semantic = &project.file(file).semantic;

        if let Some(completion) = completion_of(semantic, statement.node_id()) {
            if leaves_iteration(semantic.nodes(), completion, node) {
                return true;
            }
        }

        match statement {
            Statement::BlockStatement(block) => {
                self.covers_sequence(file, node, &block.body, sites)
            }
            Statement::ExpressionStatement(statement) => {
                covers_expression(&statement.expression, sites)
            }
            Statement::LabeledStatement(statement) => {
                self.covers_statement(file, node, &statement.body, sites)
            }
            Statement::IfStatement(statement) => match &statement.alternate {
                Some(alternate) => {
                    self.covers_statement(file, node, &statement.consequent, sites)
                        && self.covers_statement(file, node, alternate, sites)
                }
                None => false,
            },
            _ => false,
        }
    }

    fn covers_sequence(
        &self,
        file: FileId,
        node: NodeId,
        body: &'a [Statement<'a>],
        sites: &[NodeId],
    ) -> bool {
        let Some((last, leading)) = body.split_last() else {
            return false;
        };

        for statement in leading {
            if self.covers_statement(file, node, statement, sites) {
                return true;
            }

            if self.skips_remainder(file, node, statement) {
                return false;
            }
        }

        self.covers_statement(file, node, last, sites)
    }

    fn skips_remainder(&self, file: FileId, node: NodeId, statement: &'a Statement<'a>) -> bool {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();
        let root = statement.node_id();

        Subtree::of(Root::Statement(statement), true, false)
            .into_iter()
            .filter_map(|kind| match kind {
                AstKind::BreakStatement(jump) => Some(jump.node_id()),
                AstKind::ContinueStatement(jump) => Some(jump.node_id()),
                _ => None,
            })
            .any(|jump| match completion_of(semantic, jump) {
                Some(completion) => match completion {
                    Completion::Break(target) | Completion::Continue(target) => {
                        !leaves_iteration(nodes, completion, node)
                            && !is_within(nodes, target, root)
                    }
                    _ => false,
                },
                None => true,
            })
    }
}

fn local_symbol_of(file: FileId, counter: Binding) -> Option<SymbolId> {
    let Binding::Symbol {
        file: owner,
        symbol,
    } = counter;

    (owner == file).then_some(symbol)
}

fn is_replacing(write: &CounterWrite) -> bool {
    write.step == Step::Replacing
}

fn covers_expression(value: &Expression<'_>, sites: &[NodeId]) -> bool {
    match value {
        Expression::ParenthesizedExpression(inner) => covers_expression(&inner.expression, sites),
        Expression::TSAsExpression(inner) => covers_expression(&inner.expression, sites),
        Expression::TSSatisfiesExpression(inner) => covers_expression(&inner.expression, sites),
        Expression::TSNonNullExpression(inner) => covers_expression(&inner.expression, sites),
        Expression::TSTypeAssertion(inner) => covers_expression(&inner.expression, sites),
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .iter()
            .any(|value| covers_expression(value, sites)),
        Expression::ConditionalExpression(conditional) => {
            covers_expression(&conditional.consequent, sites)
                && covers_expression(&conditional.alternate, sites)
        }
        Expression::AssignmentExpression(_) | Expression::UpdateExpression(_) => {
            sites.contains(&value.node_id())
        }
        _ => false,
    }
}

fn leaves_iteration(nodes: &AstNodes<'_>, completion: Completion, node: NodeId) -> bool {
    match completion {
        Completion::Return | Completion::Throw => true,
        Completion::Break(target) => target == node || !is_within(nodes, target, node),
        Completion::Continue(target) => target != node,
        Completion::Normal => false,
    }
}

fn is_within(nodes: &AstNodes<'_>, node: NodeId, ancestor: NodeId) -> bool {
    node == ancestor || nodes.ancestor_ids(node).any(|found| found == ancestor)
}

fn constant_bound_of(rule: &'static str, condition: &'static str) -> Verdict {
    Verdict::Proven {
        factor: Cost::ONE,
        rule,
        condition: Some(condition),
    }
}

/// A counter scaled geometrically across `quantity`: logarithmic in that quantity, which is
/// constant for a constant range.
fn logarithmic_bound_of(rule: &'static str, condition: &'static str, quantity: Cost) -> Verdict {
    if quantity.is_one() {
        return constant_bound_of(rule, condition);
    }

    match Cost::logarithm(quantity) {
        Ok(factor) => Verdict::Proven {
            factor,
            rule,
            condition: Some(condition),
        },
        Err(_) => unresolved_bound_of(),
    }
}

/// A loop over a collection whose size no rule tracks (`input-size-envelope`).
fn untracked_bound_of() -> Verdict {
    Verdict::Unresolved {
        reason: UnknownReason::SizeRelation,
    }
}

fn unresolved_bound_of() -> Verdict {
    Verdict::Unresolved {
        reason: UnknownReason::Bound,
    }
}

#[cfg(test)]
#[path = "bounds.test.rs"]
mod tests;

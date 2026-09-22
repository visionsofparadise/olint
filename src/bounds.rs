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
use crate::budgets::{comparison_pairs_of, conjuncts_of, is_less, Direction, Strictness, Subtree};
use crate::cost::Cost;
use crate::declarations::{Binding, Declaration};
use crate::directives::PerfTag;
use crate::flow::{completion_of, control_target_of, Completion};
use crate::project::FileId;
use crate::syntax::{
    collapsed_text_of, identifier_of, is_identifier_pattern, is_iteration_kind, loop_body_of,
    member_expression_of, unwrap, Root,
};
use crate::unknowns::UnknownReason;
use crate::values::Primitive;

const MAXIMUM_VALUE_DEPTH: usize = 4;

const SMALLEST_GROWTH_RATIO: f64 = 2.0;

const LARGEST_CONTRACTION_RATIO: f64 = 0.5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bound {
    Proven {
        factor: Cost,
        proof: Option<&'static str>,
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

    pub fn proof(&self) -> Option<&'static str> {
        match self {
            Bound::Proven { proof, .. } => *proof,
            Bound::Unresolved { .. } => None,
        }
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

    pub fn label(&self) -> &'static str {
        match self {
            Bound::Unresolved { reason } => reason.text(),
            Bound::Proven {
                proof: Some(proof), ..
            } => proof,
            Bound::Proven { factor, .. } if *factor == Cost::LOG => "log",
            Bound::Proven { .. } => "N",
        }
    }

    fn strength(&self) -> u8 {
        match self {
            Bound::Proven { factor, .. } if factor.is_one() => 0,
            Bound::Proven { factor, .. } if *factor == Cost::LOG => 1,
            Bound::Proven { .. } => 2,
            Bound::Unresolved { .. } => 3,
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

    pub fn bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Bound {
        let bound = self.inner_bound_of(file, loop_kind);

        if self.bound_seen.insert((file, loop_kind.node_id())) {
            self.stats.count(&format!(
                "loop {}: {}",
                loop_label(loop_kind),
                bound.label()
            ));
        }

        bound
    }

    fn inner_bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Bound {
        if self.perf_tags(file, loop_kind).contains(&PerfTag::Bounded) {
            return constant_bound_of("@perf bounded");
        }

        let Some(body) = loop_body_of(loop_kind) else {
            return linear_bound_of();
        };

        if self.runs_at_most_once(file, loop_kind.node_id(), body) {
            return constant_bound_of("single iteration");
        }

        match loop_kind {
            AstKind::ForOfStatement(statement) => {
                if self.is_constant_sized(file, &statement.right) {
                    constant_bound_of("constant collection")
                } else if self.is_share_sized(file, &statement.right) {
                    constant_bound_of("share of budget")
                } else {
                    linear_bound_of()
                }
            }
            AstKind::ForInStatement(statement) => {
                if self.is_constant_sized(file, &statement.right)
                    || self.is_closed(file, &statement.right)
                {
                    constant_bound_of("closed object type")
                } else {
                    linear_bound_of()
                }
            }
            AstKind::ForStatement(statement) => self.bound_of_for(file, statement, body),
            AstKind::WhileStatement(statement) => {
                self.bound_of_while(file, loop_kind.node_id(), &statement.test, body)
            }
            AstKind::DoWhileStatement(statement) => {
                self.bound_of_while(file, loop_kind.node_id(), &statement.test, body)
            }
            _ => linear_bound_of(),
        }
    }

    fn bound_of_for(
        &mut self,
        file: FileId,
        statement: &'a ForStatement<'a>,
        body: &'a Statement<'a>,
    ) -> Bound {
        let Some(test) = statement.test.as_ref() else {
            return linear_bound_of();
        };
        let variable = self.loop_variable_of(file, statement);

        if let Some(bound) = self.share_bound_of(file, test, variable.as_ref()) {
            return bound;
        }

        let repetition = Repetition {
            node: statement.node_id(),
            body,
            update: statement.update.as_ref().map(unwrap),
            initial: variable,
            returns_to_head: self.returns_to_head(file, statement.node_id(), body),
            geometric_proof: "geometric step",
        };

        self.bound_of_repetition(file, test, &repetition)
    }

    fn bound_of_while(
        &mut self,
        file: FileId,
        node: NodeId,
        test: &'a Expression<'a>,
        body: &'a Statement<'a>,
    ) -> Bound {
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
    ) -> Bound {
        let comparisons = self.comparisons_of(file, test);
        let mut best: Option<Bound> = None;

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

        best.unwrap_or_else(linear_bound_of)
    }

    fn comparisons_of(&mut self, file: FileId, test: &'a Expression<'a>) -> Vec<Comparison<'a>> {
        let mut found = Vec::new();

        for conjunct in conjuncts_of(test) {
            let Some(pairs) = comparison_pairs_of(conjunct) else {
                continue;
            };

            for (counter, endpoint, direction, strictness) in pairs {
                let Some(reference) = identifier_of(counter) else {
                    continue;
                };
                let Some(counter) = self.binding_of_identifier(file, reference) else {
                    continue;
                };

                found.push(Comparison {
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
    ) -> Option<Bound> {
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

    fn write_sites_of(&self, file: FileId, counter: Binding, node: NodeId) -> Option<Vec<NodeId>> {
        let symbol = local_symbol_of(file, counter)?;
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();

        Some(
            semantic
                .scoping()
                .get_resolved_references(symbol)
                .filter(|reference| reference.is_write())
                .map(|reference| reference.node_id())
                .filter(|site| is_within(nodes, *site, node))
                .collect(),
        )
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

        if !matches!(name, "floor" | "trunc") {
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
    ) -> Option<Bound> {
        if progression.writes.is_empty() {
            return None;
        }

        let mut ratios = Vec::new();

        for write in &progression.writes {
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
                if !ratios.iter().all(|ratio| *ratio >= SMALLEST_GROWTH_RATIO) {
                    return None;
                }

                let (_, initial) = repetition
                    .initial
                    .filter(|(binding, _)| *binding == comparison.counter)
                    .or_else(|| self.entry_value_of(file, comparison.counter, repetition))?;

                (self.numeric_value_of(file, initial)? >= 1.0)
                    .then(|| logarithmic_bound_of(repetition.geometric_proof))
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

                clears_the_endpoint.then(|| logarithmic_bound_of(repetition.geometric_proof))
            }
        }
    }

    fn additive_bound_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        progression: &Progression,
        repetition: &Repetition<'a>,
    ) -> Option<Bound> {
        if progression.writes.is_empty() {
            return None;
        }

        let toward = match comparison.direction {
            Direction::Up => 1.0,
            Direction::Down => -1.0,
        };
        let mut advances = Vec::new();

        for write in &progression.writes {
            match write.step {
                Step::Additive(delta) => advances.push(delta.map(|delta| delta * toward)),
                _ => return None,
            }
        }

        if advances.iter().any(Option::is_none) {
            return Some(unresolved_bound_of());
        }

        let guaranteed: Option<f64> = progression
            .unconditional
            .iter()
            .map(|write| match write.step {
                Step::Additive(delta) => delta.map(|delta| delta * toward),
                _ => None,
            })
            .try_fold(0.0, |total, advance| advance.map(|advance| total + advance));

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
            return None;
        }

        if !self.is_stable_endpoint(file, comparison.endpoint, repetition) {
            return None;
        }

        let (distance, proof) = self.distance_of(file, comparison, repetition)?;
        let repetitions = (distance / guaranteed).floor() + 1.0;

        repetitions.is_finite().then(|| constant_bound_of(proof))
    }

    fn distance_of(
        &mut self,
        file: FileId,
        comparison: &Comparison<'a>,
        repetition: &Repetition<'a>,
    ) -> Option<(f64, &'static str)> {
        let (_, initial) = repetition
            .initial
            .filter(|(binding, _)| *binding == comparison.counter)
            .or_else(|| self.entry_value_of(file, comparison.counter, repetition))?;
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

        (offset >= 0.0).then_some((offset, "constant offset from start"))
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

        let settled = semantic
            .scoping()
            .get_resolved_references(symbol)
            .filter(|reference| reference.is_write())
            .all(|reference| is_within(nodes, reference.node_id(), repetition.node));

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
    ) -> Option<Bound> {
        if comparison.direction != Direction::Up {
            return None;
        }

        let reference = identifier_of(unwrap(comparison.endpoint))?;
        let upper = self.binding_of_identifier(file, reference)?;
        let lower = comparison.counter;

        if upper == lower || repetition.returns_to_head {
            return None;
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
            .then(|| logarithmic_bound_of("halving"))
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

        let value = self.truncated_argument_of(file, value).unwrap_or(value);
        let Expression::BinaryExpression(binary) = value else {
            return false;
        };
        let left = unwrap(&binary.left);
        let right = unwrap(&binary.right);

        match binary.operator {
            BinaryOperator::Division
            | BinaryOperator::ShiftRight
            | BinaryOperator::ShiftRightZeroFill => {
                self.is_halving_divisor(file, binary.operator, right)
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
        let value = self.truncated_argument_of(file, value).unwrap_or(value);
        let Expression::BinaryExpression(binary) = value else {
            return false;
        };
        let halving = self.is_halving_divisor(file, binary.operator, &binary.right);

        if !halving {
            return false;
        }

        let Expression::BinaryExpression(width) = unwrap(&binary.left) else {
            return false;
        };

        width.operator == BinaryOperator::Subtraction
            && self.is_counter_reference(file, interval.1, unwrap(&width.left))
            && self.is_counter_reference(file, interval.0, unwrap(&width.right))
    }

    fn share_bound_of(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        variable: Option<&(Binding, &'a Expression<'a>)>,
    ) -> Option<Bound> {
        let Expression::BinaryExpression(binary) = unwrap(test) else {
            return None;
        };

        if !is_less(binary.operator) {
            return None;
        }

        let counter = identifier_of(unwrap(&binary.left))?;
        let counter = self.binding_of_identifier(file, counter)?;
        let (_, initial) = variable.filter(|(binding, _)| *binding == counter)?;
        let endpoint = unwrap(&binary.right);

        if self.is_share_sized(file, endpoint) {
            return Some(constant_bound_of("share of budget"));
        }

        let Expression::BinaryExpression(sum) = endpoint else {
            return None;
        };

        if sum.operator != BinaryOperator::Addition {
            return None;
        }

        let shared = (self.is_same_reading(file, initial, &sum.left)
            && self.is_share_sized(file, &sum.right))
            || (self.is_same_reading(file, initial, &sum.right)
                && self.is_share_sized(file, &sum.left));

        shared.then(|| constant_bound_of("share of budget"))
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

fn constant_bound_of(proof: &'static str) -> Bound {
    Bound::Proven {
        factor: Cost::ONE,
        proof: Some(proof),
    }
}

fn logarithmic_bound_of(proof: &'static str) -> Bound {
    Bound::Proven {
        factor: Cost::LOG,
        proof: Some(proof),
    }
}

fn linear_bound_of() -> Bound {
    Bound::Proven {
        factor: Cost::N,
        proof: None,
    }
}

fn unresolved_bound_of() -> Bound {
    Bound::Unresolved {
        reason: UnknownReason::Bound,
    }
}

#[cfg(test)]
#[path = "bounds.test.rs"]
mod tests;

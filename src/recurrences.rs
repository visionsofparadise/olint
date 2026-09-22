use oxc_ast::ast::{Argument, BindingPattern, Expression, Statement, TSType};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{BinaryOperator, LogicalOperator};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::cost::Cost;
use crate::declarations::{parameters_of, Binding, FunctionNode};
use crate::project::FileId;
use crate::summaries::Substitutions;
use crate::syntax::unwrap;

pub const MAXIMUM_RECURRENCE_MEMBERS: usize = 16;
pub const MAXIMUM_RECURRENCE_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentRelation {
    Decrement { amount: u64 },
    Division { divisor: u64, truncating: bool },
    Unchanged,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CallStep {
    pub callee_position: usize,
    pub caller_position: usize,
    pub relation: ArgumentRelation,
    pub lower_bound: Option<f64>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecurrenceEdge {
    pub callee: usize,
    pub multiplicity: Cost,
    pub relation: ArgumentRelation,
    pub lower_bound: Option<f64>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecurrenceEquation {
    pub local: Cost,
    pub measure: Cost,
    pub edges: Vec<RecurrenceEdge>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum RecurrenceSolution {
    Solved {
        factors: Vec<Cost>,
        proof: &'static str,
    },
    Unsupported {
        reason: &'static str,
    },
}

pub fn weaker_relation_of(left: ArgumentRelation, right: ArgumentRelation) -> ArgumentRelation {
    match (left, right) {
        (ArgumentRelation::Unchanged, _) | (_, ArgumentRelation::Unchanged) => {
            ArgumentRelation::Unchanged
        }
        (
            ArgumentRelation::Decrement { amount: left },
            ArgumentRelation::Decrement { amount: right },
        ) => ArgumentRelation::Decrement {
            amount: left.min(right),
        },
        (ArgumentRelation::Decrement { amount }, _)
        | (_, ArgumentRelation::Decrement { amount }) => ArgumentRelation::Decrement { amount },
        (
            ArgumentRelation::Division {
                divisor: left,
                truncating: left_exact,
            },
            ArgumentRelation::Division {
                divisor: right,
                truncating: right_exact,
            },
        ) => ArgumentRelation::Division {
            divisor: left.min(right),
            truncating: left_exact && right_exact,
        },
    }
}

fn guard_admits(relation: ArgumentRelation, lower_bound: Option<f64>) -> bool {
    match relation {
        ArgumentRelation::Unchanged => true,
        ArgumentRelation::Decrement { amount } => amount >= 1 && lower_bound.is_some(),
        ArgumentRelation::Division {
            divisor,
            truncating,
        } => {
            let floor = match truncating {
                true => 0.0,
                false => 1.0,
            };

            divisor >= 2 && lower_bound.is_some_and(|bound| bound >= floor)
        }
    }
}

fn reduces(relation: ArgumentRelation) -> bool {
    !matches!(relation, ArgumentRelation::Unchanged)
}

fn has_neutral_cycle(equations: &[RecurrenceEquation]) -> bool {
    let mut entered = vec![false; equations.len()];
    let mut settled = vec![false; equations.len()];

    for start in 0..equations.len() {
        if settled[start] {
            continue;
        }

        let mut stack = vec![(start, 0usize)];

        entered[start] = true;

        while let Some((member, next)) = stack.pop() {
            let neutral: Vec<usize> = equations[member]
                .edges
                .iter()
                .filter(|edge| !reduces(edge.relation))
                .map(|edge| edge.callee)
                .collect();

            if next >= neutral.len() {
                entered[member] = false;
                settled[member] = true;

                continue;
            }

            stack.push((member, next + 1));

            let callee = neutral[next];

            if entered[callee] {
                return true;
            }

            if settled[callee] {
                continue;
            }

            entered[callee] = true;

            stack.push((callee, 0));
        }
    }

    false
}

fn branching_of(equation: &RecurrenceEquation) -> Option<u64> {
    equation.edges.iter().try_fold(0u64, |total, edge| {
        total.checked_add(edge.multiplicity.constant_of()?)
    })
}

pub fn solution_of(equations: &[RecurrenceEquation]) -> RecurrenceSolution {
    if equations.is_empty() || equations.len() > MAXIMUM_RECURRENCE_MEMBERS {
        return RecurrenceSolution::Unsupported {
            reason: "component size",
        };
    }

    for equation in equations {
        if equation.edges.is_empty() {
            return RecurrenceSolution::Unsupported {
                reason: "invisible recursive call",
            };
        }

        for edge in &equation.edges {
            if edge.callee >= equations.len() {
                return RecurrenceSolution::Unsupported {
                    reason: "member outside the component",
                };
            }

            if !guard_admits(edge.relation, edge.lower_bound) {
                return RecurrenceSolution::Unsupported {
                    reason: "unguarded reduction",
                };
            }
        }
    }

    let chain = equations
        .iter()
        .all(|equation| branching_of(equation) == Some(1));

    if chain {
        return chain_solution_of(equations);
    }

    branching_solution_of(equations)
}

fn chain_solution_of(equations: &[RecurrenceEquation]) -> RecurrenceSolution {
    let reducing: Vec<&RecurrenceEdge> = equations
        .iter()
        .flat_map(|equation| equation.edges.iter())
        .filter(|edge| reduces(edge.relation))
        .collect();

    if reducing.is_empty() {
        return RecurrenceSolution::Unsupported {
            reason: "no proven measure reduction",
        };
    }

    if has_neutral_cycle(equations) {
        return RecurrenceSolution::Unsupported {
            reason: "cycle without a measure reduction",
        };
    }

    let decrementing = reducing
        .iter()
        .any(|edge| matches!(edge.relation, ArgumentRelation::Decrement { .. }));
    let mut factors = Vec::new();

    for equation in equations {
        let depth = match decrementing {
            true => Ok(equation.measure.clone()),
            false => Cost::logarithm(equation.measure.clone()),
        };
        let Ok(depth) = depth else {
            return RecurrenceSolution::Unsupported {
                reason: "measure logarithm",
            };
        };

        factors.push(depth);
    }

    let proof = match decrementing {
        true => "guarded decrement depth",
        false => "guarded geometric reduction depth",
    };

    RecurrenceSolution::Solved { factors, proof }
}

fn branching_solution_of(equations: &[RecurrenceEquation]) -> RecurrenceSolution {
    let mut amount = None;

    for equation in equations {
        for edge in &equation.edges {
            match edge.relation {
                ArgumentRelation::Decrement { amount: step } if amount.unwrap_or(step) == step => {
                    amount = Some(step)
                }
                _ => {
                    return RecurrenceSolution::Unsupported {
                        reason: "branching without a uniform decrement",
                    }
                }
            }
        }
    }

    let Some(amount) = amount else {
        return RecurrenceSolution::Unsupported {
            reason: "branching without a decrement",
        };
    };
    let mut multiplicities = Vec::new();

    for equation in equations {
        let Ok(multiplicity) = Cost::sum(
            equation
                .edges
                .iter()
                .map(|edge| edge.multiplicity.clone())
                .collect(),
        ) else {
            return RecurrenceSolution::Unsupported {
                reason: "branching multiplicity expression",
            };
        };

        multiplicities.push(multiplicity);
    }

    if equations.len() == 1 && amount == 1 && multiplicities[0] == equations[0].measure {
        let Ok(levels) = Cost::factorial(equations[0].measure.clone()) else {
            return RecurrenceSolution::Unsupported {
                reason: "measure factorial",
            };
        };

        return RecurrenceSolution::Solved {
            factors: vec![levels],
            proof: "guarded decrement with measure multiplicity",
        };
    }

    let Ok(branching) = Cost::maximum(multiplicities) else {
        return RecurrenceSolution::Unsupported {
            reason: "branching multiplicity expression",
        };
    };

    if branching.is_one() {
        return RecurrenceSolution::Unsupported {
            reason: "branching below two",
        };
    }

    let mut factors = Vec::new();

    for equation in equations {
        let exponent = match amount {
            1 => Ok(equation.measure.clone()),
            divisor => Cost::ratio(equation.measure.clone(), Cost::constant(divisor)),
        };
        let Ok(exponent) = exponent else {
            return RecurrenceSolution::Unsupported {
                reason: "decrement ratio",
            };
        };
        let Ok(levels) = Cost::power(branching.clone(), exponent) else {
            return RecurrenceSolution::Unsupported {
                reason: "branching power",
            };
        };

        factors.push(levels);
    }

    RecurrenceSolution::Solved {
        factors,
        proof: "guarded decrement with branching",
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn numeric_parameter_binding_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        position: usize,
    ) -> Option<Binding> {
        let parameters = parameters_of(function)?;
        let parameter = parameters.items.get(position)?;
        let TSType::TSNumberKeyword(_) = parameter
            .type_annotation
            .as_ref()
            .map(|annotation| &annotation.type_annotation)?
        else {
            return None;
        };
        let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
            return None;
        };
        let symbol = identifier.symbol_id.get()?;

        Some(Binding::Symbol { file, symbol })
    }

    pub(crate) fn recurrence_measure_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        position: usize,
        inputs: &Substitutions,
    ) -> Option<Cost> {
        let binding = self.numeric_parameter_binding_of(file, function, position)?;

        inputs.get(&binding)?.value.size.clone()
    }

    pub(crate) fn note_unresolved_multiplicity(&mut self, part: &crate::cost::Part) {
        if part
            .cost
            .mentions_dimension_from(crate::values::RECURRENCE_FLOOR)
        {
            self.forget_recurrence_multiplicity();
        }
    }

    pub(crate) fn reduced_measure_size_of(
        &mut self,
        file: FileId,
        argument: &'a Expression<'a>,
    ) -> Option<Cost> {
        if !self.charge_work(Event::RecurrenceStep, 1) {
            return None;
        }

        let (relation, binding) = self.relation_of(file, argument, 0)?;

        if matches!(relation, ArgumentRelation::Unchanged) {
            return None;
        }

        if !matches!(
            self.declarations.of_binding(self.project, binding),
            Some(crate::declarations::Declaration::Parameter { .. })
        ) || !self.is_parameter_unwritten(binding)
        {
            return None;
        }

        self.current_substitutions.get(&binding)?.value.size.clone()
    }

    pub(crate) fn call_steps_of(
        &mut self,
        (callee_file, callee): (FileId, FunctionNode<'a>),
        (caller_file, caller): (FileId, FunctionNode<'a>),
        (call_file, arguments): (FileId, &'a [Argument<'a>]),
    ) -> Vec<CallStep> {
        let mut steps = Vec::new();
        let Some(parameters) = parameters_of(callee) else {
            return steps;
        };
        let count = parameters.items.len().min(arguments.len());

        for (position, argument) in arguments.iter().enumerate().take(count) {
            if !self.charge_work(Event::RecurrenceStep, 1) {
                return Vec::new();
            }

            if self
                .numeric_parameter_binding_of(callee_file, callee, position)
                .is_none()
            {
                continue;
            }

            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let Some((relation, source)) = self.relation_of(call_file, argument, 0) else {
                continue;
            };
            let Some(caller_position) = self.caller_position_of(caller_file, caller, source) else {
                continue;
            };
            let lower_bound = self.lower_bound_of(call_file, argument.node_id(), source);

            steps.push(CallStep {
                callee_position: position,
                caller_position,
                relation,
                lower_bound,
            });
        }

        steps
    }

    fn caller_position_of(
        &mut self,
        caller_file: FileId,
        caller: FunctionNode<'a>,
        binding: Binding,
    ) -> Option<usize> {
        let parameters = parameters_of(caller)?;

        (0..parameters.items.len()).find(|position| {
            self.numeric_parameter_binding_of(caller_file, caller, *position) == Some(binding)
        })
    }

    fn relation_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        depth: usize,
    ) -> Option<(ArgumentRelation, Binding)> {
        if depth > MAXIMUM_RECURRENCE_DEPTH || !self.charge_work(Event::RecurrenceStep, 1) {
            return None;
        }

        match unwrap(value) {
            Expression::Identifier(reference) => {
                let binding = self.binding_of_identifier(file, reference)?;

                Some((ArgumentRelation::Unchanged, binding))
            }
            Expression::CallExpression(call) => {
                let truncating = matches!(
                    self.member_path_of(file, &call.callee).as_deref(),
                    Some("Math.floor") | Some("Math.trunc")
                );

                if !truncating || call.arguments.len() != 1 {
                    return None;
                }

                let inner = call.arguments[0].as_expression()?;
                let (relation, binding) = self.relation_of(file, inner, depth + 1)?;

                Some((truncated_relation_of(relation), binding))
            }
            Expression::BinaryExpression(binary) => {
                self.binary_relation_of(file, binary, depth + 1)
            }
            _ => None,
        }
    }

    fn binary_relation_of(
        &mut self,
        file: FileId,
        binary: &'a oxc_ast::ast::BinaryExpression<'a>,
        depth: usize,
    ) -> Option<(ArgumentRelation, Binding)> {
        let left = unwrap(&binary.left);

        match binary.operator {
            BinaryOperator::Subtraction => {
                let amount = self.numeric_value_of(file, &binary.right)?;
                let (relation, binding) = self.relation_of(file, left, depth)?;

                Some((decrement_relation_of(relation, amount)?, binding))
            }
            BinaryOperator::Addition => {
                let amount = self.numeric_value_of(file, &binary.right)?;
                let (relation, binding) = self.relation_of(file, left, depth)?;

                Some((decrement_relation_of(relation, -amount)?, binding))
            }
            BinaryOperator::Division => {
                let divisor = self.numeric_value_of(file, &binary.right)?;
                let (relation, binding) = self.relation_of(file, left, depth)?;

                Some((division_relation_of(relation, divisor, false)?, binding))
            }
            BinaryOperator::ShiftRight | BinaryOperator::ShiftRightZeroFill => {
                let places = self.numeric_value_of(file, &binary.right)?;
                let (relation, binding) = self.relation_of(file, left, depth)?;

                if !(1.0..=31.0).contains(&places) || places.fract() != 0.0 {
                    return None;
                }

                Some((
                    division_relation_of(relation, (2.0_f64).powi(places as i32), true)?,
                    binding,
                ))
            }
            BinaryOperator::BitwiseOR => {
                if self.numeric_value_of(file, &binary.right) != Some(0.0) {
                    return None;
                }

                let (relation, binding) = self.relation_of(file, left, depth)?;

                Some((truncated_relation_of(relation), binding))
            }
            _ => None,
        }
    }

    fn lower_bound_of(&mut self, file: FileId, node: NodeId, measure: Binding) -> Option<f64> {
        let ancestors: Vec<NodeId> = self
            .project
            .file(file)
            .semantic
            .nodes()
            .ancestor_ids(node)
            .collect();
        let mut inner = self.kind_of_node(file, node).span();
        let mut bound: Option<f64> = None;

        for ancestor in ancestors {
            if !self.charge_work(Event::RecurrenceStep, 1) {
                return None;
            }

            let kind = self.kind_of_node(file, ancestor);

            match kind {
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => break,
                AstKind::IfStatement(statement) => {
                    let taken = encloses(statement.consequent.span(), inner);
                    let found = self.condition_bound_of(file, &statement.test, measure, taken, 0);

                    bound = stronger_bound_of(bound, found);
                }
                AstKind::ConditionalExpression(expression) => {
                    let taken = encloses(expression.consequent.span(), inner);
                    let found = self.condition_bound_of(file, &expression.test, measure, taken, 0);

                    bound = stronger_bound_of(bound, found);
                }
                AstKind::LogicalExpression(expression) => {
                    if encloses(expression.right.span(), inner) {
                        let taken = expression.operator == LogicalOperator::And;
                        let found =
                            self.condition_bound_of(file, &expression.left, measure, taken, 0);

                        bound = stronger_bound_of(bound, found);
                    }
                }
                AstKind::BlockStatement(block) => {
                    let found = self.preceding_bound_of(file, &block.body, inner, measure);

                    bound = stronger_bound_of(bound, found);
                }
                AstKind::FunctionBody(body) => {
                    let found = self.preceding_bound_of(file, &body.statements, inner, measure);

                    bound = stronger_bound_of(bound, found);
                }
                _ => {}
            }

            inner = kind.span();
        }

        bound
    }

    fn preceding_bound_of(
        &mut self,
        file: FileId,
        statements: &'a [Statement<'a>],
        inner: Span,
        measure: Binding,
    ) -> Option<f64> {
        let mut bound = None;

        for statement in statements {
            if !self.charge_work(Event::RecurrenceStep, 1) {
                return None;
            }

            if statement.span().start >= inner.start {
                break;
            }

            let Statement::IfStatement(guard) = statement else {
                continue;
            };

            if guard.alternate.is_some() || !exits_unconditionally(&guard.consequent, 0) {
                continue;
            }

            let found = self.condition_bound_of(file, &guard.test, measure, false, 0);

            bound = stronger_bound_of(bound, found);
        }

        bound
    }

    fn condition_bound_of(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        measure: Binding,
        taken: bool,
        depth: usize,
    ) -> Option<f64> {
        if depth >= MAXIMUM_RECURRENCE_DEPTH || !self.charge_work(Event::RecurrenceStep, 1) {
            return None;
        }

        match unwrap(test) {
            Expression::LogicalExpression(logical)
                if logical.operator
                    == match taken {
                        true => LogicalOperator::And,
                        false => LogicalOperator::Or,
                    } =>
            {
                let left = self.condition_bound_of(file, &logical.left, measure, taken, depth + 1);
                let right =
                    self.condition_bound_of(file, &logical.right, measure, taken, depth + 1);

                stronger_bound_of(left, right)
            }
            Expression::BinaryExpression(binary) => {
                self.comparison_bound_of(file, binary, measure, taken)
            }
            _ => None,
        }
    }

    fn comparison_bound_of(
        &mut self,
        file: FileId,
        binary: &'a oxc_ast::ast::BinaryExpression<'a>,
        measure: Binding,
        taken: bool,
    ) -> Option<f64> {
        let left = self.measure_reference_of(file, &binary.left, measure);
        let right = self.measure_reference_of(file, &binary.right, measure);
        let (mirrored, endpoint) = match (left, right) {
            (true, false) => (false, self.numeric_value_of(file, &binary.right)?),
            (false, true) => (true, self.numeric_value_of(file, &binary.left)?),
            _ => return None,
        };
        let operator = comparison_operator_of(binary.operator, mirrored, !taken)?;

        match operator {
            BinaryOperator::GreaterThan => Some(endpoint),
            BinaryOperator::GreaterEqualThan => Some(endpoint - 1.0),
            _ => None,
        }
    }

    fn measure_reference_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        measure: Binding,
    ) -> bool {
        let Expression::Identifier(reference) = unwrap(value) else {
            return false;
        };

        self.binding_of_identifier(file, reference) == Some(measure)
    }

    fn member_path_of(&mut self, file: FileId, callee: &'a Expression<'a>) -> Option<String> {
        let Expression::StaticMemberExpression(member) = unwrap(callee) else {
            return None;
        };
        let Expression::Identifier(object) = unwrap(&member.object) else {
            return None;
        };

        if self.binding_of_identifier(file, object).is_some() {
            return None;
        }

        Some(format!("{}.{}", object.name, member.property.name))
    }
}

fn encloses(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn truncated_relation_of(relation: ArgumentRelation) -> ArgumentRelation {
    match relation {
        ArgumentRelation::Division { divisor, .. } => ArgumentRelation::Division {
            divisor,
            truncating: true,
        },
        other => other,
    }
}

fn decrement_relation_of(relation: ArgumentRelation, amount: f64) -> Option<ArgumentRelation> {
    if !matches!(relation, ArgumentRelation::Unchanged) {
        return None;
    }

    if !amount.is_finite()
        || amount.fract() != 0.0
        || amount < 1.0
        || amount > 9_007_199_254_740_992.0
    {
        return None;
    }

    Some(ArgumentRelation::Decrement {
        amount: amount as u64,
    })
}

fn division_relation_of(
    relation: ArgumentRelation,
    divisor: f64,
    truncating: bool,
) -> Option<ArgumentRelation> {
    if !matches!(relation, ArgumentRelation::Unchanged) {
        return None;
    }

    if !divisor.is_finite() || divisor.fract() != 0.0 || divisor < 2.0 || divisor > 4_294_967_296.0
    {
        return None;
    }

    Some(ArgumentRelation::Division {
        divisor: divisor as u64,
        truncating,
    })
}

fn stronger_bound_of(left: Option<f64>, right: Option<f64>) -> Option<f64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.max(right)),
        (found, None) | (None, found) => found,
    }
}

fn comparison_operator_of(
    operator: BinaryOperator,
    mirrored: bool,
    negated: bool,
) -> Option<BinaryOperator> {
    let (strict, greater) = match operator {
        BinaryOperator::LessThan => (true, false),
        BinaryOperator::LessEqualThan => (false, false),
        BinaryOperator::GreaterThan => (true, true),
        BinaryOperator::GreaterEqualThan => (false, true),
        _ => return None,
    };

    Some(match (greater ^ mirrored ^ negated, strict ^ negated) {
        (true, true) => BinaryOperator::GreaterThan,
        (true, false) => BinaryOperator::GreaterEqualThan,
        (false, true) => BinaryOperator::LessThan,
        (false, false) => BinaryOperator::LessEqualThan,
    })
}

fn exits_unconditionally(statement: &Statement<'_>, depth: usize) -> bool {
    if depth >= MAXIMUM_RECURRENCE_DEPTH {
        return false;
    }

    match statement {
        Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => true,
        Statement::BlockStatement(block) => {
            block.body.iter().all(|inner| {
                !matches!(
                    inner,
                    Statement::BreakStatement(_) | Statement::ContinueStatement(_)
                )
            }) && block
                .body
                .last()
                .is_some_and(|inner| exits_unconditionally(inner, depth + 1))
        }
        _ => false,
    }
}

#[cfg(test)]
#[path = "recurrences.test.rs"]
mod tests;

use std::collections::HashMap;

use oxc_ast::ast::{
    ArrowFunctionExpression, AssignmentTarget, DoWhileStatement, Expression, ForInStatement,
    ForOfStatement, ForStatement, ForStatementInit, ForStatementLeft, Function,
    IdentifierReference, SimpleAssignmentTarget, Statement, VariableDeclarationKind,
    WhileStatement,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{
    AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator, UpdateOperator,
};
use oxc_syntax::scope::ScopeFlags;

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::cost::{Cost, CostComparison};
use crate::declarations::{Binding, Declaration, FunctionId, FunctionNode, ParameterNode};
use crate::native::Role;
use crate::project::FileId;
use crate::syntax::{
    body_root_of, call_of, collapsed_text_of, compact_text_of, identifier_of,
    is_identifier_pattern, is_iteration_kind, loop_body_of, member_expression_of, member_name_of,
    unwrap, Root,
};
use crate::tables::MUTATORS;
use crate::values::ValueId;

#[derive(Clone, Debug)]
pub enum WriteKind {
    IncrementConstant,
    DecrementConstant,
    IncrementIdentifier(String),
    DecrementIdentifier(String),
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Up,
    Down,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strictness {
    Strict,
    Inclusive,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Potential {
    Constant(f64),
    Enveloped,
    Symbolic(Cost),
}

impl Potential {
    pub fn cost(&self) -> Cost {
        match self {
            Potential::Constant(_) => Cost::ONE,
            Potential::Enveloped => Cost::N,
            Potential::Symbolic(cost) => cost.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepMagnitude {
    Constant,
    Stable,
}

#[derive(Clone, Debug)]
pub struct Budget {
    pub direction: Direction,
    pub text: String,
    pub scope: Option<NodeId>,
    pub potential: Potential,
    pub guards: Vec<NodeId>,
}

pub struct BudgetContext {
    pub budgets: HashMap<Binding, Budget>,
    pub writes: HashMap<Binding, Vec<WriteKind>>,
    pub function: FunctionId,
}

#[derive(Clone, Debug)]
pub struct Spend {
    pub text: String,
    pub share: Option<Binding>,
    pub step: Option<NodeId>,
    pub scope: Option<NodeId>,
    pub magnitude: StepMagnitude,
    pub potential: Potential,
}

impl Spend {
    pub fn cancels(&self) -> bool {
        self.magnitude == StepMagnitude::Constant
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VisitBudget {
    pub cost: Cost,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Visits {
    Stable { written: bool },
    Budgeted(VisitBudget),
    Unresolved,
}

pub(crate) struct Addition<'a> {
    pub file: FileId,
    pub call: NodeId,
    pub guard: Option<(&'a Expression<'a>, String)>,
}

#[derive(Default)]
pub(crate) struct CollectionWrites<'a> {
    pub additions: Vec<Addition<'a>>,
    pub deletions: Vec<(FileId, NodeId)>,
}

impl CollectionWrites<'_> {
    pub(crate) fn sites(&self) -> Vec<(FileId, NodeId)> {
        self.additions
            .iter()
            .map(|addition| (addition.file, addition.call))
            .chain(self.deletions.iter().copied())
            .collect()
    }
}

pub fn charge_covers(charge: &Cost, required: &Cost) -> bool {
    required.compare_legacy(charge) == CostComparison::Within
}

pub fn tests_after_body(loop_kind: AstKind<'_>) -> bool {
    matches!(loop_kind, AstKind::DoWhileStatement(_))
}

pub(crate) struct Subtree<'a> {
    pub kinds: Vec<AstKind<'a>>,
    prune_functions: bool,
    prune_loops: bool,
}

impl<'a> Subtree<'a> {
    pub(crate) fn of(root: Root<'a>, prune_functions: bool, prune_loops: bool) -> Vec<AstKind<'a>> {
        let mut subtree = Subtree {
            kinds: Vec::new(),
            prune_functions,
            prune_loops,
        };

        match root {
            Root::Statement(statement) => subtree.visit_statement(statement),
            Root::Expression(expression) => subtree.visit_expression(expression),
            Root::Body(body) => subtree.visit_function_body(body),
        }

        subtree.kinds
    }
}

impl<'a> Visit<'a> for Subtree<'a> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        self.kinds.push(kind);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if !self.prune_functions {
            oxc_ast_visit::walk::walk_function(self, function, flags);
        }
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        if !self.prune_functions {
            oxc_ast_visit::walk::walk_arrow_function_expression(self, arrow);
        }
    }

    fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
        if !self.prune_loops {
            oxc_ast_visit::walk::walk_for_statement(self, statement);
        }
    }

    fn visit_for_in_statement(&mut self, statement: &ForInStatement<'a>) {
        if !self.prune_loops {
            oxc_ast_visit::walk::walk_for_in_statement(self, statement);
        }
    }

    fn visit_for_of_statement(&mut self, statement: &ForOfStatement<'a>) {
        if !self.prune_loops {
            oxc_ast_visit::walk::walk_for_of_statement(self, statement);
        }
    }

    fn visit_while_statement(&mut self, statement: &WhileStatement<'a>) {
        if !self.prune_loops {
            oxc_ast_visit::walk::walk_while_statement(self, statement);
        }
    }

    fn visit_do_while_statement(&mut self, statement: &DoWhileStatement<'a>) {
        if !self.prune_loops {
            oxc_ast_visit::walk::walk_do_while_statement(self, statement);
        }
    }
}

pub(crate) fn is_less(operator: BinaryOperator) -> bool {
    matches!(
        operator,
        BinaryOperator::LessThan | BinaryOperator::LessEqualThan
    )
}

pub(crate) type ComparisonPair<'a> = (
    &'a Expression<'a>,
    &'a Expression<'a>,
    Direction,
    Strictness,
);

pub(crate) fn comparison_pairs_of<'a>(
    conjunct: &'a Expression<'a>,
) -> Option<[ComparisonPair<'a>; 2]> {
    let Expression::BinaryExpression(binary) = conjunct else {
        return None;
    };
    let left = unwrap(&binary.left);
    let right = unwrap(&binary.right);
    let strictness = strictness_of(binary.operator);

    if is_less(binary.operator) {
        return Some([
            (left, right, Direction::Up, strictness),
            (right, left, Direction::Down, strictness),
        ]);
    }

    is_greater(binary.operator).then_some([
        (left, right, Direction::Down, strictness),
        (right, left, Direction::Up, strictness),
    ])
}

fn is_greater(operator: BinaryOperator) -> bool {
    matches!(
        operator,
        BinaryOperator::GreaterThan | BinaryOperator::GreaterEqualThan
    )
}

fn strictness_of(operator: BinaryOperator) -> Strictness {
    match operator {
        BinaryOperator::LessThan | BinaryOperator::GreaterThan => Strictness::Strict,
        _ => Strictness::Inclusive,
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn text_of(&self, file: FileId, span: Span) -> &'a str {
        span.source_text(self.project.file(file).text)
    }

    pub(crate) fn binding_of_identifier(
        &self,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<Binding> {
        self.declarations
            .binding_of_reference(self.project, file, reference)
    }

    pub(crate) fn enclosing_function_of(&self, file: FileId, node: NodeId) -> Option<NodeId> {
        let nodes = self.project.file(file).semantic.nodes();

        nodes.ancestors(node).find_map(|ancestor| {
            matches!(
                ancestor.kind(),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            )
            .then(|| ancestor.id())
        })
    }

    pub(crate) fn counted_subtree(
        &mut self,
        file: FileId,
        root: Root<'a>,
        event: Event,
    ) -> Vec<AstKind<'a>> {
        let node = match root {
            Root::Statement(node) => node.node_id(),
            Root::Expression(node) => node.node_id(),
            Root::Body(node) => node.node_id(),
        };
        let mut pending = vec![node];
        let mut kinds = Vec::new();

        while let Some(node) = pending.pop() {
            if !self.charge_work(event, 1) {
                break;
            }

            let kind = self.kind_of_node(file, node);

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                continue;
            }

            kinds.push(kind);

            let mut children = self.children_of(file, node);

            children.reverse();
            pending.extend(children);
        }

        kinds
    }

    pub fn collect_budgets(&mut self, file: FileId, function: FunctionNode<'a>) -> BudgetContext {
        let body = body_root_of(function);
        let writes = match body {
            Some(body) => self.writes_of(file, body),
            None => HashMap::new(),
        };
        let mut budgets: HashMap<Binding, Budget> = HashMap::new();
        let kinds = body
            .map(|body| self.counted_subtree(file, body, Event::BudgetPrepassNode))
            .unwrap_or_default();

        for kind in kinds {
            let condition = match kind {
                AstKind::WhileStatement(statement) => Some(&statement.test),
                AstKind::DoWhileStatement(statement) => Some(&statement.test),
                AstKind::ForStatement(statement) => statement.test.as_ref(),
                _ => None,
            };

            if let Some(condition) = condition {
                self.consider_condition(
                    file,
                    function,
                    kind.node_id(),
                    condition,
                    &writes,
                    &mut budgets,
                );
            }
        }

        BudgetContext {
            budgets,
            writes,
            function: FunctionId {
                file,
                node: function.node_id(),
            },
        }
    }

    fn consider_condition(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        node: NodeId,
        condition: &'a Expression<'a>,
        writes: &HashMap<Binding, Vec<WriteKind>>,
        budgets: &mut HashMap<Binding, Budget>,
    ) {
        for conjunct in conjuncts_of(condition) {
            let Some(pairs) = comparison_pairs_of(conjunct) else {
                continue;
            };

            for (counter, bound, direction, _) in pairs {
                let Some(counter) = identifier_of(counter) else {
                    continue;
                };
                let Some(binding) = self.binding_of_identifier(file, counter) else {
                    continue;
                };

                let Some(origin) = self.counter_origin_of(binding, function) else {
                    continue;
                };

                if monotone_direction_of(binding, writes) != Some(direction) {
                    continue;
                }

                if !self.is_invariant(file, bound, writes) {
                    continue;
                }

                if let Some(found) = budgets.get_mut(&binding) {
                    found.guards.push(node);

                    continue;
                }

                let potential = match self.numeric_value_of(file, bound) {
                    Some(endpoint) => Potential::Constant((endpoint - origin.initial).abs()),
                    None => {
                        let size = identifier_of(unwrap(bound))
                            .and_then(|reference| self.binding_of_identifier(file, reference))
                            .and_then(|binding| self.current_substitutions.get(&binding))
                            .and_then(|facts| facts.value.size.clone())
                            .or_else(|| match unwrap(bound) {
                                Expression::StaticMemberExpression(member)
                                    if member.property.name == "length" =>
                                {
                                    Some(self.collection_size_of(file, &member.object).length)
                                }
                                _ => None,
                            });

                        size.map_or(Potential::Enveloped, Potential::Symbolic)
                    }
                };

                budgets.insert(
                    binding,
                    Budget {
                        direction,
                        text: collapsed_text_of(self.text_of(file, conjunct.span())),
                        scope: origin.scope,
                        potential,
                        guards: vec![node],
                    },
                );
            }
        }
    }

    fn counter_origin_of(
        &mut self,
        binding: Binding,
        function: FunctionNode<'a>,
    ) -> Option<CounterOrigin> {
        let Declaration::Variable {
            file, declarator, ..
        } = self.declarations.of_binding(self.project, binding)?
        else {
            return None;
        };

        if !is_identifier_pattern(&declarator.id) {
            return None;
        }

        if self.enclosing_function_of(file, declarator.node_id()) != Some(function.node_id()) {
            return None;
        }

        let initial = self.numeric_value_of(file, declarator.init.as_ref()?)?;
        let nodes = self.project.file(file).semantic.nodes();
        let declaration_node = nodes.parent_id(declarator.node_id());
        let AstKind::VariableDeclaration(declaration) = nodes.kind(declaration_node) else {
            return None;
        };

        if matches!(declaration.kind, VariableDeclarationKind::Var) {
            return None;
        }

        if let AstKind::ForStatement(statement) = nodes.parent_kind(declaration_node) {
            if matches!(&statement.init, Some(ForStatementInit::VariableDeclaration(init)) if std::ptr::eq(&**init, declaration))
            {
                return Some(CounterOrigin {
                    scope: Some(statement.node_id()),
                    initial,
                });
            }
        }

        for ancestor in nodes.ancestors(declaration_node) {
            if ancestor.id() == function.node_id() {
                break;
            }

            if is_iteration_kind(&ancestor.kind()) {
                return Some(CounterOrigin {
                    scope: Some(ancestor.id()),
                    initial,
                });
            }
        }

        Some(CounterOrigin {
            scope: None,
            initial,
        })
    }

    fn is_invariant(
        &mut self,
        file: FileId,
        e: &'a Expression<'a>,
        writes: &HashMap<Binding, Vec<WriteKind>>,
    ) -> bool {
        self.referenced_bindings_of(file, e.node_id(), false)
            .iter()
            .all(|binding| writes.get(binding).is_none_or(|found| found.is_empty()))
    }

    fn referenced_bindings_of(
        &mut self,
        file: FileId,
        root: NodeId,
        writes_only: bool,
    ) -> Vec<Binding> {
        let mut bindings = Vec::new();
        let mut pending = vec![root];

        while let Some(node) = pending.pop() {
            if !self.charge_work(Event::BudgetPrepassNode, 1) {
                break;
            }

            let kind = self.kind_of_node(file, node);

            if let AstKind::IdentifierReference(reference) = kind {
                let is_write = reference.reference_id.get().is_some_and(|id| {
                    self.project
                        .file(file)
                        .semantic
                        .scoping()
                        .get_reference(id)
                        .is_write()
                });

                if !writes_only || is_write {
                    if let Some(binding) = self.binding_of_identifier(file, reference) {
                        bindings.push(binding);
                    }
                }
            }

            pending.extend(self.children_of(file, node));
        }

        bindings
    }

    fn writes_of(&mut self, file: FileId, body: Root<'a>) -> HashMap<Binding, Vec<WriteKind>> {
        let mut writes: HashMap<Binding, Vec<WriteKind>> = HashMap::new();

        for kind in self.counted_subtree(file, body, Event::BudgetPrepassNode) {
            match kind {
                AstKind::AssignmentExpression(assignment) => match assignment.operator {
                    AssignmentOperator::Addition | AssignmentOperator::Subtraction => {
                        let increment = assignment.operator == AssignmentOperator::Addition;
                        let right = unwrap(&assignment.right);
                        let signed = self
                            .numeric_value_of(file, right)
                            .map(|step| signed_direction_of(step, increment));
                        let write = if let Some(direction) = signed {
                            match direction {
                                Some(Direction::Up) => WriteKind::IncrementConstant,
                                Some(Direction::Down) => WriteKind::DecrementConstant,
                                None => WriteKind::Other,
                            }
                        } else if self.is_numeric_constant(file, right) {
                            if increment {
                                WriteKind::IncrementConstant
                            } else {
                                WriteKind::DecrementConstant
                            }
                        } else if let Some(identifier) = identifier_of(right) {
                            let name = identifier.name.to_string();

                            if increment {
                                WriteKind::IncrementIdentifier(name)
                            } else {
                                WriteKind::DecrementIdentifier(name)
                            }
                        } else {
                            WriteKind::Other
                        };

                        self.add_target_write(file, &assignment.left, write, &mut writes);
                    }
                    AssignmentOperator::Assign
                        if matches!(
                            assignment.left,
                            AssignmentTarget::ArrayAssignmentTarget(_)
                                | AssignmentTarget::ObjectAssignmentTarget(_)
                        ) =>
                    {
                        let bindings =
                            self.referenced_bindings_of(file, assignment.left.node_id(), true);

                        for binding in bindings {
                            writes.entry(binding).or_default().push(WriteKind::Other);
                        }
                    }
                    _ => {
                        self.add_target_write(file, &assignment.left, WriteKind::Other, &mut writes)
                    }
                },
                AstKind::UpdateExpression(update) => {
                    let write = match update.operator {
                        UpdateOperator::Increment => WriteKind::IncrementConstant,
                        UpdateOperator::Decrement => WriteKind::DecrementConstant,
                    };

                    if let Some(binding) = self.simple_target_binding_of(file, &update.argument) {
                        writes.entry(binding).or_default().push(write);
                    }
                }
                AstKind::CallExpression(call) => {
                    let callee = &call.callee;

                    if let Some(member) = callee.as_member_expression() {
                        if !matches!(
                            member,
                            oxc_ast::ast::MemberExpression::ComputedMemberExpression(_)
                        ) && member_name_of(member)
                            .is_some_and(|name| MUTATORS.contains(&name.as_str()))
                        {
                            if let Some(binding) =
                                self.expression_write_binding_of(file, member.object())
                            {
                                writes.entry(binding).or_default().push(WriteKind::Other);
                            }
                        }
                    }
                }
                AstKind::UnaryExpression(unary) if unary.operator == UnaryOperator::Delete => {
                    if let Some(binding) = self.expression_write_binding_of(file, &unary.argument) {
                        writes.entry(binding).or_default().push(WriteKind::Other);
                    }
                }
                AstKind::ForOfStatement(statement) => {
                    self.add_left_write(file, &statement.left, &mut writes)
                }
                AstKind::ForInStatement(statement) => {
                    self.add_left_write(file, &statement.left, &mut writes)
                }
                _ => {}
            }
        }

        writes
    }

    fn add_left_write(
        &mut self,
        file: FileId,
        left: &'a ForStatementLeft<'a>,
        writes: &mut HashMap<Binding, Vec<WriteKind>>,
    ) {
        let Some(target) = left.as_assignment_target() else {
            return;
        };

        if let Some(simple) = target.as_simple_assignment_target() {
            if let Some(binding) = self.simple_target_binding_of(file, simple) {
                writes.entry(binding).or_default().push(WriteKind::Other);
            }

            return;
        }

        for binding in self.referenced_bindings_of(file, target.node_id(), true) {
            writes.entry(binding).or_default().push(WriteKind::Other);
        }
    }

    fn add_target_write(
        &self,
        file: FileId,
        target: &'a AssignmentTarget<'a>,
        write: WriteKind,
        writes: &mut HashMap<Binding, Vec<WriteKind>>,
    ) {
        let binding = target
            .as_simple_assignment_target()
            .and_then(|simple| self.simple_target_binding_of(file, simple));

        if let Some(binding) = binding {
            writes.entry(binding).or_default().push(write);
        }
    }

    fn simple_target_binding_of(
        &self,
        file: FileId,
        target: &'a SimpleAssignmentTarget<'a>,
    ) -> Option<Binding> {
        match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                self.binding_of_identifier(file, reference)
            }
            SimpleAssignmentTarget::TSAsExpression(inner) => {
                self.expression_write_binding_of(file, &inner.expression)
            }
            SimpleAssignmentTarget::TSSatisfiesExpression(inner) => {
                self.expression_write_binding_of(file, &inner.expression)
            }
            SimpleAssignmentTarget::TSNonNullExpression(inner) => {
                self.expression_write_binding_of(file, &inner.expression)
            }
            SimpleAssignmentTarget::TSTypeAssertion(inner) => {
                self.expression_write_binding_of(file, &inner.expression)
            }
            SimpleAssignmentTarget::ComputedMemberExpression(member) => {
                self.accessed_binding_of(file, &member.object)
            }
            SimpleAssignmentTarget::StaticMemberExpression(member) => {
                self.declarations.binding_of_access(
                    self.project,
                    file,
                    unwrap(&member.object),
                    member.property.name.as_str(),
                )
            }
            _ => None,
        }
    }

    fn expression_write_binding_of(&self, file: FileId, e: &'a Expression<'a>) -> Option<Binding> {
        match unwrap(e) {
            Expression::ComputedMemberExpression(member) => {
                self.accessed_binding_of(file, &member.object)
            }
            other => self.accessed_binding_of(file, other),
        }
    }

    fn accessed_binding_of(&self, file: FileId, e: &'a Expression<'a>) -> Option<Binding> {
        match unwrap(e) {
            Expression::Identifier(reference) => self.binding_of_identifier(file, reference),
            Expression::StaticMemberExpression(member) => self.declarations.binding_of_access(
                self.project,
                file,
                unwrap(&member.object),
                member.property.name.as_str(),
            ),
            _ => None,
        }
    }

    pub fn is_share_sized(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        if self.share_bindings.is_empty() {
            return false;
        }

        let e = unwrap(e);

        if let Expression::Identifier(reference) = e {
            if let Some(binding) = self.binding_of_identifier(file, reference) {
                if self.share_bindings.contains(&binding) {
                    return true;
                }
            }

            return match self
                .declarations
                .of_reference(self.project, file, reference)
            {
                Some(Declaration::Variable {
                    file: target,
                    declarator,
                    constant: true,
                }) if is_identifier_pattern(&declarator.id) => match &declarator.init {
                    Some(initializer) => self.is_share_sized(target, initializer),
                    None => false,
                },
                _ => false,
            };
        }

        if let Expression::BinaryExpression(binary) = e {
            if binary.operator == BinaryOperator::Addition {
                return (self.is_share_sized(file, &binary.left)
                    && self.is_numeric_constant(file, &binary.right))
                    || (self.is_numeric_constant(file, &binary.left)
                        && self.is_share_sized(file, &binary.right));
            }
        }

        match call_of(e) {
            Some(call) => self.is_share_sized_call(file, call),
            None => false,
        }
    }

    pub(crate) fn is_share_sized_call(
        &mut self,
        file: FileId,
        call: &'a oxc_ast::ast::CallExpression<'a>,
    ) -> bool {
        if self.share_bindings.is_empty() {
            return false;
        }

        let Some(member) = member_expression_of(&call.callee) else {
            return false;
        };

        if matches!(
            member,
            oxc_ast::ast::MemberExpression::ComputedMemberExpression(_)
        ) {
            return false;
        }

        let named =
            member_name_of(member).is_some_and(|name| name == "subarray" || name == "slice");

        if !named || call.arguments.len() != 2 {
            return false;
        }

        let (Some(first), Some(second)) = (
            call.arguments[0].as_expression(),
            call.arguments[1].as_expression(),
        ) else {
            return false;
        };
        let first = unwrap(first);
        let second = unwrap(second);

        if is_zero(first) && self.is_share_sized(file, second) {
            return true;
        }

        if let Expression::BinaryExpression(binary) = second {
            if binary.operator == BinaryOperator::Addition {
                let first_text = compact_text_of(self.text_of(file, first.span()));

                return (compact_text_of(self.text_of(file, binary.left.span())) == first_text
                    && self.is_share_sized(file, &binary.right))
                    || (compact_text_of(self.text_of(file, binary.right.span())) == first_text
                        && self.is_share_sized(file, &binary.left));
            }
        }

        false
    }

    pub fn spent_budget(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Option<Spend> {
        if self
            .budget_context
            .as_ref()
            .is_none_or(|context| context.budgets.is_empty())
        {
            return None;
        }

        let node = loop_kind.node_id();

        if let AstKind::ForStatement(statement) = loop_kind {
            if let Some(update) = &statement.update {
                if let Some(spend) = self.spend_of(file, node, update) {
                    return Some(spend);
                }
            }
        }

        let body = loop_body_of(loop_kind)?;

        if has_continue_at_level(body) {
            return None;
        }

        let statements: Vec<&'a Statement<'a>> = match body {
            Statement::BlockStatement(block) => block.body.iter().collect(),
            other => vec![other],
        };

        for statement in statements {
            if let Statement::ExpressionStatement(expression) = statement {
                if let Some(spend) = self.spend_of(file, node, &expression.expression) {
                    return Some(spend);
                }
            }
        }

        None
    }

    fn spend_of(&mut self, file: FileId, node: NodeId, e: &'a Expression<'a>) -> Option<Spend> {
        let advance = self.advance_of(file, e)?;
        let context = self.budget_context.as_ref()?;
        let budget = context.budgets.get(&advance.binding)?;

        if budget.direction != advance.direction {
            return None;
        }

        if !budget.guards.contains(&node) {
            return None;
        }

        let Some((identifier, identifier_binding)) = advance.identifier else {
            let proven = context
                .writes
                .get(&advance.binding)
                .is_some_and(|found| found.iter().all(is_proven_constant));

            return Some(Spend {
                text: budget.text.clone(),
                share: None,
                step: None,
                scope: budget.scope,
                magnitude: match proven {
                    true => StepMagnitude::Constant,
                    false => StepMagnitude::Stable,
                },
                potential: budget.potential.clone(),
            });
        };
        let text = format!("{}, by {}", budget.text, identifier);
        let scope = budget.scope;
        let potential = budget.potential.clone();
        let stable = identifier_binding.is_some_and(|binding| {
            match self.declarations.of_binding(self.project, binding) {
                Some(Declaration::Variable {
                    declarator,
                    constant: true,
                    ..
                }) => is_identifier_pattern(&declarator.id),
                Some(Declaration::Parameter { parameter, .. }) => {
                    let identifier = match parameter {
                        ParameterNode::Formal(formal) => is_identifier_pattern(&formal.pattern),
                        ParameterNode::Rest(rest) => is_identifier_pattern(&rest.rest.argument),
                    };

                    identifier
                        && context
                            .writes
                            .get(&binding)
                            .is_none_or(|found| found.is_empty())
                }
                _ => false,
            }
        });

        if !stable {
            return None;
        }

        Some(Spend {
            text,
            share: identifier_binding,
            step: Some(unwrap(e).node_id()),
            scope,
            magnitude: StepMagnitude::Stable,
            potential,
        })
    }

    fn advance_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Advance> {
        let e = unwrap(e);

        match e {
            Expression::UpdateExpression(update) => {
                let SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) =
                    &update.argument
                else {
                    return None;
                };
                let binding = self.binding_of_identifier(file, reference)?;

                Some(Advance {
                    binding,
                    direction: match update.operator {
                        UpdateOperator::Increment => Direction::Up,
                        UpdateOperator::Decrement => Direction::Down,
                    },
                    identifier: None,
                })
            }
            Expression::AssignmentExpression(assignment) => {
                let added = match assignment.operator {
                    AssignmentOperator::Addition => true,
                    AssignmentOperator::Subtraction => false,
                    _ => return None,
                };
                let AssignmentTarget::AssignmentTargetIdentifier(reference) = &assignment.left
                else {
                    return None;
                };
                let binding = self.binding_of_identifier(file, reference)?;
                let right = unwrap(&assignment.right);

                if let Some(step) = self.numeric_value_of(file, right) {
                    return signed_direction_of(step, added).map(|direction| Advance {
                        binding,
                        direction,
                        identifier: None,
                    });
                }

                let direction = match added {
                    true => Direction::Up,
                    false => Direction::Down,
                };
                let identifier = identifier_of(right)?;

                Some(Advance {
                    binding,
                    direction,
                    identifier: Some((
                        identifier.name.to_string(),
                        self.binding_of_identifier(file, identifier),
                    )),
                })
            }
            _ => None,
        }
    }

    pub(crate) fn collection_writes_in(
        &mut self,
        file: FileId,
        body: Root<'a>,
        collection: ValueId,
        writes: &mut CollectionWrites<'a>,
    ) {
        let root = match body {
            Root::Statement(node) => node.node_id(),
            Root::Expression(node) => node.node_id(),
            Root::Body(node) => node.node_id(),
        };

        for kind in self.counted_subtree(file, body, Event::BudgetPrepassNode) {
            let AstKind::CallExpression(call) = kind else {
                continue;
            };
            let Some(member) = member_expression_of(unwrap(&call.callee)) else {
                continue;
            };

            let receiver = self.storage_value_of(file, member.object());

            if !self.values.may_alias(receiver, collection) {
                continue;
            }

            let Some((_, model)) = self.modelled_call_of(file, call) else {
                continue;
            };

            match model.receiver {
                Role::Grown if receiver == collection => {
                    let guard = self.size_guard_of(file, call.node_id(), root, collection);

                    writes.additions.push(Addition {
                        file,
                        call: call.node_id(),
                        guard,
                    });
                }
                Role::Shrunk => writes.deletions.push((file, call.node_id())),
                _ => {}
            }
        }
    }

    fn size_guard_of(
        &mut self,
        file: FileId,
        node: NodeId,
        root: NodeId,
        collection: ValueId,
    ) -> Option<(&'a Expression<'a>, String)> {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let mut child = node;

        while child != root {
            if !self.charge_work(Event::BudgetPrepassNode, 1) {
                return None;
            }

            let parent = nodes.parent_id(child);

            if parent == child {
                return None;
            }

            match nodes.kind(parent) {
                AstKind::IfStatement(statement) if statement.consequent.node_id() == child => {
                    if let Some(guard) = self.size_guard_in(file, &statement.test, collection) {
                        return Some(guard);
                    }
                }
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => return None,
                kind if is_iteration_kind(&kind) => return None,
                _ => {}
            }

            child = parent;
        }

        None
    }

    fn size_guard_in(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        collection: ValueId,
    ) -> Option<(&'a Expression<'a>, String)> {
        for conjunct in conjuncts_of(test) {
            let Some(pairs) = comparison_pairs_of(conjunct) else {
                continue;
            };

            for (measured, endpoint, direction, _) in pairs {
                let Expression::StaticMemberExpression(member) = measured else {
                    continue;
                };

                if direction != Direction::Up
                    || member.property.name != "size"
                    || self.storage_value_of(file, &member.object) != collection
                    || self.intrinsic_replaced_of(file, measured)
                {
                    continue;
                }

                return Some((
                    endpoint,
                    collapsed_text_of(self.text_of(file, conjunct.span())),
                ));
            }
        }

        None
    }

    pub(crate) fn endpoint_cost_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Cost> {
        if !self.charge_work(Event::BudgetPrepassNode, 1) {
            return None;
        }

        match unwrap(e) {
            Expression::BinaryExpression(binary)
                if matches!(
                    binary.operator,
                    BinaryOperator::Multiplication | BinaryOperator::Addition
                ) =>
            {
                let left = self.endpoint_cost_of(file, &binary.left)?;
                let right = self.endpoint_cost_of(file, &binary.right)?;
                let combined = match binary.operator {
                    BinaryOperator::Multiplication => Cost::product(vec![left, right]),
                    _ => Cost::sum(vec![left, right]),
                };

                combined.ok()
            }
            other => self.count_of(file, other),
        }
    }
}

struct CounterOrigin {
    scope: Option<NodeId>,
    initial: f64,
}

struct Advance {
    binding: Binding,
    direction: Direction,
    identifier: Option<(String, Option<Binding>)>,
}

fn has_continue_at_level(body: &Statement<'_>) -> bool {
    Subtree::of_statement(body)
        .iter()
        .any(|kind| matches!(kind, AstKind::ContinueStatement(_)))
}

impl<'a> Subtree<'a> {
    fn of_statement(statement: &Statement<'a>) -> Vec<AstKind<'a>> {
        let mut subtree = Subtree {
            kinds: Vec::new(),
            prune_functions: true,
            prune_loops: true,
        };

        subtree.visit_statement(statement);

        subtree.kinds
    }
}

pub(crate) fn conjuncts_of<'a>(e: &'a Expression<'a>) -> Vec<&'a Expression<'a>> {
    let e = unwrap(e);

    match e {
        Expression::LogicalExpression(logical) if logical.operator == LogicalOperator::And => {
            let mut found = conjuncts_of(&logical.left);

            found.extend(conjuncts_of(&logical.right));

            found
        }
        _ => vec![e],
    }
}

fn is_proven_constant(write: &WriteKind) -> bool {
    matches!(
        write,
        WriteKind::IncrementConstant | WriteKind::DecrementConstant
    )
}

fn signed_direction_of(step: f64, added: bool) -> Option<Direction> {
    let signed = match added {
        true => step,
        false => -step,
    };

    if signed > 0.0 {
        return Some(Direction::Up);
    }

    (signed < 0.0).then_some(Direction::Down)
}

fn is_zero(e: &Expression<'_>) -> bool {
    matches!(e, Expression::NumericLiteral(literal) if literal.value == 0.0)
}

pub(crate) fn monotone_direction_of(
    binding: Binding,
    writes: &HashMap<Binding, Vec<WriteKind>>,
) -> Option<Direction> {
    let found = writes.get(&binding)?;

    if found.is_empty() {
        return None;
    }

    if found.iter().all(|write| {
        matches!(
            write,
            WriteKind::IncrementConstant | WriteKind::IncrementIdentifier(_)
        )
    }) {
        return Some(Direction::Up);
    }

    if found.iter().all(|write| {
        matches!(
            write,
            WriteKind::DecrementConstant | WriteKind::DecrementIdentifier(_)
        )
    }) {
        return Some(Direction::Down);
    }

    None
}

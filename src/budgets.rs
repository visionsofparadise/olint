use std::collections::HashMap;

use oxc_ast::ast::{
    ArrowFunctionExpression, AssignmentTarget, BindingIdentifier, DoWhileStatement, Expression,
    ForInStatement, ForOfStatement, ForStatement, ForStatementInit, Function, IdentifierReference,
    SimpleAssignmentTarget, Statement, VariableDeclarationKind, WhileStatement,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{
    AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator, UpdateOperator,
};
use oxc_syntax::scope::ScopeFlags;

use crate::analysis::Analysis;
use crate::declarations::{Binding, Declaration, FunctionId, FunctionNode, ParameterNode};
use crate::project::FileId;
use crate::syntax::{
    body_root_of, call_of, collapsed_text_of, compact_text_of, identifier_of,
    is_identifier_pattern, is_iteration_kind, loop_body_of, member_expression_of, member_name_of,
    unwrap, Root,
};
use crate::tables::MUTATORS;

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

#[derive(Clone, Debug)]
pub struct Budget {
    pub direction: Direction,
    pub text: String,
    pub scope: Option<NodeId>,
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
    pub scope: Option<NodeId>,
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

pub(crate) struct Sides<'a> {
    pub left: Option<&'a Expression<'a>>,
    pub right: &'a Expression<'a>,
}

pub(crate) fn sides_of<'a>(e: &'a Expression<'a>) -> Option<Sides<'a>> {
    match e {
        Expression::BinaryExpression(binary) => Some(Sides {
            left: Some(&binary.left),
            right: &binary.right,
        }),
        Expression::LogicalExpression(logical) => Some(Sides {
            left: Some(&logical.left),
            right: &logical.right,
        }),
        Expression::AssignmentExpression(assignment) => Some(Sides {
            left: None,
            right: &assignment.right,
        }),
        Expression::SequenceExpression(sequence) => {
            let right = sequence.expressions.last()?;
            let left = match sequence.expressions.len() {
                2 => sequence.expressions.first(),
                _ => None,
            };

            Some(Sides { left, right })
        }
        _ => None,
    }
}

pub(crate) fn is_less(operator: BinaryOperator) -> bool {
    matches!(
        operator,
        BinaryOperator::LessThan | BinaryOperator::LessEqualThan
    )
}

fn is_greater(operator: BinaryOperator) -> bool {
    matches!(
        operator,
        BinaryOperator::GreaterThan | BinaryOperator::GreaterEqualThan
    )
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

    pub fn collect_budgets(&mut self, file: FileId, function: FunctionNode<'a>) -> BudgetContext {
        let body = body_root_of(function);
        let writes = match body {
            Some(body) => self.writes_of(file, body),
            None => HashMap::new(),
        };
        let mut budgets: HashMap<Binding, Budget> = HashMap::new();
        let kinds = body
            .map(|body| Subtree::of(body, true, false))
            .unwrap_or_default();

        for kind in kinds {
            let condition = match kind {
                AstKind::WhileStatement(statement) => Some(&statement.test),
                AstKind::DoWhileStatement(statement) => Some(&statement.test),
                AstKind::ForStatement(statement) => statement.test.as_ref(),
                _ => None,
            };

            if let Some(condition) = condition {
                self.consider_condition(file, function, condition, &writes, &mut budgets);
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
        condition: &'a Expression<'a>,
        writes: &HashMap<Binding, Vec<WriteKind>>,
        budgets: &mut HashMap<Binding, Budget>,
    ) {
        for conjunct in conjuncts_of(condition) {
            let Expression::BinaryExpression(binary) = conjunct else {
                continue;
            };
            let left = unwrap(&binary.left);
            let right = unwrap(&binary.right);
            let pairs = if is_less(binary.operator) {
                [(left, right, Direction::Up), (right, left, Direction::Down)]
            } else if is_greater(binary.operator) {
                [(left, right, Direction::Down), (right, left, Direction::Up)]
            } else {
                continue;
            };

            for (counter, bound, direction) in pairs {
                let Some(counter) = identifier_of(counter) else {
                    continue;
                };
                let Some(binding) = self.binding_of_identifier(file, counter) else {
                    continue;
                };

                if budgets.contains_key(&binding) {
                    continue;
                }

                let Some(scope) = self.budget_scope_of(binding, function) else {
                    continue;
                };

                if monotone_direction_of(binding, writes) != Some(direction) {
                    continue;
                }

                if !self.is_invariant(file, bound, writes) {
                    continue;
                }

                budgets.insert(
                    binding,
                    Budget {
                        direction,
                        text: collapsed_text_of(self.text_of(file, conjunct.span())),
                        scope,
                    },
                );
            }
        }
    }

    fn budget_scope_of(
        &self,
        binding: Binding,
        function: FunctionNode<'a>,
    ) -> Option<Option<NodeId>> {
        match self.declarations.of_binding(self.project, binding)? {
            Declaration::Parameter {
                parameter,
                function: owner,
                ..
            } => {
                let identifier = match parameter {
                    ParameterNode::Formal(formal) => is_identifier_pattern(&formal.pattern),
                    ParameterNode::Rest(rest) => is_identifier_pattern(&rest.rest.argument),
                };

                (identifier && owner == function).then_some(None)
            }
            Declaration::Variable {
                file, declarator, ..
            } => {
                if !is_identifier_pattern(&declarator.id) {
                    return None;
                }

                if self.enclosing_function_of(file, declarator.node_id())
                    != Some(function.node_id())
                {
                    return None;
                }

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
                        return Some(Some(statement.node_id()));
                    }
                }

                for ancestor in nodes.ancestors(declaration_node) {
                    if ancestor.id() == function.node_id() {
                        break;
                    }

                    if is_iteration_kind(&ancestor.kind()) {
                        return Some(Some(ancestor.id()));
                    }
                }

                Some(None)
            }
            _ => None,
        }
    }

    fn is_invariant(
        &mut self,
        file: FileId,
        e: &'a Expression<'a>,
        writes: &HashMap<Binding, Vec<WriteKind>>,
    ) -> bool {
        self.reads_of(file, e.node_id())
            .iter()
            .all(|binding| writes.get(binding).is_none_or(|found| found.is_empty()))
    }

    pub(crate) fn reads_of(&mut self, file: FileId, root: NodeId) -> Vec<Binding> {
        let mut reads = Vec::new();
        let mut node = root;

        loop {
            let kind = self.kind_of_node(file, node);
            let binding = match kind {
                AstKind::IdentifierReference(reference) => {
                    let shorthand = matches!(
                        self.project.file(file).semantic.nodes().parent_kind(node),
                        AstKind::AssignmentTargetPropertyIdentifier(_)
                    );

                    if shorthand {
                        None
                    } else {
                        self.binding_of_identifier(file, reference)
                    }
                }
                AstKind::BindingIdentifier(identifier) => binding_identifier_of(file, identifier),
                _ => None,
            };

            if let Some(binding) = binding {
                reads.push(binding);
            }

            let stops = match kind {
                AstKind::ArrowFunctionExpression(arrow) => arrow.r#async,
                AstKind::Function(function) => function.r#async || function.generator,
                AstKind::YieldExpression(expression) => expression.delegate,
                AstKind::FormalParameterRest(_) | AstKind::BindingRestElement(_) => true,
                AstKind::ArrayAssignmentTarget(target) => {
                    matches!(target.elements.first(), Some(None))
                }
                _ => false,
            };

            if stops {
                return reads;
            }

            match self.children_of(file, node).first() {
                Some(child) => node = *child,
                None => return reads,
            }
        }
    }

    fn writes_of(&mut self, file: FileId, body: Root<'a>) -> HashMap<Binding, Vec<WriteKind>> {
        let mut writes: HashMap<Binding, Vec<WriteKind>> = HashMap::new();

        for kind in Subtree::of(body, true, false) {
            match kind {
                AstKind::AssignmentExpression(assignment) => match assignment.operator {
                    AssignmentOperator::Addition | AssignmentOperator::Subtraction => {
                        let increment = assignment.operator == AssignmentOperator::Addition;
                        let right = unwrap(&assignment.right);
                        let write = if self.is_numeric_constant(file, right) {
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
                        let bindings = self.reads_of(file, assignment.left.node_id());

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
                _ => {}
            }
        }

        writes
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

        if let AstKind::ForStatement(statement) = loop_kind {
            if let Some(update) = &statement.update {
                if let Some(spend) = self.spend_of(file, update) {
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
                if let Some(spend) = self.spend_of(file, &expression.expression) {
                    return Some(spend);
                }
            }
        }

        None
    }

    fn spend_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Spend> {
        let advance = self.advance_of(file, e)?;
        let context = self.budget_context.as_ref()?;
        let budget = context.budgets.get(&advance.binding)?;

        if budget.direction != advance.direction {
            return None;
        }

        let Some((identifier, identifier_binding)) = advance.identifier else {
            return Some(Spend {
                text: budget.text.clone(),
                share: None,
                scope: budget.scope,
            });
        };
        let text = format!("{}, by {}", budget.text, identifier);
        let scope = budget.scope;
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

        Some(Spend {
            text,
            share: if stable { identifier_binding } else { None },
            scope,
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
                let direction = match assignment.operator {
                    AssignmentOperator::Addition => Direction::Up,
                    AssignmentOperator::Subtraction => Direction::Down,
                    _ => return None,
                };
                let AssignmentTarget::AssignmentTargetIdentifier(reference) = &assignment.left
                else {
                    return None;
                };
                let binding = self.binding_of_identifier(file, reference)?;
                let right = unwrap(&assignment.right);

                if self.is_numeric_constant(file, right) {
                    return Some(Advance {
                        binding,
                        direction,
                        identifier: None,
                    });
                }

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
}

struct Advance {
    binding: Binding,
    direction: Direction,
    identifier: Option<(String, Option<Binding>)>,
}

pub(crate) fn binding_identifier_of(
    file: FileId,
    identifier: &BindingIdentifier<'_>,
) -> Option<Binding> {
    identifier
        .symbol_id
        .get()
        .map(|symbol| Binding::Symbol { file, symbol })
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

fn conjuncts_of<'a>(e: &'a Expression<'a>) -> Vec<&'a Expression<'a>> {
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

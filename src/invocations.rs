use oxc_ast::ast::{
    ArrayExpressionElement, AssignmentTarget, AssignmentTargetMaybeDefault,
    AssignmentTargetProperty, BindingPattern, Class, Expression, ForOfStatement, FormalParameter,
    MethodDefinitionKind, SimpleAssignmentTarget, SpreadElement, TaggedTemplateExpression,
    YieldExpression,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, UnaryOperator};

use crate::analysis::Analysis;
use crate::cost::{Cost, Part, Preference, Reading};
use crate::declarations::{FunctionNode, TargetSet};
use crate::declared_types::{is_primitive_result, Kind};
use crate::project::{FileId, Project};
use crate::receivers::Placement;
use crate::syntax::{member_expression_of, unwrap};
use crate::unknowns::UnknownReason;
use crate::values::{outermost_of, protocol_key_of, Iteration, MemberKey, ValueId};

use std::rc::Rc;

const COERCION_KEYS: [&str; 3] = ["@@toPrimitive", "valueOf", "toString"];
const MAXIMUM_RETURN_DEPTH: usize = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Read,
    Write,
    Update,
}

#[derive(Clone, Default)]
struct Sources<'a> {
    values: Vec<(FileId, &'a Expression<'a>)>,
    open: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct ImplicitSite {
    file: FileId,
    span: Span,
    targets: TargetSet,
    operation: &'static str,
    receivers: Vec<ValueId>,
    visits: Option<bool>,
}

pub(crate) struct IterationParts {
    pub(crate) acquire: Part,
    pub(crate) next: Part,
    pub(crate) close: Part,
    pub(crate) unresolved: bool,
}

pub(crate) fn construction_context_of<'a>(
    project: &Project<'a>,
    file: FileId,
    node: NodeId,
) -> Option<(&'a Class<'a>, Placement)> {
    let nodes = project.file(file).semantic.nodes();
    let span = nodes.kind(node).span();
    let class_of = |element: NodeId| {
        nodes
            .ancestors(element)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Class(class) => Some(class),
                _ => None,
            })
    };
    let field_of = |element: NodeId, value: Option<&Expression<'_>>, is_static: bool| {
        value
            .filter(|value| value.span().contains_inclusive(span))
            .and_then(|_| class_of(element))
            .map(|class| (class, placement_of(is_static)))
    };

    for ancestor in nodes.ancestors(node) {
        match ancestor.kind() {
            AstKind::ArrowFunctionExpression(_) => return None,
            AstKind::Function(_) => {
                return match nodes.parent_kind(ancestor.id()) {
                    AstKind::MethodDefinition(method)
                        if method.kind == MethodDefinitionKind::Constructor =>
                    {
                        class_of(ancestor.id()).map(|class| (class, Placement::Instance))
                    }
                    _ => None,
                };
            }
            AstKind::PropertyDefinition(property) => {
                return field_of(ancestor.id(), property.value.as_ref(), property.r#static);
            }
            AstKind::AccessorProperty(property) => {
                return field_of(ancestor.id(), property.value.as_ref(), property.r#static);
            }
            AstKind::StaticBlock(_) => {
                return class_of(ancestor.id()).map(|class| (class, Placement::Static));
            }
            AstKind::Class(_) | AstKind::MethodDefinition(_) => return None,
            _ => {}
        }
    }

    None
}

fn placement_of(is_static: bool) -> Placement {
    match is_static {
        true => Placement::Static,
        false => Placement::Instance,
    }
}

fn member_role_of(nodes: &AstNodes<'_>, node: NodeId) -> Option<Role> {
    let current = outermost_of(nodes, node);
    let span = nodes.kind(current).span();

    match nodes.parent_kind(current) {
        AstKind::CallExpression(call) if call.callee.span() == span => None,
        AstKind::NewExpression(new) if new.callee.span() == span => None,
        AstKind::TaggedTemplateExpression(tagged) if tagged.tag.span() == span => None,
        AstKind::UnaryExpression(unary) if unary.operator == UnaryOperator::Delete => None,
        AstKind::AssignmentExpression(assignment) if assignment.left.span() == span => {
            match assignment.operator {
                AssignmentOperator::Assign => Some(Role::Write),
                _ => Some(Role::Update),
            }
        }
        AstKind::UpdateExpression(_) => Some(Role::Update),
        AstKind::AssignmentTargetWithDefault(target) if target.binding.span() == span => {
            Some(Role::Write)
        }
        AstKind::AssignmentTargetPropertyProperty(property) if property.binding.span() == span => {
            Some(Role::Write)
        }
        AstKind::ArrayAssignmentTarget(_) | AstKind::AssignmentTargetRest(_) => Some(Role::Write),
        AstKind::ForInStatement(statement) if statement.left.span() == span => Some(Role::Write),
        AstKind::ForOfStatement(statement) if statement.left.span() == span => Some(Role::Write),
        _ => Some(Role::Read),
    }
}

fn is_coercing_binary(operator: BinaryOperator) -> bool {
    !matches!(
        operator,
        BinaryOperator::StrictEquality
            | BinaryOperator::StrictInequality
            | BinaryOperator::Instanceof
            | BinaryOperator::In
    )
}

fn coercion_keys() -> Vec<MemberKey> {
    COERCION_KEYS
        .iter()
        .map(|name| protocol_key_of(name))
        .collect()
}

fn iteration_keys() -> Vec<MemberKey> {
    ["@@iterator", "@@asyncIterator", "next", "return"]
        .iter()
        .map(|name| protocol_key_of(name))
        .collect()
}

fn element_sources_of<'a>(
    file: FileId,
    source: &'a Expression<'a>,
    count: usize,
) -> Vec<Sources<'a>> {
    let Expression::ArrayExpression(array) = unwrap(source) else {
        return vec![
            Sources {
                values: Vec::new(),
                open: true,
            };
            count
        ];
    };
    let spread = array
        .elements
        .iter()
        .any(|element| matches!(element, ArrayExpressionElement::SpreadElement(_)));

    (0..count)
        .map(|index| match array.elements.get(index) {
            _ if spread => Sources {
                values: Vec::new(),
                open: true,
            },
            Some(element) => Sources {
                values: element
                    .as_expression()
                    .map(|expression| (file, expression))
                    .into_iter()
                    .collect(),
                open: false,
            },
            None => Sources::default(),
        })
        .collect()
}

fn joined_sources_of<'a>(all: Vec<Vec<Sources<'a>>>, count: usize) -> Vec<Sources<'a>> {
    let mut joined = vec![Sources::default(); count];

    for sources in all {
        for (index, found) in sources.into_iter().enumerate() {
            joined[index].values.extend(found.values);

            joined[index].open |= found.open;
        }
    }

    joined
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn implicit_reading_of(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        let mut reading = Reading::empty();

        for part in self.implicit_parts_of(file, kind) {
            reading = reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
        }

        reading
    }

    pub(crate) fn record_implicit_effects(&mut self, file: FileId, kind: AstKind<'a>) {
        self.implicit_parts_of(file, kind);

        match kind {
            AstKind::TaggedTemplateExpression(tagged) => {
                self.tag_part_of(file, tagged);
            }
            AstKind::ForOfStatement(statement) => {
                self.iteration_parts_of(file, statement);
            }
            AstKind::SpreadElement(spread) => {
                self.spread_iteration_part_of(file, spread);
            }
            _ => {}
        }
    }

    pub(crate) fn record_iteration_effects(
        &mut self,
        file: FileId,
        statement: &'a ForOfStatement<'a>,
    ) {
        let iteration = self.iteration_of(file, &statement.right, statement.r#await);
        let span = statement.right.span();

        for targets in [iteration.acquire, iteration.next, iteration.close] {
            for known in targets.known {
                self.call_implicit(known, file, span);
            }
        }
    }

    pub(crate) fn has_implicit_calls(&mut self, file: FileId, kind: AstKind<'a>) -> bool {
        let mut targets = match kind {
            AstKind::StaticMemberExpression(_)
            | AstKind::ComputedMemberExpression(_)
            | AstKind::PrivateFieldExpression(_) => {
                match member_role_of(self.project.file(file).semantic.nodes(), kind.node_id()) {
                    Some(Role::Read | Role::Update) => {
                        vec![self.accessor_targets_of(file, kind, false)]
                    }
                    _ => Vec::new(),
                }
            }
            _ => Vec::new(),
        };

        for operand in self.coerced_operands_of(file, kind) {
            targets.push(self.coercion_targets_of(file, operand));
        }

        targets
            .iter()
            .any(|targets| targets.open || !targets.known.is_empty())
    }

    pub(crate) fn tag_part_of(
        &mut self,
        file: FileId,
        tagged: &'a TaggedTemplateExpression<'a>,
    ) -> Part {
        let targets = self
            .resolved_expression_callee_of(file, &tagged.tag, tagged.node_id())
            .targets;
        let mut receivers: Vec<&'a Expression<'a>> = tagged.quasi.expressions.iter().collect();

        if let Some(member) = member_expression_of(unwrap(&tagged.tag)) {
            receivers.push(member.object());
        }

        self.implicit_part_of((file, tagged.span), &targets, "tag", &receivers)
    }

    pub(crate) fn iteration_parts_of(
        &mut self,
        file: FileId,
        statement: &'a ForOfStatement<'a>,
    ) -> IterationParts {
        let iteration = self.iteration_of(file, &statement.right, statement.r#await);
        let closes = (iteration.close.open || !iteration.close.known.is_empty())
            && self.closes_early(file, statement.node_id());
        let (acquire, next, close) =
            self.protocol_parts_of(file, &statement.right, &iteration, closes);

        IterationParts {
            acquire,
            next,
            close,
            unresolved: iteration.acquire.open || iteration.next.open,
        }
    }

    pub(crate) fn spread_iteration_part_of(
        &mut self,
        file: FileId,
        spread: &'a SpreadElement<'a>,
    ) -> Option<Part> {
        if matches!(
            self.project
                .file(file)
                .semantic
                .nodes()
                .parent_kind(spread.node_id()),
            AstKind::ObjectExpression(_)
        ) {
            return None;
        }

        self.delegated_part_of(file, spread.span, &spread.argument, false)
    }

    fn delegated_part_of(
        &mut self,
        file: FileId,
        span: Span,
        iterable: &'a Expression<'a>,
        asynchronous: bool,
    ) -> Option<Part> {
        let iteration = self.iteration_of(file, iterable, asynchronous);

        if is_inert(&iteration) {
            return None;
        }

        let (acquire, next, _) = self.protocol_parts_of(file, iterable, &iteration, false);
        let visits = self.visits_of((file, span), next, iteration.next.open);

        Some(acquire.max(visits, &mut self.unknowns, &mut self.traces))
    }

    fn protocol_parts_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
        closes: bool,
    ) -> (Part, Part, Part) {
        let span = iterable.span();
        let acquire = self.implicit_part_of(
            (file, span),
            &iteration.acquire,
            "iterator acquisition",
            &[iterable],
        );
        let next =
            self.implicit_part_of((file, span), &iteration.next, "iterator next", &[iterable]);
        let close = match closes {
            true => self.implicit_part_of(
                (file, span),
                &iteration.close,
                "iterator close",
                &[iterable],
            ),
            false => Part::none(),
        };

        (acquire, next, close)
    }

    fn visits_of(&mut self, (file, span): (FileId, Span), next: Part, unresolved: bool) -> Part {
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);

        if unresolved {
            let bound = self.unknowns.origin(origin, UnknownReason::Bound);
            let scaled = self.unknowns.scale(next.unknowns, None);

            return Part {
                unknowns: self.unknowns.join(scaled, Some(bound)),
                preference: next.preference.max(Preference::Unmarked),
                ..next
            };
        }

        crate::cost::nest(
            "iterator visits".to_string(),
            site,
            origin,
            Cost::N,
            next,
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn implicit_parts_of(&mut self, file: FileId, kind: AstKind<'a>) -> Vec<Part> {
        let mut parts = Vec::new();

        if let Some(object) = accessed_object_of(kind) {
            let role = member_role_of(self.project.file(file).semantic.nodes(), kind.node_id());
            let span = kind.span();

            if matches!(role, Some(Role::Read | Role::Update)) {
                let targets = self.accessor_targets_of(file, kind, false);

                parts.push(self.implicit_part_of((file, span), &targets, "getter", &[object]));
            }

            if matches!(role, Some(Role::Write | Role::Update)) {
                let targets = self.accessor_targets_of(file, kind, true);

                parts.push(self.implicit_part_of((file, span), &targets, "setter", &[object]));
            }
        }

        for operand in self.coerced_operands_of(file, kind) {
            let targets = self.coercion_targets_of(file, operand);

            parts.push(self.implicit_part_of(
                (file, operand.span()),
                &targets,
                "coercion",
                &[operand],
            ));
        }

        let coerced_target = match kind {
            AstKind::AssignmentExpression(assignment)
                if !matches!(assignment.operator, AssignmentOperator::Assign)
                    && !assignment.operator.is_logical() =>
            {
                assignment.left.as_simple_assignment_target()
            }
            AstKind::UpdateExpression(update) => Some(&update.argument),
            _ => None,
        };

        if let Some(target) = coerced_target {
            parts.push(self.target_coercion_part_of(file, target, kind.span()));
        }

        if matches!(
            kind,
            AstKind::ObjectPattern(_)
                | AstKind::ArrayPattern(_)
                | AstKind::ObjectAssignmentTarget(_)
                | AstKind::ArrayAssignmentTarget(_)
        ) {
            parts.extend(self.pattern_part_of(file, kind));
        }

        if let AstKind::YieldExpression(yielded) = kind {
            parts.extend(self.yielded_part_of(file, yielded));
        }

        parts
    }

    fn yielded_part_of(&mut self, file: FileId, yielded: &'a YieldExpression<'a>) -> Option<Part> {
        let argument = yielded.argument.as_ref().filter(|_| yielded.delegate)?;
        let asynchronous = self
            .project
            .file(file)
            .semantic
            .nodes()
            .ancestors(yielded.node_id())
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(function.r#async),
                _ => None,
            })
            .unwrap_or(false);

        self.delegated_part_of(file, yielded.span, argument, asynchronous)
    }

    fn coerced_operands_of(&mut self, file: FileId, kind: AstKind<'a>) -> Vec<&'a Expression<'a>> {
        let operands: Vec<&'a Expression<'a>> = match kind {
            AstKind::UnaryExpression(unary)
                if matches!(
                    unary.operator,
                    UnaryOperator::UnaryPlus
                        | UnaryOperator::UnaryNegation
                        | UnaryOperator::BitwiseNot
                ) =>
            {
                vec![&unary.argument]
            }
            AstKind::BinaryExpression(binary) if binary.operator == BinaryOperator::In => {
                vec![&binary.left]
            }
            AstKind::BinaryExpression(binary) if is_coercing_binary(binary.operator) => {
                vec![&binary.left, &binary.right]
            }
            AstKind::AssignmentExpression(assignment)
                if !matches!(assignment.operator, AssignmentOperator::Assign)
                    && !assignment.operator.is_logical() =>
            {
                vec![&assignment.right]
            }
            AstKind::ComputedMemberExpression(member)
                if self.expression_key(file, &member.expression).is_none() =>
            {
                vec![&member.expression]
            }
            AstKind::ObjectProperty(property) if property.computed => {
                self.unknown_key_of(file, &property.key)
            }
            AstKind::BindingProperty(property) if property.computed => {
                self.unknown_key_of(file, &property.key)
            }
            AstKind::AssignmentTargetPropertyProperty(property) if property.computed => {
                self.unknown_key_of(file, &property.name)
            }
            AstKind::MethodDefinition(method) if method.computed => {
                self.unknown_key_of(file, &method.key)
            }
            AstKind::PropertyDefinition(property) if property.computed => {
                self.unknown_key_of(file, &property.key)
            }
            AstKind::AccessorProperty(property) if property.computed => {
                self.unknown_key_of(file, &property.key)
            }
            AstKind::TemplateLiteral(template)
                if !matches!(
                    self.project
                        .file(file)
                        .semantic
                        .nodes()
                        .parent_kind(template.node_id()),
                    AstKind::TaggedTemplateExpression(_)
                ) =>
            {
                template.expressions.iter().collect()
            }
            _ => Vec::new(),
        };

        operands
            .into_iter()
            .filter(|operand| !self.is_primitive_operand(file, operand))
            .collect()
    }

    fn unknown_key_of(
        &mut self,
        file: FileId,
        key: &'a oxc_ast::ast::PropertyKey<'a>,
    ) -> Vec<&'a Expression<'a>> {
        key.as_expression()
            .filter(|expression| self.expression_key(file, expression).is_none())
            .into_iter()
            .collect()
    }

    pub(crate) fn class_key_part_of(&mut self, file: FileId, element: NodeId) -> Part {
        let kind = self.kind_of_node(file, element);
        let mut part = Part::none();

        for operand in self.coerced_operands_of(file, kind) {
            let found = self.operand_coercion_part_of(file, operand);

            part = part.max(found, &mut self.unknowns, &mut self.traces);
        }

        part
    }

    fn is_primitive_operand(&mut self, file: FileId, operand: &'a Expression<'a>) -> bool {
        if self.is_declared_primitive(file, operand) {
            return true;
        }

        let operand = unwrap(operand);

        if is_primitive_result(operand) {
            return true;
        }

        if let Expression::StaticMemberExpression(member) = operand {
            if member.property.name == "length" && self.is_primitive_operand(file, &member.object) {
                return true;
            }
        }

        self.holds_primitive(file, operand)
            || self.proven_kind(file, operand) == Kind::String
            || self.returns_primitive(file, operand, 0)
    }

    fn returns_primitive(
        &mut self,
        file: FileId,
        operand: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        let Expression::CallExpression(call) = unwrap(operand) else {
            return false;
        };

        if depth >= MAXIMUM_RETURN_DEPTH {
            return false;
        }

        let targets = self.resolved_callee_of(file, call).targets;

        if targets.open || targets.known.is_empty() {
            return false;
        }

        targets.known.into_iter().all(|target| {
            let deferred = match self.function_at(target) {
                FunctionNode::Function(function) => function.r#async || function.generator,
                FunctionNode::Arrow(arrow) => arrow.r#async,
            };

            !deferred
                && self
                    .returned_expressions_of(target)
                    .into_iter()
                    .all(|returned| {
                        let returned = unwrap(returned);

                        is_primitive_result(returned)
                            || self.holds_primitive(target.file, returned)
                            || self.returns_primitive(target.file, returned, depth + 1)
                    })
        })
    }

    fn coercion_targets_of(&mut self, file: FileId, operand: &'a Expression<'a>) -> TargetSet {
        self.protocol_targets_of(file, operand, &coercion_keys())
    }

    fn target_coercion_part_of(
        &mut self,
        file: FileId,
        target: &'a SimpleAssignmentTarget<'a>,
        span: Span,
    ) -> Part {
        if !self.may_implement_any(&coercion_keys()) {
            return Part::none();
        }

        let (sources, receivers) = match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                if self.is_primitive_binding(file, reference) {
                    return Part::none();
                }

                let sources = match self.local_values_of(file, reference) {
                    Some(values) => Sources {
                        values,
                        open: false,
                    },
                    None => Sources {
                        values: Vec::new(),
                        open: true,
                    },
                };

                (sources, Vec::new())
            }
            SimpleAssignmentTarget::TSAsExpression(inner) => {
                return self.operand_coercion_part_of(file, &inner.expression);
            }
            SimpleAssignmentTarget::TSSatisfiesExpression(inner) => {
                return self.operand_coercion_part_of(file, &inner.expression);
            }
            SimpleAssignmentTarget::TSNonNullExpression(inner) => {
                return self.operand_coercion_part_of(file, &inner.expression);
            }
            SimpleAssignmentTarget::TSTypeAssertion(inner) => {
                return self.operand_coercion_part_of(file, &inner.expression);
            }
            other => {
                let Some(member) = other.as_member_expression() else {
                    return Part::none();
                };
                let object = member.object();
                let sources = match self.member_key(file, member) {
                    Some(key) => {
                        let (values, open) = self.property_values_of((file, object), &key);

                        Sources { values, open }
                    }
                    None => Sources {
                        values: Vec::new(),
                        open: true,
                    },
                };

                (sources, vec![object])
            }
        };
        let mut targets = TargetSet {
            known: Vec::new(),
            open: sources.open,
        };

        for (source, value) in sources.values {
            if self.is_primitive_operand(source, value) {
                continue;
            }

            let found = self.coercion_targets_of(source, value);

            join_targets(&mut targets, found);
        }

        self.implicit_part_of((file, span), &targets, "coercion", &receivers)
    }

    fn operand_coercion_part_of(&mut self, file: FileId, operand: &'a Expression<'a>) -> Part {
        if self.is_primitive_operand(file, operand) {
            return Part::none();
        }

        let targets = self.coercion_targets_of(file, operand);

        self.implicit_part_of((file, operand.span()), &targets, "coercion", &[operand])
    }

    fn pattern_sources_of(&mut self, file: FileId, kind: AstKind<'a>) -> Option<Sources<'a>> {
        if !matches!(
            kind,
            AstKind::ObjectPattern(_)
                | AstKind::ArrayPattern(_)
                | AstKind::ObjectAssignmentTarget(_)
                | AstKind::ArrayAssignmentTarget(_)
        ) {
            return None;
        }

        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let parent = nodes.parent_id(kind.node_id());
        let span = kind.span();
        let open = Sources {
            values: Vec::new(),
            open: true,
        };

        match nodes.kind(parent) {
            AstKind::VariableDeclarator(declarator) if declarator.id.span() == span => {
                match nodes.parent_kind(nodes.parent_id(parent)) {
                    AstKind::ForOfStatement(statement) => {
                        Some(element_sources_of(file, &statement.right, 1).remove(0))
                    }
                    AstKind::ForInStatement(_) => Some(open),
                    _ => Some(match &declarator.init {
                        Some(init) => Sources {
                            values: vec![(file, init)],
                            open: false,
                        },
                        None => open,
                    }),
                }
            }
            AstKind::FormalParameter(parameter) => {
                Some(self.pattern_parameter_sources_of(file, parameter))
            }
            AstKind::CatchParameter(_) => Some(open),
            AstKind::AssignmentExpression(assignment) if assignment.left.span() == span => {
                Some(Sources {
                    values: vec![(file, &assignment.right)],
                    open: false,
                })
            }
            AstKind::ForOfStatement(statement) if statement.left.span() == span => {
                Some(element_sources_of(file, &statement.right, 1).remove(0))
            }
            AstKind::ForInStatement(statement) if statement.left.span() == span => Some(open),
            _ => None,
        }
    }

    fn pattern_parameter_sources_of(
        &mut self,
        file: FileId,
        parameter: &'a FormalParameter<'a>,
    ) -> Sources<'a> {
        let function = self
            .project
            .file(file)
            .semantic
            .nodes()
            .ancestor_kinds(parameter.node_id())
            .find_map(function_of_kind);
        let mut sources = Sources {
            values: parameter
                .initializer
                .iter()
                .map(|initializer| (file, &**initializer))
                .collect(),
            open: true,
        };

        if let Some(arguments) =
            function.and_then(|function| self.call_arguments_of(file, function, parameter))
        {
            sources.values.extend(arguments.into_iter().flatten());

            sources.open = false;
        }

        sources
    }

    fn pattern_part_of(&mut self, file: FileId, kind: AstKind<'a>) -> Option<Part> {
        let site = (file, kind.node_id());
        let plan = match self.implicit_plan(site) {
            Some(plan) => plan,
            None => {
                let sources = self.pattern_sources_of(file, kind)?;
                let exhaustions = self.target_exhaustions();
                let mut plan = Vec::new();

                self.plan_pattern_of(file, kind, sources, &mut plan);

                let plan = Rc::new(plan);

                if exhaustions == self.target_exhaustions() && !self.work_exhausted() {
                    self.store_implicit_plan(site, Rc::clone(&plan));
                }

                plan
            }
        };
        let mut part = Part::none();

        for planned in plan.iter() {
            let found = self.planned_part_of(planned);

            part = part.max(found, &mut self.unknowns, &mut self.traces);
        }

        Some(part)
    }

    fn planned_part_of(&mut self, planned: &ImplicitSite) -> Part {
        let found = self.implicit_values_part_of(
            (planned.file, planned.span),
            &planned.targets,
            planned.operation,
            &planned.receivers,
        );

        match planned.visits {
            Some(unresolved) => self.visits_of((planned.file, planned.span), found, unresolved),
            None => found,
        }
    }

    fn plan_pattern_of(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
        sources: Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) {
        match kind {
            AstKind::ObjectPattern(_) | AstKind::ArrayPattern(_) => {
                let pattern = match self
                    .project
                    .file(file)
                    .semantic
                    .nodes()
                    .parent_kind(kind.node_id())
                {
                    AstKind::VariableDeclarator(declarator) => &declarator.id,
                    AstKind::FormalParameter(parameter) => &parameter.pattern,
                    AstKind::CatchParameter(parameter) => &parameter.pattern,
                    _ => return,
                };

                self.plan_binding_pattern_of(file, pattern, sources, plan);
            }
            AstKind::ObjectAssignmentTarget(object) => {
                self.plan_object_target_of(file, object, sources, plan)
            }
            AstKind::ArrayAssignmentTarget(array) => {
                self.plan_array_target_of(file, array, sources, plan)
            }
            _ => {}
        }
    }

    fn plan_binding_pattern_of(
        &mut self,
        file: FileId,
        pattern: &'a BindingPattern<'a>,
        sources: Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) {
        match pattern {
            BindingPattern::BindingIdentifier(_) => {}
            BindingPattern::AssignmentPattern(assignment) => {
                let mut sources = sources;

                sources.values.push((file, &assignment.right));

                self.plan_binding_pattern_of(file, &assignment.left, sources, plan);
            }
            BindingPattern::ObjectPattern(object) => {
                for property in &object.properties {
                    let key = self.property_key(file, &property.key, property.computed);
                    let child =
                        self.plan_property_read_of(file, property.span, key, &sources, plan);

                    self.plan_binding_pattern_of(file, &property.value, child, plan);
                }
            }
            BindingPattern::ArrayPattern(array) => self.plan_elements_of(
                (file, array.span),
                (&sources, array.rest.is_none()),
                &array.elements,
                plan,
                |analysis, element, sources, plan| {
                    analysis.plan_binding_pattern_of(file, element, sources, plan)
                },
            ),
        }
    }

    fn plan_object_target_of(
        &mut self,
        file: FileId,
        object: &'a oxc_ast::ast::ObjectAssignmentTarget<'a>,
        sources: Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) {
        for property in &object.properties {
            match property {
                AssignmentTargetProperty::AssignmentTargetPropertyIdentifier(property) => {
                    let key = Some(MemberKey::Name(property.binding.name.to_string()));

                    self.plan_property_read_of(file, property.span, key, &sources, plan);
                }
                AssignmentTargetProperty::AssignmentTargetPropertyProperty(property) => {
                    let key = self.property_key(file, &property.name, property.computed);
                    let child =
                        self.plan_property_read_of(file, property.span, key, &sources, plan);

                    self.plan_maybe_default_of(file, &property.binding, child, plan);
                }
            }
        }
    }

    fn plan_array_target_of(
        &mut self,
        file: FileId,
        array: &'a oxc_ast::ast::ArrayAssignmentTarget<'a>,
        sources: Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) {
        self.plan_elements_of(
            (file, array.span),
            (&sources, array.rest.is_none()),
            &array.elements,
            plan,
            |analysis, element, sources, plan| {
                analysis.plan_maybe_default_of(file, element, sources, plan)
            },
        );
    }

    fn plan_elements_of<T>(
        &mut self,
        (file, span): (FileId, Span),
        (sources, closes): (&Sources<'a>, bool),
        elements: &'a [Option<T>],
        plan: &mut Vec<ImplicitSite>,
        mut recurse: impl FnMut(&mut Self, &'a T, Sources<'a>, &mut Vec<ImplicitSite>),
    ) {
        let found = self.plan_element_reads_of(file, span, sources, closes, elements.len(), plan);

        for (element, sources) in elements.iter().zip(found) {
            if let Some(element) = element {
                recurse(self, element, sources, plan);
            }
        }
    }

    fn plan_maybe_default_of(
        &mut self,
        file: FileId,
        target: &'a AssignmentTargetMaybeDefault<'a>,
        sources: Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) {
        let (target, sources) = match target {
            AssignmentTargetMaybeDefault::AssignmentTargetWithDefault(defaulted) => {
                let mut sources = sources;

                sources.values.push((file, &defaulted.init));

                (&defaulted.binding, sources)
            }
            other => match other.as_assignment_target() {
                Some(target) => (target, sources),
                None => return,
            },
        };

        match target {
            AssignmentTarget::ObjectAssignmentTarget(object) => {
                self.plan_object_target_of(file, object, sources, plan)
            }
            AssignmentTarget::ArrayAssignmentTarget(array) => {
                self.plan_array_target_of(file, array, sources, plan)
            }
            _ => {}
        }
    }

    fn plan_property_read_of(
        &mut self,
        file: FileId,
        span: Span,
        key: Option<MemberKey>,
        sources: &Sources<'a>,
        plan: &mut Vec<ImplicitSite>,
    ) -> Sources<'a> {
        let mut targets = TargetSet {
            known: Vec::new(),
            open: sources.open && self.may_access(key.as_ref()),
        };
        let mut child = Sources {
            values: Vec::new(),
            open: sources.open || key.is_none(),
        };
        let mut receivers = Vec::new();

        for (source, value) in sources.values.iter().copied() {
            let Some(key) = key.clone() else {
                receivers.push(self.storage_value_of(source, value));

                targets.open |= self.may_access(None);

                continue;
            };
            let found = self.property_accessors_of((source, value), key.clone(), false);
            let (values, open) = self.property_values_of((source, value), &key);

            if found.open {
                receivers.push(self.storage_value_of(source, value));
            }

            join_targets(&mut targets, found);
            child.values.extend(values);

            child.open |= open;
        }

        plan.push(ImplicitSite {
            file,
            span,
            targets,
            operation: "getter",
            receivers,
            visits: None,
        });

        child
    }

    fn plan_element_reads_of(
        &mut self,
        file: FileId,
        span: Span,
        sources: &Sources<'a>,
        closes: bool,
        count: usize,
        plan: &mut Vec<ImplicitSite>,
    ) -> Vec<Sources<'a>> {
        let mut elements = Vec::new();

        if sources.open && self.may_implement_any(&iteration_keys()) {
            plan.push(ImplicitSite {
                file,
                span,
                targets: TargetSet {
                    known: Vec::new(),
                    open: true,
                },
                operation: "iterator",
                receivers: Vec::new(),
                visits: None,
            });
        }

        for (source, value) in sources.values.iter().copied() {
            let iteration = self.iteration_of(source, value, false);

            if !is_inert(&iteration) {
                let receivers = vec![self.storage_value_of(source, value)];
                let span = value.span();

                plan.push(ImplicitSite {
                    file: source,
                    span,
                    targets: iteration.acquire.clone(),
                    operation: "iterator acquisition",
                    receivers: receivers.clone(),
                    visits: None,
                });
                plan.push(ImplicitSite {
                    file: source,
                    span,
                    targets: iteration.next.clone(),
                    operation: "iterator next",
                    receivers: receivers.clone(),
                    visits: (!closes).then_some(iteration.next.open),
                });

                if closes {
                    plan.push(ImplicitSite {
                        file: source,
                        span,
                        targets: iteration.close.clone(),
                        operation: "iterator close",
                        receivers,
                        visits: None,
                    });
                }
            }

            elements.push(element_sources_of(source, value, count));
        }

        let mut joined = joined_sources_of(elements, count);

        for element in &mut joined {
            element.open |= sources.open;
        }

        joined
    }

    fn implicit_part_of(
        &mut self,
        (file, span): (FileId, Span),
        targets: &TargetSet,
        operation: &str,
        receivers: &[&'a Expression<'a>],
    ) -> Part {
        let values: Vec<ValueId> = match targets.open {
            true => receivers
                .iter()
                .map(|receiver| self.storage_value_of(file, receiver))
                .collect(),
            false => Vec::new(),
        };

        self.implicit_values_part_of((file, span), targets, operation, &values)
    }

    fn implicit_values_part_of(
        &mut self,
        (file, span): (FileId, Span),
        targets: &TargetSet,
        operation: &str,
        receivers: &[ValueId],
    ) -> Part {
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);
        let mut part = Part::none();

        for known in &targets.known {
            let function = self.function_at(*known);
            let (called, cyclic) = self.call_implicit(*known, file, span);
            let called = match called.cost.is_one() {
                true => called,
                false => match self.trace_name_of(known.file, function) {
                    Ok(name) => called.explain(
                        format_args!("call {name}() [{operation}]"),
                        site,
                        origin,
                        true,
                        &mut self.traces,
                        &mut self.unknowns,
                    ),
                    Err(_) => called.explanation_failed(origin, &mut self.unknowns),
                },
            };
            let called = called.called(origin, &mut self.unknowns);
            let called = self.called_part_of(known.file, function, called, cyclic);

            part = part.max(called, &mut self.unknowns, &mut self.traces);
        }

        if !targets.open {
            return part;
        }

        let unknown = self.unknown_implicit_part(file, span, receivers);

        match targets.known.is_empty() {
            true => unknown,
            false => {
                part.unknowns = self.unknowns.join(part.unknowns, unknown.unknowns);

                match part.preference {
                    Preference::Absent => part.preferred(Preference::Unmarked),
                    _ => part,
                }
            }
        }
    }

    fn unknown_implicit_part(&mut self, file: FileId, span: Span, receivers: &[ValueId]) -> Part {
        let invoked = self.values.at(self.source_span(file, span)).value;

        for value in std::iter::once(invoked).chain(receivers.iter().copied()) {
            if value != invoked && !self.current_effects.escapes.contains(&value) {
                self.current_effects.escapes.push(value);
            }

            if !self.current_effects.unknown_reachable.contains(&value) {
                self.current_effects.unknown_reachable.push(value);
            }
        }

        self.unknown_part(file, span, UnknownReason::Target)
    }
}

fn function_of_kind<'a>(kind: AstKind<'a>) -> Option<FunctionNode<'a>> {
    match kind {
        AstKind::Function(function) => Some(FunctionNode::Function(function)),
        AstKind::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
        _ => None,
    }
}

fn join_targets(targets: &mut TargetSet, found: TargetSet) {
    targets.open |= found.open;

    for known in found.known {
        if !targets.known.contains(&known) {
            targets.known.push(known);
        }
    }
}

fn is_inert(iteration: &Iteration) -> bool {
    [&iteration.acquire, &iteration.next, &iteration.close]
        .iter()
        .all(|targets| !targets.open && targets.known.is_empty())
}

fn accessed_object_of<'a>(kind: AstKind<'a>) -> Option<&'a Expression<'a>> {
    match kind {
        AstKind::StaticMemberExpression(member) => Some(&member.object),
        AstKind::ComputedMemberExpression(member) => Some(&member.object),
        AstKind::PrivateFieldExpression(member) => Some(&member.object),
        _ => None,
    }
}

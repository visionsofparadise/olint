use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, AssignmentTargetMaybeDefault,
    AssignmentTargetProperty, BindingPattern, Class, Expression, ForOfStatement, FormalParameter,
    JSXAttributeItem, JSXAttributeName, JSXAttributeValue, JSXChild, JSXElementName, JSXExpression,
    JSXExpressionContainer, JSXMemberExpression, JSXMemberExpressionObject, JSXOpeningElement,
    MethodDefinitionKind, ObjectPropertyKind, PropertyKind, SimpleAssignmentTarget, SpreadElement,
    TaggedTemplateExpression, YieldExpression,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, UnaryOperator};
use oxc_syntax::scope::ScopeId;

use crate::analysis::Analysis;
use crate::constants::constant_initializer_of;
use crate::cost::{Cost, ExecutionPhase, Part, Preference, Reading};
use crate::declarations::{Declaration, FunctionId, FunctionNode, TargetSet};
use crate::declared_types::{is_primitive_result, Kind};
use crate::project::{has_key_after_spread, FileId, JsxRuntime, Project};
use crate::receivers::Placement;
use crate::syntax::{member_expression_of, unwrap};
use crate::unknowns::UnknownReason;
use crate::values::{
    outermost_of, protocol_key_of, ArgumentFacts, Definedness, Iteration, MemberKey, ValueFacts,
    ValueId,
};

use std::rc::Rc;

const COERCION_KEYS: [&str; 3] = ["@@toPrimitive", "valueOf", "toString"];
const HAS_INSTANCE_KEYS: [&str; 1] = ["@@hasInstance"];
const AWAITED_KEYS: [&str; 1] = ["then"];
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
    visits: Option<Option<Cost>>,
}

pub(crate) struct IterationParts {
    pub(crate) acquire: Reading,
    pub(crate) next: Reading,
    pub(crate) close: Reading,
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

pub(crate) fn coercion_keys() -> Vec<MemberKey> {
    COERCION_KEYS
        .iter()
        .map(|name| protocol_key_of(name))
        .collect()
}

fn has_instance_keys() -> Vec<MemberKey> {
    HAS_INSTANCE_KEYS
        .iter()
        .map(|name| protocol_key_of(name))
        .collect()
}

fn awaited_keys() -> Vec<MemberKey> {
    AWAITED_KEYS
        .iter()
        .map(|name| protocol_key_of(name))
        .collect()
}

pub(crate) fn iteration_keys() -> Vec<MemberKey> {
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
                self.spread_part_of(file, spread);
            }
            AstKind::JSXSpreadAttribute(_) | AstKind::JSXSpreadChild(_) => {
                self.jsx_spread_part_of(file, kind);
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

        for targets in self.iteration_effect_targets_of(file, &statement.right, &iteration) {
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

        if let Some(constructor) = checked_constructor_of(kind) {
            targets.push(self.has_instance_targets_of(file, constructor));
        }

        if let Some(operand) = awaited_operand_of(kind) {
            targets.push(self.awaited_targets_of(file, operand));
        }

        targets
            .iter()
            .any(|targets| targets.open || !targets.known.is_empty())
    }

    pub(crate) fn tag_part_of(
        &mut self,
        file: FileId,
        tagged: &'a TaggedTemplateExpression<'a>,
    ) -> Reading {
        let targets = self
            .resolved_expression_callee_of(file, &tagged.tag, tagged.node_id())
            .targets;
        let mut receivers: Vec<&'a Expression<'a>> = tagged.quasi.expressions.iter().collect();

        if let Some(member) = member_expression_of(unwrap(&tagged.tag)) {
            receivers.push(member.object());
        }

        self.implicit_call_reading_of((file, tagged.span), &targets, "tag", &receivers)
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

    pub(crate) fn spread_part_of(
        &mut self,
        file: FileId,
        spread: &'a SpreadElement<'a>,
    ) -> Option<Reading> {
        if matches!(
            self.project
                .file(file)
                .semantic
                .nodes()
                .parent_kind(spread.node_id()),
            AstKind::ObjectExpression(_)
        ) {
            return Some(self.copied_part_of(
                file,
                (spread.node_id(), spread.span),
                &spread.argument,
            ));
        }

        self.delegated_part_of(file, spread.span, &spread.argument, false)
    }

    pub(crate) fn inspected_part_of(&mut self, file: FileId, value: &'a Expression<'a>) -> Reading {
        if self.is_primitive_operand(file, value) || self.has_primitive_elements(file, value) {
            return Reading::empty();
        }

        self.implicit_plan_part_of((file, value.node_id()), |analysis, plan| {
            let sources = Sources {
                values: vec![(file, value)],
                open: false,
            };

            analysis.plan_rest_reads_of((file, value.span()), &sources, &[], plan);
        })
    }

    pub(crate) fn unknown_visits_part_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
    ) -> Reading {
        let receiver = self.storage_value_of(file, value);
        let visited = self.unknown_implicit_part(file, value.span(), &[receiver]);

        self.visits_of(
            (file, value.span()),
            Reading::of_part(visited),
            Some(Cost::N),
        )
    }

    fn copied_part_of(
        &mut self,
        file: FileId,
        (node, span): (NodeId, Span),
        argument: &'a Expression<'a>,
    ) -> Reading {
        self.implicit_plan_part_of((file, node), |analysis, plan| {
            let sources = Sources {
                values: vec![(file, argument)],
                open: false,
            };

            analysis.plan_rest_reads_of((file, span), &sources, &[], plan);
        })
    }

    pub(crate) fn jsx_spread_part_of(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
    ) -> Option<Reading> {
        match kind {
            AstKind::JSXSpreadAttribute(spread) if is_inlined_spread(&spread.argument) => {
                self.lowered_jsx_getters_of(file, spread)
            }
            AstKind::JSXSpreadAttribute(spread) => {
                Some(self.copied_part_of(file, (spread.node_id(), spread.span), &spread.argument))
            }
            AstKind::JSXSpreadChild(child) => {
                self.delegated_part_of(file, child.span, &child.expression, false)
            }
            _ => None,
        }
    }

    fn lowered_jsx_getters_of(
        &mut self,
        file: FileId,
        spread: &'a oxc_ast::ast::JSXSpreadAttribute<'a>,
    ) -> Option<Reading> {
        if !self.project.jsx_spreads_lowered(file) {
            return None;
        }

        let AstKind::JSXOpeningElement(opening) = self
            .project
            .file(file)
            .semantic
            .nodes()
            .parent_kind(spread.node_id())
        else {
            return None;
        };
        let mut copied = false;
        let mut targets = TargetSet {
            known: Vec::new(),
            open: false,
        };
        let mut properties = Vec::new();

        for attribute in &opening.attributes {
            let attribute = match attribute {
                JSXAttributeItem::Attribute(attribute) => {
                    let name = match &attribute.name {
                        JSXAttributeName::Identifier(name) => name.name.to_string(),
                        JSXAttributeName::NamespacedName(name) => {
                            format!("{}:{}", name.namespace.name, name.name.name)
                        }
                    };

                    properties.push(JsxProperty {
                        key: Some(MemberKey::Name(name)),
                        kind: PropertyKind::Init,
                        getter: None,
                    });

                    continue;
                }
                JSXAttributeItem::SpreadAttribute(attribute) => attribute,
            };
            let current = attribute.node_id() == spread.node_id();

            if !is_inlined_spread(&attribute.argument) {
                join_jsx_getters(&mut targets, &properties, copied);
                properties.clear();

                copied = true;

                continue;
            }

            if let Expression::ObjectExpression(object) = &attribute.argument {
                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::SpreadProperty(_) => {
                            join_jsx_getters(&mut targets, &properties, copied);
                            properties.clear();

                            copied = true;
                        }
                        ObjectPropertyKind::ObjectProperty(property) => {
                            let getter = match &property.value {
                                Expression::FunctionExpression(function)
                                    if current && property.kind == PropertyKind::Get =>
                                {
                                    Some(FunctionId {
                                        file,
                                        node: function.node_id(),
                                    })
                                }
                                _ => None,
                            };

                            properties.push(JsxProperty {
                                key: self.property_key(file, &property.key, property.computed),
                                kind: property.kind,
                                getter,
                            });
                        }
                    }
                }
            }
        }

        join_jsx_getters(&mut targets, &properties, copied);

        Some(self.implicit_call_reading_of((file, spread.span), &targets, "jsx spread getter", &[]))
    }

    fn implicit_plan_part_of(
        &mut self,
        site: (FileId, NodeId),
        build: impl FnOnce(&mut Self, &mut Vec<ImplicitSite>),
    ) -> Reading {
        let plan = match self.implicit_plan(site) {
            Some(plan) => plan,
            None => {
                let exhaustions = self.target_exhaustions();
                let mut plan = Vec::new();

                build(self, &mut plan);

                let plan = Rc::new(plan);

                if exhaustions == self.target_exhaustions() && !self.work_exhausted() {
                    self.store_implicit_plan(site, Rc::clone(&plan));
                }

                plan
            }
        };
        let mut part = Reading::empty();

        for planned in plan.iter() {
            let found = self.planned_part_of(planned);

            part = part.merge(found, &mut self.unknowns, &mut self.traces);
        }

        part
    }

    pub(crate) fn delegated_part_of(
        &mut self,
        file: FileId,
        span: Span,
        iterable: &'a Expression<'a>,
        asynchronous: bool,
    ) -> Option<Reading> {
        let iteration = self.iteration_of(file, iterable, asynchronous);
        let count = self.iteration_count_of(file, iterable, &iteration);
        let latent = self.iteration_latent_of(file, iterable, &iteration);

        if latent.is_none() && count.is_some() && is_inert(&iteration) {
            return None;
        }

        let (acquire, next, _) = self.protocol_parts_of(file, iterable, &iteration, false);
        let visits = self.visits_of((file, span), next, count);
        let mut reading = acquire.merge(visits, &mut self.unknowns, &mut self.traces);

        if let Some(latent) = latent {
            let consumed = self.consumed_part_of(file, iterable.span(), &latent);

            reading = reading.merge(consumed, &mut self.unknowns, &mut self.traces);
        }

        (!reading.holds_no_work()).then_some(reading)
    }

    fn protocol_parts_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
        closes: bool,
    ) -> (Reading, Reading, Reading) {
        let span = iterable.span();
        let [acquired, advanced, closed] = self.iteration_accessors_of(file, iterable, iteration);
        let results = self.iteration_result_accessors_of(iteration);
        let acquisition_getters = self.implicit_call_reading_of(
            (file, span),
            &acquired,
            "iterator acquisition getter",
            &[iterable],
        );
        let next_getters = self.implicit_call_reading_of(
            (file, span),
            &advanced,
            "iterator next getter",
            &[iterable],
        );
        let acquire = self.implicit_call_reading_of(
            (file, span),
            &iteration.acquire,
            "iterator acquisition",
            &[iterable],
        );
        let acquire = acquire
            .merge(acquisition_getters, &mut self.unknowns, &mut self.traces)
            .merge(next_getters, &mut self.unknowns, &mut self.traces);
        let next = self.implicit_call_reading_of(
            (file, span),
            &iteration.next,
            "iterator next",
            &[iterable],
        );
        let result_getters = self.implicit_call_reading_of(
            (file, span),
            &results,
            "iterator result getter",
            &[iterable],
        );
        let result_getters = match iteration.asynchronous {
            true => result_getters.in_phase(
                ExecutionPhase::Scheduled,
                &mut self.unknowns,
                &mut self.traces,
            ),
            false => result_getters,
        };
        let mut next = next.merge(result_getters, &mut self.unknowns, &mut self.traces);

        if iteration.asynchronous {
            for target in &iteration.next.known {
                if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                    let unknown = self.unknown_part(file, span, UnknownReason::ResourceExhaustion);

                    next = next.merge(unknown, &mut self.unknowns, &mut self.traces);

                    break;
                }

                let asynchronous = match self.function_at(*target) {
                    FunctionNode::Function(function) => function.r#async,
                    FunctionNode::Arrow(arrow) => arrow.r#async,
                    FunctionNode::Construction(_) => false,
                };

                let returned = self.returned_expressions_of(*target);

                if !self.charge_work(
                    crate::analysis::work::Event::TraversalEdge,
                    returned.len() as u64,
                ) {
                    let unknown = self.unknown_part(file, span, UnknownReason::ResourceExhaustion);

                    next = next.merge(unknown, &mut self.unknowns, &mut self.traces);

                    break;
                }

                for returned in returned {
                    let key = MemberKey::Name("then".to_string());
                    let accessors =
                        self.property_accessors_of((target.file, returned), key.clone(), false);
                    let methods = self.protocol_targets_of(target.file, returned, &[key]);

                    if accessors.open
                        || methods.open
                        || !accessors.known.is_empty()
                        || !methods.known.is_empty()
                    {
                        if !asynchronous {
                            let resolution = self.assimilated_reading_of(target.file, returned);

                            next = next.merge(resolution, &mut self.unknowns, &mut self.traces);
                        }

                        let unknown = self.unknown_part(file, span, UnknownReason::Target);

                        next = next.merge(unknown, &mut self.unknowns, &mut self.traces);
                    }
                }
            }
        }

        let close = match closes {
            true => self.implicit_call_reading_of(
                (file, span),
                &iteration.close,
                "iterator close",
                &[iterable],
            ),
            false => Reading::empty(),
        };

        let close = if closes {
            let getter = self.implicit_call_reading_of(
                (file, span),
                &closed,
                "iterator close getter",
                &[iterable],
            );
            let close = close.merge(getter, &mut self.unknowns, &mut self.traces);

            match iteration.asynchronous {
                true => close.in_phase(
                    ExecutionPhase::Scheduled,
                    &mut self.unknowns,
                    &mut self.traces,
                ),
                false => close,
            }
        } else {
            close
        };

        (acquire, next, close)
    }

    fn visits_of(
        &mut self,
        (file, span): (FileId, Span),
        next: Reading,
        count: Option<Cost>,
    ) -> Reading {
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);

        let Some(count) = count else {
            let bound = self.unknowns.origin(origin, UnknownReason::Bound);

            for (_, _, part) in &next.completions {
                self.note_unresolved_multiplicity(part);
            }

            return next
                .map_parts(|part| part.scaled(None, &mut self.unknowns))
                .retaining(Some(bound), &mut self.unknowns);
        };

        next.executed().map_parts(|part| {
            crate::cost::nest(
                "iterator visits".to_string(),
                site,
                origin,
                count.clone(),
                part,
                &mut self.unknowns,
                &mut self.traces,
            )
        })
    }

    fn implicit_parts_of(&mut self, file: FileId, kind: AstKind<'a>) -> Vec<Reading> {
        let mut parts = Vec::new();

        if let Some(object) = accessed_object_of(kind) {
            let role = member_role_of(self.project.file(file).semantic.nodes(), kind.node_id());
            let span = kind.span();

            if matches!(role, Some(Role::Read | Role::Update)) {
                let targets = self.accessor_targets_of(file, kind, false);

                parts.push(self.implicit_call_reading_of(
                    (file, span),
                    &targets,
                    "getter",
                    &[object],
                ));
            }

            if matches!(role, Some(Role::Write | Role::Update)) {
                let targets = self.accessor_targets_of(file, kind, true);

                parts.push(self.implicit_call_reading_of(
                    (file, span),
                    &targets,
                    "setter",
                    &[object],
                ));
            }
        }

        for operand in self.coerced_operands_of(file, kind) {
            let targets = self.coercion_targets_of(file, operand);

            parts.push(self.implicit_call_reading_of(
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

        if let Some(constructor) = checked_constructor_of(kind) {
            let targets = self.has_instance_targets_of(file, constructor);

            parts.push(self.implicit_call_reading_of(
                (file, kind.span()),
                &targets,
                "instanceof",
                &[constructor],
            ));
        }

        if let Some(operand) = awaited_operand_of(kind) {
            parts.push(self.assimilated_reading_of(file, operand));
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

        parts.extend(self.jsx_factory_part_of(file, kind));

        if let AstKind::JSXMemberExpression(member) = kind {
            parts.extend(self.jsx_member_part_of(file, member));
        }

        parts
    }

    pub(crate) fn count_yield(&mut self, file: FileId, yielded: &'a YieldExpression<'a>) {
        let Some(produced) = self.produced.take() else {
            return;
        };
        let mut count = Some(Cost::ONE);

        for (_, _, factor, resolved) in &self.enclosing_factors {
            count = match (count, resolved) {
                (Some(count), true) => count.multiply(factor).ok(),
                _ => None,
            };
        }

        if let (Some(argument), true) = (&yielded.argument, yielded.delegate) {
            let asynchronous = self.delegation_is_async(file, yielded);
            let iteration = self.iteration_of(file, argument, asynchronous);
            let delegated = self.iteration_count_of(file, argument, &iteration);

            count = match (count, delegated) {
                (Some(count), Some(delegated)) => count.multiply(&delegated).ok(),
                _ => None,
            };
        }

        self.produced = Some(produced.joined(count));
    }

    fn delegation_is_async(&self, file: FileId, yielded: &YieldExpression<'_>) -> bool {
        self.project
            .file(file)
            .semantic
            .nodes()
            .ancestors(yielded.node_id())
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(function.r#async),
                _ => None,
            })
            .unwrap_or(false)
    }

    fn yielded_part_of(
        &mut self,
        file: FileId,
        yielded: &'a YieldExpression<'a>,
    ) -> Option<Reading> {
        let argument = yielded.argument.as_ref().filter(|_| yielded.delegate)?;
        let asynchronous = self.delegation_is_async(file, yielded);

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

    pub(crate) fn class_key_part_of(&mut self, file: FileId, element: NodeId) -> Reading {
        let kind = self.kind_of_node(file, element);
        let mut part = Reading::empty();

        for operand in self.coerced_operands_of(file, kind) {
            let found = self.operand_coercion_part_of(file, operand);

            part = part.merge(found, &mut self.unknowns, &mut self.traces);
        }

        part
    }

    pub(crate) fn is_primitive_operand(
        &mut self,
        file: FileId,
        operand: &'a Expression<'a>,
    ) -> bool {
        if self.is_declared_primitive(file, operand) {
            return true;
        }

        let operand = unwrap(operand);

        if let Expression::AwaitExpression(awaited) = operand {
            return self.is_primitive_operand(file, &awaited.argument);
        }

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
            !self.is_deferred_function(target)
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

    pub(crate) fn returns_only_primitives(&mut self, target: FunctionId) -> bool {
        !self.is_deferred_function(target)
            && self
                .returned_expressions_of(target)
                .into_iter()
                .all(|returned| self.is_primitive_operand(target.file, returned))
    }

    pub(crate) fn is_deferred_function(&self, target: FunctionId) -> bool {
        match self.function_at(target) {
            FunctionNode::Function(function) => function.r#async || function.generator,
            FunctionNode::Arrow(arrow) => arrow.r#async,
            FunctionNode::Construction(_) => false,
        }
    }

    fn coercion_targets_of(&mut self, file: FileId, operand: &'a Expression<'a>) -> TargetSet {
        self.protocol_targets_of(file, operand, &coercion_keys())
    }

    fn has_instance_targets_of(
        &mut self,
        file: FileId,
        constructor: &'a Expression<'a>,
    ) -> TargetSet {
        self.protocol_targets_of(file, constructor, &has_instance_keys())
    }

    fn awaited_targets_of(&mut self, file: FileId, operand: &'a Expression<'a>) -> TargetSet {
        if self.is_primitive_operand(file, operand) {
            return TargetSet {
                known: Vec::new(),
                open: false,
            };
        }

        self.protocol_targets_of(file, operand, &awaited_keys())
    }

    fn target_coercion_part_of(
        &mut self,
        file: FileId,
        target: &'a SimpleAssignmentTarget<'a>,
        span: Span,
    ) -> Reading {
        if !self.may_implement_any(&coercion_keys()) {
            return Reading::empty();
        }

        let (sources, receivers) = match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                if self.is_primitive_binding(file, reference) {
                    return Reading::empty();
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
                    return Reading::empty();
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

        self.implicit_call_reading_of((file, span), &targets, "coercion", &receivers)
    }

    pub(crate) fn operand_coercion_part_of(
        &mut self,
        file: FileId,
        operand: &'a Expression<'a>,
    ) -> Reading {
        if self.is_primitive_operand(file, operand) {
            return Reading::empty();
        }

        let targets = self.coercion_targets_of(file, operand);

        self.implicit_call_reading_of((file, operand.span()), &targets, "coercion", &[operand])
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

    fn pattern_part_of(&mut self, file: FileId, kind: AstKind<'a>) -> Option<Reading> {
        let planned = self.implicit_plan_part_of((file, kind.node_id()), |analysis, plan| {
            if let Some(sources) = analysis.pattern_sources_of(file, kind) {
                analysis.plan_pattern_of(file, kind, sources, plan);
            }
        });
        let destructured = match kind {
            AstKind::ArrayPattern(_) | AstKind::ArrayAssignmentTarget(_) => {
                self.pattern_sources_of(file, kind)
            }
            _ => None,
        };

        let Some(Sources {
            values,
            open: false,
        }) = destructured
        else {
            return Some(planned);
        };
        let [(source, value)] = values[..] else {
            return Some(planned);
        };
        let iteration = self.iteration_of(source, value, false);
        let Some(latent) = self.iteration_latent_of(source, value, &iteration) else {
            return Some(planned);
        };
        let consumed = self.consumed_part_of(source, value.span(), &latent);

        Some(planned.merge(consumed, &mut self.unknowns, &mut self.traces))
    }

    fn planned_part_of(&mut self, planned: &ImplicitSite) -> Reading {
        let found = self.implicit_values_part_of(
            (planned.file, planned.span),
            &planned.targets,
            planned.operation,
            &planned.receivers,
        );

        match &planned.visits {
            Some(count) => self.visits_of((planned.file, planned.span), found, count.clone()),
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
                let mut excluded = Vec::new();

                for property in &object.properties {
                    let key = self.property_key(file, &property.key, property.computed);
                    let child = self.plan_property_read_of(
                        file,
                        property.span,
                        key.clone(),
                        &sources,
                        plan,
                    );

                    excluded.extend(key);

                    self.plan_binding_pattern_of(file, &property.value, child, plan);
                }

                if let Some(rest) = &object.rest {
                    self.plan_rest_reads_of((file, rest.span), &sources, &excluded, plan);
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
        let mut excluded = Vec::new();

        for property in &object.properties {
            match property {
                AssignmentTargetProperty::AssignmentTargetPropertyIdentifier(property) => {
                    let key = Some(MemberKey::Name(property.binding.name.to_string()));

                    self.plan_property_read_of(file, property.span, key.clone(), &sources, plan);

                    excluded.extend(key);
                }
                AssignmentTargetProperty::AssignmentTargetPropertyProperty(property) => {
                    let key = self.property_key(file, &property.name, property.computed);
                    let child = self.plan_property_read_of(
                        file,
                        property.span,
                        key.clone(),
                        &sources,
                        plan,
                    );

                    excluded.extend(key);

                    self.plan_maybe_default_of(file, &property.binding, child, plan);
                }
            }
        }

        if let Some(rest) = &object.rest {
            self.plan_rest_reads_of((file, rest.span), &sources, &excluded, plan);
        }
    }

    fn plan_rest_reads_of(
        &mut self,
        (file, span): (FileId, Span),
        sources: &Sources<'a>,
        excluded: &[MemberKey],
        plan: &mut Vec<ImplicitSite>,
    ) {
        let mut receivers = Vec::new();
        let mut constant = !sources.open;
        let mut known = Vec::new();

        for (source, value) in sources.values.iter().copied() {
            for (key, getter) in self.literal_getters_of(source, value, 0) {
                if !excluded.contains(&key) && !known.contains(&getter) {
                    known.push(getter);
                }
            }

            constant &= self.is_closed(source, value);

            receivers.push(self.storage_value_of(source, value));
        }

        if !known.is_empty() {
            plan.push(ImplicitSite {
                file,
                span,
                targets: TargetSet { known, open: false },
                operation: "getter",
                receivers: Vec::new(),
                visits: None,
            });
        }

        if !self.may_access(None) {
            return;
        }

        plan.push(ImplicitSite {
            file,
            span,
            targets: TargetSet {
                known: Vec::new(),
                open: true,
            },
            operation: "getter",
            receivers,
            visits: (!constant).then_some(Some(Cost::N)),
        });
    }

    fn literal_getters_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        depth: usize,
    ) -> Vec<(MemberKey, FunctionId)> {
        if depth > MAXIMUM_RETURN_DEPTH || !self.charge_targets(1) {
            return Vec::new();
        }

        match unwrap(value) {
            Expression::ObjectExpression(object) => {
                let mut getters = Vec::new();

                if !self.charge_targets(object.properties.len() as u64) {
                    return getters;
                }

                for property in &object.properties {
                    let ObjectPropertyKind::ObjectProperty(property) = property else {
                        continue;
                    };
                    let Expression::FunctionExpression(getter) = &property.value else {
                        continue;
                    };

                    if property.kind != PropertyKind::Get {
                        continue;
                    }

                    if let Some(key) = self.property_key(file, &property.key, property.computed) {
                        getters.push((
                            key,
                            FunctionId {
                                file,
                                node: getter.node_id(),
                            },
                        ));
                    }
                }

                getters
            }
            _ => match self.constant_source_of(file, value) {
                Some((target, initializer)) => {
                    self.literal_getters_of(target, initializer, depth + 1)
                }
                None => Vec::new(),
            },
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

            let visits = self.iteration_count_of(source, value, &iteration);
            let [acquired, advanced, closed] =
                self.iteration_accessors_of(source, value, &iteration);
            let results = self.iteration_result_accessors_of(&iteration);
            let reads = [&acquired, &advanced, &closed, &results]
                .iter()
                .any(|targets| targets.open || !targets.known.is_empty());

            if !is_inert(&iteration) || reads || (!closes && visits.is_none()) {
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
                    visits: (!closes).then_some(visits.clone()),
                });

                for (targets, operation, repeated) in [
                    (acquired, "iterator acquisition getter", false),
                    (advanced, "iterator next getter", false),
                    (results, "iterator result getter", !closes),
                ] {
                    plan.push(ImplicitSite {
                        file: source,
                        span,
                        targets,
                        operation,
                        receivers: receivers.clone(),
                        visits: repeated.then_some(visits.clone()),
                    });
                }

                if closes {
                    plan.push(ImplicitSite {
                        file: source,
                        span,
                        targets: closed,
                        operation: "iterator close getter",
                        receivers: receivers.clone(),
                        visits: None,
                    });
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

    pub(crate) fn supplied_implicit_reading_of(
        &mut self,
        (file, span): (FileId, Span),
        targets: &TargetSet,
        operation: &str,
        supplied: Option<ArgumentFacts>,
        receivers: &[&'a Expression<'a>],
    ) -> Reading {
        let mut reading = Reading::empty();
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);

        for target in &targets.known {
            let copies = supplied
                .as_ref()
                .map_or(0, |facts| facts.value.targets.known.len()) as u64;

            if !self.charge_targets(1 + copies) {
                let unknown = self.unknown_part(
                    file,
                    span,
                    crate::unknowns::UnknownReason::ResourceExhaustion,
                );

                return match !reading.completions.is_empty() {
                    true => reading.retaining(unknown.unknowns, &mut self.unknowns),
                    false => Reading::of_part(unknown),
                };
            }

            let function = self.function_at(*target);
            let called = self.call_supplied(*target, (file, span), (vec![supplied.clone()], None));
            let called =
                self.explained_call_of((target.file, function), called, (site, origin), operation);
            reading = reading.merge(called, &mut self.unknowns, &mut self.traces);
        }

        if targets.open {
            let unknown = self.implicit_call_reading_of(
                (file, span),
                &TargetSet {
                    known: Vec::new(),
                    open: true,
                },
                operation,
                receivers,
            );
            reading = match targets.known.is_empty() {
                true => unknown,
                false => reading.retaining(unknown.main().unknowns, &mut self.unknowns),
            };
        }

        reading
    }

    pub(crate) fn implicit_call_reading_of(
        &mut self,
        (file, span): (FileId, Span),
        targets: &TargetSet,
        operation: &str,
        receivers: &[&'a Expression<'a>],
    ) -> Reading {
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
    ) -> Reading {
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);
        let mut part = Reading::empty();

        for known in &targets.known {
            let function = self.function_at(*known);
            let called = self.call_implicit(*known, file, span);
            let called =
                self.explained_call_of((known.file, function), called, (site, origin), operation);

            part = part.merge(called, &mut self.unknowns, &mut self.traces);
        }

        if !targets.open {
            return part;
        }

        let unknown = self.unknown_implicit_part(file, span, receivers);

        match targets.known.is_empty() {
            true => Reading::of_part(unknown),
            false => part.retaining(unknown.unknowns, &mut self.unknowns),
        }
    }

    fn explained_call_of(
        &mut self,
        (file, function): (FileId, FunctionNode<'a>),
        (called, cyclic): (Reading, bool),
        (site, origin): (crate::project::Site, crate::unknowns::SourceSpan),
        operation: &str,
    ) -> Reading {
        let called = called.map_parts(|called| match called.cost.is_one() {
            true => called,
            false => match self.trace_name_of(file, function) {
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
        });
        let called = called.called(origin, &mut self.unknowns);

        self.called_reading_of(file, function, called, cyclic)
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

    pub(crate) fn jsx_factory_part_of(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
    ) -> Option<Reading> {
        let (span, opening, children) = jsx_parts_of(kind)?;
        let runtime = self.project.jsx_runtime_of(file);
        let passed = self.jsx_passed_values_of(file, opening, children);
        let mut part = Reading::empty();

        if let JsxRuntime::Classic { factory, fragment } = &runtime {
            let fragment = opening.is_none().then_some(fragment);

            for names in std::iter::once(factory).chain(fragment) {
                let entity = self.entity_part_of(file, kind, names);

                part = part.merge(entity, &mut self.unknowns, &mut self.traces);
            }
        }

        let Some(((declaration, closed), shape)) = self.jsx_factory_of(file, kind, &runtime) else {
            let unknown = self.unknown_implicit_part(file, span, &passed);

            return Some(part.merge(unknown, &mut self.unknowns, &mut self.traces));
        };
        let declaration = declaration.map(|declaration| {
            self.declarations
                .executable_declaration(self.project, declaration)
        });
        let targets = self.resolved_of_declaration(declaration, closed).targets;

        if targets.known.is_empty() {
            let unknown = self.unknown_implicit_part(file, span, &passed);

            return Some(part.merge(unknown, &mut self.unknowns, &mut self.traces));
        }

        let arguments = self.jsx_arguments_of(file, kind, &runtime, shape);
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);
        let outer = std::mem::take(&mut self.current_effects);

        for known in &targets.known {
            let function = self.function_at(*known);
            let called = self.call_supplied(*known, (file, span), arguments.clone());
            let called = self.explained_call_of(
                (known.file, function),
                called,
                (site, origin),
                "jsx factory",
            );

            part = part.merge(called, &mut self.unknowns, &mut self.traces);
        }

        let effects = std::mem::replace(&mut self.current_effects, outer);
        let reached = effects.unknown_global
            || !effects.member_writes.is_empty()
            || !effects.unknown_reachable.is_empty();

        self.current_effects.join(&effects);

        for value in &passed {
            if !self.current_effects.escapes.contains(value) {
                self.current_effects.escapes.push(*value);
            }

            if reached && !self.current_effects.unknown_reachable.contains(value) {
                self.current_effects.unknown_reachable.push(*value);
            }
        }

        if !targets.open {
            return Some(part);
        }

        let unknown = self.unknown_implicit_part(file, span, &passed);

        Some(part.retaining(unknown.unknowns, &mut self.unknowns))
    }

    fn jsx_member_part_of(
        &mut self,
        file: FileId,
        member: &'a JSXMemberExpression<'a>,
    ) -> Option<Reading> {
        let nodes = self.project.file(file).semantic.nodes();

        if !matches!(
            nodes.parent_kind(member.node_id()),
            AstKind::JSXOpeningElement(_)
        ) {
            return None;
        }

        let mut members = vec![(
            member.span,
            MemberKey::Name(member.property.name.to_string()),
        )];
        let mut object = &member.object;
        let sources = loop {
            match object {
                JSXMemberExpressionObject::IdentifierReference(reference) => {
                    let source = self
                        .declarations
                        .of_reference(self.project, file, reference)
                        .and_then(constant_initializer_of);

                    break Sources {
                        open: source.is_none(),
                        values: source.into_iter().collect(),
                    };
                }
                JSXMemberExpressionObject::MemberExpression(inner) => {
                    members.push((inner.span, MemberKey::Name(inner.property.name.to_string())));

                    object = &inner.object;
                }
                JSXMemberExpressionObject::ThisExpression(_) => {
                    break Sources {
                        values: Vec::new(),
                        open: true,
                    }
                }
            }
        };

        Some(
            self.implicit_plan_part_of((file, member.node_id()), |analysis, plan| {
                let mut sources = sources;

                for (span, key) in members.into_iter().rev() {
                    sources = analysis.plan_property_read_of(file, span, Some(key), &sources, plan);
                }
            }),
        )
    }

    fn entity_part_of(&mut self, file: FileId, kind: AstKind<'a>, names: &[String]) -> Reading {
        let Some(root) = names.first() else {
            return Reading::empty();
        };
        let scope = self
            .project
            .file(file)
            .semantic
            .nodes()
            .get_node(kind.node_id())
            .scope_id();
        let (declaration, _) = self.declarations.scoped_entity_of(
            self.project,
            (file, scope),
            std::slice::from_ref(root),
        );
        let source = declaration.and_then(constant_initializer_of);
        let mut sources = Sources {
            open: source.is_none(),
            values: source.into_iter().collect(),
        };
        let mut plan = Vec::new();

        for name in names.iter().skip(1) {
            sources = self.plan_property_read_of(
                file,
                kind.span(),
                Some(MemberKey::Name(name.clone())),
                &sources,
                &mut plan,
            );
        }

        let mut part = Reading::empty();

        for planned in &plan {
            let found = self.planned_part_of(planned);

            part = part.merge(found, &mut self.unknowns, &mut self.traces);
        }

        part
    }

    fn jsx_factory_of(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
        runtime: &JsxRuntime,
    ) -> Option<((Option<Declaration<'a>>, bool), JsxShape)> {
        let (_, opening, children) = jsx_parts_of(kind)?;

        match runtime {
            JsxRuntime::Untransformed => None,
            JsxRuntime::Classic { factory, .. } => {
                let scope = self
                    .project
                    .file(file)
                    .semantic
                    .nodes()
                    .get_node(kind.node_id())
                    .scope_id();

                Some((
                    self.declarations
                        .scoped_entity_of(self.project, (file, scope), factory),
                    JsxShape::Positional,
                ))
            }
            JsxRuntime::Automatic { source, .. } if opening.is_some_and(has_key_after_spread) => {
                Some((
                    self.declarations.module_export_of(
                        self.project,
                        file,
                        (source, "createElement"),
                    ),
                    JsxShape::Positional,
                ))
            }
            JsxRuntime::Automatic {
                runtime,
                development,
                ..
            } => {
                let name = match (*development, has_static_children(children)) {
                    (true, _) => "jsxDEV",
                    (false, true) => "jsxs",
                    (false, false) => "jsx",
                };

                Some((
                    self.declarations
                        .module_export_of(self.project, file, (runtime, name)),
                    JsxShape::Properties,
                ))
            }
        }
    }

    fn jsx_arguments_of(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
        runtime: &JsxRuntime,
        shape: JsxShape,
    ) -> (Vec<Option<ArgumentFacts>>, Option<ArgumentFacts>) {
        let Some((span, opening, children)) = jsx_parts_of(kind) else {
            return (Vec::new(), None);
        };
        let scope = self
            .project
            .file(file)
            .semantic
            .nodes()
            .get_node(kind.node_id())
            .scope_id();
        let tag = self.jsx_tag_facts_of((file, scope), (span, opening), runtime);
        let spread = opening.is_some_and(|opening| {
            opening.attributes.iter().any(|attribute| match attribute {
                JSXAttributeItem::SpreadAttribute(spread) => !is_constant_spread(&spread.argument),
                JSXAttributeItem::Attribute(_) => false,
            })
        });
        let mut properties = self
            .values
            .allocation(self.source_span(file, opening.map_or(span, |opening| opening.span)));

        properties.size = (!spread).then_some(Cost::ONE);

        let mut supplied = vec![Some(tag), Some(defined_facts_of(properties))];
        let mut constant = true;

        match shape {
            JsxShape::Properties => supplied.push(Some(self.jsx_key_facts_of(file, opening))),
            JsxShape::Positional => {
                for child in children.iter().filter(|child| is_semantic_child(child)) {
                    if let JSXChild::Spread(_) = child {
                        constant = false;

                        break;
                    }

                    supplied.push(Some(self.jsx_child_facts_of(file, child)));
                }
            }
        }

        let mut collected = self.values.allocation(self.source_span(file, span));

        collected.size = constant.then_some(Cost::ONE);

        (supplied, Some(defined_facts_of(collected)))
    }

    fn jsx_tag_facts_of(
        &mut self,
        (file, scope): (FileId, ScopeId),
        (span, opening): (Span, Option<&'a JSXOpeningElement<'a>>),
        runtime: &JsxRuntime,
    ) -> ArgumentFacts {
        let span = opening.map_or(span, |opening| opening.name.span());
        let value = self.values.at(self.source_span(file, span));
        let unknown = ArgumentFacts {
            value: value.clone(),
            callback: None,
            preference: Preference::Absent,
            definedness: Definedness::Unknown,
        };
        let (declaration, closed) = match opening.map(|opening| &opening.name) {
            Some(JSXElementName::IdentifierReference(reference)) => self
                .declarations
                .callable_reference(self.project, file, reference),
            Some(JSXElementName::Identifier(_) | JSXElementName::NamespacedName(_)) => {
                return ArgumentFacts {
                    definedness: Definedness::Defined,
                    ..unknown
                }
            }
            Some(_) => return unknown,
            None => match runtime {
                JsxRuntime::Classic { fragment, .. } => {
                    self.declarations
                        .scoped_entity_of(self.project, (file, scope), fragment)
                }
                JsxRuntime::Automatic { runtime, .. } => {
                    self.declarations
                        .module_export_of(self.project, file, (runtime, "Fragment"))
                }
                JsxRuntime::Untransformed => return unknown,
            },
        };
        let function = declaration
            .map(|declaration| {
                self.declarations
                    .executable_declaration(self.project, declaration)
            })
            .and_then(|declaration| self.declarations.function_of(declaration));

        match function {
            Some((target, function)) => {
                self.callback_facts_of((file, span), value, (target, function), !closed)
            }
            None => unknown,
        }
    }

    fn jsx_key_facts_of(
        &mut self,
        file: FileId,
        opening: Option<&'a JSXOpeningElement<'a>>,
    ) -> ArgumentFacts {
        let key = opening.and_then(|opening| {
            opening
                .attributes
                .iter()
                .find_map(|attribute| match attribute {
                    JSXAttributeItem::Attribute(attribute) if attribute.is_key() => Some(attribute),
                    _ => None,
                })
        });

        match key.map(|key| (key.span, key.value.as_ref())) {
            None => ArgumentFacts {
                value: self.values.undefined(),
                callback: None,
                preference: Preference::Unmarked,
                definedness: Definedness::Undefined,
            },
            Some((_, Some(JSXAttributeValue::ExpressionContainer(container)))) => {
                self.container_facts_of(file, container)
            }
            Some((span, _)) => defined_facts_of(self.values.at(self.source_span(file, span))),
        }
    }

    fn container_facts_of(
        &mut self,
        file: FileId,
        container: &'a JSXExpressionContainer<'a>,
    ) -> ArgumentFacts {
        match container.expression.as_expression() {
            Some(expression) => self.expression_facts_of(file, expression.span(), Some(expression)),
            None => defined_facts_of(self.values.at(self.source_span(file, container.span))),
        }
    }

    fn jsx_child_facts_of(&mut self, file: FileId, child: &'a JSXChild<'a>) -> ArgumentFacts {
        match child {
            JSXChild::ExpressionContainer(container) => self.container_facts_of(file, container),
            JSXChild::Element(element) => {
                defined_facts_of(self.values.allocation(self.source_span(file, element.span)))
            }
            JSXChild::Fragment(fragment) => defined_facts_of(
                self.values
                    .allocation(self.source_span(file, fragment.span)),
            ),
            other => defined_facts_of(self.values.at(self.source_span(file, other.span()))),
        }
    }

    fn jsx_passed_values_of(
        &mut self,
        file: FileId,
        opening: Option<&'a JSXOpeningElement<'a>>,
        children: &'a [JSXChild<'a>],
    ) -> Vec<ValueId> {
        let mut expressions: Vec<&'a Expression<'a>> = Vec::new();
        let mut values = Vec::new();

        if let Some(opening) = opening {
            let reference = match &opening.name {
                JSXElementName::IdentifierReference(reference) => Some(&**reference),
                JSXElementName::MemberExpression(member) => {
                    let mut object = &member.object;

                    loop {
                        match object {
                            JSXMemberExpressionObject::IdentifierReference(reference) => {
                                break Some(&**reference)
                            }
                            JSXMemberExpressionObject::MemberExpression(inner) => {
                                object = &inner.object
                            }
                            JSXMemberExpressionObject::ThisExpression(_) => break None,
                        }
                    }
                }
                _ => None,
            };

            if let Some(reference) = reference {
                values.push(self.reference_storage_value_of(file, reference));
            }

            for attribute in &opening.attributes {
                match attribute {
                    JSXAttributeItem::SpreadAttribute(spread) => expressions.push(&spread.argument),
                    JSXAttributeItem::Attribute(attribute) => {
                        if let Some(JSXAttributeValue::ExpressionContainer(container)) =
                            &attribute.value
                        {
                            expressions.extend(container.expression.as_expression());
                        }
                    }
                }
            }
        }

        for child in children {
            match child {
                JSXChild::ExpressionContainer(container) => {
                    expressions.extend(container.expression.as_expression());
                }
                JSXChild::Spread(spread) => expressions.push(&spread.expression),
                _ => {}
            }
        }

        for expression in expressions {
            let value = self.storage_value_of(file, expression);

            if !values.contains(&value) {
                values.push(value);
            }
        }

        values
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum JsxShape {
    Positional,
    Properties,
}

type JsxParts<'a> = (Span, Option<&'a JSXOpeningElement<'a>>, &'a [JSXChild<'a>]);

struct JsxProperty {
    key: Option<MemberKey>,
    kind: PropertyKind,
    getter: Option<FunctionId>,
}

fn join_jsx_getters(targets: &mut TargetSet, properties: &[JsxProperty], copied: bool) {
    if !copied {
        return;
    }

    for (index, property) in properties.iter().enumerate() {
        let Some(getter) = property.getter else {
            continue;
        };
        let later: Vec<_> = properties[index + 1..]
            .iter()
            .filter(|later| later.kind != PropertyKind::Set)
            .collect();

        if property.key.is_some() && later.iter().any(|later| later.key == property.key) {
            continue;
        }

        if property.key.is_none() && !later.is_empty()
            || later.iter().any(|later| later.key.is_none())
        {
            targets.open = true;
        }

        targets.known.push(getter);
    }
}

fn jsx_parts_of<'a>(kind: AstKind<'a>) -> Option<JsxParts<'a>> {
    match kind {
        AstKind::JSXElement(element) => Some((
            element.span,
            Some(&*element.opening_element),
            &element.children,
        )),
        AstKind::JSXFragment(fragment) => Some((fragment.span, None, &fragment.children)),
        _ => None,
    }
}

fn is_semantic_child(child: &JSXChild<'_>) -> bool {
    match child {
        JSXChild::Text(text) => {
            !(text.value.trim().is_empty() && text.value.contains(['\n', '\r']))
        }
        JSXChild::ExpressionContainer(container) => {
            !matches!(container.expression, JSXExpression::EmptyExpression(_))
        }
        _ => true,
    }
}

pub(crate) fn is_inlined_spread(argument: &Expression<'_>) -> bool {
    let Expression::ObjectExpression(object) = argument else {
        return false;
    };

    !object.properties.iter().any(|property| match property {
        ObjectPropertyKind::ObjectProperty(property) => {
            !property.computed
                && !property.shorthand
                && !property.method
                && property.kind == PropertyKind::Init
                && property.key.static_name().as_deref() == Some("__proto__")
        }
        ObjectPropertyKind::SpreadProperty(_) => false,
    })
}

fn is_constant_spread(argument: &Expression<'_>) -> bool {
    match argument {
        Expression::ObjectExpression(object) => {
            is_inlined_spread(argument)
                && !object
                    .properties
                    .iter()
                    .any(|property| matches!(property, ObjectPropertyKind::SpreadProperty(_)))
        }
        _ => false,
    }
}

fn has_static_children(children: &[JSXChild<'_>]) -> bool {
    let mut semantic = children.iter().filter(|child| is_semantic_child(child));

    matches!(
        (semantic.next(), semantic.next()),
        (Some(_), Some(_)) | (Some(JSXChild::Spread(_)), None)
    )
}

fn defined_facts_of(value: ValueFacts) -> ArgumentFacts {
    ArgumentFacts {
        value,
        callback: None,
        preference: Preference::Absent,
        definedness: Definedness::Defined,
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

fn checked_constructor_of<'a>(kind: AstKind<'a>) -> Option<&'a Expression<'a>> {
    match kind {
        AstKind::BinaryExpression(binary) if binary.operator == BinaryOperator::Instanceof => {
            Some(&binary.right)
        }
        _ => None,
    }
}

fn awaited_operand_of<'a>(kind: AstKind<'a>) -> Option<&'a Expression<'a>> {
    match kind {
        AstKind::AwaitExpression(awaited) => Some(&awaited.argument),
        _ => None,
    }
}

fn accessed_object_of<'a>(kind: AstKind<'a>) -> Option<&'a Expression<'a>> {
    match kind {
        AstKind::StaticMemberExpression(member) => Some(&member.object),
        AstKind::ComputedMemberExpression(member) => Some(&member.object),
        AstKind::PrivateFieldExpression(member) => Some(&member.object),
        _ => None,
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn resolved_promise_reading_of(
        &mut self,
        file: FileId,
        span: Span,
        arguments: &'a [Argument<'a>],
    ) -> Reading {
        match arguments.first() {
            None => Reading::empty(),
            Some(argument) => match argument.as_expression() {
                Some(expression) => self.assimilated_reading_of(file, expression),
                None => Reading::of_part(self.unknown_part(file, span, UnknownReason::Target)),
            },
        }
    }

    pub(crate) fn assimilated_reading_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Reading {
        if self.is_primitive_operand(file, expression) {
            return Reading::empty();
        }

        let key = MemberKey::Name("then".to_string());
        let accessors = self.property_accessors_of((file, expression), key.clone(), false);

        if self.is_intrinsic_promise(file, expression) {
            let replacement =
                self.protocol_targets_of(file, expression, std::slice::from_ref(&key));

            if replacement.known.is_empty()
                && !replacement.open
                && accessors.known.is_empty()
                && !accessors.open
            {
                return Reading::empty();
            }
        }

        if !self.enter_promise_assimilation(file, expression.node_id()) {
            return Reading::of_part(self.unknown_part(
                file,
                expression.span(),
                UnknownReason::ResourceExhaustion,
            ));
        }

        let getter = self.implicit_call_reading_of(
            (file, expression.span()),
            &accessors,
            "promise then getter",
            &[expression],
        );
        let mut reading = getter;
        let (values, open) = self.property_values_of((file, expression), &key);
        let targets = self.protocol_targets_of(file, expression, std::slice::from_ref(&key));
        let settlers = self.promise_settlers_of(file, expression.span());
        let mut callbacks = Vec::new();

        for (source, value) in values {
            if self.is_primitive_operand(source, value)
                || self.is_non_callable_expression(source, value)
                || matches!(
                    unwrap(value),
                    Expression::ObjectExpression(_) | Expression::ArrayExpression(_)
                )
            {
                continue;
            }

            let facts = self.expression_facts_of(source, value.span(), Some(value));

            callbacks.push(facts);
        }

        for target in &targets.known {
            if accessors.known.contains(target)
                || callbacks
                    .iter()
                    .any(|facts| facts.value.targets.known.contains(target))
            {
                continue;
            }

            let function = self.function_at(*target);
            let value = self.values.at(self.source_span(file, expression.span()));
            let facts = self.callback_facts_of(
                (file, expression.span()),
                value,
                (target.file, function),
                false,
            );

            callbacks.push(facts);
        }

        for facts in callbacks {
            let invoked =
                self.invoke_callback_with_facts(&facts, file, expression.span(), &settlers, false);
            let invoked = invoked.in_phase(
                ExecutionPhase::Scheduled,
                &mut self.unknowns,
                &mut self.traces,
            );

            reading = reading.merge(invoked, &mut self.unknowns, &mut self.traces);
        }

        let builtin = !matches!(
            self.proven_kind(file, expression),
            Kind::Unknown | Kind::Other
        );

        if targets.open || (open && !builtin) {
            let unknown = self.unknown_part(file, expression.span(), UnknownReason::Target);

            reading = reading.merge(
                Reading::of_part(unknown).in_phase(
                    ExecutionPhase::Scheduled,
                    &mut self.unknowns,
                    &mut self.traces,
                ),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        self.leave_promise_assimilation(file, expression.node_id());

        reading
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn has_native_iteration(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
    ) -> bool {
        if !iteration.native
            || iteration.acquire.open
            || iteration.next.open
            || !iteration.acquire.known.is_empty()
            || !iteration.next.known.is_empty()
        {
            return false;
        }

        let [acquired, advanced, _] = self.iteration_accessors_of(file, iterable, iteration);

        !acquired.open && !advanced.open && acquired.known.is_empty() && advanced.known.is_empty()
    }

    pub(crate) fn iteration_count_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
    ) -> Option<Cost> {
        self.iteration_count_at(file, iterable, iteration, 0)
    }

    pub(crate) fn iteration_count_at(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
        depth: usize,
    ) -> Option<Cost> {
        if depth > 32 || !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
            return None;
        }

        if iteration.acquire.open || iteration.next.open {
            return None;
        }

        let [acquired, advanced, _] = self.iteration_accessors_of(file, iterable, iteration);

        if acquired.open
            || advanced.open
            || (!acquired.known.is_empty() && iteration.acquire.known.is_empty())
            || (!advanced.known.is_empty() && iteration.next.known.is_empty())
        {
            return None;
        }

        if let Some(latent) = self.iteration_latent_of(file, iterable, iteration) {
            return match iteration.next.known.is_empty() {
                true => latent.yields,
                false => None,
            };
        }

        if iteration.next.known.is_empty() && !iteration.acquire.known.is_empty() {
            let mut counts = Vec::new();

            for target in &iteration.acquire.known {
                if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                    return None;
                }

                let returned = self.returned_expressions_of(*target);

                if returned.is_empty() {
                    return None;
                }

                for expression in returned {
                    if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                        return None;
                    }

                    let source = self.intrinsic_iteration_source_of(target.file, expression)?;
                    let source_iteration = self.iteration_of(target.file, source, false);

                    counts.push(self.iteration_count_at(
                        target.file,
                        source,
                        &source_iteration,
                        depth + 1,
                    )?);
                }
            }

            return Cost::maximum(counts).ok();
        }

        if iteration.native && iteration.next.known.is_empty() {
            let size = self.collection_size_at(file, iterable, depth + 1);

            if !size.length_resolved {
                return None;
            }

            if size.exceeds {
                return Some(size.length);
            }

            if self.is_constant_sized(file, iterable) || self.is_share_sized(file, iterable) {
                return Some(Cost::ONE);
            }

            return Some(match size.length.is_one() {
                true => self.count_of(file, iterable).unwrap_or(Cost::N),
                false => size.length,
            });
        }

        if iteration.next.known.is_empty() {
            return None;
        }

        iteration
            .next
            .known
            .iter()
            .all(|target| self.finishes_iteration_of(*target, iteration.asynchronous))
            .then_some(Cost::ONE)
    }

    fn finishes_iteration_of(&mut self, target: FunctionId, asynchronous: bool) -> bool {
        if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
            return false;
        }

        match self.function_at(target) {
            FunctionNode::Function(function)
                if function.generator || (function.r#async && !asynchronous) =>
            {
                return false
            }
            FunctionNode::Arrow(arrow) if arrow.r#async && !asynchronous => return false,
            _ => {}
        }

        let returned = self.returned_expressions_of(target);

        !returned.is_empty() && returned.into_iter().all(|expression| {
            let Expression::ObjectExpression(object) = unwrap(expression) else {
                return false;
            };

            if asynchronous {
                let key = MemberKey::Name("then".to_string());
                let accessors = self.property_accessors_of((target.file, expression), key.clone(), false);
                let then = self.protocol_targets_of(target.file, expression, &[key]);

                if accessors.open || !accessors.known.is_empty() || then.open || !then.known.is_empty() {
                    return false;
                }
            }

            for property in object.properties.iter().rev() {
                if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                    return false;
                }

                let ObjectPropertyKind::ObjectProperty(property) = property else {
                    return false;
                };

                if property.computed {
                    return false;
                }

                if property.key.static_name().as_deref() == Some("done") {
                    return property.kind == PropertyKind::Init
                        && matches!(unwrap(&property.value), Expression::BooleanLiteral(value) if value.value);
                }
            }

            false
        })
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn iteration_effect_targets_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
    ) -> Vec<TargetSet> {
        let [acquired, advanced, closed] = self.iteration_accessors_of(file, iterable, iteration);
        let results = self.iteration_result_accessors_of(iteration);

        vec![
            iteration.acquire.clone(),
            iteration.next.clone(),
            iteration.close.clone(),
            acquired,
            advanced,
            closed,
            results,
        ]
    }

    fn iteration_accessors_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        iteration: &Iteration,
    ) -> [TargetSet; 3] {
        let mut found = std::array::from_fn(|_| TargetSet {
            known: Vec::new(),
            open: false,
        });
        let keys: &[&str] = match iteration.asynchronous {
            true => &["asyncIterator", "iterator"],
            false => &["iterator"],
        };

        for key in keys {
            let accessors = self.iterator_accessors_on(
                file,
                iterable,
                MemberKey::WellKnown((*key).to_string()),
            );

            self.merge_iterator_targets(&mut found[0], accessors);
        }

        for target in &iteration.acquire.known {
            if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                for targets in &mut found {
                    targets.open = true;
                }

                return found;
            }

            if matches!(self.function_at(*target), FunctionNode::Function(function) if function.generator)
            {
                continue;
            }

            for returned in self.returned_expressions_of(*target) {
                if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                    for targets in &mut found {
                        targets.open = true;
                    }

                    return found;
                }

                for (index, key) in [(1, "next"), (2, "return")] {
                    let accessors = self.property_accessors_of(
                        (target.file, returned),
                        MemberKey::Name(key.to_string()),
                        false,
                    );

                    self.merge_iterator_targets(&mut found[index], accessors);
                }
            }
        }

        if iteration.acquire.known.is_empty() && !iteration.acquire.open {
            for (index, key) in [(1, "next"), (2, "return")] {
                let accessors = self.intrinsic_iterator_accessors_of(key);

                self.merge_iterator_targets(&mut found[index], accessors);
            }
        }

        found
    }

    fn iteration_result_accessors_of(&mut self, iteration: &Iteration) -> TargetSet {
        let mut found = TargetSet {
            known: Vec::new(),
            open: false,
        };

        for target in &iteration.next.known {
            if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                found.open = true;

                return found;
            }

            let finished = self.finishes_iteration_of(*target, iteration.asynchronous);

            for returned in self.returned_expressions_of(*target) {
                if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                    found.open = true;

                    return found;
                }

                for key in ["done", "value"] {
                    if key == "value" && finished {
                        continue;
                    }

                    let accessors = self.property_accessors_of(
                        (target.file, returned),
                        MemberKey::Name(key.to_string()),
                        false,
                    );

                    self.merge_iterator_targets(&mut found, accessors);
                }
            }
        }

        found
    }
}

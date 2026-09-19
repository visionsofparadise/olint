use oxc_ast::ast::{
    Argument, AssignmentTarget, AssignmentTargetMaybeDefault, AssignmentTargetProperty,
    ClassElement, Expression, ForStatementLeft, MemberExpression, MethodDefinitionKind,
    NewExpression, SimpleAssignmentTarget, Statement,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::UnaryOperator;

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::constants::constant_initializer_of;
use crate::declarations::{Binding, Declaration, FunctionId};
use crate::project::FileId;
use crate::syntax::{
    body_root_of, is_iteration_kind, loop_body_of, member_expression_of, unwrap, Root,
};
use crate::tables::LINEAR_CONSTRUCTORS;
use crate::types::ResolvedCallee;
use crate::values::{is_direct_call, ValueId};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Effects {
    pub binding_writes: Vec<Binding>,
    pub member_writes: Vec<ValueId>,
    pub escapes: Vec<ValueId>,
    pub unknown_reachable: Vec<ValueId>,
    pub unknown_global: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueFlow {
    Read,
    Member,
    Receiver(NodeId),
    Alias(NodeId),
    Stored(NodeId),
    Argument(NodeId, usize),
    Escaped(NodeId),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Invalidation {
    pub bound: bool,
    pub budget: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Storage {
    bindings: Vec<Binding>,
    values: Vec<(ValueId, Option<Binding>)>,
    unresolved: bool,
    calls: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Writes {
    All,
    Qualified,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Prepass {
    Loop,
    Skipped,
}

const CONSTANT_GLOBALS: [&str; 3] = ["undefined", "NaN", "Infinity"];
const FRESH_CONSTRUCTORS: [&str; 5] = ["Date", "Error", "RegExp", "Promise", "ArrayBuffer"];
const MAXIMUM_ALIAS_DEPTH: usize = 8;

pub fn value_flow_of(nodes: &AstNodes<'_>, node: NodeId) -> ValueFlow {
    let mut current = node;
    let mut contained = false;

    loop {
        let span = nodes.kind(current).span();
        let parent = nodes.parent_id(current);

        if parent == current {
            return ValueFlow::Escaped(current);
        }

        match nodes.kind(parent) {
            AstKind::ParenthesizedExpression(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSTypeAssertion(_)
            | AstKind::TSInstantiationExpression(_)
            | AstKind::LogicalExpression(_) => current = parent,
            AstKind::ArrayExpression(_) => {
                contained = true;
                current = parent;
            }
            AstKind::ConditionalExpression(conditional) if conditional.test.span() == span => {
                return ValueFlow::Read
            }
            AstKind::ConditionalExpression(_) => current = parent,
            AstKind::SequenceExpression(sequence) => {
                if sequence.expressions.last().map(GetSpan::span) != Some(span) {
                    return ValueFlow::Read;
                }

                current = parent;
            }
            AstKind::ObjectProperty(property) if property.value.span() == span => {
                contained = true;
                current = nodes.parent_id(parent);
            }
            AstKind::ObjectProperty(_) => return ValueFlow::Read,
            AstKind::SpreadElement(_) => {
                return match nodes.parent_kind(parent) {
                    AstKind::CallExpression(_) | AstKind::NewExpression(_) => {
                        ValueFlow::Escaped(nodes.parent_id(parent))
                    }
                    _ => ValueFlow::Read,
                }
            }
            AstKind::StaticMemberExpression(member) if member.object.span() == span => {
                return member_flow_of(nodes, parent, member.span, contained)
            }
            AstKind::ComputedMemberExpression(member) if member.object.span() == span => {
                return member_flow_of(nodes, parent, member.span, contained)
            }
            AstKind::PrivateFieldExpression(member) if member.object.span() == span => {
                return member_flow_of(nodes, parent, member.span, contained)
            }
            AstKind::StaticMemberExpression(_)
            | AstKind::ComputedMemberExpression(_)
            | AstKind::PrivateFieldExpression(_) => return ValueFlow::Read,
            AstKind::CallExpression(call) => {
                return argument_flow_of(&call.arguments, span, parent)
            }
            AstKind::NewExpression(new) => return argument_flow_of(&new.arguments, span, parent),
            AstKind::VariableDeclarator(declarator)
                if declarator.init.as_ref().map(GetSpan::span) == Some(span) =>
            {
                return ValueFlow::Alias(parent)
            }
            AstKind::AssignmentExpression(assignment) if assignment.right.span() == span => {
                return match &assignment.left {
                    AssignmentTarget::AssignmentTargetIdentifier(_)
                    | AssignmentTarget::ArrayAssignmentTarget(_)
                    | AssignmentTarget::ObjectAssignmentTarget(_) => ValueFlow::Alias(parent),
                    _ => ValueFlow::Stored(parent),
                }
            }
            AstKind::ForOfStatement(statement) if statement.right.span() == span => {
                return ValueFlow::Alias(parent)
            }
            AstKind::AssignmentTargetWithDefault(target) if target.init.span() == span => {
                return ValueFlow::Alias(parent)
            }
            AstKind::AssignmentTargetPropertyIdentifier(property)
                if property.init.as_ref().map(GetSpan::span) == Some(span) =>
            {
                return ValueFlow::Alias(parent)
            }
            AstKind::AssignmentExpression(_)
            | AstKind::ExpressionStatement(_)
            | AstKind::VariableDeclarator(_)
            | AstKind::ForOfStatement(_)
            | AstKind::ForInStatement(_)
            | AstKind::BinaryExpression(_)
            | AstKind::UnaryExpression(_)
            | AstKind::UpdateExpression(_)
            | AstKind::TemplateLiteral(_)
            | AstKind::IfStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
            | AstKind::ForStatement(_)
            | AstKind::SwitchStatement(_)
            | AstKind::SwitchCase(_)
            | AstKind::ExportSpecifier(_)
            | AstKind::ExportDefaultDeclaration(_)
            | AstKind::TSExportAssignment(_)
            | AstKind::ArrayAssignmentTarget(_)
            | AstKind::ObjectAssignmentTarget(_)
            | AstKind::AssignmentTargetWithDefault(_)
            | AstKind::AssignmentTargetPropertyIdentifier(_)
            | AstKind::AssignmentTargetPropertyProperty(_)
            | AstKind::AssignmentTargetRest(_)
            | AstKind::TSTypeQuery(_)
            | AstKind::TSQualifiedName(_) => return ValueFlow::Read,
            _ => return ValueFlow::Escaped(parent),
        }
    }
}

fn argument_flow_of(arguments: &[Argument<'_>], span: Span, call: NodeId) -> ValueFlow {
    match arguments
        .iter()
        .position(|argument| argument.span() == span)
    {
        Some(index) => ValueFlow::Argument(call, index),
        None => ValueFlow::Read,
    }
}

fn member_flow_of(nodes: &AstNodes<'_>, member: NodeId, span: Span, contained: bool) -> ValueFlow {
    let mut current = member;
    let mut current_span = span;

    loop {
        let parent = nodes.parent_id(current);

        match nodes.kind(parent) {
            AstKind::ParenthesizedExpression(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSTypeAssertion(_) => {
                current = parent;
                current_span = nodes.kind(parent).span();
            }
            AstKind::CallExpression(call) if call.callee.span() == current_span => {
                return match contained {
                    true => ValueFlow::Escaped(parent),
                    false => ValueFlow::Receiver(parent),
                }
            }
            AstKind::TaggedTemplateExpression(tagged) if tagged.tag.span() == current_span => {
                return match contained {
                    true => ValueFlow::Escaped(parent),
                    false => ValueFlow::Receiver(parent),
                }
            }
            _ => {
                return match contained {
                    true => ValueFlow::Escaped(member),
                    false => ValueFlow::Member,
                }
            }
        }
    }
}

impl Storage {
    fn merge(&mut self, other: Storage) {
        for binding in other.bindings {
            push_binding(&mut self.bindings, binding);
        }

        for value in other.values {
            if !self.values.contains(&value) {
                self.values.push(value);
            }
        }

        self.unresolved |= other.unresolved;
        self.calls |= other.calls;
    }
}

impl Effects {
    pub fn unknown() -> Self {
        Self {
            unknown_global: true,
            ..Self::default()
        }
    }

    pub fn is_empty(&self) -> bool {
        self.binding_writes.is_empty()
            && self.member_writes.is_empty()
            && self.escapes.is_empty()
            && self.unknown_reachable.is_empty()
            && !self.unknown_global
    }

    pub fn join(&mut self, other: &Self) {
        for binding in &other.binding_writes {
            if !self.binding_writes.contains(binding) {
                self.binding_writes.push(*binding);
            }
        }

        for (ours, theirs) in [
            (&mut self.member_writes, &other.member_writes),
            (&mut self.escapes, &other.escapes),
            (&mut self.unknown_reachable, &other.unknown_reachable),
        ] {
            for value in theirs {
                if !ours.contains(value) {
                    ours.push(*value);
                }
            }
        }

        self.unknown_global |= other.unknown_global;
    }

    pub fn substitute(&mut self, parameter: ValueId, argument: ValueId) {
        for values in [
            &mut self.member_writes,
            &mut self.escapes,
            &mut self.unknown_reachable,
        ] {
            let mut substituted = false;

            values.retain(|value| {
                let matched = *value == parameter;

                substituted |= matched;

                !matched
            });

            if substituted && !values.contains(&argument) {
                values.push(argument);
            }
        }
    }
}

fn push_binding(bindings: &mut Vec<Binding>, binding: Binding) {
    if !bindings.contains(&binding) {
        bindings.push(binding);
    }
}

fn push_value(values: &mut Vec<ValueId>, value: ValueId) {
    if !values.contains(&value) {
        values.push(value);
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn storage_value_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> ValueId {
        let mut file = file;
        let mut expression = unwrap(expression);

        for _ in 0..MAXIMUM_ALIAS_DEPTH {
            match expression {
                Expression::Identifier(reference) => {
                    let declaration = self
                        .declarations
                        .of_reference(self.project, file, reference);

                    match declaration.and_then(constant_initializer_of) {
                        Some((target, initializer)) => {
                            file = target;
                            expression = unwrap(initializer);
                        }
                        None => {
                            return match declaration {
                                Some(declaration) => {
                                    self.declared_value_of(declaration, file, reference.span)
                                }
                                None => {
                                    self.values.at(self.source_span(file, reference.span)).value
                                }
                            }
                        }
                    }
                }
                Expression::ObjectExpression(_)
                | Expression::ArrayExpression(_)
                | Expression::FunctionExpression(_)
                | Expression::ArrowFunctionExpression(_)
                | Expression::ClassExpression(_)
                | Expression::RegExpLiteral(_) => {
                    return self
                        .values
                        .allocation(self.source_span(file, expression.span()))
                        .value
                }
                Expression::NewExpression(new) if self.is_fresh_construction(file, new) => {
                    return self
                        .values
                        .allocation(self.source_span(file, expression.span()))
                        .value
                }
                _ => {
                    return self
                        .values
                        .at(self.source_span(file, expression.span()))
                        .value
                }
            }
        }

        self.values
            .at(self.source_span(file, expression.span()))
            .value
    }

    fn is_fresh_construction(&mut self, file: FileId, new: &'a NewExpression<'a>) -> bool {
        let Expression::Identifier(reference) = unwrap(&new.callee) else {
            return false;
        };
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference);

        match declaration {
            None => {
                LINEAR_CONSTRUCTORS.contains(&reference.name.as_str())
                    || FRESH_CONSTRUCTORS.contains(&reference.name.as_str())
                    || (reference.name == "Object" && new.arguments.is_empty())
            }
            Some(Declaration::Class { file, class }) if class.heritage.is_none() => {
                let constructor = class.body.body.iter().find_map(|element| match element {
                    ClassElement::MethodDefinition(method)
                        if method.kind == MethodDefinitionKind::Constructor =>
                    {
                        method.value.body.as_deref()
                    }
                    _ => None,
                });
                let Some(body) = constructor else {
                    return true;
                };
                let kinds = self.counted_subtree(file, Root::Body(body), Event::EffectPrepassNode);

                !self.work_exhausted()
                    && kinds.iter().all(|kind| match kind {
                        AstKind::ReturnStatement(statement) => {
                            statement.argument.as_ref().is_none_or(|argument| {
                                matches!(unwrap(argument), Expression::ThisExpression(_))
                            })
                        }
                        _ => true,
                    })
            }
            _ => false,
        }
    }

    fn declared_value_of(
        &mut self,
        declaration: Declaration<'a>,
        file: FileId,
        span: Span,
    ) -> ValueId {
        match declaration {
            Declaration::Variable {
                file, declarator, ..
            } => {
                self.values
                    .at(self.source_span(file, declarator.id.span()))
                    .value
            }
            Declaration::Parameter {
                file,
                parameter: crate::declarations::ParameterNode::Formal(parameter),
                ..
            } => {
                self.values
                    .at(self.source_span(file, parameter.pattern.span()))
                    .value
            }
            Declaration::Parameter {
                file,
                parameter: crate::declarations::ParameterNode::Rest(parameter),
                ..
            } => {
                self.values
                    .at(self.source_span(file, parameter.rest.argument.span()))
                    .value
            }
            Declaration::Function { file, function } => {
                let span = self.kind_of_node(file, function.node_id()).span();

                self.values.allocation(self.source_span(file, span)).value
            }
            Declaration::Class { file, class } => {
                self.values
                    .allocation(self.source_span(file, class.span))
                    .value
            }
            _ => self.values.at(self.source_span(file, span)).value,
        }
    }

    pub(crate) fn record_write_effects(&mut self, file: FileId, kind: AstKind<'a>) {
        self.record_writes(file, kind, Writes::All);
    }

    fn record_writes(&mut self, file: FileId, kind: AstKind<'a>, writes: Writes) {
        match kind {
            AstKind::AssignmentExpression(assignment) => {
                self.record_target_writes(file, &assignment.left, writes)
            }
            AstKind::UpdateExpression(update) => {
                self.record_simple_target_write(file, &update.argument, writes)
            }
            AstKind::UnaryExpression(unary) if unary.operator == UnaryOperator::Delete => {
                if let Some(member) = member_expression_of(unwrap(&unary.argument)) {
                    self.record_member_write(file, member);
                }
            }
            AstKind::ForInStatement(statement) => {
                self.record_left_writes(file, &statement.left, writes)
            }
            AstKind::ForOfStatement(statement) => {
                self.record_left_writes(file, &statement.left, writes)
            }
            _ => {}
        }
    }

    fn record_left_writes(&mut self, file: FileId, left: &'a ForStatementLeft<'a>, _: Writes) {
        if let Some(target) = left.as_assignment_target() {
            self.record_target_writes(file, target, Writes::All);
        }
    }

    fn record_target_writes(
        &mut self,
        file: FileId,
        target: &'a AssignmentTarget<'a>,
        writes: Writes,
    ) {
        if let Some(simple) = target.as_simple_assignment_target() {
            return self.record_simple_target_write(file, simple, writes);
        }

        let writes = Writes::All;

        match target {
            AssignmentTarget::ArrayAssignmentTarget(array) => {
                for element in array.elements.iter().flatten() {
                    self.record_maybe_default_writes(file, element, writes);
                }

                if let Some(rest) = &array.rest {
                    self.record_target_writes(file, &rest.target, writes);
                }
            }
            AssignmentTarget::ObjectAssignmentTarget(object) => {
                for property in &object.properties {
                    match property {
                        AssignmentTargetProperty::AssignmentTargetPropertyIdentifier(property) => {
                            self.record_binding_write(file, &property.binding, writes)
                        }
                        AssignmentTargetProperty::AssignmentTargetPropertyProperty(property) => {
                            self.record_maybe_default_writes(file, &property.binding, writes)
                        }
                    }
                }

                if let Some(rest) = &object.rest {
                    self.record_target_writes(file, &rest.target, writes);
                }
            }
            _ => {}
        }
    }

    fn record_maybe_default_writes(
        &mut self,
        file: FileId,
        target: &'a AssignmentTargetMaybeDefault<'a>,
        writes: Writes,
    ) {
        match target {
            AssignmentTargetMaybeDefault::AssignmentTargetWithDefault(target) => {
                self.record_target_writes(file, &target.binding, writes)
            }
            _ => {
                if let Some(target) = target.as_assignment_target() {
                    self.record_target_writes(file, target, writes);
                }
            }
        }
    }

    fn record_simple_target_write(
        &mut self,
        file: FileId,
        target: &'a SimpleAssignmentTarget<'a>,
        writes: Writes,
    ) {
        match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                self.record_binding_write(file, reference, writes)
            }
            SimpleAssignmentTarget::TSAsExpression(inner) => {
                self.record_expression_write(file, &inner.expression, Writes::All)
            }
            SimpleAssignmentTarget::TSSatisfiesExpression(inner) => {
                self.record_expression_write(file, &inner.expression, Writes::All)
            }
            SimpleAssignmentTarget::TSNonNullExpression(inner) => {
                self.record_expression_write(file, &inner.expression, Writes::All)
            }
            SimpleAssignmentTarget::TSTypeAssertion(inner) => {
                self.record_expression_write(file, &inner.expression, Writes::All)
            }
            _ => {
                if let Some(member) = target.as_member_expression() {
                    self.record_member_write(file, member);
                }
            }
        }
    }

    fn record_expression_write(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        writes: Writes,
    ) {
        match unwrap(expression) {
            Expression::Identifier(reference) => self.record_binding_write(file, reference, writes),
            other => match member_expression_of(other) {
                Some(member) => self.record_member_write(file, member),
                None => self.current_effects.unknown_global = true,
            },
        }
    }

    fn record_binding_write(
        &mut self,
        file: FileId,
        reference: &'a oxc_ast::ast::IdentifierReference<'a>,
        writes: Writes,
    ) {
        match self.binding_of_identifier(file, reference) {
            Some(binding) => {
                if writes == Writes::All {
                    push_binding(&mut self.current_effects.binding_writes, binding);
                }
            }
            None => self.current_effects.unknown_global = true,
        }
    }

    fn record_member_write(&mut self, file: FileId, member: &'a MemberExpression<'a>) {
        let object = member.object();
        let value = self.storage_value_of(file, object);

        push_value(&mut self.current_effects.member_writes, value);

        match member {
            MemberExpression::StaticMemberExpression(access) => {
                if let Some(binding) = self.declarations.binding_of_access(
                    self.project,
                    file,
                    unwrap(object),
                    access.property.name.as_str(),
                ) {
                    push_binding(&mut self.current_effects.binding_writes, binding);
                }
            }
            _ => {
                if let Expression::Identifier(reference) = unwrap(object) {
                    if matches!(
                        self.declarations
                            .of_reference(self.project, file, reference),
                        Some(Declaration::Namespace { .. })
                    ) {
                        self.current_effects.unknown_global = true;
                    }
                }
            }
        }
    }

    pub(crate) fn record_unknown_reach(
        &mut self,
        file: FileId,
        callee: Option<&'a Expression<'a>>,
        arguments: &'a [Argument<'a>],
        span: Span,
    ) {
        let invoked = self.values.at(self.source_span(file, span)).value;

        if let Some(Expression::Identifier(reference)) = callee.map(unwrap) {
            if reference.name == "eval" && self.binding_of_identifier(file, reference).is_none() {
                self.current_effects.unknown_global = true;
            }
        }

        push_value(&mut self.current_effects.unknown_reachable, invoked);

        if let Some(member) = callee.map(unwrap).and_then(member_expression_of) {
            let receiver = self.storage_value_of(file, member.object());

            push_value(&mut self.current_effects.unknown_reachable, receiver);
            push_value(&mut self.current_effects.escapes, receiver);
        }

        for argument in arguments {
            let expression = match argument {
                Argument::SpreadElement(spread) => &spread.argument,
                other => match other.as_expression() {
                    Some(expression) => expression,
                    None => continue,
                },
            };
            let value = self.storage_value_of(file, expression);

            push_value(&mut self.current_effects.unknown_reachable, value);
            push_value(&mut self.current_effects.escapes, value);
        }
    }

    pub(crate) fn loop_invalidation_of(
        &mut self,
        file: FileId,
        loop_kind: AstKind<'a>,
    ) -> Invalidation {
        let repeated: Vec<&'a Expression<'a>> = match loop_kind {
            AstKind::WhileStatement(statement) => vec![&statement.test],
            AstKind::DoWhileStatement(statement) => vec![&statement.test],
            AstKind::ForStatement(statement) => statement
                .test
                .iter()
                .chain(statement.update.iter())
                .collect(),
            _ => Vec::new(),
        };
        let mut header = Effects::default();

        for expression in repeated {
            let effects = self.called_effects_in(file, Root::Expression(expression));

            header.join(&effects);
        }

        let mut effects = match loop_body_of(loop_kind) {
            Some(body) => self.called_effects_in(file, Root::Statement(body)),
            None => Effects::default(),
        };

        effects.join(&header);

        let mut invalidation = self.invalidation_of(file, loop_kind, &effects);

        invalidation.bound |= header.unknown_global || !header.unknown_reachable.is_empty();

        invalidation
    }

    fn called_effects_in(&mut self, file: FileId, root: Root<'a>) -> Effects {
        let saved = std::mem::take(&mut self.current_effects);

        self.prepass_effects_in(file, root);

        let effects = std::mem::replace(&mut self.current_effects, saved);

        self.current_effects.join(&effects);

        effects
    }

    fn prepass_effects_in(&mut self, file: FileId, root: Root<'a>) {
        if self.fallback_active() || self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return;
        }

        let kinds = self.counted_subtree(file, root, Event::EffectPrepassNode);

        if self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return;
        }

        self.prepass_effects_of(file, kinds, Prepass::Loop);
    }

    pub(crate) fn opaque_effects_at(&mut self, file: FileId, node: NodeId) -> bool {
        if self.fallback_active() || self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return true;
        }

        let mut pending = vec![node];
        let mut kinds = Vec::new();

        while let Some(node) = pending.pop() {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                self.current_effects.unknown_global = true;

                return true;
            }

            let kind = self.kind_of_node(file, node);

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                continue;
            }

            kinds.push(kind);
            pending.extend(self.children_of(file, node));
        }

        self.prepass_effects_of(file, kinds, Prepass::Skipped);

        self.current_effects.unknown_global
    }

    fn prepass_effects_of(&mut self, file: FileId, kinds: Vec<AstKind<'a>>, prepass: Prepass) {
        for kind in kinds {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                self.current_effects.unknown_global = true;

                return;
            }

            match prepass {
                Prepass::Skipped => self.record_writes(file, kind, Writes::All),
                Prepass::Loop => self.record_writes(file, kind, Writes::Qualified),
            }

            match kind {
                AstKind::CallExpression(call) => {
                    let ResolvedCallee {
                        declaration,
                        closed,
                        targets,
                    } = self.resolved_callee_of(file, call);

                    if let Some(Declaration::Parameter { .. }) = declaration {
                        let facts = self
                            .parameter_binding_of(declaration.unwrap())
                            .and_then(|binding| self.current_substitutions.get(&binding).cloned());

                        if let Some(facts) = &facts {
                            self.invoke_argument(facts, file, call.span, &call.arguments);
                        }

                        if facts.is_none() || !closed {
                            self.record_unknown_reach(
                                file,
                                Some(&call.callee),
                                &call.arguments,
                                call.span,
                            );
                        }
                    } else {
                        for target in &targets.known {
                            let function = self.function_at(*target);

                            self.call_user(target.file, function, file, &call.arguments, call.span);
                        }

                        if targets.open {
                            self.record_unknown_reach(
                                file,
                                Some(&call.callee),
                                &call.arguments,
                                call.span,
                            );
                        }
                    }
                }
                AstKind::NewExpression(new) => {
                    let targets = self.constructor_targets_of(file, new);

                    for target in &targets.known {
                        let function = self.function_at(*target);

                        self.call_user(target.file, function, file, &new.arguments, new.span);
                    }

                    if targets.known.is_empty() || targets.open {
                        self.record_unknown_reach(
                            file,
                            Some(&new.callee),
                            &new.arguments,
                            new.span,
                        );
                    }
                }
                _ => {}
            }

            if self.current_effects.unknown_global {
                return;
            }
        }
    }

    fn invalidation_of(
        &mut self,
        file: FileId,
        loop_kind: AstKind<'a>,
        effects: &Effects,
    ) -> Invalidation {
        if effects.unknown_global {
            return Invalidation {
                bound: true,
                budget: true,
            };
        }

        let function = self.enclosing_function_of(file, loop_kind.node_id());
        let nodes = self.project.file(file).semantic.nodes();
        let repeated = nodes
            .ancestors(loop_kind.node_id())
            .take_while(|ancestor| Some(ancestor.id()) != function)
            .filter(|ancestor| is_iteration_kind(&ancestor.kind()))
            .last()
            .map_or(loop_kind.node_id(), |ancestor| ancestor.id());
        let header = self.header_storage_of(file, loop_kind);
        let bound = self.affects(file, function, effects, &header, Some(repeated));
        let budget = match self.budget_storage_of() {
            Some(storage) => self.affects(file, function, effects, &storage, None),
            None => false,
        };

        Invalidation { bound, budget }
    }

    fn affects(
        &mut self,
        file: FileId,
        function: Option<NodeId>,
        effects: &Effects,
        storage: &Storage,
        repeated: Option<NodeId>,
    ) -> bool {
        let reached = !effects.unknown_reachable.is_empty();

        if reached && storage.unresolved {
            return true;
        }

        if storage.calls
            && (reached || !effects.binding_writes.is_empty() || !effects.member_writes.is_empty())
        {
            return true;
        }

        if storage
            .bindings
            .iter()
            .any(|binding| self.has_unclassified_write(*binding, repeated))
        {
            return true;
        }

        for binding in &storage.bindings {
            if effects.binding_writes.contains(binding)
                || (reached && !self.is_isolated_binding(file, function, *binding))
            {
                return true;
            }
        }

        for (value, holder) in &storage.values {
            if effects
                .member_writes
                .iter()
                .any(|written| self.values.may_alias(*written, *value))
            {
                return true;
            }

            if reached && !self.is_isolated_value(file, function, *value, *holder) {
                return true;
            }
        }

        false
    }

    fn header_storage_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Storage {
        let body = loop_body_of(loop_kind).map(|body| body.node_id());
        let mut storage = Storage::default();

        for child in self.children_of(file, loop_kind.node_id()) {
            if Some(child) != body {
                self.collect_storage(file, child, &mut storage);
            }
        }

        let iterated = match loop_kind {
            AstKind::ForOfStatement(statement) => Some(&statement.right),
            AstKind::ForInStatement(statement) => Some(&statement.right),
            _ => None,
        };

        if let Some(iterated) = iterated {
            self.collect_value(file, iterated, &mut storage);
        }

        storage
    }

    fn collect_storage(&mut self, file: FileId, root: NodeId, storage: &mut Storage) {
        let mut pending = vec![root];

        while let Some(node) = pending.pop() {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                storage.unresolved = true;

                return;
            }

            match self.kind_of_node(file, node) {
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => {
                    continue
                }
                AstKind::IdentifierReference(reference) => {
                    match self.binding_of_identifier(file, reference) {
                        Some(binding) => {
                            if !storage.bindings.contains(&binding) {
                                storage.bindings.push(binding);
                            }
                        }
                        None => {
                            storage.unresolved |=
                                !CONSTANT_GLOBALS.contains(&reference.name.as_str());
                        }
                    }
                }
                AstKind::StaticMemberExpression(member) => {
                    self.collect_value(file, &member.object, storage)
                }
                AstKind::ComputedMemberExpression(member) => {
                    self.collect_value(file, &member.object, storage)
                }
                AstKind::PrivateFieldExpression(member) => {
                    self.collect_value(file, &member.object, storage)
                }
                AstKind::ThisExpression(_) | AstKind::Super(_) => storage.unresolved = true,
                AstKind::CallExpression(_)
                | AstKind::NewExpression(_)
                | AstKind::TaggedTemplateExpression(_) => storage.calls = true,
                _ => {}
            }

            pending.extend(self.children_of(file, node));
        }
    }

    fn collect_value(&mut self, file: FileId, object: &'a Expression<'a>, storage: &mut Storage) {
        let value = self.storage_value_of(file, object);
        let holder = match unwrap(object) {
            Expression::Identifier(reference) => self.binding_of_identifier(file, reference),
            _ => None,
        };

        if !storage.values.contains(&(value, holder)) {
            storage.values.push((value, holder));
        }
    }

    fn budget_storage_of(&mut self) -> Option<Storage> {
        let context = self.budget_context.as_ref()?;

        if context.budgets.is_empty() && self.share_bindings.is_empty() {
            return None;
        }

        let function = context.function;
        let counters: Vec<Binding> = context.budgets.keys().copied().collect();
        let mut storage = match self.budget_storage.get(&function) {
            Some(storage) => storage.clone(),
            None => {
                let storage = self.budgeted_loop_storage_of(function, &counters);

                self.budget_storage.insert(function, storage.clone());

                storage
            }
        };

        for binding in &self.share_bindings {
            if !storage.bindings.contains(binding) {
                storage.bindings.push(*binding);
            }
        }

        Some(storage)
    }

    fn budgeted_loop_storage_of(&mut self, function: FunctionId, counters: &[Binding]) -> Storage {
        let file = function.file;
        let mut storage = Storage::default();
        let Some(body) = body_root_of(self.function_at(function)) else {
            return storage;
        };

        for kind in self.counted_subtree(file, body, Event::EffectPrepassNode) {
            let (tests, body): (Vec<&'a Expression<'a>>, &'a Statement<'a>) = match kind {
                AstKind::WhileStatement(statement) => (vec![&statement.test], &statement.body),
                AstKind::DoWhileStatement(statement) => (vec![&statement.test], &statement.body),
                AstKind::ForStatement(statement) => (
                    statement
                        .test
                        .iter()
                        .chain(statement.update.iter())
                        .collect(),
                    &statement.body,
                ),
                _ => continue,
            };
            let mut found = Storage::default();

            for test in tests {
                self.collect_storage(file, test.node_id(), &mut found);
            }

            if !found
                .bindings
                .iter()
                .any(|binding| counters.contains(binding))
            {
                continue;
            }

            for statement in advancing_statements_of(body) {
                if self
                    .spent_binding_of(file, statement)
                    .is_some_and(|binding| counters.contains(&binding))
                {
                    self.collect_storage(file, statement.node_id(), &mut found);
                }
            }

            storage.merge(found);
        }

        if self.work_exhausted() {
            storage.unresolved = true;
        }

        storage
    }

    fn spent_binding_of(&self, file: FileId, statement: &'a Statement<'a>) -> Option<Binding> {
        let Statement::ExpressionStatement(statement) = statement else {
            return None;
        };
        let reference = match unwrap(&statement.expression) {
            Expression::AssignmentExpression(assignment) => match &assignment.left {
                AssignmentTarget::AssignmentTargetIdentifier(reference) => reference,
                _ => return None,
            },
            Expression::UpdateExpression(update) => match &update.argument {
                SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => reference,
                _ => return None,
            },
            _ => return None,
        };

        self.binding_of_identifier(file, reference)
    }

    pub(crate) fn is_isolated_binding(
        &mut self,
        file: FileId,
        function: Option<NodeId>,
        binding: Binding,
    ) -> bool {
        let Some(function) = function else {
            return false;
        };
        let Binding::Symbol {
            file: owner,
            symbol,
        } = binding;

        if owner != file {
            return false;
        }

        if let Some(isolated) = self.isolated_bindings.get(&(binding, function)) {
            return *isolated;
        }

        let project = self.project;
        let semantic = &project.file(file).semantic;
        let declaration = semantic.scoping().symbol_declaration(symbol);
        let parameter = matches!(
            semantic.nodes().kind(declaration),
            AstKind::FormalParameter(_) | AstKind::FormalParameterRest(_)
        ) || matches!(
            semantic.nodes().parent_kind(declaration),
            AstKind::FormalParameter(_) | AstKind::FormalParameterRest(_)
        );
        let (evaluates, arguments) = self.dynamic_scope_of(file, function);
        let isolated = !evaluates
            && !(parameter && arguments)
            && self.enclosing_function_of(file, declaration) == Some(function)
            && semantic
                .scoping()
                .get_resolved_references(symbol)
                .filter(|reference| reference.is_write())
                .all(|reference| {
                    self.enclosing_function_of(file, reference.node_id()) == Some(function)
                });

        self.isolated_bindings.insert((binding, function), isolated);

        isolated
    }

    fn is_isolated_value(
        &mut self,
        file: FileId,
        function: Option<NodeId>,
        value: ValueId,
        holder: Option<Binding>,
    ) -> bool {
        let (
            Some(function),
            Some(Binding::Symbol {
                file: owner,
                symbol,
            }),
        ) = (function, holder)
        else {
            return false;
        };

        if owner != file
            || !self.values.is_allocation(value)
            || self.dynamic_scope_of(file, function).0
        {
            return false;
        }

        let project = self.project;
        let semantic = &project.file(file).semantic;
        let declaration = semantic.scoping().symbol_declaration(symbol);
        let AstKind::VariableDeclarator(declarator) = semantic.nodes().kind(declaration) else {
            return false;
        };
        let Some(initializer) = &declarator.init else {
            return false;
        };

        if self.storage_value_of(file, initializer) != value {
            return false;
        }

        let nodes = semantic.nodes();

        self.enclosing_function_of(file, declaration) == Some(function)
            && semantic
                .scoping()
                .get_resolved_references(symbol)
                .all(|reference| {
                    self.enclosing_function_of(file, reference.node_id()) == Some(function)
                        && matches!(
                            value_flow_of(nodes, reference.node_id()),
                            ValueFlow::Read | ValueFlow::Member
                        )
                })
    }

    pub(crate) fn dynamic_scope_of(&mut self, file: FileId, function: NodeId) -> (bool, bool) {
        if let Some(found) = self.dynamic_scopes.get(&(file, function)) {
            return *found;
        }

        let semantic = &self.project.file(file).semantic;
        let nodes = semantic.nodes();
        let scoping = semantic.scoping();
        let references = |name: &str| {
            scoping
                .root_unresolved_references()
                .get(name)
                .map(|references| {
                    references
                        .iter()
                        .map(|reference| scoping.get_reference(*reference).node_id())
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        let evaluates = references("eval").into_iter().any(|node| {
            is_direct_call(nodes, node)
                && nodes
                    .ancestor_ids(node)
                    .any(|ancestor| ancestor == function)
        });
        let arguments = references("arguments").into_iter().any(|node| {
            nodes
                .ancestors(node)
                .find(|ancestor| matches!(ancestor.kind(), AstKind::Function(_)))
                .is_some_and(|owner| owner.id() == function)
        });

        self.dynamic_scopes
            .insert((file, function), (evaluates, arguments));

        (evaluates, arguments)
    }

    fn has_unclassified_write(&mut self, binding: Binding, repeated: Option<NodeId>) -> bool {
        if let Some(found) = self.unclassified_writes.get(&(binding, repeated)) {
            return *found;
        }

        let Binding::Symbol { file, symbol } = binding;
        let semantic = &self.project.file(file).semantic;
        let nodes = semantic.nodes();
        let found = semantic
            .scoping()
            .get_resolved_references(symbol)
            .filter(|reference| reference.is_write())
            .any(|reference| {
                let node = reference.node_id();
                let span = nodes.kind(node).span();

                repeated.is_none_or(|repeated| {
                    nodes
                        .ancestor_ids(node)
                        .any(|ancestor| ancestor == repeated)
                }) && !match nodes.parent_kind(node) {
                    AstKind::AssignmentExpression(assignment) => assignment.left.span() == span,
                    AstKind::UpdateExpression(_) => true,
                    _ => false,
                }
            });

        self.unclassified_writes.insert((binding, repeated), found);

        found
    }

    pub(crate) fn is_declared_within(&self, binding: Binding, function: FunctionId) -> bool {
        let Binding::Symbol { file, symbol } = binding;

        if file != function.file {
            return false;
        }

        let semantic = &self.project.file(file).semantic;
        let declaration = semantic.scoping().symbol_declaration(symbol);

        semantic
            .nodes()
            .ancestor_ids(declaration)
            .any(|ancestor| ancestor == function.node)
    }
}

fn advancing_statements_of<'a>(body: &'a Statement<'a>) -> Vec<&'a Statement<'a>> {
    let statements = match body {
        Statement::BlockStatement(block) => block.body.iter().collect(),
        other => vec![other],
    };

    statements
        .into_iter()
        .filter(|statement| {
            matches!(
                statement,
                Statement::ExpressionStatement(expression)
                    if matches!(
                        unwrap(&expression.expression),
                        Expression::AssignmentExpression(_) | Expression::UpdateExpression(_)
                    )
            )
        })
        .collect()
}

#[cfg(test)]
#[path = "effects.test.rs"]
mod tests;

use oxc_ast::ast::{
    Argument, AssignmentTarget, AssignmentTargetMaybeDefault, AssignmentTargetProperty,
    CallExpression, ClassElement, Expression, ForOfStatement, ForStatementLeft,
    IdentifierReference, MemberExpression, MethodDefinitionKind, NewExpression,
    SimpleAssignmentTarget, Statement,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::UnaryOperator;

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::budgets::{CollectionWrites, VisitBudget, Visits};
use crate::constants::constant_initializer_of;
use crate::cost::Cost;
use crate::declarations::{Binding, Declaration, FunctionId};
use crate::declared_types::Kind;
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
pub(crate) struct BudgetStorage {
    loops: Vec<(NodeId, Storage)>,
    exhausted: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct Storage {
    bindings: Vec<Binding>,
    values: Vec<(ValueId, Option<Binding>)>,
    unresolved: bool,
    calls: bool,
}

impl Storage {
    pub(crate) fn weight(&self) -> u64 {
        (self.bindings.len() + self.values.len() + 1) as u64
    }

    pub(crate) fn unresolved() -> Self {
        Self {
            unresolved: true,
            ..Self::default()
        }
    }

    pub(crate) fn joined(mut self, other: Self) -> Self {
        self.extend(other);
        self.bindings.sort_by_key(|binding| match binding {
            Binding::Symbol { file, symbol } => (file.0, symbol.index()),
        });
        self.bindings.dedup();
        self.values.sort_by_key(|(value, holder)| {
            (
                *value,
                holder.map(|binding| match binding {
                    Binding::Symbol { file, symbol } => (file.0, symbol.index()),
                }),
            )
        });
        self.values.dedup();

        self
    }

    fn extend(&mut self, other: Self) {
        self.bindings.extend(other.bindings);
        self.values.extend(other.values);

        self.unresolved |= other.unresolved;
        self.calls |= other.calls;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Writes {
    All,
    Qualified,
}

#[derive(Default)]
struct Scheduling {
    active: std::collections::HashSet<FunctionId>,
    cycles: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Prepass {
    Loop,
    Skipped,
    Traversal,
}

const CONSTANT_GLOBALS: [&str; 3] = ["undefined", "NaN", "Infinity"];
const FRESH_CONSTRUCTORS: [&str; 5] = ["Date", "Error", "RegExp", "Promise", "ArrayBuffer"];
const MAXIMUM_ALIAS_DEPTH: usize = 8;

fn is_contained_flow(nodes: &AstNodes<'_>, flow: ValueFlow) -> bool {
    match flow {
        ValueFlow::Read | ValueFlow::Member => true,
        ValueFlow::Alias(node) => matches!(nodes.kind(node), AstKind::ForOfStatement(_)),
        _ => false,
    }
}

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
    pub(crate) fn canonicalize(&mut self) {
        self.binding_writes.sort_by_key(|binding| match binding {
            Binding::Symbol { file, symbol } => (file.0, symbol.index()),
        });
        self.binding_writes.dedup();
        self.member_writes.sort();
        self.member_writes.dedup();
        self.escapes.sort();
        self.escapes.dedup();
        self.unknown_reachable.sort();
        self.unknown_reachable.dedup();
    }

    pub(crate) fn weight(&self) -> u64 {
        (self.binding_writes.len()
            + self.member_writes.len()
            + self.unknown_reachable.len()
            + self.escapes.len()
            + 1) as u64
    }

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

    pub(crate) fn reference_storage_value_of(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> ValueId {
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference);

        match declaration.map(|declaration| (declaration, constant_initializer_of(declaration))) {
            Some((_, Some((target, initializer)))) => self.storage_value_of(target, initializer),
            Some((declaration, None)) => self.declared_value_of(declaration, file, reference.span),
            None => self.values.at(self.source_span(file, reference.span)).value,
        }
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

        if let AstKind::ForOfStatement(statement) = loop_kind {
            let saved = std::mem::take(&mut self.current_effects);

            self.record_iteration_effects(file, statement);

            let effects = std::mem::replace(&mut self.current_effects, saved);

            self.current_effects.join(&effects);
            header.join(&effects);
        }

        let mut effects = match loop_body_of(loop_kind) {
            Some(body) => self.called_effects_in(file, Root::Statement(body)),
            None => Effects::default(),
        };

        effects.join(&header);

        let live = match loop_kind {
            AstKind::ForOfStatement(statement) => self.live_iteration_of(file, statement),
            _ => None,
        };
        let classified = matches!(
            live,
            Some(Visits::Stable { written: true } | Visits::Budgeted(_))
        );
        let mut invalidation = self.invalidation_of(file, loop_kind, &effects, classified);

        invalidation.bound |= header.unknown_global || !header.unknown_reachable.is_empty();

        let pending = self.pending_invalidation_of(file, loop_kind);
        invalidation.bound |= pending.bound;
        invalidation.budget |= pending.budget;

        invalidation
    }

    pub(crate) fn live_iteration_of(
        &mut self,
        file: FileId,
        statement: &'a ForOfStatement<'a>,
    ) -> Option<Visits> {
        if !matches!(unwrap(&statement.right), Expression::Identifier(_)) {
            return None;
        }

        if !matches!(
            self.receiver_kind_of(file, &statement.right, ""),
            Kind::Set | Kind::Map
        ) {
            return None;
        }

        if self
            .pending_invalidation_of(file, AstKind::ForOfStatement(statement))
            .bound
        {
            return Some(Visits::Unresolved);
        }

        if statement.r#await {
            return None;
        }

        Some(self.live_visits_of(
            file,
            &statement.right,
            &[(file, Root::Statement(&statement.body))],
        ))
    }

    fn pending_invalidation_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Invalidation {
        let owner = self.enclosing_function_of(file, loop_kind.node_id());
        let asynchronous =
            owner.is_some_and(|node| match self.function_at(FunctionId { file, node }) {
                crate::declarations::FunctionNode::Function(function) => function.r#async,
                crate::declarations::FunctionNode::Arrow(arrow) => arrow.r#async,
                crate::declarations::FunctionNode::Construction(_) => false,
            });
        let awaiting = matches!(loop_kind, AstKind::ForOfStatement(statement) if statement.r#await);

        if !awaiting && !asynchronous {
            return Invalidation::default();
        }

        if !awaiting && !self.suspends(file, loop_kind.node_id()) {
            let generator = owner.is_some_and(|node| matches!(self.function_at(FunctionId { file, node }), crate::declarations::FunctionNode::Function(function) if function.r#async && function.generator));
            let yielding = generator
                && loop_body_of(loop_kind).is_some_and(|body| {
                    self.counted_subtree(file, Root::Statement(body), Event::EffectPrepassNode)
                        .into_iter()
                        .any(|kind| matches!(kind, AstKind::YieldExpression(_)))
                        || self.work_exhausted()
                });

            if !yielding {
                return Invalidation::default();
            }
        }

        let Some(owner) = owner else {
            return Invalidation {
                bound: true,
                budget: true,
            };
        };
        let mut effects = self.interference.clone();

        for (_, pending) in self.pending_effects_of(FunctionId { file, node: owner }) {
            if !self.charge_work(
                Event::EffectPrepassNode,
                pending.weight().saturating_mul(effects.weight()),
            ) {
                return Invalidation {
                    bound: true,
                    budget: true,
                };
            }

            effects.join(&pending);
        }

        if self.work_exhausted() || effects.unknown_global {
            return Invalidation {
                bound: true,
                budget: true,
            };
        }

        if effects.binding_writes.is_empty()
            && effects.member_writes.is_empty()
            && effects.unknown_reachable.is_empty()
        {
            return Invalidation::default();
        }

        let header = self.iteration_storage_of(file, loop_kind);
        let mut header = self.interference_storage_of(header);

        header.bindings.retain(|binding| {
            effects.binding_writes.contains(binding) || !effects.unknown_reachable.is_empty()
        });

        let bound = self.affects(file, Some(owner), &effects, &header, None);
        let budget = self
            .budget_storage_of(file, loop_kind.node_id())
            .is_some_and(|storage| {
                let storage = self.interference_storage_of(storage);

                self.affects(file, Some(owner), &effects, &storage, None)
            });

        if self.work_exhausted() || header.unresolved {
            return Invalidation {
                bound: true,
                budget: true,
            };
        }

        Invalidation { bound, budget }
    }

    fn iteration_storage_of(&mut self, file: FileId, kind: AstKind<'a>) -> Storage {
        if let AstKind::ForOfStatement(statement) = kind {
            let iteration = self.iteration_of(file, &statement.right, statement.r#await);

            if let Some(latent) = self.iteration_latent_of(file, &statement.right, &iteration) {
                return latent.storage;
            }
        }

        self.header_storage_of(file, kind, false)
    }

    pub(crate) fn generator_storage_of(
        &mut self,
        file: FileId,
        function: crate::declarations::FunctionNode<'a>,
    ) -> Storage {
        let Some(root) = body_root_of(function) else {
            return Storage::unresolved();
        };
        let kinds = self.counted_subtree(file, root, Event::EffectPrepassNode);
        let mut storage = Storage::default();

        for kind in kinds {
            if loop_body_of(kind).is_some() {
                let header = self.iteration_storage_of(file, kind);

                storage.extend(header);
            }

            if let AstKind::YieldExpression(yielded) = kind {
                if yielded.delegate {
                    if let Some(argument) = &yielded.argument {
                        let asynchronous = matches!(function, crate::declarations::FunctionNode::Function(function) if function.r#async);
                        let iteration = self.iteration_of(file, argument, asynchronous);
                        let delegated = match self.iteration_latent_of(file, argument, &iteration) {
                            Some(latent) => latent.storage,
                            None => {
                                let mut found = Storage::default();

                                self.collect_storage(file, argument.node_id(), &mut found);
                                self.collect_value(file, argument, &mut found);

                                found
                            }
                        };

                        storage.extend(delegated);
                    }
                }
            }
        }

        storage = self.interference_storage_of(storage);
        let size = storage.weight();

        if !self.charge_work(
            Event::EffectPrepassNode,
            size.saturating_mul(u64::from(size.ilog2()) + 1),
        ) {
            return Storage::unresolved();
        }

        storage.unresolved |= self.work_exhausted();

        storage.joined(Storage::default())
    }

    fn interference_storage_of(&mut self, mut storage: Storage) -> Storage {
        for index in 0..self.storage_arguments.len() {
            if !self.charge_work(Event::EffectPrepassNode, storage.weight()) {
                storage.unresolved = true;

                break;
            }

            let (binding, actual) = self.storage_arguments[index];

            let Some(declared) = self.parameter_storage_of(binding) else {
                continue;
            };

            for (value, _) in &mut storage.values {
                if *value == declared {
                    *value = actual;
                }
            }
        }

        storage
    }

    fn parameter_storage_of(&mut self, binding: Binding) -> Option<ValueId> {
        if !self.is_parameter_unwritten(binding) {
            return None;
        }

        let declaration = self.declarations.of_binding(self.project, binding)?;
        let Binding::Symbol { file, .. } = binding;

        Some(self.declared_value_of(declaration, file, Span::default()))
    }

    pub(crate) fn pending_enabled(&mut self) -> bool {
        if let Some(enabled) = self.pending_enabled {
            return enabled;
        }

        let project = self.project;

        for source in &project.files {
            for node in source.semantic.nodes().iter() {
                if !self.charge_work(Event::EffectPrepassNode, 1) {
                    return true;
                }

                if matches!(node.kind(), AstKind::AwaitExpression(_))
                    || matches!(node.kind(), AstKind::ForOfStatement(statement) if statement.r#await)
                    || matches!(node.kind(), AstKind::Function(function) if function.r#async && function.generator)
                {
                    self.pending_enabled = Some(true);

                    return true;
                }
            }
        }

        self.pending_enabled = Some(false);

        false
    }

    pub(crate) fn invocation_interference_of(
        &mut self,
        file: FileId,
        span: oxc_span::Span,
    ) -> Effects {
        if self.collecting_pending || !self.pending_enabled() {
            return Effects::default();
        }

        let mut effects = self.interference.clone();

        if let Some(owner) = self.active_function_of() {
            for (site, pending) in self.pending_effects_of(owner) {
                if site != self.source_span(file, span) {
                    if !self.charge_work(
                        Event::EffectPrepassNode,
                        pending.weight().saturating_mul(effects.weight()),
                    ) {
                        effects.unknown_global = true;

                        break;
                    }

                    effects.join(&pending);
                }
            }
        }

        effects.escapes.clear();
        effects.canonicalize();

        effects
    }

    fn pending_effects_of(
        &mut self,
        owner: FunctionId,
    ) -> Vec<(crate::unknowns::SourceSpan, Effects)> {
        let unknown = vec![(
            self.source_span(owner.file, self.kind_of_node(owner.file, owner.node).span()),
            Effects::unknown(),
        )];
        let Some(key) = self.pending_effect_key_of(owner) else {
            return unknown;
        };

        if let Some(found) = self.pending_effects.get(&key) {
            return found.clone().unwrap_or(unknown);
        }

        self.pending_effects.insert(key.clone(), None);

        let Some(root) = body_root_of(self.function_at(owner)) else {
            self.pending_effects.remove(&key);

            return unknown;
        };
        let kinds = self.counted_subtree(owner.file, root, Event::EffectPrepassNode);
        let mut active = Scheduling::default();
        let mut effects = Vec::new();

        for kind in kinds {
            let schedules = self.kind_may_schedule(owner.file, kind, &mut active);

            if schedules {
                let saved = std::mem::take(&mut self.current_effects);
                let collecting = std::mem::replace(&mut self.collecting_pending, true);

                self.prepass_effects_of(owner.file, vec![kind], Prepass::Traversal);
                self.record_pending_latent_effects(owner.file, kind);

                self.collecting_pending = collecting;
                let mut pending = std::mem::replace(&mut self.current_effects, saved);

                for index in 0..self.storage_arguments.len() {
                    if !self.charge_work(Event::EffectPrepassNode, pending.weight()) {
                        pending.unknown_global = true;

                        break;
                    }

                    let (binding, actual) = self.storage_arguments[index];

                    let Some(declared) = self.parameter_storage_of(binding) else {
                        continue;
                    };

                    pending.substitute(declared, actual);
                }

                if pending != Effects::default() {
                    effects.push((self.source_span(owner.file, kind.span()), pending));
                }
            }

            if self.work_exhausted() {
                self.pending_effects.remove(&key);
                effects.extend(unknown);

                return effects;
            }
        }

        self.pending_effects.insert(key, Some(effects.clone()));

        effects
    }
    fn record_pending_latent_effects(&mut self, file: FileId, kind: AstKind<'a>) {
        let mut consumed = Vec::new();

        match kind {
            AstKind::ForOfStatement(statement) => {
                consumed.push((&statement.right, statement.r#await))
            }
            AstKind::SpreadElement(spread) => consumed.push((&spread.argument, false)),
            AstKind::CallExpression(call) => {
                if let Some((site, model)) = self.modelled_call_of(file, call) {
                    if model.receiver == crate::native::Role::Iterated {
                        consumed.extend(site.receiver.map(|value| (value, false)));
                    }

                    extend_iterated_arguments(&mut consumed, site.arguments, model);
                }
            }
            AstKind::NewExpression(new) => {
                if let Some(model) = self.construction_model_of(file, new) {
                    extend_iterated_arguments(&mut consumed, &new.arguments, model);
                }
            }
            _ => {}
        }

        for (expression, asynchronous) in consumed {
            let iteration = self.iteration_of(file, expression, asynchronous);

            if let Some(latent) = self.iteration_latent_of(file, expression, &iteration) {
                if !self.charge_work(
                    Event::EffectPrepassNode,
                    latent
                        .effects
                        .weight()
                        .saturating_mul(self.current_effects.weight()),
                ) {
                    self.current_effects.unknown_global = true;

                    return;
                }

                self.current_effects.join(&latent.effects);
            }
        }
    }

    fn kind_may_schedule(
        &mut self,
        file: FileId,
        kind: AstKind<'a>,
        active: &mut Scheduling,
    ) -> bool {
        match kind {
            AstKind::CallExpression(call) => self.call_may_schedule(file, call, active),
            AstKind::NewExpression(new) => {
                if let Expression::Identifier(reference) = unwrap(&new.callee) {
                    if matches!(
                        reference.name.as_str(),
                        "Set" | "Map" | "WeakSet" | "WeakMap"
                    ) && self.is_intrinsic_reference(file, reference)
                    {
                        if self.intrinsic_replaced_of(file, &new.callee)
                            || (reference.name.as_str().contains("Map")
                                && self.has_indexed_accessors())
                            || self.may_implement_any(&[crate::values::MemberKey::Name(
                                if reference.name.as_str().contains("Map") {
                                    "set"
                                } else {
                                    "add"
                                }
                                .to_string(),
                            )])
                        {
                            return true;
                        }

                        return new.arguments.first().is_some_and(|argument| {
                            match argument.as_expression() {
                                Some(expression) => {
                                    self.iteration_may_schedule(file, expression, false, active)
                                }
                                None => true,
                            }
                        });
                    }
                }

                let Some(model) = self.construction_model_of(file, new) else {
                    let construction = self.construction_of(file, &new.callee);

                    return construction.targets.open || !construction.targets.known.is_empty()
                        || construction.implicit.into_iter().any(|(_, class)| {
                            !self.charge_work(Event::EffectPrepassNode, class.body.body.len() as u64)
                                || class.heritage.is_some() || crate::flow::class_phases_of(class).decorated.is_some() || class.body.body.iter().any(|element| matches!(element,
                                ClassElement::PropertyDefinition(property) if !property.r#static)
                                || matches!(element, ClassElement::AccessorProperty(property) if !property.r#static))
                        });
                };

                if self.intrinsic_replaced_of(file, &new.callee) {
                    return true;
                }

                if self.has_indexed_accessors()
                    || self.may_access(Some(&crate::values::MemberKey::Name("length".to_string())))
                    || self.may_implement_any(&crate::invocations::coercion_keys())
                {
                    return true;
                }

                for (index, argument) in new.arguments.iter().enumerate() {
                    let role = model.arguments.get(index).copied().unwrap_or(model.rest);

                    if role.invokes() {
                        return true;
                    }

                    let Some(expression) = argument.as_expression() else {
                        return true;
                    };

                    if matches!(role, crate::native::Role::Iterated)
                        && self.iteration_may_schedule(file, expression, false, active)
                    {
                        return true;
                    }

                    if matches!(
                        role,
                        crate::native::Role::Coerced
                            | crate::native::Role::Inspected
                            | crate::native::Role::Serialized
                    ) {
                        return true;
                    }
                }

                false
            }
            AstKind::ForOfStatement(statement) => {
                self.iteration_may_schedule(file, &statement.right, statement.r#await, active)
            }
            AstKind::SpreadElement(spread) => {
                self.iteration_may_schedule(file, &spread.argument, false, active)
            }
            AstKind::TaggedTemplateExpression(_)
            | AstKind::JSXSpreadAttribute(_)
            | AstKind::JSXSpreadChild(_) => true,
            _ => self.has_implicit_calls(file, kind),
        }
    }

    fn iteration_may_schedule(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        asynchronous: bool,
        active: &mut Scheduling,
    ) -> bool {
        let saved = std::mem::replace(&mut self.collecting_pending, true);
        let iteration = self.iteration_of(file, value, asynchronous);
        let latent = self.iteration_latent_of(file, value, &iteration);
        self.collecting_pending = saved;

        if latent.is_some_and(|latent| self.latent_may_schedule(&latent)) {
            return true;
        }

        self.iteration_effect_targets_of(file, value, &iteration)
            .into_iter()
            .any(|targets| {
                targets.open
                    || targets
                        .known
                        .into_iter()
                        .any(|target| self.function_may_schedule(target, active))
            })
    }

    fn call_may_schedule(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        active: &mut Scheduling,
    ) -> bool {
        if !self.charge_work(Event::EffectPrepassNode, 1) {
            return true;
        }

        if let Some((site, model)) = self.modelled_call_of(file, call) {
            if model.identity
                == crate::native::Identity::Receiver(crate::declared_types::Kind::Array)
                && site.name == "concat"
            {
                return true;
            }

            if model.phase == crate::cost::ExecutionPhase::Scheduled {
                return true;
            }

            if model.identity == crate::native::Identity::Namespace("Array")
                && site.name == "from"
                && (self.has_indexed_accessors()
                    || self.may_access(Some(&crate::values::MemberKey::Name("length".to_string())))
                    || self.may_implement_any(&crate::invocations::coercion_keys()))
            {
                return true;
            }

            if model.identity == crate::native::Identity::Namespace("Object")
                && site.name == "fromEntries"
                && (self.has_indexed_accessors()
                    || self.may_implement_any(&crate::invocations::coercion_keys()))
            {
                return true;
            }

            for (index, argument) in site.arguments.iter().enumerate() {
                let role = model.arguments.get(index).copied().unwrap_or(model.rest);

                if !role.invokes() {
                    if role == crate::native::Role::Iterated {
                        if argument.as_expression().is_none_or(|expression| {
                            self.iteration_may_schedule(file, expression, false, active)
                        }) {
                            return true;
                        }
                    } else if matches!(
                        role,
                        crate::native::Role::Inspected
                            | crate::native::Role::Coerced
                            | crate::native::Role::Serialized
                    ) {
                        return true;
                    }

                    continue;
                }

                let Some(expression) = argument.as_expression() else {
                    return true;
                };
                let targets = self
                    .resolved_expression_callee_of(file, expression, expression.node_id())
                    .targets;

                if targets.open || targets.known.is_empty() {
                    return true;
                }

                for target in targets.known {
                    if self.function_may_schedule(target, active) {
                        return true;
                    }
                }
            }

            if model.receiver != crate::native::Role::Callee {
                if model.receiver == crate::native::Role::Iterated {
                    return site.receiver.is_none_or(|receiver| {
                        self.iteration_may_schedule(file, receiver, false, active)
                    });
                }

                if matches!(
                    model.receiver,
                    crate::native::Role::Inspected
                        | crate::native::Role::Coerced
                        | crate::native::Role::Serialized
                ) {
                    return true;
                }

                return false;
            }
        }

        let targets = self.resolved_callee_of(file, call).targets;

        if targets.open || targets.known.is_empty() {
            return true;
        }

        for target in targets.known {
            if self.function_may_schedule(target, active) {
                return true;
            }
        }

        false
    }

    fn function_may_schedule(&mut self, target: FunctionId, active: &mut Scheduling) -> bool {
        let Some(key) = self.scheduling_key_of(target) else {
            return true;
        };

        if let Some(found) = self.scheduling.get(&key) {
            return *found;
        }

        if active.active.contains(&target) {
            active.cycles = active.cycles.saturating_add(1);

            return false;
        }

        if active.active.len() >= 64 || !self.charge_work(Event::EffectPrepassNode, 1) {
            return true;
        }

        let cycles = active.cycles;

        active.active.insert(target);

        let function = self.function_at(target);
        let (asynchronous, generator) = match function {
            crate::declarations::FunctionNode::Function(function) => {
                (function.r#async, function.generator)
            }
            crate::declarations::FunctionNode::Arrow(arrow) => (arrow.r#async, false),
            crate::declarations::FunctionNode::Construction(_) => (false, false),
        };
        let schedules = if generator {
            false
        } else if asynchronous {
            true
        } else if let Some(body) = body_root_of(function) {
            let kinds = self.counted_subtree(target.file, body, Event::EffectPrepassNode);

            kinds
                .into_iter()
                .any(|kind| self.kind_may_schedule(target.file, kind, active))
                || self.work_exhausted()
        } else {
            true
        };

        active.active.remove(&target);

        if (schedules || active.cycles == cycles || active.active.is_empty())
            && !self.work_exhausted()
            && self.charge_work(Event::GraphNode, 1)
        {
            self.scheduling.insert(key, schedules);
        }

        schedules || self.work_exhausted()
    }

    pub(crate) fn live_visits_of(
        &mut self,
        file: FileId,
        collection: &'a Expression<'a>,
        bodies: &[(FileId, Root<'a>)],
    ) -> Visits {
        let value = self.storage_value_of(file, collection);
        let holder = match unwrap(collection) {
            Expression::Identifier(reference) => self.binding_of_identifier(file, reference),
            _ => None,
        };
        let function = self.enclosing_function_of(file, collection.node_id());
        let storage = Storage {
            values: vec![(value, holder)],
            ..Storage::default()
        };
        let effects = self.traversal_effects_of(bodies, &[]);

        if !self.affects(file, function, &effects, &storage, None) {
            return Visits::Stable { written: false };
        }

        let mut writes = CollectionWrites::default();

        for (body_file, body) in bodies {
            self.collection_writes_in(*body_file, *body, value, &mut writes);
        }

        let remaining = self.traversal_effects_of(bodies, &writes.sites());

        if self.work_exhausted() || self.affects(file, function, &remaining, &storage, None) {
            return Visits::Unresolved;
        }

        if writes.additions.is_empty() {
            return Visits::Stable { written: true };
        }

        if !writes.deletions.is_empty() {
            return Visits::Unresolved;
        }

        let mut costs = Vec::new();
        let mut texts: Vec<String> = Vec::new();

        for addition in writes.additions {
            let Some((endpoint, text)) = addition.guard else {
                return Visits::Unresolved;
            };
            let mut endpoint_storage = Storage::default();

            self.collect_storage(addition.file, endpoint.node_id(), &mut endpoint_storage);

            let owner = self.enclosing_function_of(addition.file, endpoint.node_id());

            if endpoint_storage.calls
                || endpoint_storage.unresolved
                || self.affects(addition.file, owner, &remaining, &endpoint_storage, None)
            {
                return Visits::Unresolved;
            }

            let Some(cost) = self.endpoint_cost_of(addition.file, endpoint) else {
                return Visits::Unresolved;
            };

            costs.push(cost);

            if !texts.contains(&text) {
                texts.push(text);
            }
        }

        match Cost::maximum(costs) {
            Ok(cost) => Visits::Budgeted(VisitBudget {
                cost,
                text: texts.join(", "),
            }),
            Err(_) => Visits::Unresolved,
        }
    }

    fn traversal_effects_of(
        &mut self,
        bodies: &[(FileId, Root<'a>)],
        excluded: &[(FileId, NodeId)],
    ) -> Effects {
        let saved = std::mem::take(&mut self.current_effects);

        for (file, body) in bodies {
            if self.fallback_active() || self.work_exhausted() {
                self.current_effects.unknown_global = true;

                break;
            }

            let kinds: Vec<AstKind<'a>> = self
                .counted_subtree(*file, *body, Event::EffectPrepassNode)
                .into_iter()
                .filter(|kind| !excluded.contains(&(*file, kind.node_id())))
                .collect();

            if self.work_exhausted() {
                self.current_effects.unknown_global = true;

                break;
            }

            self.prepass_effects_of(*file, kinds, Prepass::Traversal);
        }

        std::mem::replace(&mut self.current_effects, saved)
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
                Prepass::Skipped | Prepass::Traversal => {
                    self.record_writes(file, kind, Writes::All)
                }
                Prepass::Loop => self.record_writes(file, kind, Writes::Qualified),
            }

            self.record_implicit_effects(file, kind);

            match kind {
                AstKind::CallExpression(call)
                    if matches!(unwrap(&call.callee), Expression::Super(_)) =>
                {
                    self.super_construction_part_of(file, call);
                }
                AstKind::CallExpression(call) if self.invoke_returned_call(file, call) => {}
                AstKind::CallExpression(call) => {
                    let ResolvedCallee {
                        declaration,
                        closed,
                        targets,
                    } = self.resolved_callee_of(file, call);

                    if let Some(Declaration::Parameter { .. }) = declaration {
                        let facts = self
                            .parameter_binding_of(declaration.unwrap())
                            .filter(|binding| self.is_parameter_unwritten(*binding))
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

                        let native =
                            targets.known.is_empty() && self.records_native_effects(file, call);

                        if targets.open && !native {
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
                    let construction = self.construction_targets_of(file, new);
                    let targets = &construction.targets;

                    for target in &targets.known {
                        let function = self.function_at(*target);

                        self.call_user(target.file, function, file, &new.arguments, new.span);
                    }

                    for implicit in &construction.implicit {
                        self.construction_part_of((file, &new.arguments, new.span), *implicit);
                    }

                    let unresolved = targets.known.is_empty() && construction.implicit.is_empty();
                    let native = unresolved && self.records_construction_effects(file, new);

                    if (unresolved || targets.open) && !native {
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

    fn invoke_returned_call(&mut self, file: FileId, call: &'a CallExpression<'a>) -> bool {
        let Expression::CallExpression(inner) = unwrap(&call.callee) else {
            return false;
        };
        let Some((returned, open)) = self
            .returned_facts_of(file, inner)
            .filter(|(returned, open)| *open || !returned.is_empty())
        else {
            return false;
        };

        for facts in &returned {
            self.invoke_argument(facts, file, call.span, &call.arguments);
        }

        if open {
            self.record_unknown_reach(file, Some(&call.callee), &call.arguments, call.span);
        }

        true
    }

    fn invalidation_of(
        &mut self,
        file: FileId,
        loop_kind: AstKind<'a>,
        effects: &Effects,
        classified: bool,
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
        let header = self.header_storage_of(file, loop_kind, classified);
        let bound = self.affects(file, function, effects, &header, Some(repeated));
        let budget = match self.budget_storage_of(file, loop_kind.node_id()) {
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
            let isolated = self.is_isolated_value(file, function, *value, *holder);
            let written = match isolated {
                true => effects.member_writes.contains(value),
                false => effects
                    .member_writes
                    .iter()
                    .any(|written| self.values.may_alias(*written, *value)),
            };

            if written || (reached && !isolated) {
                return true;
            }
        }

        false
    }

    fn header_storage_of(
        &mut self,
        file: FileId,
        loop_kind: AstKind<'a>,
        classified: bool,
    ) -> Storage {
        let body = loop_body_of(loop_kind).map(|body| body.node_id());
        let iterated = match loop_kind {
            AstKind::ForOfStatement(statement) => Some(&statement.right),
            AstKind::ForInStatement(statement) => Some(&statement.right),
            _ => None,
        };
        let skipped = iterated
            .filter(|_| classified)
            .map(|iterated| iterated.node_id());
        let mut storage = Storage::default();

        for child in self.children_of(file, loop_kind.node_id()) {
            if Some(child) != body && Some(child) != skipped {
                self.collect_storage(file, child, &mut storage);
            }
        }

        if let Some(iterated) = iterated.filter(|_| !classified) {
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
                | AstKind::TaggedTemplateExpression(_)
                | AstKind::JSXElement(_)
                | AstKind::JSXFragment(_) => storage.calls = true,
                _ => {}
            }

            let kind = self.kind_of_node(file, node);

            storage.calls |= self.has_implicit_calls(file, kind);

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

    fn budget_storage_of(&mut self, file: FileId, loop_node: NodeId) -> Option<Storage> {
        let context = self.budget_context.as_ref()?;

        if context.budgets.is_empty() && self.share_bindings.is_empty() {
            return None;
        }

        let function = context.function;
        let counters: Vec<Binding> = context.budgets.keys().copied().collect();
        let budgeted = match self.budget_storage.get(&function) {
            Some(budgeted) => budgeted.clone(),
            None => {
                let budgeted = self.budgeted_loop_storage_of(function, &counters);

                self.budget_storage.insert(function, budgeted.clone());

                budgeted
            }
        };
        let mut storage = Storage {
            unresolved: budgeted.exhausted,
            ..Storage::default()
        };

        let reachable: Vec<Storage> = match function.file == file {
            true => {
                let nodes = self.project.file(file).semantic.nodes();

                budgeted
                    .loops
                    .iter()
                    .filter(|(node, _)| {
                        *node == loop_node || nodes.ancestor_ids(*node).any(|id| id == loop_node)
                    })
                    .map(|(_, found)| found.clone())
                    .collect()
            }
            false => budgeted
                .loops
                .iter()
                .map(|(_, found)| found.clone())
                .collect(),
        };

        for found in reachable {
            storage.merge(found);
        }

        for binding in &self.share_bindings {
            if !storage.bindings.contains(binding) {
                storage.bindings.push(*binding);
            }
        }

        Some(storage)
    }

    fn budgeted_loop_storage_of(
        &mut self,
        function: FunctionId,
        counters: &[Binding],
    ) -> BudgetStorage {
        let file = function.file;
        let mut budgeted = BudgetStorage::default();
        let Some(body) = body_root_of(self.function_at(function)) else {
            return budgeted;
        };

        for kind in self.counted_subtree(file, body, Event::EffectPrepassNode) {
            let (node, tests, body): (NodeId, Vec<&'a Expression<'a>>, &'a Statement<'a>) =
                match kind {
                    AstKind::WhileStatement(statement) => {
                        (statement.node_id(), vec![&statement.test], &statement.body)
                    }
                    AstKind::DoWhileStatement(statement) => {
                        (statement.node_id(), vec![&statement.test], &statement.body)
                    }
                    AstKind::ForStatement(statement) => (
                        statement.node_id(),
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

            budgeted.loops.push((node, found));
        }

        budgeted.exhausted = self.work_exhausted();

        budgeted
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
                        && is_contained_flow(nodes, value_flow_of(nodes, reference.node_id()))
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

fn extend_iterated_arguments<'a>(
    consumed: &mut Vec<(&'a Expression<'a>, bool)>,
    arguments: &'a [Argument<'a>],
    model: &crate::native::NativeModel,
) {
    for (index, argument) in arguments.iter().enumerate() {
        if model.arguments.get(index).copied().unwrap_or(model.rest)
            == crate::native::Role::Iterated
        {
            consumed.extend(argument.as_expression().map(|value| (value, false)));
        }
    }
}

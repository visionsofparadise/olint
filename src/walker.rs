use oxc_ast::ast::{
    Argument, AssignmentTarget, AssignmentTargetRest, BindingPattern, BindingRestElement,
    CallExpression, Class, Expression, FormalParameterRest, FunctionBody, IdentifierReference,
    MemberExpression, MethodDefinitionKind, NewExpression, SpreadElement, Statement,
};
use oxc_ast::{AstKind, AstType};
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::bounds::{loop_label, short};
use crate::budgets::{charge_covers, tests_after_body};
use crate::cost::{Cost, ExecutionPhase, Part, Preference, Reading};
use crate::declarations::{
    function_of_initializer, parameters_of, Binding, Declaration, FunctionNode, ParameterNode,
    TargetSet,
};
use crate::declared_types::Kind;
use crate::directives::{cost_tag_of, preference_of, PerfTag};
use crate::flow::{
    class_phases_of, completion_of, enclosing_iteration_of, interceptions_of, is_suspension,
    loop_phases_of, Completion, Resumption,
};
use crate::invocations::is_inlined_spread;
use crate::native::{Matching, Native, Pattern};
use crate::project::{FileId, Site};
use crate::syntax::{
    body_root_of, identifier_of, is_identifier_pattern, is_iteration_kind, loop_body_of,
    member_expression_of, unwrap, Root,
};
use crate::tables::{
    ARRAY_LINEAR, ARRAY_N_LOG_N, CALLBACK_METHODS, LINEAR_CONSTRUCTORS, MAP_LINEAR, REGEXP_LINEAR,
    SET_LINEAR,
};
use crate::types::ResolvedCallee;
use crate::unknowns::{SourceSpan, UnknownId, UnknownReason};
use crate::values::Construction;
use crate::values::{ArgumentFacts, Definedness};

fn is_type_kind(ty: AstType) -> bool {
    crate::syntax::is_type_kind(ty) || ty == AstType::TSInstantiationExpression
}

fn is_deferred_kind(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
    ) || is_type_kind(kind.ty())
}

fn is_opaque_kind(kind: &AstKind<'_>) -> bool {
    is_deferred_kind(kind) || matches!(kind, AstKind::Class(_))
}

fn is_function_argument(argument: &Argument<'_>) -> bool {
    matches!(
        argument,
        Argument::FunctionExpression(_) | Argument::ArrowFunctionExpression(_)
    )
}

fn is_listed(table: &[&str], name: &str) -> bool {
    table.contains(&name)
}

pub const MAXIMUM_ESCAPE_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Replacement {
    pub transfer: NodeId,
    pub completion: Completion,
}

pub type FinalizerReplacements =
    std::collections::HashMap<(FileId, NodeId), Option<Vec<Replacement>>>;

fn escape_unit_of(escape: Completion) -> &'static str {
    match escape {
        Completion::Return | Completion::Throw => "call",
        _ => "loop",
    }
}

fn is_transfer_kind(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::BreakStatement(_)
            | AstKind::ContinueStatement(_)
            | AstKind::ReturnStatement(_)
            | AstKind::ThrowStatement(_)
    )
}

fn completion_word_of(completion: Completion) -> &'static str {
    match completion {
        Completion::Normal => "normal",
        Completion::Return => "return",
        Completion::Throw => "throw",
        Completion::Break(_) => "break",
        Completion::Continue(_) => "continue",
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn source_span(&self, file: FileId, span: Span) -> SourceSpan {
        SourceSpan {
            file,
            start: span.start,
            end: span.end,
        }
    }

    pub(crate) fn unknown_part(&mut self, file: FileId, span: Span, reason: UnknownReason) -> Part {
        let origin = self.source_span(file, span);
        let unknown = self.unknowns.origin(origin, reason);

        Part::none().retaining(Some(unknown), &mut self.unknowns)
    }

    pub(crate) fn unknown_reading(
        &mut self,
        file: FileId,
        span: Span,
        reason: UnknownReason,
    ) -> Reading {
        self.current_effects.unknown_global = true;

        Reading::of_part(self.unknown_part(file, span, reason))
    }

    pub(crate) fn unknown_invocation(
        &mut self,
        file: FileId,
        span: Span,
        arguments: &'a [Argument<'a>],
        reason: UnknownReason,
    ) -> Reading {
        self.record_unknown_reach(file, None, arguments, span);

        Reading::of_part(self.unknown_part(file, span, reason))
    }

    pub fn cost_of_statement(&mut self, file: FileId, s: &'a Statement<'a>) -> Reading {
        let kind = self.kind_of_node(file, s.node_id());

        self.cost_of_node(file, kind)
    }

    pub fn cost_of_expression(&mut self, file: FileId, e: &'a Expression<'a>) -> Reading {
        let kind = self.kind_of_node(file, e.node_id());

        self.cost_of_node(file, kind)
    }

    pub fn cost_of_function_body(&mut self, file: FileId, function: FunctionNode<'a>) -> Reading {
        match body_root_of(function) {
            Some(Root::Body(body)) => {
                let kind = self.kind_of_node(file, body.node_id());

                self.cost_of_node(file, kind)
            }
            Some(Root::Expression(expression)) => {
                let reading = self.cost_of_expression(file, expression);

                if matches!(function, FunctionNode::Arrow(arrow) if arrow.r#async) {
                    let returned = self.assimilated_reading_of(file, expression);

                    reading.merge(returned, &mut self.unknowns, &mut self.traces)
                } else {
                    reading
                }
            }
            _ => Reading::empty(),
        }
    }

    pub(crate) fn cost_of_parameters(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
    ) -> Option<Reading> {
        let parameters = parameters_of(function)?;
        let mut reading: Option<Reading> = None;

        for parameter in &parameters.items {
            if let Some(initializer) = &parameter.initializer {
                let definedness = self.parameter_definedness_of(file, parameter);

                if definedness != Definedness::Defined {
                    let kind = self.kind_of_node(file, initializer.node_id());
                    let cost = self.cost_of_node(file, kind);
                    let cost = self.sibling_of(file, kind, cost);

                    reading = Some(self.merge_parameter(reading, cost));
                }

                if definedness == Definedness::Undefined {
                    self.bind_parameter_default(file, parameter);
                }
            }

            if !is_identifier_pattern(&parameter.pattern) {
                let kind = self.kind_of_node(file, parameter.pattern.node_id());
                let cost = self.cost_of_node(file, kind);
                let cost = self.sibling_of(file, kind, cost);

                reading = Some(self.merge_parameter(reading, cost));
            }
        }

        if let Some(rest) = parameters.rest.as_ref() {
            if let Some(cost) = self.cost_of_parameter_rest(file, rest) {
                reading = Some(self.merge_parameter(reading, cost));
            }

            if !is_identifier_pattern(&rest.rest.argument) {
                let kind = self.kind_of_node(file, rest.rest.argument.node_id());
                let cost = self.cost_of_node(file, kind);
                let cost = self.sibling_of(file, kind, cost);

                reading = Some(self.merge_parameter(reading, cost));
            }
        }

        reading
    }

    fn cost_of_parameter_rest(
        &mut self,
        file: FileId,
        rest: &'a FormalParameterRest<'a>,
    ) -> Option<Reading> {
        if self.collected_arguments_are_constant(file, &rest.rest.argument) {
            return None;
        }

        let label = self.rest_label_of(file, rest.rest.span);
        let site = self.site_of_node(file, rest.node_id());
        let part = self.nest_part(
            label,
            site,
            self.source_span(file, rest.rest.span),
            Cost::N,
            Part::unmarked(Cost::ONE, None),
        );

        Some(Reading::of_part(part))
    }

    fn collected_arguments_are_constant(
        &mut self,
        file: FileId,
        argument: &'a BindingPattern<'a>,
    ) -> bool {
        let BindingPattern::BindingIdentifier(identifier) = argument else {
            return false;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            return false;
        };

        self.is_constant_collection(Binding::Symbol { file, symbol })
    }

    fn is_constant_collection(&mut self, binding: Binding) -> bool {
        if !self.is_parameter_unwritten(binding) {
            return false;
        }

        self.current_substitutions
            .get(&binding)
            .and_then(|facts| facts.value.size.as_ref())
            .is_some_and(Cost::is_one)
    }

    fn rest_label_of(&self, file: FileId, span: Span) -> String {
        let written = self.text_of(file, span);

        format!(
            "spread ...{}",
            short(written.strip_prefix("...").unwrap_or(written).trim_start())
        )
    }

    fn merge_parameter(&mut self, reading: Option<Reading>, cost: Reading) -> Reading {
        match reading {
            Some(reading) => reading.merge(cost, &mut self.unknowns, &mut self.traces),
            None => cost,
        }
    }

    pub(crate) fn kind_of_node(&self, file: FileId, node: NodeId) -> AstKind<'a> {
        self.project.file(file).semantic.nodes().kind(node)
    }

    pub(crate) fn site_of_node(&self, file: FileId, node: NodeId) -> Site {
        let span = self.kind_of_node(file, node).span();

        self.project.site_of(file, span)
    }

    pub(crate) fn children_of(&mut self, file: FileId, node: NodeId) -> Vec<NodeId> {
        let project = self.project;

        if !self.children.contains_key(&file)
            && !self.charge_work(
                Event::GraphNode,
                project.file(file).semantic.nodes().len() as u64,
            )
        {
            return Vec::new();
        }

        self.children.entry(file).or_insert_with(|| {
            let nodes = project.file(file).semantic.nodes();
            let mut children: Vec<Vec<NodeId>> = vec![Vec::new(); nodes.len()];

            for (id, _) in nodes.iter_enumerated() {
                let parent = nodes.parent_id(id);

                if parent != id {
                    children[parent.index()].push(id);
                }
            }

            for list in &mut children {
                list.sort_by_key(|child| (nodes.kind(*child).span().start, child.index()));
            }

            children
        });

        let count = self.children[&file][node.index()].len();

        if !self.charge_work(Event::TraversalEdge, count as u64) {
            return Vec::new();
        }

        self.children[&file][node.index()].clone()
    }

    fn cost_of_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> Reading {
        let kind = self.kind_of_node(file, argument.node_id());

        self.cost_of_node(file, kind)
    }

    fn cost_of_node(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        if !self.charge_work(Event::WalkerNode, 1) {
            return Reading::of_part(self.deferred_unknown(
                file,
                kind.span(),
                UnknownReason::ResourceExhaustion,
            ));
        }

        let iteration = is_iteration_kind(&kind);

        if iteration {
            if let Some(reading) = self.stable_loop(file, kind.node_id()) {
                return reading;
            }
        }

        let serial = self.contribution_serial();
        let diagnostics = (self.warnings.len(), self.errors.len());
        let scoped = self.pending_scoped.is_empty() && self.share_bindings.is_empty();
        let reading = self.cost_of_node_inner(file, kind);

        if iteration && scoped {
            self.retain_stable_loop(file, kind.node_id(), serial, diagnostics, &reading);
        }

        reading
    }

    fn cost_of_node_inner(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        if is_deferred_kind(&kind) {
            return Reading::empty();
        }

        self.record_write_effects(file, kind);

        let tags = self.perf_tags(file, kind).to_vec();

        if tags.contains(&PerfTag::Ignore) {
            self.current_effects.unknown_global |= self.opaque_effects_at(file, kind.node_id());

            self.stats.count("@perf ignore: statement");

            return Reading::empty();
        }

        if holds_function(&kind) {
            return self.reading_of_node(file, kind, &tags);
        }

        let site = self.site_of_node(file, kind.node_id());

        self.warn_conflict(&tags, site);

        let Some(preference) = preference_of(&tags) else {
            return self.reading_of_node(file, kind, &tags);
        };

        self.stats.count(if preference == Preference::Hot {
            "@perf hot: statement"
        } else {
            "@perf cold: statement"
        });

        let outer = std::mem::take(&mut self.pending_scoped);
        let reading = self.reading_of_node(file, kind, &tags);
        let inner = std::mem::replace(&mut self.pending_scoped, outer);

        for (scope, part) in inner {
            let pending = self.pending_scoped.remove(&scope).unwrap_or_default().max(
                part.preferred(preference),
                &mut self.unknowns,
                &mut self.traces,
            );

            self.pending_scoped.insert(scope, pending);
        }

        reading.preferred(preference)
    }

    fn reading_of_node(&mut self, file: FileId, kind: AstKind<'a>, tags: &[PerfTag]) -> Reading {
        let iteration = is_iteration_kind(&kind);

        if tags.contains(&PerfTag::Bounded) && !iteration {
            self.current_effects.unknown_global |= self.opaque_effects_at(file, kind.node_id());

            self.stats.count("@perf bounded: statement");

            return Reading::empty();
        }

        if let Some((cost, text)) = cost_tag_of(tags) {
            self.current_effects.unknown_global |= self.opaque_effects_at(file, kind.node_id());

            self.stats.count(if iteration {
                "@perf O(...): loop"
            } else {
                "@perf O(...): statement"
            });

            let site = self.site_of_node(file, kind.node_id());

            let (cost, unresolved) = match cost.bind_known(&mut |cost| self.bind_current_cost(cost))
            {
                Ok(bound) => bound,
                Err(crate::cost::CostError::Resource | crate::cost::CostError::Overflow) => {
                    return self.unknown_reading(
                        file,
                        kind.span(),
                        UnknownReason::ResourceExhaustion,
                    );
                }
                Err(error) => {
                    self.errors.insert(format!(
                        "invalid {text} at {}:{}: {error:?}",
                        self.project.file(file).relative,
                        site.line
                    ));

                    return self.unknown_reading(
                        file,
                        kind.span(),
                        UnknownReason::UnsupportedModel,
                    );
                }
            };

            let mut reading = tagged_reading_of(
                cost.unwrap_or(Cost::ONE),
                &text,
                site,
                self.source_span(file, kind.span()),
                &mut self.traces,
                &mut self.unknowns,
            );

            if unresolved {
                let unknown = self.unknown_reading(file, kind.span(), UnknownReason::SizeRelation);
                let mut main = reading.main();
                main.unknowns = self.unknowns.join(main.unknowns, unknown.main().unknowns);
                reading = reading.with_main(main);
            }

            return reading;
        }

        match kind {
            AstKind::IfStatement(statement) => {
                let mut reading = self.cost_of_expression(file, &statement.test);
                let mut branches = vec![&statement.consequent];

                if let Some(alternate) = &statement.alternate {
                    branches.push(alternate);
                }

                for branch in branches {
                    let part = self.branch_reading_of(file, branch, statement.node_id());
                    let kind = self.kind_of_node(file, branch.node_id());

                    reading = reading.merge(
                        self.sibling_of(file, kind, part),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }

                if statement.alternate.is_none() {
                    reading = reading.merge(
                        Reading::empty().sibling(),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }

                reading
            }
            AstKind::SwitchStatement(statement) => {
                let mut reading = self.cost_of_expression(file, &statement.discriminant);

                for case in &statement.cases {
                    let case = self.kind_of_node(file, case.node_id());
                    let part = self.cost_of_node(file, case);

                    reading = reading.merge(
                        self.sibling_of(file, case, part),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }

                reading
            }
            AstKind::TryStatement(statement) => {
                let mut parts = vec![self.kind_of_node(file, statement.block.node_id())];

                if let Some(handler) = &statement.handler {
                    parts.push(self.kind_of_node(file, handler.node_id()));
                }

                if let Some(finalizer) = &statement.finalizer {
                    parts.push(self.kind_of_node(file, finalizer.node_id()));
                }

                let mut reading = Reading::empty();

                for part in parts {
                    let cost = self.cost_of_node(file, part);

                    reading = reading.merge(
                        self.sibling_of(file, part, cost),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }

                reading
            }
            AstKind::BlockStatement(block) => self.cost_of_statements(file, None, &block.body),
            AstKind::StaticBlock(block) => self.cost_of_statements(file, None, &block.body),
            AstKind::PropertyDefinition(property) => match &property.value {
                Some(value) => self.cost_of_expression(file, value),
                None => Reading::empty(),
            },
            AstKind::AccessorProperty(accessor) => match &accessor.value {
                Some(value) => self.cost_of_expression(file, value),
                None => Reading::empty(),
            },
            AstKind::Class(class) => self.cost_of_class_definition(file, class),
            AstKind::FunctionBody(body) => self.cost_of_function_statements(file, body),
            AstKind::TSModuleBlock(block) => self.cost_of_statements(file, None, &block.body),
            AstKind::SwitchCase(case) => {
                self.cost_of_statements(file, case.test.as_ref(), &case.consequent)
            }
            _ if iteration => self.cost_of_loop(file, kind),
            AstKind::ReturnStatement(statement) => self.cost_of_exit(
                file,
                statement.argument.as_ref(),
                statement.node_id(),
                Completion::Return,
            ),
            AstKind::ThrowStatement(statement) => self.cost_of_exit(
                file,
                Some(&statement.argument),
                statement.node_id(),
                Completion::Throw,
            ),
            AstKind::SpreadElement(spread) => self.cost_of_spread(file, spread),
            AstKind::JSXSpreadAttribute(spread) if is_inlined_spread(&spread.argument) => {
                let inner = self.cost_of_expression(file, &spread.argument);

                match self.jsx_spread_part_of(file, kind) {
                    Some(part) => {
                        inner.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces)
                    }
                    None => inner,
                }
            }
            AstKind::JSXSpreadAttribute(spread) => {
                let implicit = self.jsx_spread_part_of(file, kind);

                self.cost_of_spread_copy(
                    file,
                    (spread.node_id(), spread.span),
                    &spread.argument,
                    implicit,
                )
            }
            AstKind::JSXSpreadChild(child) => {
                let implicit = self.jsx_spread_part_of(file, kind);

                self.cost_of_spread_copy(
                    file,
                    (child.node_id(), child.span),
                    &child.expression,
                    implicit,
                )
            }
            AstKind::AssignmentTargetRest(rest) => self.cost_of_rest_target(file, rest),
            AstKind::BindingRestElement(rest) => self.cost_of_binding_rest(file, rest),
            AstKind::NewExpression(new) => self.cost_of_new(file, new),
            AstKind::CallExpression(call) => self.cost_of_call(file, call),
            AstKind::TaggedTemplateExpression(tagged) => {
                let mut reading = self.cost_of_callee(file, &tagged.tag);

                for expression in &tagged.quasi.expressions {
                    let cost = self.cost_of_expression(file, expression);

                    reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
                }

                let tag = self.tag_part_of(file, tagged);

                reading.merge(Reading::of_part(tag), &mut self.unknowns, &mut self.traces)
            }
            _ => {
                if let AstKind::YieldExpression(yielded) = kind {
                    self.count_yield(file, yielded);
                }

                let mut reading = Reading::empty();

                for child in self.children_of(file, kind.node_id()) {
                    let child = self.kind_of_node(file, child);
                    let cost = self.cost_of_node(file, child);

                    reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
                }

                let implicit = self.implicit_reading_of(file, kind);

                if let AstKind::YieldExpression(yielded) = kind {
                    if !yielded.delegate && self.is_async_context(file, yielded.node_id(), true) {
                        if let Some(argument) = &yielded.argument {
                            let returned = self.async_generator_resolution_of(file, argument);

                            reading = reading.merge(returned, &mut self.unknowns, &mut self.traces);
                        }
                    }
                }

                reading.merge(implicit, &mut self.unknowns, &mut self.traces)
            }
        }
    }

    fn cost_of_statements(
        &mut self,
        file: FileId,
        test: Option<&'a Expression<'a>>,
        statements: &'a [Statement<'a>],
    ) -> Reading {
        let mut reading = match test {
            Some(test) => self.cost_of_expression(file, test),
            None => Reading::empty(),
        };

        let asynchronous = statements
            .first()
            .is_some_and(|statement| self.is_async_context(file, statement.node_id(), false));
        let mut suspended = None;

        for statement in statements {
            let kind = self.kind_of_node(file, statement.node_id());
            let cost = self.cost_of_node(file, kind);
            let mut cost = self.sibling_of(file, kind, cost);
            let contains = asynchronous && self.suspends(file, statement.node_id());
            let definite = contains && self.direct_suspension_of(file, statement);

            if contains
                && !definite
                && cost.completions.iter().any(|channel| {
                    channel.0 == ExecutionPhase::Immediate && !channel.2.cost.is_one()
                })
            {
                cost = self.uncertain_phase_of(file, statement.node_id(), cost);
            }

            let cost = match suspended {
                Some((node, true)) => cost
                    .map_parts(|part| match part.cost.is_one() {
                        true => part,
                        false => part.explain(
                            "continuation after await [scheduled]",
                            self.site_of_node(file, node),
                            self.source_span(file, self.kind_of_node(file, node).span()),
                            false,
                            &mut self.traces,
                            &mut self.unknowns,
                        ),
                    })
                    .in_phase(
                        ExecutionPhase::Scheduled,
                        &mut self.unknowns,
                        &mut self.traces,
                    ),
                Some((node, false)) => self.uncertain_phase_of(file, node, cost),
                None => cost,
            };

            reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);

            if contains && (definite || suspended.is_none()) {
                suspended = Some((statement.node_id(), definite));
            }
        }

        reading
    }

    fn direct_suspension_of(&mut self, file: FileId, statement: &'a Statement<'a>) -> bool {
        let expression = match statement {
            Statement::ExpressionStatement(statement) => Some(&statement.expression),
            Statement::ReturnStatement(statement) => statement.argument.as_ref(),
            Statement::VariableDeclaration(declaration) if declaration.declarations.len() == 1 => {
                declaration.declarations[0].init.as_ref()
            }
            _ => None,
        };

        match expression.map(unwrap) {
            Some(Expression::AwaitExpression(awaited)) => {
                !self.suspends(file, awaited.argument.node_id())
            }
            _ => false,
        }
    }

    fn uncertain_phase_of(&mut self, file: FileId, node: NodeId, reading: Reading) -> Reading {
        let unknown = self.unknowns.origin(
            self.source_span(file, self.kind_of_node(file, node).span()),
            UnknownReason::UnsupportedModel,
        );
        let reading = reading.retaining(Some(unknown), &mut self.unknowns);
        let scheduled = reading.clone().in_phase(
            ExecutionPhase::Scheduled,
            &mut self.unknowns,
            &mut self.traces,
        );

        reading.merge(scheduled, &mut self.unknowns, &mut self.traces)
    }

    fn cost_of_function_statements(&mut self, file: FileId, body: &'a FunctionBody<'a>) -> Reading {
        self.cost_of_statements(file, None, &body.statements)
    }

    pub(crate) fn suspends(&mut self, file: FileId, node: NodeId) -> bool {
        let mut pending = vec![(node, false)];

        while let Some((current, visited)) = pending.pop() {
            if self.suspensions.contains_key(&(file, current)) {
                continue;
            }

            if self.work_exhausted() {
                return true;
            }

            let kind = self.kind_of_node(file, current);

            if is_suspension(&kind) || is_deferred_kind(&kind) {
                self.suspensions
                    .insert((file, current), is_suspension(&kind));
            } else if visited {
                let suspends = self.children_of(file, current).into_iter().any(|child| {
                    self.suspensions
                        .get(&(file, child))
                        .copied()
                        .unwrap_or(false)
                });

                if self.work_exhausted() {
                    return true;
                }

                self.suspensions.insert((file, current), suspends);
            } else {
                pending.push((current, true));
                pending.extend(
                    self.children_of(file, current)
                        .into_iter()
                        .map(|child| (child, false)),
                );
            }
        }

        self.suspensions
            .get(&(file, node))
            .copied()
            .unwrap_or(false)
    }

    fn is_async_context(&self, file: FileId, node: NodeId, generator: bool) -> bool {
        self.project
            .file(file)
            .semantic
            .nodes()
            .ancestors(node)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => {
                    Some(function.r#async && function.generator == generator)
                }
                AstKind::ArrowFunctionExpression(arrow) => Some(arrow.r#async && !generator),
                _ => None,
            })
            .unwrap_or(false)
    }

    fn async_generator_resolution_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Reading {
        let reading = self.assimilated_reading_of(file, expression);

        if self.is_primitive_operand(file, expression) {
            return reading;
        }

        let unknown = self.unknown_part(file, expression.span(), UnknownReason::UnsupportedModel);

        reading.merge(
            Reading::of_part(unknown),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn sibling_of(&mut self, file: FileId, kind: AstKind<'a>, reading: Reading) -> Reading {
        if is_opaque_kind(&kind) || self.perf_tags(file, kind).contains(&PerfTag::Ignore) {
            return reading;
        }

        reading.sibling()
    }

    fn nest_part(
        &mut self,
        label: String,
        site: Site,
        origin: crate::unknowns::SourceSpan,
        factor: Cost,
        inner: Part,
    ) -> Part {
        crate::cost::nest(
            label,
            site,
            origin,
            factor,
            inner,
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn nest_reading(
        &mut self,
        label: String,
        site: Site,
        origin: crate::unknowns::SourceSpan,
        factor: Cost,
        reading: Reading,
    ) -> Reading {
        reading.map_parts(|part| self.nest_part(label.clone(), site, origin, factor.clone(), part))
    }

    fn absorbed_escapes_of(
        &mut self,
        file: FileId,
        iteration: NodeId,
        reading: &mut Reading,
    ) -> Reading {
        let mut absorbed = Reading::empty();
        let mut kept = Vec::new();

        for (phase, completion, part) in std::mem::take(&mut reading.completions) {
            if completion != Completion::Normal && self.absorbs_escape(file, completion, iteration)
            {
                absorbed.join(
                    phase,
                    Completion::Normal,
                    part,
                    &mut self.unknowns,
                    &mut self.traces,
                );

                continue;
            }

            kept.push((phase, completion, part));
        }

        reading.completions = kept;

        absorbed
    }

    fn append_linear_operation(
        &mut self,
        reading: Reading,
        label: String,
        site: Site,
        (file, span): (FileId, Span),
    ) -> Reading {
        let part = self.nest_part(
            label,
            site,
            self.source_span(file, span),
            Cost::N,
            Part::unmarked(Cost::ONE, None),
        );

        reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces)
    }

    fn append_call(
        &mut self,
        reading: Reading,
        target: FileId,
        function: FunctionNode<'a>,
        part: Reading,
        cyclic: bool,
    ) -> Reading {
        let called = self.called_reading_of(target, function, part, cyclic);

        reading.merge(
            Reading::of_part(called),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    pub(crate) fn exits_iteration(
        &self,
        file: FileId,
        escape: Completion,
        iteration: NodeId,
    ) -> bool {
        match escape {
            Completion::Break(target) => {
                target == iteration || self.is_ancestor(file, target, iteration)
            }
            Completion::Continue(target) => {
                target != iteration && self.is_ancestor(file, target, iteration)
            }
            _ => false,
        }
    }

    fn absorbs_escape(&self, file: FileId, escape: Completion, iteration: NodeId) -> bool {
        if !self.exits_iteration(file, escape, iteration) {
            return false;
        }

        let semantic = &self.project.file(file).semantic;

        match enclosing_iteration_of(semantic, iteration) {
            Some(outer) => !self.exits_iteration(file, escape, outer),
            None => true,
        }
    }

    fn weaker_escape_of(&self, file: FileId, held: Completion, other: Completion) -> Completion {
        let boundary_of = |escape: Completion| match escape {
            Completion::Break(target) | Completion::Continue(target) => Some(target),
            _ => None,
        };
        let (Some(mine), Some(theirs)) = (boundary_of(held), boundary_of(other)) else {
            return match boundary_of(other).is_some() {
                true => other,
                false => held,
            };
        };

        if mine == theirs {
            return match matches!(other, Completion::Continue(_)) {
                true => other,
                false => held,
            };
        }

        match self.is_ancestor(file, mine, theirs) {
            true => other,
            false => held,
        }
    }

    fn escape_of(
        &self,
        file: FileId,
        completion: Completion,
        enclosing: NodeId,
    ) -> Option<Completion> {
        match completion {
            Completion::Return | Completion::Throw => Some(completion),
            Completion::Break(_) | Completion::Continue(_)
                if self.exits_iteration(file, completion, enclosing) =>
            {
                Some(completion)
            }
            _ => None,
        }
    }

    fn targets_within(
        &self,
        file: FileId,
        branch: NodeId,
        node: NodeId,
        completion: Completion,
    ) -> bool {
        match completion {
            Completion::Break(target) | Completion::Continue(target) => {
                target != branch && self.is_ancestor(file, branch, target)
            }
            Completion::Throw => self.caught_within(file, branch, node),
            _ => false,
        }
    }

    fn caught_within(&self, file: FileId, region: NodeId, node: NodeId) -> bool {
        let semantic = &self.project.file(file).semantic;

        interceptions_of(semantic, node)
            .into_iter()
            .find_map(|interception| match interception.resumption {
                Resumption::Handler(_) => Some(interception.statement),
                Resumption::Finalizer(_) => None,
            })
            .is_some_and(|statement| {
                statement == region || self.is_ancestor(file, region, statement)
            })
    }

    fn finalizer_replacements_of(
        &mut self,
        file: FileId,
        finalizer: NodeId,
    ) -> Option<Vec<Replacement>> {
        if let Some(cached) = self.finalizer_replacements.get(&(file, finalizer)) {
            return cached.clone();
        }

        let project = self.project;
        let semantic = &project.file(file).semantic;
        let mut found = Vec::new();
        let mut pending = vec![finalizer];
        let mut resolved = true;

        while let Some(node) = pending.pop() {
            let kind = self.kind_of_node(file, node);

            if is_deferred_kind(&kind) {
                continue;
            }

            if is_transfer_kind(&kind) {
                match completion_of(semantic, node) {
                    Some(completion) if !self.targets_within(file, finalizer, node, completion) => {
                        found.push(Replacement {
                            transfer: node,
                            completion,
                        })
                    }
                    Some(_) => {}
                    None => resolved = false,
                }
            }

            pending.extend(self.children_of(file, node));
        }

        let replacements = resolved.then_some(found);

        if !self.work_exhausted() {
            self.finalizer_replacements
                .insert((file, finalizer), replacements.clone());
        }

        replacements
    }

    fn escape_of_completion(
        &mut self,
        file: FileId,
        node: NodeId,
        completion: Completion,
        enclosing: NodeId,
        depth: usize,
    ) -> Option<Completion> {
        if depth >= MAXIMUM_ESCAPE_DEPTH {
            self.escape_depth_exhausted = true;

            return None;
        }

        let key = (file, node, completion, enclosing);

        if let Some(cached) = self.completion_escapes.get(&key) {
            return *cached;
        }

        self.completion_escapes.insert(key, None);

        let held = self.escape_depth_exhausted;
        self.escape_depth_exhausted = false;

        let resolved = self.resolved_escape_of(file, node, completion, enclosing, depth);
        let exhausted = self.escape_depth_exhausted;

        self.escape_depth_exhausted = held || exhausted;

        if !self.work_exhausted() && !exhausted {
            self.completion_escapes.insert(key, resolved);
        } else {
            self.completion_escapes.remove(&key);
        }

        resolved
    }

    fn resolved_escape_of(
        &mut self,
        file: FileId,
        node: NodeId,
        completion: Completion,
        enclosing: NodeId,
        depth: usize,
    ) -> Option<Completion> {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let mut escape = self.escape_of(file, completion, enclosing)?;

        for interception in interceptions_of(semantic, node) {
            let inside = self.is_ancestor(file, enclosing, interception.statement);
            let caught = Completion::Break(interception.statement);

            match interception.resumption {
                Resumption::Handler(_) if inside => return None,
                Resumption::Handler(_) => escape = self.weaker_escape_of(file, escape, caught),
                Resumption::Finalizer(finalizer) => {
                    let replacements = self.finalizer_replacements_of(file, finalizer);

                    if self.work_exhausted() {
                        return None;
                    }

                    let Some(replacements) = replacements else {
                        if inside {
                            return None;
                        }

                        escape = self.weaker_escape_of(file, escape, caught);

                        continue;
                    };

                    if !inside {
                        if !replacements.is_empty() {
                            escape = self.weaker_escape_of(file, escape, caught);
                        }

                        continue;
                    }

                    for replacement in replacements {
                        let replaced = self.escape_of_completion(
                            file,
                            replacement.transfer,
                            replacement.completion,
                            enclosing,
                            depth + 1,
                        )?;

                        escape = self.weaker_escape_of(file, escape, replaced);
                    }
                }
            }
        }

        Some(escape)
    }

    fn branch_escape_of(
        &mut self,
        file: FileId,
        body: &'a Statement<'a>,
        site_node: NodeId,
    ) -> Option<(Completion, Completion)> {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let branch = body.node_id();
        let completion = completion_of(semantic, branch)?;
        let enclosing = enclosing_iteration_of(semantic, site_node)?;
        let mut escape = self.escape_of_completion(file, branch, completion, enclosing, 0)?;
        let mut pending = vec![branch];

        while let Some(node) = pending.pop() {
            let kind = self.kind_of_node(file, node);

            if is_deferred_kind(&kind) {
                continue;
            }

            if is_transfer_kind(&kind) {
                let transfer = completion_of(semantic, node)
                    .filter(|transfer| !self.targets_within(file, branch, node, *transfer));

                if let Some(transfer) = transfer {
                    let resolved = self.escape_of_completion(file, node, transfer, enclosing, 0)?;

                    escape = self.weaker_escape_of(file, escape, resolved);
                }
            }

            pending.extend(self.children_of(file, node));
        }

        if self.work_exhausted() {
            return None;
        }

        Some((completion, escape))
    }

    fn branch_reading_of(
        &mut self,
        file: FileId,
        body: &'a Statement<'a>,
        site_node: NodeId,
    ) -> Reading {
        let reading = self.cost_of_statement(file, body);

        if reading
            .completions
            .iter()
            .all(|channel| channel.2.cost.is_one())
        {
            return reading;
        }

        self.escape_depth_exhausted = false;

        let escaped = self.branch_escape_of(file, body, site_node);
        let exhausted = std::mem::take(&mut self.escape_depth_exhausted);

        let Some((completion, escape)) = escaped else {
            return self.depth_exhausted_reading(file, site_node, reading, exhausted);
        };
        let mut lifted_reading = Reading::empty();

        for (phase, channel, part) in reading.completions {
            if channel != Completion::Normal {
                lifted_reading.join(phase, channel, part, &mut self.unknowns, &mut self.traces);

                continue;
            }

            let lifted = part.explain(
                format_args!(
                    "[{} branch: runs once per {}]",
                    completion_word_of(completion),
                    escape_unit_of(escape)
                ),
                self.site_of_node(file, site_node),
                self.source_span(file, self.kind_of_node(file, site_node).span()),
                false,
                &mut self.traces,
                &mut self.unknowns,
            );

            lifted_reading.join(phase, escape, lifted, &mut self.unknowns, &mut self.traces);
        }

        lifted_reading
    }

    fn depth_exhausted_reading(
        &mut self,
        file: FileId,
        node: NodeId,
        reading: Reading,
        exhausted: bool,
    ) -> Reading {
        if !exhausted {
            return reading;
        }

        let origin = self.source_span(file, self.kind_of_node(file, node).span());
        let unknown = self
            .unknowns
            .origin(origin, UnknownReason::ResourceExhaustion);
        let main = reading.main().retaining(Some(unknown), &mut self.unknowns);

        reading.with_main(main)
    }

    fn cost_of_loop(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        let node = kind.node_id();
        let body = loop_body_of(kind).expect("an iteration statement has a body");
        let body_node = body.node_id();
        let mut sibling = Reading::empty();
        let mut visit = Reading::empty();
        let mut unresolved = false;
        let phases = loop_phases_of(kind);

        for child in self.children_of(file, node) {
            if child == body_node {
                continue;
            }

            let repeated = phases.is_some_and(|phases| phases.repeats(child));
            let child = self.kind_of_node(file, child);
            let cost = self.cost_of_node(file, child);

            if repeated {
                visit = visit.merge(cost, &mut self.unknowns, &mut self.traces);
            } else {
                sibling = sibling.merge(cost, &mut self.unknowns, &mut self.traces);
            }
        }

        if let AstKind::ForOfStatement(statement) = kind {
            let parts = self.iteration_parts_of(file, statement);

            unresolved = parts.unresolved;
            visit = visit.merge(
                Reading::of_part(parts.next),
                &mut self.unknowns,
                &mut self.traces,
            );

            for part in [parts.acquire, parts.close] {
                sibling =
                    sibling.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
            }

            let iteration = self.iteration_of(file, &statement.right, statement.r#await);

            if let Some(latent) = self.iteration_latent_of(file, &statement.right, &iteration) {
                let consumed = self.consumed_part_of(file, statement.right.span(), &latent);

                sibling = sibling.merge(
                    Reading::of_part(consumed),
                    &mut self.unknowns,
                    &mut self.traces,
                );
            }
        }

        let mut invalidation = self.loop_invalidation_of(file, kind);

        invalidation.bound |= unresolved;
        let assumed_bound = self.perf_tags(file, kind).contains(&PerfTag::Bounded);
        let saved_budget = invalidation.budget.then(|| self.budget_context.take());
        let saved_shares = invalidation
            .budget
            .then(|| std::mem::take(&mut self.share_bindings));
        let bound = self.bound_of(file, kind);
        let mut factor = bound.factor().cloned().unwrap_or(Cost::N);

        invalidation.bound |= bound.is_unresolved();

        if let (AstKind::ForOfStatement(statement), true) = (kind, factor == Cost::N) {
            if let Some(size) = self.produced_size_of(file, &statement.right) {
                if size.exceeds {
                    factor = size.length;
                }

                if !size.length_resolved {
                    let unresolved = self.unknown_part(
                        file,
                        statement.right.span(),
                        UnknownReason::SizeRelation,
                    );

                    sibling = sibling.merge(
                        Reading::of_part(unresolved),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }
            }
        }

        let spend = if factor.is_one() {
            None
        } else {
            self.spent_budget(file, kind)
        };
        let budget = spend.filter(|spend| spend.scope != Some(node));
        let visits = budget
            .as_ref()
            .and_then(|budget| self.visits_since(file, budget.scope));
        let granted = match (&budget, &visits) {
            (Some(budget), Some(visits)) => budget.share.filter(|_| {
                visits
                    .multiply(&factor)
                    .is_ok_and(|charge| charge_covers(&charge, &budget.potential.cost()))
            }),
            _ => None,
        };

        if let Some(share) = granted {
            self.share_bindings.push(share);
        }

        self.enclosing_factors.push((
            file,
            node,
            factor.clone(),
            assumed_bound || !invalidation.bound,
        ));

        let suspends = self.is_async_context(file, body.node_id(), false)
            && self.suspends(file, body.node_id());
        let body_raw =
            self.cost_of_statement(file, body)
                .merge(visit, &mut self.unknowns, &mut self.traces);

        self.enclosing_factors.pop();

        if granted.is_some() {
            self.share_bindings.pop();
        }

        if let Some(context) = saved_budget {
            self.budget_context = context;
        }

        if let Some(shares) = saved_shares {
            self.share_bindings = shares;
        }

        let phases = [
            ExecutionPhase::Immediate,
            ExecutionPhase::Scheduled,
            ExecutionPhase::Lazy,
        ];
        let mut body = body_raw;

        if suspends && !factor.is_one() && !body.main().cost.is_one() {
            let unknown = self.unknowns.origin(
                self.source_span(file, kind.span()),
                UnknownReason::UnsupportedModel,
            );
            let prefix = body.main().retaining(Some(unknown), &mut self.unknowns);

            body = body.with_main(prefix.clone());

            body.join(
                ExecutionPhase::Scheduled,
                Completion::Normal,
                prefix,
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        for phase in phases {
            if let Some(hoisted) = self.pending_scoped.remove(&(file, node, phase)) {
                body.join(
                    phase,
                    Completion::Normal,
                    hoisted,
                    &mut self.unknowns,
                    &mut self.traces,
                );
            }
        }

        let absorbed = self.absorbed_escapes_of(file, node, &mut body);
        let mut escaping = body.clone();

        escaping
            .completions
            .retain(|channel| channel.1 != Completion::Normal);

        let escaped = absorbed
            .completions
            .iter()
            .any(|channel| !channel.2.is_absent())
            || escaping.escapes().any(|channel| !channel.2.is_absent());
        let mut result = sibling.merge(escaping, &mut self.unknowns, &mut self.traces);
        let scope = budget
            .as_ref()
            .and_then(|budget| budget.scope)
            .filter(|scope| self.is_ancestor(file, *scope, node));

        let cancels = budget.as_ref().is_some_and(|budget| {
            budget.cancels()
                && charge_covers(&factor, &budget.potential.cost())
                && match tests_after_body(kind) {
                    true => visits
                        .as_ref()
                        .is_some_and(|visits| charge_covers(&factor, visits)),
                    false => true,
                }
        });

        if let Some(budget) = &budget {
            self.stats.count(&format!(
                "loop {}: budget{}{}{}",
                loop_label(kind),
                match (budget.share.is_some(), granted.is_some()) {
                    (true, true) => " by share",
                    (true, false) => " by withheld share",
                    _ => "",
                },
                if scope.is_some() { " (scoped)" } else { "" },
                if cancels { "" } else { " (spent per visit)" }
            ));
        }

        let mut label = loop_label(kind).to_string();

        if let Some(proof) = bound.proof() {
            label.push_str(&format!(" [{proof}]"));
        }

        if let Some(budget) = &budget {
            let per = match scope {
                Some(scope) => format!(
                    ", per {} at {}",
                    loop_label(self.kind_of_node(file, scope)),
                    self.site_of_node(file, scope).line
                ),
                None => String::new(),
            };

            label.push_str(&format!(" [budget: {}{}]", budget.text, per));
        }

        let site = self.site_of_node(file, node);
        let origin = self.source_span(file, kind.span());

        for phase in phases {
            let body_main = body.part_of(phase, Completion::Normal);
            let absorbed = absorbed.part_of(phase, Completion::Normal);

            if phase != ExecutionPhase::Immediate
                && body_main == Part::none()
                && absorbed == Part::none()
            {
                continue;
            }

            if invalidation.bound && !assumed_bound {
                let reason = bound.reason().unwrap_or(UnknownReason::Bound);
                let mut unknown = Some(self.unknowns.origin(origin, reason));

                if self.fallback_active() {
                    let resource = self
                        .unknowns
                        .origin(origin, UnknownReason::ResourceExhaustion);
                    unknown = self.unknowns.join(unknown, Some(resource));
                }

                let unresolved = self.unknowns.scale(unknown, None);

                self.note_unresolved_multiplicity(&body_main);

                let main = body_main
                    .scaled(None, &mut self.unknowns)
                    .retaining(unresolved, &mut self.unknowns)
                    .max(absorbed, &mut self.unknowns, &mut self.traces);

                result.join(
                    phase,
                    Completion::Normal,
                    main,
                    &mut self.unknowns,
                    &mut self.traces,
                );

                continue;
            }

            if factor.is_one() {
                let main = body_main.max(absorbed, &mut self.unknowns, &mut self.traces);

                result.join(
                    phase,
                    Completion::Normal,
                    main,
                    &mut self.unknowns,
                    &mut self.traces,
                );

                continue;
            }

            let looped = self.nest_part(label.clone(), site, origin, factor.clone(), body_main);
            let looped = match escaped {
                true => looped,
                false => looped.executed(),
            };

            result.join(
                phase,
                Completion::Normal,
                absorbed,
                &mut self.unknowns,
                &mut self.traces,
            );

            if let (true, Some(scope)) = (cancels, scope) {
                let pending = self
                    .pending_scoped
                    .remove(&(file, scope, phase))
                    .unwrap_or_default()
                    .max(looped, &mut self.unknowns, &mut self.traces);

                self.pending_scoped.insert((file, scope, phase), pending);
            } else {
                let completion = match cancels && self.inside_loop(file, node) {
                    true => Completion::Return,
                    false => Completion::Normal,
                };

                result.join(
                    phase,
                    completion,
                    looped,
                    &mut self.unknowns,
                    &mut self.traces,
                );
            }
        }

        result
    }

    fn visits_since(&self, file: FileId, scope: Option<NodeId>) -> Option<Cost> {
        let start = match scope {
            Some(scope) => {
                self.enclosing_factors
                    .iter()
                    .position(|(held, node, _, _)| *held == file && *node == scope)?
                    + 1
            }
            None => 0,
        };

        self.enclosing_factors[start..]
            .iter()
            .try_fold(Cost::ONE, |visits, (_, _, factor, _)| {
                visits.multiply(factor).ok()
            })
    }

    fn is_ancestor(&self, file: FileId, ancestor: NodeId, node: NodeId) -> bool {
        self.project
            .file(file)
            .semantic
            .nodes()
            .ancestor_ids(node)
            .any(|id| id == ancestor)
    }

    fn cost_of_exit(
        &mut self,
        file: FileId,
        argument: Option<&'a Expression<'a>>,
        node: NodeId,
        completion: Completion,
    ) -> Reading {
        let inner = match argument {
            Some(argument) => {
                let reading = self.cost_of_expression(file, argument);

                if completion == Completion::Return && self.is_async_context(file, node, false) {
                    let returned = self.assimilated_reading_of(file, argument);

                    reading.merge(returned, &mut self.unknowns, &mut self.traces)
                } else if completion == Completion::Return
                    && self.is_async_context(file, node, true)
                {
                    let returned = self.async_generator_resolution_of(file, argument);

                    reading.merge(returned, &mut self.unknowns, &mut self.traces)
                } else {
                    reading
                }
            }
            None => Reading::empty(),
        };
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let Some(enclosing) = enclosing_iteration_of(semantic, node) else {
            return inner;
        };

        self.escape_depth_exhausted = false;

        let resolved = self.escape_of_completion(file, node, completion, enclosing, 0);
        let exhausted = std::mem::take(&mut self.escape_depth_exhausted);

        let Some(escape) = resolved else {
            return self.depth_exhausted_reading(file, node, inner, exhausted);
        };
        let mut reading = Reading::empty();

        for (phase, _, part) in inner.completions {
            reading.join(phase, escape, part, &mut self.unknowns, &mut self.traces);
        }

        reading
    }

    fn is_constant_rest_expression(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let Some(reference) = identifier_of(e) else {
            return false;
        };

        self.is_constant_rest_reference(file, reference)
    }

    fn is_constant_rest_reference(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> bool {
        if !matches!(
            self.declarations
                .of_reference(self.project, file, reference),
            Some(Declaration::Parameter {
                parameter: ParameterNode::Rest(_),
                ..
            })
        ) {
            return false;
        }

        let Some(binding) = self
            .declarations
            .binding_of_reference(self.project, file, reference)
        else {
            return false;
        };

        self.is_constant_collection(binding)
    }

    fn cost_of_spread(&mut self, file: FileId, spread: &'a SpreadElement<'a>) -> Reading {
        let implicit = self.spread_part_of(file, spread);

        self.cost_of_spread_copy(
            file,
            (spread.node_id(), spread.span),
            &spread.argument,
            implicit,
        )
    }

    fn cost_of_spread_copy(
        &mut self,
        file: FileId,
        (node, span): (NodeId, Span),
        argument: &'a Expression<'a>,
        implicit: Option<Reading>,
    ) -> Reading {
        let inner = self.cost_of_expression(file, argument);
        let inner = match implicit {
            Some(part) => inner.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces),
            None => inner,
        };

        if self.is_constant_rest_expression(file, argument) {
            return inner;
        }

        if self.is_constant_sized(file, argument) {
            return inner;
        }

        let produced = match self.latent_of(file, argument) {
            Some(latent) => Some(self.latent_size_of(&latent)),
            None => self.produced_size_of(file, argument),
        };
        let factor = match &produced {
            Some(size) if size.exceeds => size.length.clone(),
            _ => Cost::N,
        };
        let inner = match produced.is_some_and(|size| !size.length_resolved) {
            true => {
                let unresolved = self.unknown_part(file, span, UnknownReason::SizeRelation);

                inner.merge(
                    Reading::of_part(unresolved),
                    &mut self.unknowns,
                    &mut self.traces,
                )
            }
            false => inner,
        };
        let label = format!("spread ...{}", short(self.text_of(file, argument.span())));
        let site = self.site_of_node(file, node);

        inner.merge(
            Reading::of_part(self.nest_part(
                label,
                site,
                self.source_span(file, span),
                factor,
                Part::unmarked(Cost::ONE, None),
            )),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn cost_of_binding_rest(&mut self, file: FileId, rest: &'a BindingRestElement<'a>) -> Reading {
        let constant = self.binding_rest_is_constant(file, rest);

        self.cost_of_rest_copy(file, rest.node_id(), rest.span, constant)
    }

    fn cost_of_rest_copy(
        &mut self,
        file: FileId,
        node: NodeId,
        span: Span,
        constant: bool,
    ) -> Reading {
        let mut inner = Reading::empty();

        for child in self.children_of(file, node) {
            let child = self.kind_of_node(file, child);
            let cost = self.cost_of_node(file, child);

            inner = inner.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        if constant {
            return inner;
        }

        let label = self.rest_label_of(file, span);
        let site = self.site_of_node(file, node);

        inner.merge(
            Reading::of_part(self.nest_part(
                label,
                site,
                self.source_span(file, span),
                Cost::N,
                Part::unmarked(Cost::ONE, None),
            )),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn binding_rest_is_constant(&mut self, file: FileId, rest: &'a BindingRestElement<'a>) -> bool {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let keys = match nodes.parent_kind(rest.node_id()) {
            AstKind::ObjectPattern(_) => true,
            AstKind::ArrayPattern(_) => false,
            AstKind::FormalParameterRest(_) => return true,
            _ => return false,
        };
        let pattern = nodes.parent_id(rest.node_id());
        let span = nodes.kind(pattern).span();
        let source = match nodes.parent_kind(pattern) {
            AstKind::VariableDeclarator(declarator) if declarator.id.span() == span => {
                declarator.init.as_ref()
            }
            _ => None,
        };
        let Some(source) = source else {
            return false;
        };

        match keys {
            true => self.is_closed(file, source),
            false => self.is_constant_sized(file, source),
        }
    }

    fn cost_of_rest_target(&mut self, file: FileId, rest: &'a AssignmentTargetRest<'a>) -> Reading {
        let constant = match &rest.target {
            AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                self.is_constant_rest_reference(file, reference)
                    || self.is_constant_sized_reference(file, reference)
            }
            _ => false,
        };

        self.cost_of_rest_copy(file, rest.node_id(), rest.span, constant)
    }

    fn open_remainder_of(
        &mut self,
        targets: &TargetSet,
        resolved: bool,
        file: FileId,
        span: Span,
        arguments: &'a [Argument<'a>],
        reason: UnknownReason,
    ) -> Option<UnknownId> {
        if !targets.open || !resolved {
            return None;
        }

        self.unknown_invocation(file, span, arguments, reason)
            .main()
            .unknowns
    }

    fn cost_of_callee(&mut self, file: FileId, callee: &'a Expression<'a>) -> Reading {
        let callee = unwrap(callee);

        if identifier_of(callee).is_some() {
            return Reading::empty();
        }

        let Some(member) = member_expression_of(callee) else {
            return self.cost_of_expression(file, callee);
        };
        let reading = self.cost_of_expression(file, member.object());

        match member {
            MemberExpression::ComputedMemberExpression(access) => {
                let key = self.cost_of_expression(file, &access.expression);

                reading.merge(key, &mut self.unknowns, &mut self.traces)
            }
            _ => reading,
        }
    }

    fn method_name_of(&mut self, file: FileId, member: &'a MemberExpression<'a>) -> String {
        self.static_member_name_of(file, member).unwrap_or_default()
    }

    fn cost_of_new(&mut self, file: FileId, new: &'a NewExpression<'a>) -> Reading {
        let mut reading = self.cost_of_callee(file, &new.callee);

        for argument in &new.arguments {
            let cost = self.cost_of_argument(file, argument);

            reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        let construction = self.construction_targets_of(file, new);
        let targets = &construction.targets;
        let site = self.site_of_node(file, new.node_id());
        let origin = self.source_span(file, new.span);
        let resolved = !targets.known.is_empty() || !construction.implicit.is_empty();
        let remainder = self.open_remainder_of(
            targets,
            resolved,
            file,
            new.span,
            &new.arguments,
            UnknownReason::Target,
        );

        for known in &targets.known {
            let function = self.function_at(*known);
            let target = known.file;
            let (callee, cyclic) =
                self.call_user_reading(target, function, file, &new.arguments, new.span);
            let callee = callee.map_parts(|callee| {
                if callee.cost.is_one() {
                    callee
                } else {
                    match self.trace_name_of(target, function) {
                        Ok(name) => {
                            let name = name.strip_suffix(".constructor").unwrap_or(&name);

                            callee.explain(
                                format_args!("new {name}()"),
                                site,
                                origin,
                                true,
                                &mut self.traces,
                                &mut self.unknowns,
                            )
                        }
                        Err(_) => callee.explanation_failed(origin, &mut self.unknowns),
                    }
                }
            });
            let part = callee.called(origin, &mut self.unknowns);
            let part = part.retaining(remainder, &mut self.unknowns);

            reading = self.append_call(reading, target, function, part, cyclic);
        }

        for implicit in &construction.implicit {
            let part = self.construction_part_of((file, &new.arguments, new.span), *implicit);
            let part = part.map_parts(|part| {
                if part.cost.is_one() {
                    part
                } else {
                    part.explain(
                        format_args!("new {}()", short(self.text_of(file, new.callee.span()))),
                        site,
                        origin,
                        true,
                        &mut self.traces,
                        &mut self.unknowns,
                    )
                }
            });
            let part = part
                .called(origin, &mut self.unknowns)
                .map_parts(constructed_part_of);
            let part = part.retaining(remainder, &mut self.unknowns);

            reading = reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
        }

        if resolved {
            return reading;
        }

        if let Some(model) = self.construction_model_of(file, new) {
            let native = self.construction_site_of(file, new);

            if self.intrinsic_replaced_of(file, &new.callee) {
                let unknown =
                    self.unknown_invocation(file, new.span, &new.arguments, UnknownReason::Target);

                reading = reading.merge(unknown, &mut self.unknowns, &mut self.traces);
            }

            return self.native_reading_of(&native, model, reading, true);
        }

        self.record_unknown_reach(file, Some(&new.callee), &new.arguments, new.span);

        let constructor = match &new.callee {
            Expression::Identifier(reference) => reference.name.as_str(),
            _ => "",
        };
        let first = new.arguments.first();

        if is_listed(LINEAR_CONSTRUCTORS, constructor) {
            if let Some(first) = first {
                if self.is_share_sized_argument(file, first) {
                    self.stats.count("share: constructor");
                }

                if !self.is_constant_sized_argument(file, first)
                    && !self.is_numeric_constant_argument(file, first)
                    && !self.is_share_sized_argument(file, first)
                {
                    let label = format!(
                        "new {constructor}({})",
                        short(self.text_of(file, first.span()))
                    );
                    let site = self.site_of_node(file, new.node_id());

                    return reading.merge(
                        Reading::of_part(self.nest_part(
                            label,
                            site,
                            self.source_span(file, new.span),
                            Cost::N,
                            Part::unmarked(Cost::ONE, None),
                        )),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }
            }
        }

        if is_listed(LINEAR_CONSTRUCTORS, constructor) {
            return reading;
        }

        let unknown =
            self.unknown_invocation(file, new.span, &new.arguments, UnknownReason::Target);

        reading.merge(unknown, &mut self.unknowns, &mut self.traces)
    }

    pub(crate) fn constructor_targets_of(
        &mut self,
        file: FileId,
        new: &'a NewExpression<'a>,
    ) -> TargetSet {
        self.construction_targets_of(file, new).into_targets()
    }

    pub(crate) fn construction_targets_of(
        &mut self,
        file: FileId,
        new: &'a NewExpression<'a>,
    ) -> Construction<'a> {
        match &new.callee {
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference);

                let targets = self.resolved_of_declaration(declaration, true).targets;

                match targets.known.is_empty() {
                    true => self.construction_of(file, &new.callee),
                    false => Construction {
                        targets,
                        implicit: Vec::new(),
                    },
                }
            }
            callee => match member_expression_of(unwrap(callee)) {
                Some(member) => {
                    let targets = self.resolved_member_of(file, member).targets;

                    self.member_construction_of(file, (unwrap(callee), member), targets)
                }
                None => self.construction_of(file, callee),
            },
        }
    }

    pub(crate) fn named_call_of(
        &mut self,
        (target, function): (FileId, FunctionNode<'a>),
        called: Part,
        (site, origin): (Site, SourceSpan),
    ) -> Part {
        if called.cost.is_one() {
            return called;
        }

        match self.trace_name_of(target, function) {
            Ok(name) => called.explain(
                format_args!("call {name}()"),
                site,
                origin,
                true,
                &mut self.traces,
                &mut self.unknowns,
            ),
            Err(_) => called.explanation_failed(origin, &mut self.unknowns),
        }
    }

    pub(crate) fn named_reading_call_of(
        &mut self,
        function: (FileId, FunctionNode<'a>),
        reading: Reading,
        site: (Site, crate::unknowns::SourceSpan),
    ) -> Reading {
        reading.map_parts(|part| self.named_call_of(function, part, site))
    }

    fn decorated_part_of(&mut self, file: FileId, decorated: Option<NodeId>) -> Option<Part> {
        let node = decorated?;
        let span = self.kind_of_node(file, node).span();

        self.current_effects.unknown_global = true;

        Some(self.unknown_part(file, span, UnknownReason::UnsupportedSyntax))
    }

    fn cost_of_class_definition(&mut self, file: FileId, class: &'a Class<'a>) -> Reading {
        if class.declare {
            return Reading::empty();
        }

        let phases = class_phases_of(class);
        let reading = self
            .decorated_part_of(file, phases.decorated)
            .map_or_else(Reading::empty, Reading::of_part);
        let elements: Vec<NodeId> = phases.keys.iter().map(|(element, _)| *element).collect();
        let evaluated = phases
            .heritage
            .into_iter()
            .chain(phases.keys.into_iter().map(|(_, key)| key));
        let mut reading = self.merged_costs_of(file, reading, evaluated, false);

        for element in elements {
            let part = self.class_key_part_of(file, element);

            reading = reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
        }

        self.merged_costs_of(
            file,
            reading,
            phases.statics.into_iter().map(|(element, _)| element),
            true,
        )
    }

    fn merged_costs_of(
        &mut self,
        file: FileId,
        mut reading: Reading,
        nodes: impl IntoIterator<Item = NodeId>,
        siblings: bool,
    ) -> Reading {
        for node in nodes {
            let kind = self.kind_of_node(file, node);
            let cost = self.cost_of_node(file, kind);
            let cost = match siblings {
                true => self.sibling_of(file, kind, cost),
                false => cost,
            };

            reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        reading
    }

    pub(crate) fn cost_of_instance_fields(
        &mut self,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Reading {
        if class.declare {
            return Reading::empty();
        }

        let phases = class_phases_of(class);
        let decorated = self.decorated_part_of(file, phases.decorated);
        let reading = decorated.map_or_else(Reading::empty, Reading::of_part);
        let elements = phases.instances.into_iter().map(|(element, _)| element);

        self.merged_costs_of(file, reading, elements, true)
    }

    pub(crate) fn constructed_class_of(
        &self,
        file: FileId,
        function: FunctionNode<'a>,
    ) -> Option<&'a Class<'a>> {
        let FunctionNode::Function(inner) = function else {
            return None;
        };
        let nodes = self.project.file(file).semantic.nodes();
        let method = nodes.parent_id(inner.node_id());

        match nodes.kind(method) {
            AstKind::MethodDefinition(definition)
                if definition.kind == MethodDefinitionKind::Constructor => {}
            _ => return None,
        }

        nodes
            .ancestors(method)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Class(class) => Some(class),
                _ => None,
            })
    }

    fn enclosing_constructed_class_of(&self, file: FileId, node: NodeId) -> Option<&'a Class<'a>> {
        let nodes = self.project.file(file).semantic.nodes();

        nodes
            .ancestors(node)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(Some(function)),
                AstKind::Class(_) => Some(None),
                _ => None,
            })
            .flatten()
            .and_then(|function| self.constructed_class_of(file, FunctionNode::Function(function)))
    }

    fn cost_of_super_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        reading: Reading,
    ) -> Reading {
        let part = self.super_construction_part_of(file, call);

        reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces)
    }

    pub(crate) fn super_construction_part_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Reading {
        let Some(class) = self.enclosing_constructed_class_of(file, call.node_id()) else {
            return self.unknown_invocation(
                file,
                call.span,
                &call.arguments,
                UnknownReason::Target,
            );
        };
        let site = self.site_of_node(file, call.node_id());
        let origin = self.source_span(file, call.span);
        let base =
            self.base_construction_part_of((file, &call.arguments, call.span), (file, class));
        let fields = self.instance_fields_part_of(file, class);
        let part = base.merge(fields, &mut self.unknowns, &mut self.traces);
        let part = part.map_parts(|part| {
            if part.cost.is_one() {
                part
            } else {
                part.explain(
                    "super()",
                    site,
                    origin,
                    true,
                    &mut self.traces,
                    &mut self.unknowns,
                )
            }
        });

        part.called(origin, &mut self.unknowns)
            .map_parts(constructed_part_of)
    }

    pub(crate) fn construction_part_of(
        &mut self,
        (file, arguments, span): (FileId, &'a [Argument<'a>], Span),
        (target, class): (FileId, &'a Class<'a>),
    ) -> Reading {
        if let Err(reason) = self.enter_construction((target, class.node_id())) {
            return Reading::of_part(self.deferred_unknown(file, span, reason));
        }

        let fields = self.instance_fields_part_of(target, class);
        let base = self.base_construction_part_of((file, arguments, span), (target, class));

        self.leave_construction((target, class.node_id()));

        fields.merge(base, &mut self.unknowns, &mut self.traces)
    }

    fn base_construction_part_of(
        &mut self,
        (file, arguments, span): (FileId, &'a [Argument<'a>], Span),
        (target, class): (FileId, &'a Class<'a>),
    ) -> Reading {
        if class.heritage.is_none() {
            return Reading::empty();
        }

        let plan = self.base_plan_of(target, class);
        let site = self.project.site_of(file, span);
        let origin = self.source_span(file, span);
        let mut part = self.inherited_fields_part_of(target, class, &plan);

        for known in &plan.constructors {
            let function = self.function_at(*known);
            let (called, cyclic) =
                self.call_user_reading(known.file, function, file, arguments, span);
            let called = self.named_reading_call_of((known.file, function), called, (site, origin));
            let called = self.called_reading_of(known.file, function, called, cyclic);

            part = part.merge(called, &mut self.unknowns, &mut self.traces);
        }

        if plan.open {
            let unknown = self
                .unknown_invocation(file, span, arguments, UnknownReason::Target)
                .main()
                .unknowns;

            part = part.retaining(unknown, &mut self.unknowns);
        }

        part
    }

    fn is_share_sized_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> bool {
        match argument.as_expression() {
            Some(expression) => self.is_share_sized(file, expression),
            None => false,
        }
    }

    fn is_numeric_constant_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> bool {
        match argument.as_expression() {
            Some(expression) => self.is_numeric_constant(file, expression),
            None => false,
        }
    }

    fn callback_part_of(&mut self, file: FileId, argument: Option<&'a Argument<'a>>) -> Reading {
        self.reading_of_argument(file, argument).unwrap_or_default()
    }

    fn cost_of_call(&mut self, file: FileId, call: &'a CallExpression<'a>) -> Reading {
        let mut reading = self.cost_of_callee(file, &call.callee);

        for argument in &call.arguments {
            if !is_function_argument(argument) {
                let cost = self.cost_of_argument(file, argument);

                reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
            }
        }

        let callee = unwrap(&call.callee);

        if let Expression::Super(_) = callee {
            return self.cost_of_super_call(file, call, reading);
        }

        if let Expression::CallExpression(inner) = callee {
            if let Some((returned, open)) = self
                .returned_facts_of(file, inner)
                .filter(|(returned, open)| *open || !returned.is_empty())
            {
                return self.cost_of_returned_call(file, call, (returned, open), reading);
            }
        }

        let member = self.callee_member_of(file, call);

        let ResolvedCallee {
            declaration,
            closed,
            targets,
        } = self.resolved_callee_of(file, call);
        let site = self.site_of_node(file, call.node_id());
        let exhausted = self.is_call_exhausted(file, call.node_id());
        let reason = match exhausted {
            true => UnknownReason::ResourceExhaustion,
            false => UnknownReason::Target,
        };

        if let (Some(Declaration::Parameter { parameter, .. }), Some(reference)) =
            (declaration, identifier_of(callee))
        {
            let identifier = match parameter {
                ParameterNode::Formal(formal) => is_identifier_pattern(&formal.pattern),
                ParameterNode::Rest(rest) => is_identifier_pattern(&rest.rest.argument),
            };

            let substituted = if identifier {
                self.parameter_binding_of(declaration.unwrap())
                    .filter(|binding| self.is_parameter_unwritten(*binding))
                    .and_then(|binding| self.current_substitutions.get(&binding).cloned())
            } else {
                self.pattern_argument_facts_of(file, reference, closed)
            };

            if identifier || substituted.is_some() {
                if let Some(facts) = substituted {
                    let mut part = self.invoke_argument(&facts, file, call.span, &call.arguments);

                    if !closed {
                        let unknown = self.unknown_invocation(
                            file,
                            call.span,
                            &call.arguments,
                            UnknownReason::Target,
                        );

                        part = part.retaining(unknown.main().unknowns, &mut self.unknowns);
                    }

                    let origin = self.source_span(file, call.span);
                    let part = part.map_parts(|part| {
                        let part = if part.cost.is_one() {
                            part
                        } else {
                            part.explain(
                                format_args!("call {}() [callback parameter]", reference.name),
                                site,
                                origin,
                                true,
                                &mut self.traces,
                                &mut self.unknowns,
                            )
                        };

                        part.called(origin, &mut self.unknowns)
                    });

                    return reading.merge(part, &mut self.unknowns, &mut self.traces);
                }

                let unknown = self.unknown_invocation(
                    file,
                    call.span,
                    &call.arguments,
                    UnknownReason::Target,
                );

                return reading.merge(unknown, &mut self.unknowns, &mut self.traces);
            }
        }

        let remainder = self.open_remainder_of(
            &targets,
            !targets.known.is_empty(),
            file,
            call.span,
            &call.arguments,
            reason,
        );

        for target in &targets.known {
            let function = self.function_at(*target);
            let target = target.file;
            let (called, cyclic) =
                self.call_user_reading(target, function, file, &call.arguments, call.span);
            let called = self.named_reading_call_of(
                (target, function),
                called,
                (site, self.source_span(file, call.span)),
            );

            let part = called.called(self.source_span(file, call.span), &mut self.unknowns);
            let part = part.retaining(remainder, &mut self.unknowns);

            reading = self.append_call(reading, target, function, part, cyclic);
        }

        if !targets.known.is_empty() {
            if let Some(part) = self.untracked_latent_part_of(file, call, &targets) {
                reading =
                    reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
            }

            if self.intrinsic_replaced_of(file, callee) {
                let native = self.native_of(file, call, member, true);

                if is_modelled(native) {
                    let intrinsic =
                        self.intrinsic_reading_of(file, call, member, native, Reading::empty());

                    reading = reading.merge(intrinsic, &mut self.unknowns, &mut self.traces);
                }
            }

            return reading;
        }

        if exhausted {
            self.record_unknown_reach(file, Some(&call.callee), &call.arguments, call.span);

            let unknown = self.unknown_invocation(file, call.span, &call.arguments, reason);

            return reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        let native = self.native_of(file, call, member, true);

        if !matches!(native, Native::Modelled(_)) {
            self.record_unknown_reach(file, Some(&call.callee), &call.arguments, call.span);
        }

        if self.intrinsic_replaced_of(file, callee) {
            let unknown = self.unknown_invocation(file, call.span, &call.arguments, reason);

            reading = reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        self.intrinsic_reading_of(file, call, member, native, reading)
    }

    fn cost_of_returned_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        (returned, open): (Vec<ArgumentFacts>, bool),
        mut reading: Reading,
    ) -> Reading {
        let site = self.site_of_node(file, call.node_id());
        let origin = self.source_span(file, call.span);

        for facts in returned {
            let part = self.invoke_argument(&facts, file, call.span, &call.arguments);
            let named = facts
                .value
                .targets
                .known
                .first()
                .map(|known| self.trace_name_of(known.file, self.function_at(*known)));
            let part = part.map_parts(|part| match &named {
                _ if part.cost.is_one() => part,
                Some(Ok(name)) => part.explain(
                    format_args!("call {name}()"),
                    site,
                    origin,
                    true,
                    &mut self.traces,
                    &mut self.unknowns,
                ),
                _ => part.explanation_failed(origin, &mut self.unknowns),
            });
            let part = part.called(origin, &mut self.unknowns);

            reading = reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
        }

        if open {
            let unknown =
                self.unknown_invocation(file, call.span, &call.arguments, UnknownReason::Target);

            reading = reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        reading
    }

    fn intrinsic_reading_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: Option<&'a MemberExpression<'a>>,
        native: Native,
        reading: Reading,
    ) -> Reading {
        match (native, member) {
            (Native::Modelled(model), _) => {
                let site = self.call_site_of(file, call, member);

                self.native_reading_of(&site, model, reading, true)
            }
            (Native::Receiver(kind), Some(member)) => {
                let site = self.site_of_node(file, call.node_id());

                self.cost_of_method_call(file, call, (member, kind), reading, site)
            }
            _ => {
                let unknown = self.unknown_invocation(
                    file,
                    call.span,
                    &call.arguments,
                    UnknownReason::Target,
                );

                reading.merge(unknown, &mut self.unknowns, &mut self.traces)
            }
        }
    }

    fn cost_of_method_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        (member, kind): (&'a MemberExpression<'a>, Kind),
        reading: Reading,
        site: Site,
    ) -> Reading {
        let method = self.method_name_of(file, member);
        let receiver = member.object();
        let first = call.arguments.first();

        if kind == Kind::Unknown {
            let unknown = self.unknown_invocation(
                file,
                call.span,
                &call.arguments,
                UnknownReason::UnsupportedModel,
            );

            return reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        let receiver_text = short(self.text_of(file, receiver.span()));
        let label = |suffix: &str| format!("{receiver_text}.{method}(){suffix}");
        let shared = self.is_share_sized(file, receiver)
            || (method == "set"
                && first.is_some_and(|argument| self.is_share_sized_argument(file, argument)))
            || self.is_share_sized_call(file, call);
        let bounded = self.is_constant_sized(file, receiver) || shared;
        let array_like = kind == Kind::Array;

        if shared && array_like {
            self.stats.count("share: array method");
        }

        if array_like && (is_listed(ARRAY_N_LOG_N, &method) || is_listed(ARRAY_LINEAR, &method)) {
            self.stats.count(&format!(
                "array method: {}",
                if bounded { "bounded" } else { "N" }
            ));
        }

        let sorting = match array_like {
            true if is_listed(ARRAY_N_LOG_N, &method) => Some(true),
            true if is_listed(ARRAY_LINEAR, &method) => Some(false),
            _ => None,
        };

        if let Some(sorting) = sorting {
            let produced = match bounded {
                true => None,
                false => self.produced_size_of(file, receiver),
            };
            let mut unresolved = match produced.as_ref().is_some_and(|size| !size.length_resolved) {
                true => self.unknown_part(file, call.span, UnknownReason::SizeRelation),
                false => Part::none(),
            };
            let length = produced.filter(|size| size.exceeds).map(|size| size.length);
            let factor = match (sorting, length) {
                (false, length) => length.unwrap_or(Cost::N),
                (true, None) => Cost::N_LOG_N,
                (true, Some(length)) => match Cost::logarithm(length.clone())
                    .and_then(|logarithm| length.multiply(&logarithm))
                {
                    Ok(factor) => factor,
                    Err(_) => {
                        let exhausted =
                            self.unknown_part(file, call.span, UnknownReason::ResourceExhaustion);

                        unresolved =
                            unresolved.max(exhausted, &mut self.unknowns, &mut self.traces);

                        length
                    }
                },
            };
            let callback = match sorting || is_listed(CALLBACK_METHODS, &method) {
                true => self.callback_part_of(file, first),
                false => Reading::empty(),
            };
            let suffix = match sorting {
                true => " [n log n]",
                false => "",
            };
            let part = if bounded {
                callback
            } else {
                self.nest_reading(
                    label(suffix),
                    site,
                    self.source_span(file, call.span),
                    factor,
                    callback.executed(),
                )
            };
            let part = part.merge(unresolved, &mut self.unknowns, &mut self.traces);

            return reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
        }

        if (kind == Kind::Set && is_listed(SET_LINEAR, &method))
            || (kind == Kind::Map && is_listed(MAP_LINEAR, &method))
        {
            let callback = if is_listed(CALLBACK_METHODS, &method) {
                self.callback_part_of(file, first)
            } else {
                Reading::empty()
            };

            return reading.merge(
                Reading::of_part(self.nest_reading(
                    label(""),
                    site,
                    self.source_span(file, call.span),
                    Cost::N,
                    callback.executed(),
                )),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        if kind == Kind::RegExp && is_listed(REGEXP_LINEAR, &method) {
            let subject = match first {
                Some(argument) if !self.is_constant_sized_argument(file, argument) => Cost::N,
                _ => Cost::ONE,
            };
            let pattern = Pattern {
                keys: &[],
                matching: Matching::Once,
                compiles: false,
            };
            let matched = self.matching_part_of((file, call.span), receiver, pattern, &subject);
            let reading = match subject.is_one() {
                true => reading,
                false => self.append_linear_operation(
                    reading,
                    label(" [regexp]"),
                    site,
                    (file, call.span),
                ),
            };

            if matched == Part::none() {
                return reading;
            }

            return reading.merge(
                Reading::of_part(matched),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        let unknown = self.unknown_invocation(
            file,
            call.span,
            &call.arguments,
            UnknownReason::UnsupportedModel,
        );

        reading.merge(unknown, &mut self.unknowns, &mut self.traces)
    }
}

fn is_modelled(native: Native) -> bool {
    match native {
        Native::Modelled(_) => true,
        Native::Receiver(kind) => matches!(
            kind,
            Kind::Array | Kind::Set | Kind::Map | Kind::String | Kind::RegExp
        ),
        Native::Unmodelled => false,
    }
}

fn constructed_part_of(part: Part) -> Part {
    match part.holds_no_work() {
        true => part.preferred(Preference::Absent),
        false => part.preferred(Preference::Unmarked),
    }
}

fn holds_function(kind: &AstKind<'_>) -> bool {
    match kind {
        AstKind::VariableDeclaration(declaration) => {
            declaration.declarations.len() == 1
                && function_of_initializer(declaration.declarations[0].init.as_ref()).is_some()
        }
        AstKind::ObjectProperty(property) => {
            function_of_initializer(Some(&property.value)).is_some()
        }
        _ => false,
    }
}

pub(crate) fn tagged_reading_of(
    cost: Cost,
    text: &str,
    site: Site,
    origin: crate::unknowns::SourceSpan,
    traces: &mut crate::trace::TraceArena,
    unknowns: &mut crate::unknowns::Unknowns,
) -> Reading {
    let part = Part::unmarked(cost.clone(), None);

    Reading::of_part(if cost.is_one() {
        part
    } else {
        part.explain(
            format_args!("@perf {text}"),
            site,
            origin,
            true,
            traces,
            unknowns,
        )
    })
}

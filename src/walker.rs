use oxc_ast::ast::{
    Argument, AssignmentTarget, AssignmentTargetRest, CallExpression, Expression, MemberExpression,
    NewExpression, SpreadElement, Statement,
};
use oxc_ast::{AstKind, AstType};
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::bounds::{loop_label, short};
use crate::cost::{Cost, Part, Preference, Reading};
use crate::declarations::{
    function_of_initializer, Declaration, FunctionNode, ParameterNode, TargetSet,
};
use crate::declared_types::Kind;
use crate::directives::{cost_tag_of, preference_of, PerfTag};
use crate::project::{FileId, Site};
use crate::syntax::{
    body_root_of, identifier_of, is_identifier_pattern, is_iteration_kind, loop_body_of,
    member_expression_of, member_name_of, unwrap, Root,
};
use crate::tables::{
    ARRAY_LINEAR, ARRAY_N_LOG_N, CALLBACK_METHODS, GLOBAL_FUNCTIONS_LINEAR, GLOBAL_LINEAR,
    LINEAR_CONSTRUCTORS, MAP_LINEAR, OBJECT_KEYED, REGEXP_LINEAR, SET_LINEAR, STRING_LINEAR,
};
use crate::types::ResolvedCallee;
use crate::unknowns::{SourceSpan, UnknownReason};

fn is_type_kind(ty: AstType) -> bool {
    crate::syntax::is_type_kind(ty) || ty == AstType::TSInstantiationExpression
}

fn is_opaque_kind(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_)
    ) || is_type_kind(kind.ty())
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

        Part {
            unknowns: Some(unknown),
            ..Part::unmarked(Cost::ONE, None)
        }
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
            Some(Root::Expression(expression)) => self.cost_of_expression(file, expression),
            _ => Reading::empty(),
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
        if is_opaque_kind(&kind) {
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
                reading.main.unknowns = self
                    .unknowns
                    .join(reading.main.unknowns, unknown.main.unknowns);
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
            AstKind::FunctionBody(body) => self.cost_of_statements(file, None, &body.statements),
            AstKind::TSModuleBlock(block) => self.cost_of_statements(file, None, &block.body),
            AstKind::SwitchCase(case) => {
                self.cost_of_statements(file, case.test.as_ref(), &case.consequent)
            }
            _ if iteration => self.cost_of_loop(file, kind),
            AstKind::ReturnStatement(statement) => {
                self.cost_of_exit(file, statement.argument.as_ref(), statement.node_id())
            }
            AstKind::ThrowStatement(statement) => {
                self.cost_of_exit(file, Some(&statement.argument), statement.node_id())
            }
            AstKind::SpreadElement(spread) => self.cost_of_spread(file, spread),
            AstKind::AssignmentTargetRest(rest) => self.cost_of_rest_target(file, rest),
            AstKind::NewExpression(new) => self.cost_of_new(file, new),
            AstKind::CallExpression(call) => self.cost_of_call(file, call),
            _ => {
                let mut reading = Reading::empty();

                for child in self.children_of(file, kind.node_id()) {
                    let child = self.kind_of_node(file, child);
                    let cost = self.cost_of_node(file, child);

                    reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
                }

                reading
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

        for statement in statements {
            let kind = self.kind_of_node(file, statement.node_id());
            let cost = self.cost_of_node(file, kind);

            reading = reading.merge(
                self.sibling_of(file, kind, cost),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        reading
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

    fn loop_result(&mut self, sibling: Reading, function_exit: Part, main: Part) -> Reading {
        Reading {
            main,
            function_exit: sibling.function_exit.max(
                function_exit,
                &mut self.unknowns,
                &mut self.traces,
            ),
            loop_exit: sibling.loop_exit,
            phases: sibling.phases,
        }
    }

    fn append_call(
        &mut self,
        reading: Reading,
        target: FileId,
        function: FunctionNode<'a>,
        part: Part,
        cyclic: bool,
    ) -> Reading {
        let called = self.called_part_of(target, function, part, cyclic);

        reading.merge(
            Reading::of_part(called),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn branch_reading_of(
        &mut self,
        file: FileId,
        body: &'a Statement<'a>,
        site_node: NodeId,
    ) -> Reading {
        let reading = self.cost_of_statement(file, body);
        let exit = self.ends_in(file, body);

        if let Some(exit) = exit {
            if self.inside_loop(file, site_node) && !reading.main.cost.is_one() {
                let unit = if exit == crate::bounds::Exit::Break {
                    "loop"
                } else {
                    "call"
                };
                let lifted = reading.main.explain(
                    format_args!("[{} branch: runs once per {}]", exit.text(), unit),
                    self.site_of_node(file, site_node),
                    self.source_span(file, self.kind_of_node(file, site_node).span()),
                    false,
                    &mut self.traces,
                    &mut self.unknowns,
                );

                if exit == crate::bounds::Exit::Break {
                    return Reading {
                        phases: [crate::cost::ExecutionPhase::Immediate; 3],
                        main: Part::none(),
                        function_exit: reading.function_exit,
                        loop_exit: reading.loop_exit.max(
                            lifted,
                            &mut self.unknowns,
                            &mut self.traces,
                        ),
                    };
                }

                return Reading {
                    phases: [crate::cost::ExecutionPhase::Immediate; 3],
                    main: Part::none(),
                    function_exit: reading.function_exit.max(
                        lifted,
                        &mut self.unknowns,
                        &mut self.traces,
                    ),
                    loop_exit: reading.loop_exit,
                };
            }
        }

        reading
    }

    fn cost_of_loop(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        let node = kind.node_id();
        let body = loop_body_of(kind).expect("an iteration statement has a body");
        let body_node = body.node_id();
        let mut sibling = Reading::empty();

        for child in self.children_of(file, node) {
            if child == body_node {
                continue;
            }

            let child = self.kind_of_node(file, child);
            let cost = self.cost_of_node(file, child);

            sibling = sibling.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        let invalidation = self.loop_invalidation_of(file, kind);
        let assumed_bound = self.perf_tags(file, kind).contains(&PerfTag::Bounded);
        let saved_budget = invalidation.budget.then(|| self.budget_context.take());
        let saved_shares = invalidation
            .budget
            .then(|| std::mem::take(&mut self.share_bindings));
        let bound = self.bound_of(file, kind);
        let spend = if bound.factor.is_one() {
            None
        } else {
            self.spent_budget(file, kind)
        };
        let budget = spend.filter(|spend| spend.scope != Some(node));

        if let Some(share) = budget.as_ref().and_then(|budget| budget.share) {
            self.share_bindings.push(share);
        }

        let body_raw = self.cost_of_statement(file, body);

        if budget.as_ref().is_some_and(|budget| budget.share.is_some()) {
            self.share_bindings.pop();
        }

        if let Some(context) = saved_budget {
            self.budget_context = context;
        }

        if let Some(shares) = saved_shares {
            self.share_bindings = shares;
        }

        let hoisted = self.pending_scoped.remove(&(file, node));
        let mut body = match hoisted {
            Some(hoisted) => Reading {
                main: body_raw
                    .main
                    .max(hoisted, &mut self.unknowns, &mut self.traces),
                ..body_raw
            },
            None => body_raw,
        };

        if invalidation.bound && !assumed_bound {
            let origin = self.source_span(file, kind.span());
            let mut unknown = Some(self.unknowns.origin(origin, UnknownReason::Bound));

            if self.fallback_active() {
                let resource = self
                    .unknowns
                    .origin(origin, UnknownReason::ResourceExhaustion);
                unknown = self.unknowns.join(unknown, Some(resource));
            }

            body.main.unknowns = self.unknowns.scale(body.main.unknowns, None);

            let unresolved = Part {
                unknowns: self.unknowns.scale(unknown, None),
                preference: body.main.preference.max(Preference::Unmarked),
                ..Part::unmarked(Cost::ONE, None)
            };

            body.main = body
                .main
                .max(unresolved, &mut self.unknowns, &mut self.traces);

            let main = body
                .main
                .max(body.loop_exit, &mut self.unknowns, &mut self.traces);

            let main = sibling
                .main
                .clone()
                .max(main, &mut self.unknowns, &mut self.traces);

            return self.loop_result(sibling, body.function_exit, main);
        }

        if bound.factor.is_one() {
            let main = sibling
                .main
                .clone()
                .max(body.main, &mut self.unknowns, &mut self.traces)
                .max(body.loop_exit, &mut self.unknowns, &mut self.traces);

            return self.loop_result(sibling, body.function_exit, main);
        }

        let scope = budget
            .as_ref()
            .and_then(|budget| budget.scope)
            .filter(|scope| self.is_ancestor(file, *scope, node));

        if let Some(budget) = &budget {
            self.stats.count(&format!(
                "loop {}: budget{}{}",
                loop_label(kind),
                if budget.share.is_some() {
                    " by share"
                } else {
                    ""
                },
                if scope.is_some() { " (scoped)" } else { "" }
            ));
        }

        let mut label = loop_label(kind).to_string();

        if let Some(why) = bound.why {
            label.push_str(&format!(" [{why}]"));
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
        let looped = self.nest_part(
            label,
            site,
            self.source_span(file, kind.span()),
            bound.factor,
            body.main,
        );

        let main = sibling
            .main
            .clone()
            .max(body.loop_exit, &mut self.unknowns, &mut self.traces);
        let mut result = self.loop_result(sibling, body.function_exit, main);

        if let (Some(_), Some(scope)) = (&budget, scope) {
            let pending = self
                .pending_scoped
                .remove(&(file, scope))
                .unwrap_or_default()
                .max(looped, &mut self.unknowns, &mut self.traces);

            self.pending_scoped.insert((file, scope), pending);
        } else if budget.is_some() && self.inside_loop(file, node) {
            result.function_exit =
                result
                    .function_exit
                    .max(looped, &mut self.unknowns, &mut self.traces);
        } else {
            result.main = result
                .main
                .max(looped, &mut self.unknowns, &mut self.traces);
        }

        result
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
    ) -> Reading {
        let inner = match argument {
            Some(argument) => self.cost_of_expression(file, argument),
            None => Reading::empty(),
        };

        if self.inside_loop(file, node) {
            return Reading {
                phases: [crate::cost::ExecutionPhase::Immediate; 3],
                main: Part::none(),
                function_exit: inner.total(&mut self.unknowns, &mut self.traces),
                loop_exit: Part::none(),
            };
        }

        inner
    }

    fn is_rest_parameter(&self, file: FileId, e: &'a Expression<'a>) -> bool {
        let Some(reference) = identifier_of(e) else {
            return false;
        };

        matches!(
            self.declarations
                .of_reference(self.project, file, reference),
            Some(Declaration::Parameter {
                parameter: ParameterNode::Rest(_),
                ..
            })
        )
    }

    fn cost_of_spread(&mut self, file: FileId, spread: &'a SpreadElement<'a>) -> Reading {
        let inner = self.cost_of_expression(file, &spread.argument);

        if self.is_rest_parameter(file, &spread.argument) {
            return inner;
        }

        if self.is_constant_sized(file, &spread.argument) {
            return inner;
        }

        let label = format!(
            "spread ...{}",
            short(self.text_of(file, spread.argument.span()))
        );
        let site = self.site_of_node(file, spread.node_id());

        inner.merge(
            Reading::of_part(self.nest_part(
                label,
                site,
                self.source_span(file, spread.span),
                Cost::N,
                Part::none(),
            )),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn cost_of_rest_target(&mut self, file: FileId, rest: &'a AssignmentTargetRest<'a>) -> Reading {
        let mut inner = Reading::empty();

        for child in self.children_of(file, rest.node_id()) {
            let child = self.kind_of_node(file, child);
            let cost = self.cost_of_node(file, child);

            inner = inner.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        let constant = match &rest.target {
            AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                if matches!(
                    self.declarations
                        .of_reference(self.project, file, reference),
                    Some(Declaration::Parameter {
                        parameter: ParameterNode::Rest(_),
                        ..
                    })
                ) {
                    return inner;
                }

                self.is_constant_sized_reference(file, reference)
            }
            _ => false,
        };

        if constant {
            return inner;
        }

        let written = self.text_of(file, rest.span);
        let label = format!(
            "spread ...{}",
            short(written.strip_prefix("...").unwrap_or(written).trim_start())
        );
        let site = self.site_of_node(file, rest.node_id());

        inner.merge(
            Reading::of_part(self.nest_part(
                label,
                site,
                self.source_span(file, rest.span),
                Cost::N,
                Part::none(),
            )),
            &mut self.unknowns,
            &mut self.traces,
        )
    }

    fn with_open_remainder(
        &mut self,
        mut part: Part,
        targets: &TargetSet,
        file: FileId,
        span: Span,
        arguments: &'a [Argument<'a>],
        reason: UnknownReason,
    ) -> Part {
        if targets.open {
            let unknown = self.unknown_invocation(file, span, arguments, reason);

            part.unknowns = self.unknowns.join(part.unknowns, unknown.main.unknowns);
        }

        part
    }

    fn cost_of_new(&mut self, file: FileId, new: &'a NewExpression<'a>) -> Reading {
        let mut reading = Reading::empty();

        for argument in &new.arguments {
            let cost = self.cost_of_argument(file, argument);

            reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
        }

        let targets = self.constructor_targets_of(file, new);

        for known in &targets.known {
            let function = self.function_at(*known);
            let target = known.file;
            let (callee, cyclic) = self.call_user(target, function, file, &new.arguments, new.span);
            let callee = if callee.cost.is_one() {
                callee
            } else {
                match self.trace_name_of(target, function) {
                    Ok(name) => {
                        let name = name.strip_suffix(".constructor").unwrap_or(&name);

                        callee.explain(
                            format_args!("new {name}()"),
                            self.site_of_node(file, new.node_id()),
                            self.source_span(file, new.span),
                            true,
                            &mut self.traces,
                            &mut self.unknowns,
                        )
                    }
                    Err(_) => callee
                        .explanation_failed(self.source_span(file, new.span), &mut self.unknowns),
                }
            };
            let part = callee.called(self.source_span(file, new.span), &mut self.unknowns);
            let part = self.with_open_remainder(
                part,
                &targets,
                file,
                new.span,
                &new.arguments,
                UnknownReason::Target,
            );

            reading = self.append_call(reading, target, function, part, cyclic);
        }

        if !targets.known.is_empty() {
            return reading;
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
                            Part::none(),
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
        match &new.callee {
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference);

                self.resolved_of_declaration(declaration, true).targets
            }
            callee => match callee.as_member_expression() {
                Some(member) => self.resolved_member_of(file, member).targets,
                None => TargetSet::default(),
            },
        }
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

    fn callback_part_of(&mut self, file: FileId, argument: Option<&'a Argument<'a>>) -> Part {
        self.part_of_argument(file, argument).unwrap_or_default()
    }

    fn cost_of_call(&mut self, file: FileId, call: &'a CallExpression<'a>) -> Reading {
        let mut reading = Reading::empty();

        for argument in &call.arguments {
            if !is_function_argument(argument) {
                let cost = self.cost_of_argument(file, argument);

                reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
            }
        }

        let callee = unwrap(&call.callee);
        let member = member_expression_of(callee)
            .filter(|member| !matches!(member, MemberExpression::ComputedMemberExpression(_)));

        if let Some(member) = member {
            let cost = self.cost_of_expression(file, member.object());

            reading = reading.merge(cost, &mut self.unknowns, &mut self.traces);
        }

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

            if identifier {
                let substituted = self
                    .parameter_binding_of(declaration.unwrap())
                    .and_then(|binding| self.current_substitutions.get(&binding).cloned());

                if let Some(facts) = substituted {
                    let mut part = self.invoke_argument(&facts, file, call.span, &call.arguments);

                    if !closed {
                        let unknown = self.unknown_invocation(
                            file,
                            call.span,
                            &call.arguments,
                            UnknownReason::Target,
                        );

                        part.unknowns = self.unknowns.join(part.unknowns, unknown.main.unknowns);
                    }

                    let part = if part.cost.is_one() {
                        part
                    } else {
                        part.explain(
                            format_args!("call {}() [callback parameter]", reference.name),
                            site,
                            self.source_span(file, call.span),
                            true,
                            &mut self.traces,
                            &mut self.unknowns,
                        )
                    };

                    return reading.merge(
                        Reading::of_part(Part {
                            cost: part.cost.clone(),
                            origin: Some(self.source_span(file, call.span)),
                            cost_error: part.cost_error,
                            trace: part.trace,
                            preference: part.preference,
                            unknowns: self
                                .unknowns
                                .called(part.unknowns, self.source_span(file, call.span)),
                        }),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
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

        for target in &targets.known {
            let function = self.function_at(*target);
            let target = target.file;
            let (called, cyclic) =
                self.call_user(target, function, file, &call.arguments, call.span);
            let called = if called.cost.is_one() {
                called
            } else {
                match self.trace_name_of(target, function) {
                    Ok(name) => called.explain(
                        format_args!("call {name}()"),
                        site,
                        self.source_span(file, call.span),
                        true,
                        &mut self.traces,
                        &mut self.unknowns,
                    ),
                    Err(_) => called
                        .explanation_failed(self.source_span(file, call.span), &mut self.unknowns),
                }
            };

            let part = called.called(self.source_span(file, call.span), &mut self.unknowns);
            let part =
                self.with_open_remainder(part, &targets, file, call.span, &call.arguments, reason);

            reading = self.append_call(reading, target, function, part, cyclic);
        }

        if !targets.known.is_empty() {
            if self.intrinsic_replaced_of(file, callee)
                && self.has_intrinsic_model(file, call, member)
            {
                let intrinsic =
                    self.intrinsic_reading_of(file, call, member, Reading::empty(), site);

                reading = reading.merge(intrinsic, &mut self.unknowns, &mut self.traces);
            }

            return reading;
        }

        self.record_unknown_reach(file, Some(&call.callee), &call.arguments, call.span);

        if exhausted {
            let unknown = self.unknown_invocation(file, call.span, &call.arguments, reason);

            return reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        if self.intrinsic_replaced_of(file, callee) {
            let unknown = self.unknown_invocation(file, call.span, &call.arguments, reason);

            reading = reading.merge(unknown, &mut self.unknowns, &mut self.traces);
        }

        self.intrinsic_reading_of(file, call, member, reading, site)
    }

    fn has_intrinsic_model(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: Option<&'a MemberExpression<'a>>,
    ) -> bool {
        let Some(member) = member else {
            return identifier_of(unwrap(&call.callee)).is_some_and(|reference| {
                is_listed(GLOBAL_FUNCTIONS_LINEAR, reference.name.as_str())
            });
        };
        let method = member_name_of(member).unwrap_or_default();
        let receiver = member.object();

        if identifier_of(receiver).is_some_and(|global| {
            GLOBAL_LINEAR.iter().any(|(name, methods)| {
                *name == global.name.as_str() && methods.contains(&method.as_str())
            })
        }) {
            return true;
        }

        matches!(
            self.kind_of(file, receiver, &method),
            Kind::Array | Kind::Set | Kind::Map | Kind::String | Kind::RegExp
        )
    }

    fn intrinsic_reading_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: Option<&'a MemberExpression<'a>>,
        reading: Reading,
        site: Site,
    ) -> Reading {
        let callee = unwrap(&call.callee);

        if let Some(member) = member {
            return self.cost_of_method_call(file, call, member, reading, site);
        }

        if let Some(reference) = identifier_of(callee) {
            if is_listed(GLOBAL_FUNCTIONS_LINEAR, reference.name.as_str()) {
                return reading.merge(
                    Reading::of_part(self.nest_part(
                        format!("{}()", reference.name),
                        site,
                        self.source_span(file, call.span),
                        Cost::N,
                        Part::none(),
                    )),
                    &mut self.unknowns,
                    &mut self.traces,
                );
            }
        }

        let unknown =
            self.unknown_invocation(file, call.span, &call.arguments, UnknownReason::Target);

        reading.merge(unknown, &mut self.unknowns, &mut self.traces)
    }

    fn cost_of_method_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: &'a MemberExpression<'a>,
        reading: Reading,
        site: Site,
    ) -> Reading {
        let method = member_name_of(member).unwrap_or_default();
        let receiver = member.object();
        let first = call.arguments.first();

        if let Some(global) = identifier_of(receiver) {
            let global_name = global.name.as_str();
            let listed = GLOBAL_LINEAR
                .iter()
                .any(|(name, methods)| *name == global_name && methods.contains(&method.as_str()));

            if listed {
                let bounded = match first {
                    Some(argument) => {
                        self.is_constant_sized_argument(file, argument)
                            || (global_name == "Object"
                                && is_listed(OBJECT_KEYED, &method)
                                && (argument
                                    .as_expression()
                                    .is_some_and(|argument| self.is_enum_object(file, argument))
                                    || self.is_closed_argument(file, argument)))
                    }
                    None => false,
                };
                let callback = if method == "from" {
                    self.callback_part_of(file, call.arguments.get(1))
                } else {
                    Part::none()
                };

                self.stats.count(&format!(
                    "{global_name}.{method}: {}",
                    if bounded { "bounded" } else { "N" }
                ));

                if bounded {
                    return reading.merge(
                        Reading::of_part(callback),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }

                let argument_text = match first {
                    Some(argument) => short(self.text_of(file, argument.span())),
                    None => String::new(),
                };

                return reading.merge(
                    Reading::of_part(self.nest_part(
                        format!("{global_name}.{method}({argument_text})"),
                        site,
                        self.source_span(file, call.span),
                        Cost::N,
                        callback,
                    )),
                    &mut self.unknowns,
                    &mut self.traces,
                );
            }
        }

        let kind = self.kind_of(file, receiver, &method);

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

        if kind == Kind::String && is_listed(STRING_LINEAR, &method) {
            self.stats.count(&format!(
                "string method: {}",
                if bounded { "bounded" } else { "N" }
            ));
        }

        if array_like {
            if is_listed(ARRAY_N_LOG_N, &method) {
                let callback = self.callback_part_of(file, first);
                let part = if bounded {
                    callback
                } else {
                    self.nest_part(
                        label(" [n log n]"),
                        site,
                        self.source_span(file, call.span),
                        Cost::N_LOG_N,
                        callback,
                    )
                };

                return reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
            }

            if is_listed(ARRAY_LINEAR, &method) {
                let callback = if is_listed(CALLBACK_METHODS, &method) {
                    self.callback_part_of(file, first)
                } else {
                    Part::none()
                };
                let part = if bounded {
                    callback
                } else {
                    self.nest_part(
                        label(""),
                        site,
                        self.source_span(file, call.span),
                        Cost::N,
                        callback,
                    )
                };

                return reading.merge(Reading::of_part(part), &mut self.unknowns, &mut self.traces);
            }
        }

        if (kind == Kind::Set && is_listed(SET_LINEAR, &method))
            || (kind == Kind::Map && is_listed(MAP_LINEAR, &method))
        {
            let callback = if is_listed(CALLBACK_METHODS, &method) {
                self.callback_part_of(file, first)
            } else {
                Part::none()
            };

            return reading.merge(
                Reading::of_part(self.nest_part(
                    label(""),
                    site,
                    self.source_span(file, call.span),
                    Cost::N,
                    callback,
                )),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        if kind == Kind::String && is_listed(STRING_LINEAR, &method) && !bounded {
            return reading.merge(
                Reading::of_part(self.nest_part(
                    label(" [string]"),
                    site,
                    self.source_span(file, call.span),
                    Cost::N,
                    Part::none(),
                )),
                &mut self.unknowns,
                &mut self.traces,
            );
        }

        if kind == Kind::RegExp && is_listed(REGEXP_LINEAR, &method) {
            if let Some(argument) = first {
                if !self.is_constant_sized_argument(file, argument) {
                    return reading.merge(
                        Reading::of_part(self.nest_part(
                            label(" [regexp]"),
                            site,
                            self.source_span(file, call.span),
                            Cost::N,
                            Part::none(),
                        )),
                        &mut self.unknowns,
                        &mut self.traces,
                    );
                }
            }

            return reading;
        }

        if kind == Kind::String && is_listed(STRING_LINEAR, &method) && bounded {
            return reading;
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

use oxc_ast::ast::{
    Argument, AssignmentTarget, AssignmentTargetRest, CallExpression, Expression, MemberExpression,
    NewExpression, SpreadElement, Statement,
};
use oxc_ast::{AstKind, AstType};
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::analysis::Analysis;
use crate::annotations::{cost_tag_of, skip_tag_of, PerfTag};
use crate::bounds::{loop_label, short};
use crate::budgets::{body_root_of, identifier_of, is_iteration_kind, loop_body_of, Root};
use crate::constants::{member_expression_of, member_name_of, unwrap};
use crate::cost::{nest, Cost, Factor, Part, Reading};
use crate::declarations::{Declaration, FunctionNode, ParameterNode};
use crate::declared_types::{is_identifier_pattern, DeclaredType, Kind};
use crate::project::{FileId, Site};
use crate::tables::{
    ARRAY_LINEAR, ARRAY_N_LOG_N, CALLBACK_METHODS, GLOBAL_FUNCTIONS_LINEAR, GLOBAL_LINEAR,
    LINEAR_CONSTRUCTORS, MAP_LINEAR, OBJECT_KEYED, REGEXP_LINEAR, SET_LINEAR, STRING_LINEAR,
};

fn is_type_kind(ty: AstType) -> bool {
    matches!(
        ty,
        AstType::TSThisParameter
            | AstType::TSTypeAnnotation
            | AstType::TSLiteralType
            | AstType::TSConditionalType
            | AstType::TSUnionType
            | AstType::TSIntersectionType
            | AstType::TSParenthesizedType
            | AstType::TSTypeOperator
            | AstType::TSArrayType
            | AstType::TSIndexedAccessType
            | AstType::TSTupleType
            | AstType::TSNamedTupleMember
            | AstType::TSOptionalType
            | AstType::TSRestType
            | AstType::TSAnyKeyword
            | AstType::TSStringKeyword
            | AstType::TSBooleanKeyword
            | AstType::TSNumberKeyword
            | AstType::TSNeverKeyword
            | AstType::TSIntrinsicKeyword
            | AstType::TSUnknownKeyword
            | AstType::TSNullKeyword
            | AstType::TSUndefinedKeyword
            | AstType::TSVoidKeyword
            | AstType::TSSymbolKeyword
            | AstType::TSThisType
            | AstType::TSObjectKeyword
            | AstType::TSBigIntKeyword
            | AstType::TSTypeReference
            | AstType::TSQualifiedName
            | AstType::TSTypeParameterInstantiation
            | AstType::TSTypeParameter
            | AstType::TSTypeParameterDeclaration
            | AstType::TSTypeAliasDeclaration
            | AstType::TSClassImplements
            | AstType::TSInterfaceDeclaration
            | AstType::TSInterfaceBody
            | AstType::TSPropertySignature
            | AstType::TSIndexSignature
            | AstType::TSCallSignatureDeclaration
            | AstType::TSMethodSignature
            | AstType::TSConstructSignatureDeclaration
            | AstType::TSIndexSignatureName
            | AstType::TSInterfaceHeritage
            | AstType::TSTypePredicate
            | AstType::TSTypeLiteral
            | AstType::TSInferType
            | AstType::TSTypeQuery
            | AstType::TSImportType
            | AstType::TSImportTypeQualifiedName
            | AstType::TSFunctionType
            | AstType::TSConstructorType
            | AstType::TSMappedType
            | AstType::TSTemplateLiteralType
            | AstType::JSDocNullableType
            | AstType::JSDocNonNullableType
            | AstType::JSDocUnknownType
            | AstType::TSInstantiationExpression
    )
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

    fn children_of(&mut self, file: FileId, node: NodeId) -> Vec<NodeId> {
        let project = self.project;
        let children = self.children.entry(file).or_insert_with(|| {
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

        children[node.index()].clone()
    }

    fn cost_of_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> Reading {
        let kind = self.kind_of_node(file, argument.node_id());

        self.cost_of_node(file, kind)
    }

    fn cost_of_node(&mut self, file: FileId, kind: AstKind<'a>) -> Reading {
        if is_opaque_kind(&kind) {
            return Reading::empty();
        }

        let tags = self.perf_tags(file, kind).to_vec();
        let iteration = is_iteration_kind(&kind);

        if let Some(which) = skip_tag_of(&tags) {
            self.stats.count(&format!("@perf {which}: statement"));

            return Reading::empty();
        }

        if tags.contains(&PerfTag::Bounded) && !iteration {
            self.stats.count("@perf bounded: statement");

            return Reading::empty();
        }

        if let Some((cost, text)) = cost_tag_of(&tags) {
            self.stats.count(if iteration {
                "@perf O(...): loop"
            } else {
                "@perf O(...): statement"
            });

            let site = self.site_of_node(file, kind.node_id());

            return Reading::of_part(tagged_part_of(cost, &text, site));
        }

        match kind {
            AstKind::IfStatement(statement) => {
                let mut branches = vec![&statement.consequent];

                if let Some(alternate) = &statement.alternate {
                    branches.push(alternate);
                }

                let branches = self.hot_statements_of(file, branches, "branch");
                let mut reading = self.cost_of_expression(file, &statement.test);

                for branch in branches {
                    let part = self.branch_reading_of(file, branch, statement.node_id());

                    reading = reading.merge(part);
                }

                reading
            }
            AstKind::SwitchStatement(statement) => {
                let mut reading = self.cost_of_expression(file, &statement.discriminant);
                let cases: Vec<AstKind<'a>> = statement
                    .cases
                    .iter()
                    .map(|case| self.kind_of_node(file, case.node_id()))
                    .collect();

                for case in self.hot_kinds_of(file, cases, "case") {
                    let part = self.cost_of_node(file, case);

                    reading = reading.merge(part);
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

                for part in self.hot_kinds_of(file, parts, "try") {
                    let cost = self.cost_of_node(file, part);

                    reading = reading.merge(cost);
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

                    reading = reading.merge(cost);
                }

                reading
            }
        }
    }

    fn hot_kinds_of(
        &mut self,
        file: FileId,
        kinds: Vec<AstKind<'a>>,
        what: &str,
    ) -> Vec<AstKind<'a>> {
        let hot: Vec<AstKind<'a>> = kinds
            .iter()
            .copied()
            .filter(|kind| self.is_hot_path(file, *kind))
            .collect();

        if hot.is_empty() {
            return kinds;
        }

        self.stats.count(&format!("@perf hot: {what}"));

        hot
    }

    fn hot_statements_of(
        &mut self,
        file: FileId,
        statements: Vec<&'a Statement<'a>>,
        what: &str,
    ) -> Vec<&'a Statement<'a>> {
        let hot: Vec<&'a Statement<'a>> = statements
            .iter()
            .copied()
            .filter(|statement| {
                let kind = self.kind_of_node(file, statement.node_id());

                self.is_hot_path(file, kind)
            })
            .collect();

        if hot.is_empty() {
            return statements;
        }

        self.stats.count(&format!("@perf hot: {what}"));

        hot
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
        let hot: Vec<&'a Statement<'a>> = statements
            .iter()
            .filter(|statement| {
                let kind = self.kind_of_node(file, statement.node_id());

                self.perf_tags(file, kind).contains(&PerfTag::Hot)
            })
            .collect();
        let chosen: Vec<&'a Statement<'a>> = if hot.is_empty() {
            statements.iter().collect()
        } else {
            self.stats.count("@perf hot: block");

            hot
        };

        for statement in chosen {
            let cost = self.cost_of_statement(file, statement);

            reading = reading.merge(cost);
        }

        reading
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
                let mut chain = vec![Factor {
                    label: format!("[{} branch: runs once per {}]", exit.text(), unit),
                    site: self.site_of_node(file, site_node),
                    cost: Cost::ONE,
                    inner: Vec::new(),
                }];

                chain.extend(reading.main.chain.iter().cloned());

                let lifted = Part {
                    cost: reading.main.cost,
                    chain,
                };

                if exit == crate::bounds::Exit::Break {
                    return Reading {
                        main: Part::none(),
                        function_exit: reading.function_exit,
                        loop_exit: reading.loop_exit.max(lifted),
                    };
                }

                return Reading {
                    main: Part::none(),
                    function_exit: reading.function_exit.max(lifted),
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

            sibling = sibling.merge(cost);
        }

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

        let hoisted = self.pending_scoped.remove(&(file, node));
        let body = match hoisted {
            Some(hoisted) => Reading {
                main: body_raw.main.max(hoisted),
                ..body_raw
            },
            None => body_raw,
        };

        if bound.factor.is_one() {
            return Reading {
                main: sibling.main.max(body.main).max(body.loop_exit),
                function_exit: sibling.function_exit.max(body.function_exit),
                loop_exit: sibling.loop_exit,
            };
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
        let looped = nest(label, site, bound.factor, body.main);

        if let (Some(_), Some(scope)) = (&budget, scope) {
            let pending = self
                .pending_scoped
                .remove(&(file, scope))
                .unwrap_or_default()
                .max(looped);

            self.pending_scoped.insert((file, scope), pending);

            return Reading {
                main: sibling.main.max(body.loop_exit),
                function_exit: sibling.function_exit.max(body.function_exit),
                loop_exit: sibling.loop_exit,
            };
        }

        if budget.is_some() && self.inside_loop(file, node) {
            return Reading {
                main: sibling.main.max(body.loop_exit),
                function_exit: sibling.function_exit.max(body.function_exit).max(looped),
                loop_exit: sibling.loop_exit,
            };
        }

        Reading {
            main: sibling.main.max(looped).max(body.loop_exit),
            function_exit: sibling.function_exit.max(body.function_exit),
            loop_exit: sibling.loop_exit,
        }
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
                main: Part::none(),
                function_exit: inner.total(),
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

        inner.merge(Reading::of_part(nest(label, site, Cost::N, Part::none())))
    }

    fn cost_of_rest_target(&mut self, file: FileId, rest: &'a AssignmentTargetRest<'a>) -> Reading {
        let mut inner = Reading::empty();

        for child in self.children_of(file, rest.node_id()) {
            let child = self.kind_of_node(file, child);
            let cost = self.cost_of_node(file, child);

            inner = inner.merge(cost);
        }

        let target_span = rest.target.span();
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
            _ => self.is_tuple_site(file, DeclaredType::default(), target_span),
        };

        if constant {
            return inner;
        }

        let label = format!("spread ...{}", short(self.text_of(file, target_span)));
        let site = self.site_of_node(file, rest.node_id());

        inner.merge(Reading::of_part(nest(label, site, Cost::N, Part::none())))
    }

    pub(crate) fn member_declaration_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<Declaration<'a>> {
        if let Some(declaration) = self
            .declarations
            .member_of_receiver(self.project, file, member)
        {
            return Some(declaration);
        }

        match member {
            MemberExpression::StaticMemberExpression(access) => {
                self.callee_answer_of(file, access.span)
            }
            _ => None,
        }
    }

    fn cost_of_new(&mut self, file: FileId, new: &'a NewExpression<'a>) -> Reading {
        let mut reading = Reading::empty();

        for argument in &new.arguments {
            let cost = self.cost_of_argument(file, argument);

            reading = reading.merge(cost);
        }

        let declaration = match &new.callee {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            callee => match callee.as_member_expression() {
                Some(member) => self.member_declaration_of(file, member),
                None => None,
            },
        };
        let function =
            declaration.and_then(|declaration| self.declarations.function_of(declaration));

        if let Some((target, function)) = function {
            let callee = self.call_user(target, function, file, &new.arguments);

            if callee.cost.is_one() {
                return reading;
            }

            let name = self.name_of(target, function);
            let name = name.strip_suffix(".constructor").unwrap_or(&name);
            let site = self.site_of_node(file, new.node_id());

            return reading.merge(Reading::of_part(Part {
                cost: callee.cost,
                chain: vec![Factor {
                    label: format!("new {name}()"),
                    site,
                    cost: callee.cost,
                    inner: callee.chain,
                }],
            }));
        }

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

                    return reading.merge(Reading::of_part(nest(
                        label,
                        site,
                        Cost::N,
                        Part::none(),
                    )));
                }
            }
        }

        reading
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

                reading = reading.merge(cost);
            }
        }

        let callee = unwrap(&call.callee);
        let member = member_expression_of(callee)
            .filter(|member| !matches!(member, MemberExpression::ComputedMemberExpression(_)));

        if let Some(member) = member {
            let cost = self.cost_of_expression(file, member.object());

            reading = reading.merge(cost);
        }

        let declaration = self.callee_declaration_of(file, call);
        let site = self.site_of_node(file, call.node_id());

        if let (true, Some(Declaration::Parameter { parameter, .. }), Some(reference)) =
            (self.options.callbacks, declaration, identifier_of(callee))
        {
            let identifier = match parameter {
                ParameterNode::Formal(formal) => is_identifier_pattern(&formal.pattern),
                ParameterNode::Rest(rest) => is_identifier_pattern(&rest.rest.argument),
            };

            if identifier {
                let substituted = self
                    .binding_of_identifier(file, reference)
                    .and_then(|binding| self.current_substitutions.get(&binding).cloned());

                if let Some(part) = substituted {
                    if !part.cost.is_one() {
                        return reading.merge(Reading::of_part(Part {
                            cost: part.cost,
                            chain: vec![Factor {
                                label: format!("call {}() [callback parameter]", reference.name),
                                site,
                                cost: part.cost,
                                inner: part.chain,
                            }],
                        }));
                    }
                }

                return reading;
            }
        }

        let function =
            declaration.and_then(|declaration| self.declarations.function_of(declaration));

        if let Some((target, function)) = function {
            let called = self.call_user(target, function, file, &call.arguments);

            if called.cost.is_one() {
                return reading;
            }

            let recursive =
                called.chain.len() == 1 && called.chain[0].label.starts_with("recursive call");
            let chain = if recursive {
                let mut factor = called.chain[0].clone();

                factor.site = site;

                vec![factor]
            } else {
                vec![Factor {
                    label: format!("call {}()", self.name_of(target, function)),
                    site,
                    cost: called.cost,
                    inner: called.chain,
                }]
            };

            return reading.merge(Reading::of_part(Part {
                cost: called.cost,
                chain,
            }));
        }

        if let Some(member) = member {
            return self.cost_of_method_call(file, call, member, reading, site);
        }

        if let Some(reference) = identifier_of(callee) {
            if is_listed(GLOBAL_FUNCTIONS_LINEAR, reference.name.as_str()) {
                return reading.merge(Reading::of_part(nest(
                    format!("{}()", reference.name),
                    site,
                    Cost::N,
                    Part::none(),
                )));
            }
        }

        reading
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
                    return reading.merge(Reading::of_part(callback));
                }

                let argument_text = match first {
                    Some(argument) => short(self.text_of(file, argument.span())),
                    None => String::new(),
                };

                return reading.merge(Reading::of_part(nest(
                    format!("{global_name}.{method}({argument_text})"),
                    site,
                    Cost::N,
                    callback,
                )));
            }
        }

        let kind = self.kind_of(file, receiver, &method);
        let tag = if kind == Kind::Unknown { "?" } else { "" };
        let receiver_text = short(self.text_of(file, receiver.span()));
        let label = |suffix: &str| format!("{receiver_text}.{method}(){tag}{suffix}");
        let shared = self.is_share_sized(file, receiver)
            || (method == "set"
                && first.is_some_and(|argument| self.is_share_sized_argument(file, argument)))
            || self.is_share_sized_call(file, call);
        let bounded = self.is_constant_sized(file, receiver) || shared;
        let array_like = kind == Kind::Array || kind == Kind::Unknown;

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
                    nest(label(" [n log n]"), site, Cost::N_LOG_N, callback)
                };

                return reading.merge(Reading::of_part(part));
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
                    nest(label(""), site, Cost::N, callback)
                };

                return reading.merge(Reading::of_part(part));
            }
        }

        if (kind == Kind::Set && is_listed(SET_LINEAR, &method))
            || (kind == Kind::Map && is_listed(MAP_LINEAR, &method))
        {
            let callback = self.callback_part_of(file, first);

            return reading.merge(Reading::of_part(nest(label(""), site, Cost::N, callback)));
        }

        if self.options.strings_linear
            && (kind == Kind::String || kind == Kind::Unknown)
            && is_listed(STRING_LINEAR, &method)
            && !bounded
        {
            return reading.merge(Reading::of_part(nest(
                label(" [string]"),
                site,
                Cost::N,
                Part::none(),
            )));
        }

        if self.options.strings_linear && kind == Kind::RegExp && is_listed(REGEXP_LINEAR, &method)
        {
            if let Some(argument) = first {
                if !self.is_constant_sized_argument(file, argument) {
                    return reading.merge(Reading::of_part(nest(
                        label(" [regexp]"),
                        site,
                        Cost::N,
                        Part::none(),
                    )));
                }
            }
        }

        reading
    }
}

fn tagged_part_of(cost: Cost, text: &str, site: Site) -> Part {
    Part {
        cost,
        chain: if cost.is_one() {
            Vec::new()
        } else {
            vec![Factor {
                label: format!("@perf {text}"),
                site,
                cost,
                inner: Vec::new(),
            }]
        },
    }
}

pub(crate) fn tagged_reading_of(cost: Cost, text: &str, site: Site) -> Reading {
    Reading::of_part(tagged_part_of(cost, text, site))
}

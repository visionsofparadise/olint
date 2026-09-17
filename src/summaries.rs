use std::collections::HashMap;

use oxc_ast::ast::{Argument, BindingPattern, Expression, MethodDefinitionKind, PropertyKind};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::analysis::{Analysis, Stats};
use crate::cost::{Cost, Factor, Part, Preference, Reading};
use crate::declarations::{Binding, Declaration, FunctionId, FunctionNode, TargetSet};
use crate::directives::{cost_tag_of, PerfTag};
use crate::effects::Effects;
use crate::project::{FileId, Site};
use crate::syntax::unwrap;
use crate::tsc::{Query, TscError, TscReply};
use crate::types::TscPass;
use crate::unknowns::{UnknownId, UnknownReason};
use crate::values::{ArgumentFacts, ValueFacts};
use crate::walker::tagged_reading_of;

pub type Substitutions = HashMap<Binding, ArgumentFacts>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SummaryId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryRecord {
    pub reading: Reading,
    pub result: ValueFacts,
    pub effects: Effects,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ArgumentKey {
    pub binding: Binding,
    pub value: ValueFacts,
    pub cost: Option<Cost>,
    pub unknowns: Vec<(UnknownId, Option<Cost>)>,
    pub preference: Preference,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SummaryKey {
    pub function: FunctionId,
    pub substitutions: Vec<(String, ArgumentKey)>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TscRounds {
    pub sites: usize,
    pub rounds: usize,
}

impl<'p, 'a> Analysis<'p, 'a> {
    fn key_of(
        &self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: &Substitutions,
    ) -> SummaryKey {
        let mut named: Vec<(String, ArgumentKey)> = substitutions
            .iter()
            .filter(|(_, facts)| {
                facts.callback.is_some()
                    || facts.value.size.is_some()
                    || facts.value.latent.is_some()
                    || !facts.value.targets.open
                    || !facts.value.targets.known.is_empty()
            })
            .map(|(binding, facts)| {
                (
                    self.binding_name_of(*binding),
                    ArgumentKey {
                        binding: *binding,
                        value: facts.value.clone(),
                        cost: facts.callback.as_ref().map(|part| part.cost),
                        unknowns: self
                            .unknowns
                            .semantic_key(facts.callback.as_ref().and_then(|part| part.unknowns)),
                        preference: facts.preference,
                    },
                )
            })
            .collect();

        named.sort_by(|left, right| {
            left.0.cmp(&right.0).then_with(|| {
                format!("{:?}", left.1.binding).cmp(&format!("{:?}", right.1.binding))
            })
        });

        SummaryKey {
            function: FunctionId {
                file,
                node: function.node_id(),
            },
            substitutions: named,
        }
    }

    fn store_summary(&mut self, key: SummaryKey, reading: Reading, effects: Effects) -> SummaryId {
        let span = self
            .kind_of_node(key.function.file, key.function.node)
            .span();
        let origin = self.source_span(key.function.file, span);
        let result = self.values.at(origin);
        let id =
            SummaryId(u32::try_from(self.summaries_arena.len()).expect("summary arena fits u32"));

        self.summaries_arena.push(SummaryRecord {
            reading,
            result,
            effects,
        });
        self.summaries.insert(key, id);

        id
    }

    fn binding_name_of(&self, binding: Binding) -> String {
        match binding {
            Binding::Symbol { file, symbol } => self
                .project
                .file(file)
                .semantic
                .scoping()
                .symbol_name(symbol)
                .to_string(),
        }
    }

    pub fn summarize(&mut self, file: FileId, function: FunctionNode<'a>) -> Reading {
        self.summarize_with(file, function, Substitutions::new(), false)
    }

    pub fn summarize_with(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        substitutions: Substitutions,
        raw: bool,
    ) -> Reading {
        let key = self.key_of(file, function, &substitutions);

        if !raw {
            if let Some(known) = self.summaries.get(&key) {
                return self.summaries_arena[known.0 as usize].reading.clone();
            }

            let tags = self.function_tags(file, function);

            if tags.contains(&PerfTag::Ignore) {
                self.stats.count("@perf ignore: function");
                self.store_summary(key, Reading::empty(), Effects::unknown());

                return Reading::empty();
            }

            if let Some((cost, text)) = cost_tag_of(&tags) {
                self.stats.count("@perf O(...): function");

                let reading = tagged_reading_of(cost, &text, self.function_site_of(file, function));

                self.store_summary(key, reading.clone(), Effects::unknown());

                return reading;
            }
        }

        if let Some(index) = self.stack.iter().position(|known| *known == key) {
            self.minimum_hit = self.minimum_hit.min(index);

            return Reading::of_part(Part::unmarked(
                Cost::N,
                vec![Factor {
                    label: format!("recursive call {}()", self.name_of(file, function)),
                    site: self.function_site_of(file, function),
                    cost: Cost::N,
                    inner: Vec::new(),
                }],
            ));
        }

        let depth = self.stack.len();

        self.stack.push(key.clone());

        let saved_effects = std::mem::take(&mut self.current_effects);
        let saved_substitutions = std::mem::replace(&mut self.current_substitutions, substitutions);
        let has_body = match function {
            FunctionNode::Function(inner) => inner.body.is_some(),
            FunctionNode::Arrow(_) => true,
        };
        let context = if has_body {
            Some(self.collect_budgets(file, function))
        } else {
            None
        };
        let saved_context = std::mem::replace(&mut self.budget_context, context);
        let saved_share = std::mem::take(&mut self.share_bindings);
        let saved_minimum = std::mem::replace(&mut self.minimum_hit, usize::MAX);
        let saved_pending = std::mem::take(&mut self.pending_cycle);
        let reading = if has_body {
            self.cost_of_function_body(file, function)
        } else {
            self.unknown_reading(
                file,
                self.kind_of_node(file, function.node_id()).span(),
                UnknownReason::Target,
            )
        };
        let effects = std::mem::replace(&mut self.current_effects, saved_effects);

        self.current_substitutions = saved_substitutions;
        self.budget_context = saved_context;
        self.share_bindings = saved_share;

        self.stack.pop();

        let hit = self.minimum_hit;
        let members = std::mem::replace(&mut self.pending_cycle, saved_pending);

        if hit < depth {
            self.pending_cycle.push(key);
            self.pending_cycle.extend(members);

            self.minimum_hit = saved_minimum.min(hit);

            return reading;
        }

        self.minimum_hit = saved_minimum;

        if raw {
            return reading;
        }

        self.store_summary(key, reading.clone(), effects.clone());

        for member in members {
            self.stats
                .count("recursion cycle: member takes root summary");

            let tagged = Reading {
                phases: reading.phases,
                main: self.cycle_tag_of(reading.main.clone(), file, function),
                function_exit: self.cycle_tag_of(reading.function_exit.clone(), file, function),
                loop_exit: self.cycle_tag_of(reading.loop_exit.clone(), file, function),
            };

            self.store_summary(member, tagged, effects.clone());
        }

        reading
    }

    fn cycle_tag_of(&self, part: Part, file: FileId, root: FunctionNode<'a>) -> Part {
        if part.cost.is_one() {
            return part;
        }

        let mut chain = vec![Factor {
            label: format!("[recursion cycle with {}()]", self.name_of(file, root)),
            site: self.function_site_of(file, root),
            cost: Cost::ONE,
            inner: Vec::new(),
        }];

        chain.extend(part.chain);

        Part { chain, ..part }
    }

    fn inherited_substitutions_of(&self, function: FunctionNode<'a>) -> Substitutions {
        self.current_substitutions
            .iter()
            .filter(|(binding, _)| {
                matches!(
                    self.declarations.of_binding(self.project, **binding),
                    Some(Declaration::Parameter { function: owner, .. }) if owner != function
                )
            })
            .map(|(binding, part)| (*binding, part.clone()))
            .collect()
    }

    pub(crate) fn argument_facts_of(
        &mut self,
        file: FileId,
        argument: &'a Argument<'a>,
    ) -> ArgumentFacts {
        let origin = self.source_span(file, argument.span());
        let mut value = self.values.at(origin);
        let expression = argument.as_expression().map(unwrap);
        let declaration = expression.and_then(|expression| match expression {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            _ => expression
                .as_member_expression()
                .and_then(|member| self.member_declaration_of(file, member)),
        });

        if let Some(Expression::Identifier(reference)) = expression {
            if let Some(binding) = self.binding_of_identifier(file, reference) {
                if let Some(facts) = self.current_substitutions.get(&binding) {
                    return facts.clone();
                }
            }
        }

        let function = match expression {
            Some(Expression::FunctionExpression(function)) => {
                Some((file, FunctionNode::Function(function)))
            }
            Some(Expression::ArrowFunctionExpression(arrow)) => {
                Some((file, FunctionNode::Arrow(arrow)))
            }
            _ => declaration.and_then(|declaration| self.declarations.function_of(declaration)),
        };
        let callback = if let Some((target, function)) = function {
            let inherited = self.inherited_substitutions_of(function);
            let key = self.key_of(target, function, &inherited);
            let (part, cyclic) = self.within_cycle_of(|analysis| {
                let reading = analysis.summarize_with(target, function, inherited, false);

                reading.total(&mut analysis.unknowns)
            });
            value.targets = TargetSet {
                known: vec![FunctionId {
                    file: target,
                    node: function.node_id(),
                }],
                open: false,
            };
            value.latent = self.summaries.get(&key).copied();

            Some(self.called_part_of(target, function, part, cyclic))
        } else {
            None
        };
        let preference = callback
            .as_ref()
            .map_or(Preference::Absent, |part| part.preference);

        ArgumentFacts {
            value,
            callback,
            preference,
        }
    }

    pub(crate) fn part_of_argument(
        &mut self,
        file: FileId,
        argument: Option<&'a Argument<'a>>,
    ) -> Option<Part> {
        let argument = argument?;
        let facts = self.argument_facts_of(file, argument);

        self.apply_argument_effects(&facts);

        facts
            .callback
            .or_else(|| Some(self.unknown_part(file, argument.span(), UnknownReason::Target)))
    }

    pub(crate) fn apply_argument_effects(&mut self, facts: &ArgumentFacts) {
        let effects = facts
            .value
            .latent
            .and_then(|id| self.summaries_arena.get(id.0 as usize))
            .map(|record| record.effects.clone())
            .unwrap_or_else(Effects::unknown);

        self.current_effects.join(&effects);
    }

    pub(crate) fn within_cycle_of<T>(&mut self, run: impl FnOnce(&mut Self) -> T) -> (T, bool) {
        let before = std::mem::replace(&mut self.minimum_hit, usize::MAX);
        let result = run(self);
        let hit = self.minimum_hit;

        self.minimum_hit = before.min(hit);

        (result, hit < self.stack.len())
    }

    pub(crate) fn called_part_of(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        part: Part,
        cyclic: bool,
    ) -> Part {
        let mark = if cyclic {
            None
        } else {
            self.function_preference_of(file, function)
        };

        match mark {
            Some(mark) => part.preferred(mark),
            None if part.cost.is_one() && part.unknowns.is_none() => {
                part.preferred(Preference::Absent)
            }
            None => part.preferred(Preference::Unmarked),
        }
    }

    pub fn call_user(
        &mut self,
        file: FileId,
        function: FunctionNode<'a>,
        call_file: FileId,
        arguments: &'a [Argument<'a>],
    ) -> Part {
        let mut substitutions = Substitutions::new();

        let (parameters, offset) = match function {
            FunctionNode::Function(inner) => {
                (&inner.params, usize::from(inner.this_param.is_some()))
            }
            FunctionNode::Arrow(arrow) => (&arrow.params, 0),
        };

        if offset == 1 {
            let _ = self.part_of_argument(call_file, arguments.first());
        }

        for (index, parameter) in parameters.items.iter().enumerate() {
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                continue;
            };
            let Some(argument) = arguments.get(index + offset) else {
                continue;
            };
            let facts = self.argument_facts_of(call_file, argument);

            if let Some(symbol) = identifier.symbol_id.get() {
                substitutions.insert(Binding::Symbol { file, symbol }, facts);
            }
        }

        let key = self.key_of(file, function, &substitutions);
        let reading = self.summarize_with(file, function, substitutions, false);
        let effects = self
            .summaries
            .get(&key)
            .map(|id| self.summaries_arena[id.0 as usize].effects.clone())
            .unwrap_or_else(Effects::unknown);

        self.current_effects.join(&effects);

        reading.total(&mut self.unknowns)
    }

    fn method_owner_of(&self, file: FileId, element: NodeId) -> String {
        let nodes = self.project.file(file).semantic.nodes();
        let body = nodes.parent_id(element);

        match (nodes.kind(body), nodes.parent_kind(body)) {
            (AstKind::ClassBody(_), AstKind::Class(class)) => {
                let name = class
                    .id
                    .as_ref()
                    .map(|id| id.name.to_string())
                    .unwrap_or_else(|| "<class>".to_string());

                format!("{name}.")
            }
            _ => String::new(),
        }
    }

    fn key_text_of(
        &self,
        file: FileId,
        key: &oxc_ast::ast::PropertyKey<'a>,
        computed: bool,
    ) -> String {
        let span = key.span();

        if !computed {
            return self.text_of(file, span).to_string();
        }

        let source = self.project.file(file).text;
        let before = &source[..span.start as usize];
        let after = &source[span.end as usize..];
        let open = before.trim_end().strip_suffix('[').map(str::len);
        let close = after
            .find(|character: char| !character.is_whitespace())
            .filter(|index| after[*index..].starts_with(']'));

        match (open, close) {
            (Some(open), Some(close)) => source[open..span.end as usize + close + 1].to_string(),
            _ => format!("[{}]", self.text_of(file, span)),
        }
    }

    fn field_name_of(
        &self,
        file: FileId,
        field: NodeId,
        key: &oxc_ast::ast::PropertyKey<'a>,
        computed: bool,
    ) -> String {
        format!(
            "{}{}",
            self.method_owner_of(file, field),
            self.key_text_of(file, key, computed)
        )
    }

    pub fn name_of(&self, file: FileId, function: FunctionNode<'a>) -> String {
        let nodes = self.project.file(file).semantic.nodes();
        let node = function.node_id();
        let parent = nodes.parent_id(node);

        if let FunctionNode::Function(inner) = function {
            if inner.is_declaration() {
                return inner
                    .id
                    .as_ref()
                    .map(|id| id.name.to_string())
                    .unwrap_or_else(|| "<default>".to_string());
            }

            match nodes.kind(parent) {
                AstKind::MethodDefinition(method) => {
                    let owner = self.method_owner_of(file, parent);

                    if method.kind == MethodDefinitionKind::Constructor {
                        return format!("{owner}constructor");
                    }

                    return format!(
                        "{owner}{}",
                        self.key_text_of(file, &method.key, method.computed)
                    );
                }
                AstKind::ObjectProperty(property)
                    if property.method || property.kind != PropertyKind::Init =>
                {
                    return self.key_text_of(file, &property.key, property.computed);
                }
                _ => {}
            }
        }

        match nodes.kind(parent) {
            AstKind::VariableDeclarator(declarator) => {
                return self.text_of(file, declarator.id.span()).to_string();
            }
            AstKind::ObjectProperty(property) => {
                return self.key_text_of(file, &property.key, property.computed);
            }
            AstKind::PropertyDefinition(property) => {
                return self.field_name_of(file, parent, &property.key, property.computed);
            }
            AstKind::AccessorProperty(property) => {
                return self.field_name_of(file, parent, &property.key, property.computed);
            }
            _ => {}
        }

        if let FunctionNode::Function(inner) = function {
            if let Some(id) = &inner.id {
                return id.name.to_string();
            }
        }

        match nodes.kind(parent) {
            AstKind::CallExpression(_) | AstKind::NewExpression(_) => "<callback>".to_string(),
            AstKind::ReturnStatement(_) => "<returned fn>".to_string(),
            _ => "<anonymous>".to_string(),
        }
    }

    pub(crate) fn function_start_of(&self, file: FileId, function: FunctionNode<'a>) -> u32 {
        let nodes = self.project.file(file).semantic.nodes();
        let node = function.node_id();

        if let FunctionNode::Function(_) = function {
            match nodes.parent_kind(node) {
                AstKind::MethodDefinition(method) => return method.span.start,
                AstKind::ObjectProperty(property)
                    if property.method || property.kind != PropertyKind::Init =>
                {
                    return property.span.start
                }
                _ => {}
            }
        }

        nodes.kind(node).span().start
    }

    pub fn function_site_of(&self, file: FileId, function: FunctionNode<'a>) -> Site {
        Site {
            file,
            line: self
                .project
                .line_of(file, self.function_start_of(file, function)),
        }
    }

    pub fn reportable(&mut self) -> Vec<(FileId, FunctionNode<'a>)> {
        let project = self.project;
        let mut found = Vec::new();

        for source in &project.files {
            let file = source.id;

            if !project.is_project_file(file)
                || project.is_test_path(file)
                || source.relative.starts_with("..")
            {
                continue;
            }

            let nodes = source.semantic.nodes();
            let mut functions: Vec<FunctionNode<'a>> = nodes
                .iter()
                .filter_map(|node| {
                    let parent = nodes.parent_kind(node.id());
                    let inline = matches!(
                        parent,
                        AstKind::CallExpression(_) | AstKind::NewExpression(_)
                    );

                    match node.kind() {
                        AstKind::Function(function) if function.body.is_some() => (!(inline
                            && function.is_expression()))
                        .then_some(FunctionNode::Function(function)),
                        AstKind::ArrowFunctionExpression(arrow) => {
                            (!inline).then_some(FunctionNode::Arrow(arrow))
                        }
                        _ => None,
                    }
                })
                .collect();

            functions.sort_by_key(|function| {
                let end = nodes.kind(function.node_id()).span().end;

                (
                    self.function_start_of(file, *function),
                    std::cmp::Reverse(end),
                )
            });

            for function in functions {
                if !self
                    .function_tags(file, function)
                    .contains(&PerfTag::Ignore)
                {
                    found.push((file, function));
                }
            }
        }

        found
    }

    pub fn reset_between_passes(&mut self) {
        self.summaries.clear();
        self.bound_seen.clear();
        self.pending_scoped.clear();

        self.current_effects = Effects::default();
        self.stats = Stats::default();
    }

    pub fn summarize_reportable(&mut self, functions: &[(FileId, FunctionNode<'a>)]) {
        for (file, function) in functions {
            self.summarize(*file, *function);

            let tags = self.function_tags(*file, *function);

            if cost_tag_of(&tags).is_some() {
                self.summarize_with(*file, *function, Substitutions::new(), true);
            }
        }
    }

    pub fn gather_answers(
        &mut self,
        functions: &[(FileId, FunctionNode<'a>)],
        mut ask: impl FnMut(&[Query]) -> Result<TscReply, TscError>,
    ) -> Result<TscRounds, TscError> {
        let mut rounds = TscRounds::default();

        self.set_pass(TscPass::Recording);

        loop {
            self.summarize_reportable(functions);

            let queries = self.needed_queries();
            let asked_nothing = queries.is_empty();

            if !asked_nothing || rounds.rounds == 0 {
                let reply = ask(&queries)?;

                rounds.sites += queries.len();
                rounds.rounds += 1;

                self.take_answers(reply)?;
            }

            self.reset_between_passes();

            if asked_nothing {
                break;
            }
        }

        self.set_pass(TscPass::Answering);

        Ok(rounds)
    }
}

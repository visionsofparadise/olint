use std::path::Path;

use oxc_ast::ast::{CallExpression, Expression, MemberExpression};
use oxc_ast::AstKind;
use oxc_span::{GetSpan, Span};

use crate::analysis::Analysis;
use crate::declarations::{
    declaration_of_node, Binding, Declaration, FunctionId, FunctionNode, ParameterNode, TargetSet,
};
use crate::declared_types::{DeclaredType, Kind};
use crate::project::FileId;
use crate::syntax::{member_expression_of, unwrap};
use crate::tables::method_matters;
use crate::tsc::{CalleeAnswer, CalleeTarget, Query, TscAnswer, TscError, TscReply, TypeAnswer};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TscPass {
    Recording,
    Answering,
    Off,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QueryKind {
    Type,
    Callee,
}

pub(crate) type SiteKey = (FileId, u32, u32, QueryKind);

fn kind_label_of(kind: Kind) -> &'static str {
    match kind {
        Kind::Array => "array",
        Kind::Set => "set",
        Kind::Map => "map",
        Kind::String => "string",
        Kind::RegExp => "regexp",
        Kind::Other => "other",
        Kind::Unknown => "unknown",
    }
}

enum Lookup<T> {
    Answered(Option<T>),
    Unanswered,
}

pub(crate) struct ResolvedCallee<'a> {
    pub(crate) declaration: Option<Declaration<'a>>,
    pub(crate) closed: bool,
    pub(crate) targets: TargetSet,
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn parameter_binding_of(&self, declaration: Declaration<'a>) -> Option<Binding> {
        let Declaration::Parameter {
            file, parameter, ..
        } = declaration
        else {
            return None;
        };
        let pattern = match parameter {
            ParameterNode::Formal(parameter) => &parameter.pattern,
            ParameterNode::Rest(parameter) => &parameter.rest.argument,
        };
        let oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) = pattern else {
            return None;
        };

        Some(Binding::Symbol {
            file,
            symbol: identifier.symbol_id.get()?,
        })
    }

    pub fn kind_of(&mut self, file: FileId, e: &'a Expression<'a>, method: &str) -> Kind {
        let mut kind = self.declared_type_of_expression(file, e).kind;

        if kind == Kind::Unknown && method_matters(method) {
            if let Some(answer) = self.type_answer_of(file, unwrap(e).span()) {
                kind = answer.kind;
            }
        }

        self.stats.count(&format!("kind: {}", kind_label_of(kind)));

        kind
    }

    pub fn is_tuple(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let declared = self.declared_type_of_expression(file, e);

        self.is_declared_tuple(declared)
    }

    pub(crate) fn is_declared_tuple(&mut self, declared: DeclaredType) -> bool {
        if declared.tuple {
            self.stats.count("types: tuple");
        }

        declared.tuple
    }

    pub fn is_closed(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let declared = self.declared_type_of_expression(file, e);

        if declared.closed {
            self.stats.count("types: closed object");
        }

        declared.closed
    }

    pub fn callee_declaration_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<Declaration<'a>> {
        self.resolved_callee_of(file, call).declaration
    }

    pub fn callee_targets_of(&mut self, file: FileId, call: &'a CallExpression<'a>) -> TargetSet {
        self.resolved_callee_of(file, call).targets
    }

    pub(crate) fn resolved_of_declaration(
        &self,
        declaration: Option<Declaration<'a>>,
        closed: bool,
    ) -> ResolvedCallee<'a> {
        let known = declaration
            .and_then(|declaration| self.declarations.function_of(declaration))
            .map(|(file, function)| FunctionId {
                file,
                node: function.node_id(),
            })
            .into_iter()
            .collect::<Vec<_>>();

        ResolvedCallee {
            declaration,
            closed,
            targets: TargetSet {
                open: !closed || known.is_empty(),
                known,
            },
        }
    }

    pub(crate) fn resolved_callee_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> ResolvedCallee<'a> {
        let callee = unwrap(&call.callee);

        if let Expression::Identifier(reference) = callee {
            let (declaration, closed) =
                self.declarations
                    .callable_reference(self.project, file, reference);
            let mut resolved = self.resolved_of_declaration(declaration, closed);

            if !closed {
                for candidate in
                    self.declarations
                        .runtime_candidates_of(self.project, file, reference)
                {
                    if let Some((file, function)) = self.declarations.function_of(candidate) {
                        let known = FunctionId {
                            file,
                            node: function.node_id(),
                        };

                        if !resolved.targets.known.contains(&known) {
                            resolved.targets.known.push(known);
                        }
                    }
                }
            }

            return resolved;
        }

        let Some(member) = member_expression_of(callee) else {
            return self.resolved_of_declaration(None, false);
        };

        if let Some(declaration) = self
            .declarations
            .member_of_receiver(self.project, file, member)
        {
            let declaration = self
                .declarations
                .executable_declaration(self.project, declaration);

            return self.resolved_of_declaration(Some(declaration), false);
        }

        let MemberExpression::StaticMemberExpression(access) = member else {
            return self.resolved_of_declaration(None, false);
        };

        match self.callee_candidates_of(file, access.span) {
            Some(answer) => self.resolved_of_callee_answer(&answer),
            None => self.resolved_of_declaration(None, false),
        }
    }

    pub(crate) fn resolved_member_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> ResolvedCallee<'a> {
        if let Some(declaration) = self
            .declarations
            .member_of_receiver(self.project, file, member)
        {
            return self.resolved_of_declaration(Some(declaration), true);
        }

        let answer = match member {
            MemberExpression::StaticMemberExpression(access) => {
                self.callee_candidates_of(file, access.span)
            }
            _ => None,
        };

        match answer {
            Some(answer) => self.resolved_of_callee_answer(&answer),
            None => self.resolved_of_declaration(None, false),
        }
    }

    fn callee_candidates_of(&mut self, file: FileId, span: Span) -> Option<CalleeAnswer> {
        let query = Query::Callee {
            file: self.query_path_of(file),
            pos: span.start,
            end: span.end,
        };

        match self.answer_of_site(site_key_of(file, span, QueryKind::Callee), query) {
            Lookup::Answered(Some(TscAnswer::Callee(answer))) => Some(answer),
            _ => None,
        }
    }

    pub fn set_pass(&mut self, pass: TscPass) {
        self.pass = pass;
    }

    pub fn needed_queries(&self) -> Vec<Query> {
        self.needed.values().cloned().collect()
    }

    pub fn take_answers(&mut self, reply: TscReply) -> Result<(), TscError> {
        if reply.answers.len() != self.needed.len() {
            return Err(TscError::Malformed(format!(
                "{} answers for {} queries",
                reply.answers.len(),
                self.needed.len()
            )));
        }

        for answer in reply.answers.iter().flatten() {
            if let TscAnswer::Callee(answer) = answer {
                for target in &answer.targets {
                    self.validate_callee_target(target)?;
                }
            }
        }

        let keys: Vec<SiteKey> = self.needed.keys().copied().collect();

        for (key, answer) in keys.into_iter().zip(reply.answers) {
            self.answers.insert(key, answer);
        }

        self.tsc_info = format!("typescript {} at {}", reply.typescript, reply.from);

        self.needed.clear();

        Ok(())
    }

    pub fn fall_back_to_declarations(&mut self) {
        self.reset_between_passes();
        self.needed.clear();
        self.answers.clear();

        self.pass = TscPass::Off;
    }

    fn type_answer_of(&mut self, file: FileId, span: Span) -> Option<TypeAnswer> {
        let query = Query::Type {
            file: self.query_path_of(file),
            pos: span.start,
            end: span.end,
        };

        match self.answer_of_site(site_key_of(file, span, QueryKind::Type), query) {
            Lookup::Answered(Some(TscAnswer::Type(answer))) => Some(answer),
            _ => None,
        }
    }

    fn answer_of_site(&mut self, key: SiteKey, query: Query) -> Lookup<TscAnswer> {
        if self.pass == TscPass::Off {
            return Lookup::Unanswered;
        }

        if let Some(answer) = self.answers.get(&key) {
            return Lookup::Answered(answer.clone());
        }

        match self.pass {
            TscPass::Recording => {
                self.needed.entry(key).or_insert(query);
            }
            TscPass::Answering => self.stats.count("tsc: miss"),
            TscPass::Off => {}
        }

        Lookup::Unanswered
    }

    fn query_path_of(&self, file: FileId) -> String {
        self.project.file(file).path.to_string_lossy().into_owned()
    }

    fn validate_callee_target(&self, target: &CalleeTarget) -> Result<(), TscError> {
        let Some(file) = self.project.file_by_path(Path::new(&target.file)) else {
            return Ok(());
        };
        let text = self.project.file(file).text;
        let (start, end) = (target.start as usize, target.end as usize);

        if start <= end
            && end <= text.len()
            && text.is_char_boundary(start)
            && text.is_char_boundary(end)
        {
            return Ok(());
        }

        Err(TscError::Malformed(format!(
            "callee target {start}..{end} lies outside the UTF-8 text of {}",
            target.file
        )))
    }

    fn resolved_of_callee_answer(&self, answer: &CalleeAnswer) -> ResolvedCallee<'a> {
        let mut declarations = Vec::new();
        let mut known = Vec::new();
        let mut open = answer.open;

        for target in &answer.targets {
            match self.executable_of_callee_target(target) {
                Some((declaration, function)) => {
                    if !known.contains(&function) {
                        known.push(function);
                        declarations.push(declaration);
                    }
                }
                None => open = true,
            }
        }

        ResolvedCallee {
            declaration: match declarations.as_slice() {
                [declaration] => Some(*declaration),
                _ => None,
            },
            closed: !open && !known.is_empty(),
            targets: TargetSet {
                open: open || known.is_empty(),
                known,
            },
        }
    }

    fn executable_of_callee_target(
        &self,
        answer: &CalleeTarget,
    ) -> Option<(Declaration<'a>, FunctionId)> {
        let target = self.project.file_by_path(Path::new(&answer.file))?;
        let nodes = self.project.file(target).semantic.nodes();
        let node =
            self.declarations
                .declaration_within(self.project, target, answer.start, answer.end)?;

        if let AstKind::ArrowFunctionExpression(arrow) = nodes.kind(node) {
            return Some((
                Declaration::Function {
                    file: target,
                    function: FunctionNode::Arrow(arrow),
                },
                FunctionId { file: target, node },
            ));
        }

        let declaration = self.declarations.executable_declaration(
            self.project,
            declaration_of_node(self.project, target, node)?,
        );
        let (file, function) = self.declarations.function_of(declaration)?;

        Some((
            declaration,
            FunctionId {
                file,
                node: function.node_id(),
            },
        ))
    }
}

fn site_key_of(file: FileId, span: Span, kind: QueryKind) -> SiteKey {
    (file, span.start, span.end, kind)
}

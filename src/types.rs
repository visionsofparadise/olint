use std::path::Path;

use oxc_ast::ast::{CallExpression, Expression, MemberExpression};
use oxc_ast::AstKind;
use oxc_span::{GetSpan, Span};

use crate::analysis::Analysis;
use crate::constants::{member_expression_of, unwrap};
use crate::declarations::{declaration_of_node, Declaration};
use crate::declared_types::{DeclaredType, Kind};
use crate::oracle::{CalleeAnswer, OracleAnswer, OracleReply, Query, TypeAnswer};
use crate::project::FileId;
use crate::tables::method_matters;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OraclePass {
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

fn is_declaration_kind(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::Function(_)
            | AstKind::ArrowFunctionExpression(_)
            | AstKind::VariableDeclarator(_)
            | AstKind::FormalParameter(_)
            | AstKind::FormalParameterRest(_)
            | AstKind::Class(_)
            | AstKind::MethodDefinition(_)
            | AstKind::PropertyDefinition(_)
            | AstKind::ObjectProperty(_)
            | AstKind::TSEnumDeclaration(_)
            | AstKind::TSEnumMember(_)
            | AstKind::TSInterfaceDeclaration(_)
            | AstKind::TSTypeAliasDeclaration(_)
            | AstKind::TSTypeParameter(_)
    )
}

enum Lookup<T> {
    Answered(Option<T>),
    Unanswered,
}

impl<'p, 'a> Analysis<'p, 'a> {
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

        self.is_tuple_site(file, declared, unwrap(e).span())
    }

    pub(crate) fn is_tuple_site(
        &mut self,
        file: FileId,
        declared: DeclaredType,
        span: Span,
    ) -> bool {
        let mut tuple = declared.tuple;

        if !tuple {
            tuple = self
                .type_answer_of(file, span)
                .is_some_and(|answer| answer.tuple);
        }

        if tuple {
            self.stats.count("types: tuple");
        }

        tuple
    }

    pub fn is_closed(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let declared = self.declared_type_of_expression(file, e);

        self.is_closed_site(file, declared, unwrap(e).span())
    }

    pub(crate) fn is_closed_site(
        &mut self,
        file: FileId,
        declared: DeclaredType,
        span: Span,
    ) -> bool {
        let mut closed = declared.closed;

        if !closed {
            closed = self
                .type_answer_of(file, span)
                .is_some_and(|answer| answer.closed);
        }

        if closed {
            self.stats.count("types: closed object");
        }

        closed
    }

    pub fn callee_declaration_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<Declaration<'a>> {
        let callee = unwrap(&call.callee);

        if let Expression::Identifier(reference) = callee {
            return self
                .declarations
                .of_reference(self.project, file, reference);
        }

        let member = member_expression_of(callee)?;

        if let Some(declaration) = self
            .declarations
            .member_of_receiver(self.project, file, member)
        {
            return Some(declaration);
        }

        let MemberExpression::StaticMemberExpression(access) = member else {
            return None;
        };

        self.callee_answer_of(file, access.span)
    }

    pub(crate) fn callee_answer_of(&mut self, file: FileId, span: Span) -> Option<Declaration<'a>> {
        let query = Query::Callee {
            file: self.query_path_of(file),
            pos: span.start,
            end: span.end,
        };

        match self.answer_of_site(site_key_of(file, span, QueryKind::Callee), query) {
            Lookup::Answered(Some(OracleAnswer::Callee(answer))) => {
                self.declaration_of_callee_answer(&answer)
            }
            _ => None,
        }
    }

    pub fn set_pass(&mut self, pass: OraclePass) {
        self.pass = pass;
    }

    pub fn needed_queries(&self) -> Vec<Query> {
        self.needed.values().cloned().collect()
    }

    pub fn take_answers(&mut self, reply: OracleReply) {
        let keys: Vec<SiteKey> = self.needed.keys().copied().collect();

        for (key, answer) in keys.into_iter().zip(reply.answers) {
            self.answers.insert(key, answer);
        }

        self.oracle_info = format!("typescript {} at {}", reply.typescript, reply.from);

        self.needed.clear();
    }

    fn type_answer_of(&mut self, file: FileId, span: Span) -> Option<TypeAnswer> {
        let query = Query::Type {
            file: self.query_path_of(file),
            pos: span.start,
            end: span.end,
        };

        match self.answer_of_site(site_key_of(file, span, QueryKind::Type), query) {
            Lookup::Answered(Some(OracleAnswer::Type(answer))) => Some(answer),
            _ => None,
        }
    }

    fn answer_of_site(&mut self, key: SiteKey, query: Query) -> Lookup<OracleAnswer> {
        if self.pass == OraclePass::Off {
            return Lookup::Unanswered;
        }

        let replaying = self.pass == OraclePass::Recording && self.replays_type_answers;

        if let Some(answer) = self.answers.get(&key) {
            if self.pass == OraclePass::Recording && key.3 == QueryKind::Type && !replaying {
                return Lookup::Unanswered;
            }

            return Lookup::Answered(answer.clone());
        }

        match self.pass {
            OraclePass::Recording if replaying && key.3 == QueryKind::Type => {}
            OraclePass::Recording => {
                self.needed.entry(key).or_insert(query);
            }
            OraclePass::Answering => self.stats.count("oracle: miss"),
            OraclePass::Off => {}
        }

        Lookup::Unanswered
    }

    fn query_path_of(&self, file: FileId) -> String {
        self.project.file(file).path.to_string_lossy().into_owned()
    }

    fn declaration_of_callee_answer(&self, answer: &CalleeAnswer) -> Option<Declaration<'a>> {
        let Some(target) = self.project.file_by_path(Path::new(&answer.file)) else {
            return Some(Declaration::External);
        };
        let nodes = self.project.file(target).semantic.nodes();
        let mut best: Option<(Span, oxc_semantic::NodeId)> = None;

        for node in nodes.iter() {
            let kind = node.kind();

            if !is_declaration_kind(&kind) {
                continue;
            }

            let span = kind.span();

            if span.start < answer.start || span.end > answer.end {
                continue;
            }

            let better = match best {
                None => true,
                Some((current, _)) => {
                    span.start < current.start
                        || (span.start == current.start && span.size() > current.size())
                }
            };

            if better {
                best = Some((span, node.id()));
            }
        }

        best.and_then(|(_, node)| declaration_of_node(self.project, target, node))
    }
}

fn site_key_of(file: FileId, span: Span, kind: QueryKind) -> SiteKey {
    (file, span.start, span.end, kind)
}

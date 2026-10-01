//! Encodes an oxc program scope into `Olint.Model.Syntax` terms as Lean source text.
//!
//! A program scope is a function, the entry, plus the functions whose summaries a derivation
//! over it cites. It encodes as a `Program` holding every named function of the scope and the
//! entry `Node`: the entry function with its typed parameters and input dimensions, at the
//! entry's own site. Numeric literals encode as their exact IEEE-754 binary64 values. A
//! construct outside the model is an [`EncodeError::Unsupported`] naming its oxc node kind, so
//! its bound stays uncertified: the encoder never approximates.
//!
//! The encoder refuses what would make the encoded program mean something else than the source:
//!
//! - type assertions (`x as T`, `x!`, `<T>x`), which the model's §2.5 read check would take at
//!   their word; `x satisfies T` checks without asserting and encodes as `x`;
//! - an identifier the model would resolve to another binding than oxc does
//!   (`Encoder::resolve`): each reference must resolve to a binding declared inside the function
//!   being encoded, to the scope function it names, or, unresolved, to a global no scope
//!   function shadows;
//! - a function declaration outside a function body's top level, where sloppy code's Annex B
//!   semantics differ from the model's block-scoped one;
//! - an object literal `__proto__` key, which sets the new object's prototype (§13.2.5.5);
//! - `try` and `throw`: the model has no handler, so a TypeError or ReferenceError a run throws ends it, which is
//!   faithful only while no `try` could catch the error;
//! - a dimension over a free variable, since the encoded entry's scope holds no free variables
//!   and `Olint.check` rejects a dimension outside it.

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fmt;

use oxc_ast::ast::{
    ArrowFunctionBody, AssignmentTarget, BindingPattern, Class, ClassElement, Expression,
    ForStatementInit, ForStatementLeft, FormalParameters, Function, FunctionBody,
    MethodDefinitionKind, ObjectPropertyKind, PropertyKey, PropertyKind, SimpleAssignmentTarget,
    Statement, TSSignature, TSType, TSTypeName, TSTypeReference, VariableDeclaration,
    VariableDeclarationKind,
};
use oxc_ast::{AstKind, AstType};
use oxc_ast_visit::Visit;
use oxc_semantic::{NodeId, Semantic, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{
    AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator, UpdateOperator,
};
use oxc_syntax::GetNodeId;

/// A function of a program scope: a `Function` or `ArrowFunctionExpression` node in a file's
/// semantic.
#[derive(Clone, Copy)]
pub struct FunctionRef<'s, 'a> {
    pub semantic: &'s Semantic<'a>,
    pub node: NodeId,
}

/// The quantity an input dimension measures (`Olint.Model.Measure`): the length of a String in
/// UTF-16 code units or of an Array, or, for a Map or Set, the length `|D|` of its `[[MapData]]`
/// or `[[SetData]]` List, deleted entries included (`Olint.Model.Heap.lengthOf`). olint's
/// tracked size of a collection is that `|D|`: any `delete` or `clear` makes the size untracked
/// (G36), so a tracked size counts every entry ever added, as `|D|` does.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Measure {
    /// The length of the entry's `k`-th argument.
    Arg(usize),
    /// The length of a variable of the node's scope. The encoder refuses it
    /// ([`EncodeError::UnscopedDimension`]): the encoded scope holds no free variables.
    Var(String),
}

/// An input dimension: olint's dimension id and the quantity it measures.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dimension {
    pub id: u64,
    pub measure: Measure,
}

/// A program scope as Lean source text: `program` elaborates as an `Olint.Model.Program` and
/// `node` as an `Olint.Model.Node`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Encoding {
    pub program: String,
    pub node: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
    /// A construct outside the model, by oxc node kind, with the feature of it that falls
    /// outside when the kind itself is modelled.
    Unsupported {
        kind: AstType,
        detail: Option<&'static str>,
        span: Span,
    },
    /// A scope function node that is no function.
    NotAFunction { kind: AstType, span: Span },
    /// A cited function with no binding name to define it under.
    Anonymous { span: Span },
    /// Two scope functions under one name.
    DuplicateName { name: String },
    /// A dimension over a free variable, which the encoded entry's empty scope does not hold.
    UnscopedDimension { name: String },
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported {
                kind,
                detail: Some(detail),
                span,
            } => write!(
                f,
                "unsupported {kind:?} `{detail}` at {}..{}",
                span.start, span.end
            ),
            Self::Unsupported {
                kind,
                detail: None,
                span,
            } => write!(f, "unsupported {kind:?} at {}..{}", span.start, span.end),
            Self::NotAFunction { kind, span } => {
                write!(
                    f,
                    "{kind:?} at {}..{} is not a function",
                    span.start, span.end
                )
            }
            Self::Anonymous { span } => {
                write!(
                    f,
                    "cited function at {}..{} has no name",
                    span.start, span.end
                )
            }
            Self::DuplicateName { name } => write!(f, "two scope functions are named `{name}`"),
            Self::UnscopedDimension { name } => {
                write!(f, "a dimension measures the free variable `{name}`")
            }
        }
    }
}

impl std::error::Error for EncodeError {}

type Encoded = Result<String, EncodeError>;

/// Encodes the scope of `entry` with the functions its derivation cites and the input
/// dimensions its bound is costed over. Program definitions are sorted by name and dimensions
/// by id, so the text depends only on the scope.
pub fn encode_scope(
    entry: FunctionRef<'_, '_>,
    cited: &[FunctionRef<'_, '_>],
    dimensions: &[Dimension],
) -> Result<Encoding, EncodeError> {
    Scope::of(entry, cited)?.encode(dimensions)
}

/// A program scope: its entry and the functions its derivation cites, by the name the program
/// defines each under.
pub struct Scope<'s, 'a> {
    entry: FunctionRef<'s, 'a>,
    named: BTreeMap<String, ((usize, NodeId), SymbolId, FunctionRef<'s, 'a>)>,
    definitions: Definitions,
}

impl<'s, 'a> Scope<'s, 'a> {
    pub fn of(
        entry: FunctionRef<'s, 'a>,
        cited: &[FunctionRef<'s, 'a>],
    ) -> Result<Self, EncodeError> {
        let mut named = BTreeMap::new();

        if let Some((name, symbol)) = binding(entry)? {
            named.insert(name, (key(entry), symbol, entry));
        }

        for function in cited {
            let span = function.semantic.nodes().kind(function.node).span();
            let (name, symbol) = binding(*function)?.ok_or(EncodeError::Anonymous { span })?;

            match named.entry(name) {
                Entry::Vacant(slot) => {
                    slot.insert((key(*function), symbol, *function));
                }
                Entry::Occupied(slot) if slot.get().0 == key(*function) => {}
                Entry::Occupied(slot) => {
                    return Err(EncodeError::DuplicateName {
                        name: slot.key().clone(),
                    })
                }
            }
        }

        let definitions = named
            .iter()
            .map(|(name, (key, symbol, _))| (name.clone(), (key.0, *symbol)))
            .collect::<BTreeMap<_, _>>();

        Ok(Self {
            entry,
            named,
            definitions,
        })
    }

    /// The scope's `Program` and its entry `Node` over `dimensions`.
    pub fn encode(&self, dimensions: &[Dimension]) -> Result<Encoding, EncodeError> {
        let mut program = Vec::with_capacity(self.named.len());

        for (name, (_, _, function)) in &self.named {
            program.push(format!(
                "({}, {})",
                string(name),
                term(*function, &self.definitions)?
            ));
        }

        Ok(Encoding {
            program: format!("⟨{}⟩", list(program)),
            node: format!("⟨{}, .entry⟩", self.entry(dimensions)?),
        })
    }

    /// The `Entry` of the scope's entry function over `dimensions`, with no free variables.
    pub fn entry(&self, dimensions: &[Dimension]) -> Encoded {
        if let Some(Dimension {
            measure: Measure::Var(name),
            ..
        }) = dimensions
            .iter()
            .find(|dimension| matches!(dimension.measure, Measure::Var(_)))
        {
            return Err(EncodeError::UnscopedDimension { name: name.clone() });
        }

        let mut dimensions = dimensions.to_vec();

        dimensions.sort();

        // A Map or Set dimension measures `|D|`, deleted entries included (see `Measure`).
        let dims = list(dimensions.iter().map(|dimension| {
            let Measure::Arg(k) = &dimension.measure else {
                unreachable!("free-variable dimensions are refused above");
            };

            format!("({}, .arg {k})", dimension.id)
        }));

        Ok(format!(
            "⟨{}, [], {dims}⟩",
            term(self.entry, &self.definitions)?
        ))
    }

    /// The `Entry` of a function the scope cites, with no free variables and no dimensions.
    pub fn cited_entry(&self, function: FunctionRef<'s, 'a>) -> Encoded {
        Ok(format!("⟨{}, [], []⟩", term(function, &self.definitions)?))
    }

    /// The `Site` of the syntax at `span` in the entry function: `.entry` for the function itself, else the outermost
    /// statement or expression of its body spanning exactly `span`. `None` when no such syntax exists.
    pub fn site(&self, span: Span) -> Result<Option<String>, EncodeError> {
        if self.entry_span() == span {
            return Ok(Some(".entry".to_string()));
        }

        self.find(span, Encoder::statement_site, Encoder::expression_site)
    }

    /// The children `Olint.Rules.seqSites` or `Olint.Rules.branchSites` gives the syntax at `span`, each as `site`
    /// encodes it, in syntax order: the entry's body statements, a block's statements, the expression of an
    /// expression statement, an initialised declaration or a `return`, and an `if`'s or a conditional's test and
    /// branches. `None` for any other syntax, and for an arrow function whose body is an expression, whose one child,
    /// the `return` the model wraps the expression in, has no syntax of its own.
    pub fn children(&self, span: Span) -> Result<Option<Children>, EncodeError> {
        if self.entry_span() == span {
            let body = match self.entry.semantic.nodes().kind(self.entry.node) {
                AstKind::Function(function) => function.body.as_deref(),
                AstKind::ArrowFunctionExpression(arrow) => match &arrow.body {
                    ArrowFunctionBody::FunctionBody(body) => Some(&**body),
                    _ => None,
                },
                _ => None,
            };

            return body
                .map(|body| {
                    Ok(Children {
                        branch: false,
                        sites: self
                            .encoder()
                            .body_terms(body)?
                            .into_iter()
                            .map(|statement| format!(".stmt ({statement})"))
                            .collect(),
                        body: Some(body.span),
                    })
                })
                .transpose();
        }

        Ok(self
            .find(
                span,
                Encoder::statement_children,
                Encoder::expression_children,
            )?
            .flatten())
    }

    fn entry_span(&self) -> Span {
        self.entry.semantic.nodes().kind(self.entry.node).span()
    }

    fn encoder(&self) -> Encoder<'_, 'a> {
        Encoder {
            semantic: self.entry.semantic,
            root: self.entry.node,
            definitions: &self.definitions,
        }
    }

    /// Encodes, by `statement` or `expression`, the outermost statement or expression of the entry's body spanning
    /// exactly `span`. `None` when no such syntax exists.
    fn find<'e, T>(
        &'e self,
        span: Span,
        statement: fn(&Encoder<'e, 'a>, &Statement<'a>) -> Result<T, EncodeError>,
        expression: fn(&Encoder<'e, 'a>, &Expression<'a>) -> Result<T, EncodeError>,
    ) -> Result<Option<T>, EncodeError> {
        let mut finder = SiteFinder {
            encoder: self.encoder(),
            span,
            statement,
            expression,
            found: None,
        };

        match self.entry.semantic.nodes().kind(self.entry.node) {
            AstKind::Function(function) => {
                if let Some(body) = &function.body {
                    finder.visit_function_body(body);
                }
            }
            AstKind::ArrowFunctionExpression(arrow) => match &arrow.body {
                ArrowFunctionBody::FunctionBody(body) => finder.visit_function_body(body),
                body => {
                    if let Some(expression) = body.as_expression() {
                        finder.visit_expression(expression);
                    }
                }
            },
            kind => {
                return Err(EncodeError::NotAFunction {
                    kind: kind.ty(),
                    span: kind.span(),
                })
            }
        }

        finder.found.transpose()
    }
}

/// The children a composing rule's constructor checks one certificate at each of (`Scope::children`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Children {
    /// Whether the children are a branch's (`branch-join`) rather than a sequence's (`seq-max`).
    pub branch: bool,
    /// Each child's `Site`, in syntax order.
    pub sites: Vec<String>,
    /// For the entry, the span of its function body, which olint derives as a node of its own between the entry and
    /// its statements.
    pub body: Option<Span>,
}

/// Finds the outermost statement or expression spanning exactly `span` and encodes it by `statement` or `expression`.
struct SiteFinder<'s, 'a, T> {
    encoder: Encoder<'s, 'a>,
    span: Span,
    statement: fn(&Encoder<'s, 'a>, &Statement<'a>) -> Result<T, EncodeError>,
    expression: fn(&Encoder<'s, 'a>, &Expression<'a>) -> Result<T, EncodeError>,
    found: Option<Result<T, EncodeError>>,
}

impl<'a, T> Visit<'a> for SiteFinder<'_, 'a, T> {
    fn visit_statement(&mut self, statement: &Statement<'a>) {
        if self.found.is_some() {
            return;
        }

        if statement.span() == self.span {
            self.found = Some((self.statement)(&self.encoder, statement));

            return;
        }

        oxc_ast_visit::walk::walk_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &Expression<'a>) {
        if self.found.is_some() {
            return;
        }

        if expression.span() == self.span {
            self.found = Some((self.expression)(&self.encoder, expression));

            return;
        }

        oxc_ast_visit::walk::walk_expression(self, expression);
    }
}

/// A scope function's identity: its file's semantic and its node.
fn key(function: FunctionRef<'_, '_>) -> (usize, NodeId) {
    (
        std::ptr::from_ref(function.semantic) as usize,
        function.node,
    )
}

/// The scope functions by the name the program defines them under: their semantic and the
/// symbol of that name's binding.
type Definitions = BTreeMap<String, (usize, SymbolId)>;

/// The name a scope function is defined under and its binding's symbol: a declaration's own
/// name, or the declarator a function expression initializes.
fn binding(function: FunctionRef<'_, '_>) -> Result<Option<(String, SymbolId)>, EncodeError> {
    let nodes = function.semantic.nodes();

    match nodes.kind(function.node) {
        AstKind::Function(inner) if inner.is_declaration() => Ok(inner
            .id
            .as_ref()
            .map(|id| (id.name.to_string(), id.symbol_id()))),
        AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => {
            Ok(declarator_binding(function.semantic, function.node))
        }
        kind => Err(EncodeError::NotAFunction {
            kind: kind.ty(),
            span: kind.span(),
        }),
    }
}

/// The binding a `const f = …` style declarator gives a function expression.
fn declarator_binding(semantic: &Semantic<'_>, node: NodeId) -> Option<(String, SymbolId)> {
    let nodes = semantic.nodes();
    let mut parent = nodes.parent_id(node);

    loop {
        match nodes.kind(parent) {
            AstKind::ParenthesizedExpression(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSTypeAssertion(_) => parent = nodes.parent_id(parent),
            AstKind::VariableDeclarator(declarator) => {
                return declarator
                    .id
                    .get_binding_identifier()
                    .map(|id| (id.name.to_string(), id.symbol_id()))
            }
            _ => return None,
        }
    }
}

/// The `Func` term of a scope function.
fn term(function: FunctionRef<'_, '_>, definitions: &Definitions) -> Encoded {
    let encoder = Encoder {
        semantic: function.semantic,
        root: function.node,
        definitions,
    };

    match function.semantic.nodes().kind(function.node) {
        AstKind::Function(inner) => encoder.function(inner),
        AstKind::ArrowFunctionExpression(arrow) => encoder.arrow(arrow),
        kind => Err(EncodeError::NotAFunction {
            kind: kind.ty(),
            span: kind.span(),
        }),
    }
}

struct Encoder<'s, 'a> {
    semantic: &'s Semantic<'a>,
    /// The scope function being encoded.
    root: NodeId,
    definitions: &'s Definitions,
}

impl<'a> Encoder<'_, 'a> {
    fn unsupported(&self, node: &impl GetNodeId, detail: Option<&'static str>) -> EncodeError {
        let kind = self.semantic.nodes().kind(node.node_id());

        EncodeError::Unsupported {
            kind: kind.ty(),
            detail,
            span: kind.span(),
        }
    }

    fn reject<T>(&self, node: &impl GetNodeId, detail: &'static str) -> Result<T, EncodeError> {
        Err(self.unsupported(node, Some(detail)))
    }

    fn is_global(&self, reference: &oxc_ast::ast::IdentifierReference<'_>) -> bool {
        self.semantic
            .scoping()
            .get_reference(reference.reference_id())
            .symbol_id()
            .is_none()
    }

    /// The name of a reference, when the model resolves it to the binding oxc does: a binding
    /// declared inside the scope function being encoded (the model binds every such binding
    /// but a function or class expression's own name), the binding of the scope function it
    /// names, or, when oxc leaves it unresolved, a global that no scope function shadows.
    fn resolve(&self, reference: &oxc_ast::ast::IdentifierReference<'a>) -> Encoded {
        let scoping = self.semantic.scoping();
        let name = reference.name.as_str();
        let semantic = std::ptr::from_ref(self.semantic) as usize;
        let resolved = match scoping.get_reference(reference.reference_id()).symbol_id() {
            None => !self.definitions.contains_key(name),
            Some(symbol) if self.definitions.get(name) == Some(&(semantic, symbol)) => true,
            Some(symbol) => {
                let nodes = self.semantic.nodes();
                let declaration = scoping.symbol_declaration(symbol);
                let inside = declaration != self.root
                    && nodes.ancestor_ids(declaration).any(|id| id == self.root);
                let own_name = match nodes.kind(declaration) {
                    AstKind::Function(function) => !function.is_declaration(),
                    AstKind::Class(class) => !class.is_declaration(),
                    _ => false,
                };

                inside && !own_name
            }
        };

        match resolved {
            true => Ok(string(name)),
            false => self.reject(reference, "binding"),
        }
    }

    fn function(&self, function: &Function<'a>) -> Encoded {
        if let Some(detail) = flag(&[
            (function.r#async, "async"),
            (function.generator, "generator"),
            (function.declare, "declare"),
        ]) {
            return self.reject(function, detail);
        }

        let Some(body) = &function.body else {
            return self.reject(function, "no body");
        };

        self.func(&function.params, self.body(body)?, false)
    }

    fn arrow(&self, arrow: &oxc_ast::ast::ArrowFunctionExpression<'a>) -> Encoded {
        if arrow.r#async {
            return self.reject(arrow, "async");
        }

        let body = match &arrow.body {
            ArrowFunctionBody::FunctionBody(body) => self.body(body)?,
            body => {
                let expression = body
                    .as_expression()
                    .expect("an arrow body is a block or an expression");

                list([format!(".ret (some ({}))", self.expression(expression)?)])
            }
        };

        self.func(&arrow.params, body, true)
    }

    /// A function body's statements; its top-level function declarations, which strict and
    /// sloppy code instantiate alike, are the only ones the encoder accepts.
    fn body(&self, body: &FunctionBody<'a>) -> Encoded {
        Ok(list(self.body_terms(body)?))
    }

    /// The `Stmt` terms of a function body's statements.
    fn body_terms(&self, body: &FunctionBody<'a>) -> Result<Vec<String>, EncodeError> {
        if let Some(directive) = body.directives.first() {
            return Err(self.unsupported(directive, None));
        }

        body.statements
            .iter()
            .map(|statement| match statement {
                Statement::FunctionDeclaration(function) => {
                    let Some(id) = &function.id else {
                        return self.reject(statement, "no name");
                    };

                    Ok(format!(
                        ".funDecl {} ({})",
                        string(&id.name),
                        self.function(function)?
                    ))
                }
                statement => self.statement(statement),
            })
            .collect()
    }

    fn func(&self, params: &FormalParameters<'a>, body: String, arrow: bool) -> Encoded {
        if let Some(rest) = &params.rest {
            return Err(self.unsupported(&rest.rest, None));
        }

        let mut typed = Vec::with_capacity(params.items.len());

        for param in &params.items {
            let property = param.accessibility.is_some() || param.readonly || param.r#override;

            if let Some(detail) = flag(&[
                (!param.decorators.is_empty(), "decorator"),
                (property, "parameter property"),
                (param.optional, "optional"),
                (param.initializer.is_some(), "initializer"),
            ]) {
                return self.reject(param, detail);
            }

            let BindingPattern::BindingIdentifier(id) = &param.pattern else {
                return Err(self.unsupported(&param.pattern, None));
            };
            let ty = match &param.type_annotation {
                Some(annotation) => self.ty(&annotation.type_annotation)?,
                None => ".any".into(),
            };

            typed.push(format!("({}, {ty})", string(&id.name)));
        }

        Ok(format!(".mk {} {body} {arrow}", list(typed)))
    }

    fn class(&self, class: &Class<'a>) -> Encoded {
        if let Some(detail) = flag(&[
            (!class.decorators.is_empty(), "decorator"),
            (class.heritage.is_some(), "extends"),
            (class.r#abstract, "abstract"),
            (class.declare, "declare"),
        ]) {
            return self.reject(class, detail);
        }

        let mut constructor = "none".to_string();
        let mut methods = Vec::new();

        for element in &class.body.body {
            let ClassElement::MethodDefinition(method) = element else {
                return Err(self.unsupported(element, None));
            };
            let detail = match method.kind {
                _ if !method.decorators.is_empty() => Some("decorator"),
                _ if method.r#static => Some("static"),
                _ if method.computed || method.optional => Some("key"),
                MethodDefinitionKind::Get => Some("get"),
                MethodDefinitionKind::Set => Some("set"),
                MethodDefinitionKind::Constructor | MethodDefinitionKind::Method => None,
            };

            if let Some(detail) = detail {
                return self.reject(element, detail);
            }

            let term = self.function(&method.value)?;

            match method.kind {
                MethodDefinitionKind::Constructor => constructor = format!("(some ({term}))"),
                _ => {
                    let PropertyKey::StaticIdentifier(name) = &method.key else {
                        return self.reject(element, "key");
                    };

                    methods.push(format!("({}, {term})", string(&name.name)));
                }
            }
        }

        Ok(format!(".mk {constructor} {}", list(methods)))
    }

    /// The children `Scope::children` gives a statement that encodes.
    fn statement_children(
        &self,
        statement: &Statement<'a>,
    ) -> Result<Option<Children>, EncodeError> {
        self.statement(statement)?;

        let sequence = |sites: Vec<String>| {
            Some(Children {
                branch: false,
                sites,
                body: None,
            })
        };

        Ok(match statement {
            Statement::ExpressionStatement(inner) => {
                sequence(vec![self.expression_site(&inner.expression)?])
            }
            Statement::VariableDeclaration(declaration) => match self.declared(declaration)?.2 {
                Some(init) => sequence(vec![self.expression_site(init)?]),
                None => None,
            },
            Statement::ReturnStatement(inner) => match &inner.argument {
                Some(argument) => sequence(vec![self.expression_site(argument)?]),
                None => None,
            },
            Statement::BlockStatement(block) => sequence(
                block
                    .body
                    .iter()
                    .map(|statement| self.statement_site(statement))
                    .collect::<Result<_, _>>()?,
            ),
            Statement::IfStatement(inner) => {
                let mut sites = vec![
                    self.expression_site(&inner.test)?,
                    self.statement_site(&inner.consequent)?,
                ];

                if let Some(alternate) = &inner.alternate {
                    sites.push(self.statement_site(alternate)?);
                }

                Some(Children {
                    branch: true,
                    sites,
                    body: None,
                })
            }
            _ => None,
        })
    }

    /// The children `Scope::children` gives an expression that encodes: a conditional's test and branches, through
    /// the parentheses and `satisfies` the encoding drops.
    fn expression_children(
        &self,
        expression: &Expression<'a>,
    ) -> Result<Option<Children>, EncodeError> {
        match expression {
            Expression::ParenthesizedExpression(inner) => {
                self.expression_children(&inner.expression)
            }
            Expression::TSSatisfiesExpression(inner) => self.expression_children(&inner.expression),
            Expression::ConditionalExpression(conditional) => Ok(Some(Children {
                branch: true,
                sites: [
                    &conditional.test,
                    &conditional.consequent,
                    &conditional.alternate,
                ]
                .into_iter()
                .map(|expression| self.expression_site(expression))
                .collect::<Result<_, _>>()?,
                body: None,
            })),
            _ => {
                self.expression(expression)?;

                Ok(None)
            }
        }
    }

    fn statement_site(&self, statement: &Statement<'a>) -> Encoded {
        Ok(format!(".stmt ({})", self.statement(statement)?))
    }

    fn expression_site(&self, expression: &Expression<'a>) -> Encoded {
        Ok(format!(".expr ({})", self.expression(expression)?))
    }

    fn statements(&self, statements: &[Statement<'a>]) -> Encoded {
        let terms = statements
            .iter()
            .map(|statement| self.statement(statement))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(list(terms))
    }

    fn optional_statement(&self, statement: Option<&Statement<'a>>) -> Encoded {
        statement.map_or(Ok("none".into()), |statement| {
            Ok(format!("(some ({}))", self.statement(statement)?))
        })
    }

    fn optional_expression(&self, expression: Option<&Expression<'a>>) -> Encoded {
        expression.map_or(Ok("none".into()), |expression| {
            Ok(format!("(some ({}))", self.expression(expression)?))
        })
    }

    fn statement(&self, statement: &Statement<'a>) -> Encoded {
        Ok(match statement {
            Statement::ExpressionStatement(inner) => {
                format!(".expr ({})", self.expression(&inner.expression)?)
            }
            Statement::VariableDeclaration(declaration) => self.declaration(declaration)?,
            Statement::BlockStatement(block) => format!(".block {}", self.statements(&block.body)?),
            Statement::EmptyStatement(_) => ".block []".into(),
            Statement::IfStatement(inner) => format!(
                ".ite ({}) ({}) {}",
                self.expression(&inner.test)?,
                self.statement(&inner.consequent)?,
                self.optional_statement(inner.alternate.as_ref())?
            ),
            Statement::ForStatement(inner) => {
                let init = match &inner.init {
                    None => "none".into(),
                    Some(ForStatementInit::VariableDeclaration(declaration)) => {
                        format!("(some ({}))", self.declaration(declaration)?)
                    }
                    Some(init) => {
                        let expression = init
                            .as_expression()
                            .expect("a for init is a declaration or an expression");

                        format!("(some (.expr ({})))", self.expression(expression)?)
                    }
                };

                format!(
                    ".forLoop {init} {} {} ({})",
                    self.optional_expression(inner.test.as_ref())?,
                    self.optional_expression(inner.update.as_ref())?,
                    self.statement(&inner.body)?
                )
            }
            Statement::ForOfStatement(inner) => {
                if inner.r#await {
                    return self.reject(statement, "await");
                }

                self.iteration("forOf", statement, &inner.left, &inner.right, &inner.body)?
            }
            Statement::ForInStatement(inner) => {
                self.iteration("forIn", statement, &inner.left, &inner.right, &inner.body)?
            }
            Statement::WhileStatement(inner) => format!(
                ".«while» ({}) ({})",
                self.expression(&inner.test)?,
                self.statement(&inner.body)?
            ),
            Statement::DoWhileStatement(inner) => format!(
                ".doWhile ({}) ({})",
                self.statement(&inner.body)?,
                self.expression(&inner.test)?
            ),
            Statement::ReturnStatement(inner) => {
                format!(
                    ".ret {}",
                    self.optional_expression(inner.argument.as_ref())?
                )
            }
            Statement::BreakStatement(inner) if inner.label.is_none() => ".brk".into(),
            Statement::ContinueStatement(inner) if inner.label.is_none() => ".cont".into(),
            Statement::BreakStatement(_) | Statement::ContinueStatement(_) => {
                return self.reject(statement, "label")
            }
            Statement::FunctionDeclaration(_) => return self.reject(statement, "block function"),
            Statement::ClassDeclaration(class) => {
                let Some(id) = &class.id else {
                    return self.reject(statement, "no name");
                };

                format!(".classDecl {} ({})", string(&id.name), self.class(class)?)
            }
            _ => return Err(self.unsupported(statement, None)),
        })
    }

    /// `.decl` for a declaration of one identifier, with its declared type (`.any` without an
    /// annotation).
    fn declaration(&self, declaration: &VariableDeclaration<'a>) -> Encoded {
        let (kind, name, init) = self.declared(declaration)?;
        let [declarator] = declaration.declarations.as_slice() else {
            unreachable!("declared checks for one declarator");
        };
        let ty = match &declarator.type_annotation {
            Some(annotation) => self.ty(&annotation.type_annotation)?,
            None => ".any".into(),
        };

        Ok(format!(
            ".decl {kind} {} ({ty}) {}",
            string(&name),
            self.optional_expression(init)?
        ))
    }

    fn declared<'d>(
        &self,
        declaration: &'d VariableDeclaration<'a>,
    ) -> Result<(&'static str, String, Option<&'d Expression<'a>>), EncodeError> {
        let kind = match declaration.kind {
            VariableDeclarationKind::Var => ".var",
            VariableDeclarationKind::Let => ".«let»",
            VariableDeclarationKind::Const => ".«const»",
            VariableDeclarationKind::Using | VariableDeclarationKind::AwaitUsing => {
                return self.reject(declaration, "using")
            }
        };

        if declaration.declare {
            return self.reject(declaration, "declare");
        }

        let [declarator] = declaration.declarations.as_slice() else {
            return self.reject(declaration, "several declarators");
        };
        let Some(id) = declarator.id.get_binding_identifier() else {
            return Err(self.unsupported(&declarator.id, None));
        };

        Ok((kind, id.name.to_string(), declarator.init.as_ref()))
    }

    /// `.forOf` and `.forIn` over a fresh `let` or `const` binding of one identifier.
    fn iteration(
        &self,
        constructor: &str,
        statement: &Statement<'a>,
        left: &ForStatementLeft<'a>,
        right: &Expression<'a>,
        body: &Statement<'a>,
    ) -> Encoded {
        let ForStatementLeft::VariableDeclaration(declaration) = left else {
            return self.reject(statement, "assignment target");
        };
        let (kind, name, init) = self.declared(declaration)?;

        if kind == ".var" || init.is_some() {
            return self.reject(&**declaration, "binding");
        }

        Ok(format!(
            ".{constructor} {} ({}) ({})",
            string(&name),
            self.expression(right)?,
            self.statement(body)?
        ))
    }

    fn expressions<'e>(&self, expressions: impl Iterator<Item = &'e Expression<'a>>) -> Encoded
    where
        'a: 'e,
    {
        let terms = expressions
            .map(|expression| self.expression(expression))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(list(terms))
    }

    fn arguments(&self, arguments: &[oxc_ast::ast::Argument<'a>]) -> Encoded {
        let mut expressions = Vec::with_capacity(arguments.len());

        for argument in arguments {
            let Some(expression) = argument.as_expression() else {
                return Err(self.unsupported(argument, None));
            };

            expressions.push(expression);
        }

        self.expressions(expressions.into_iter())
    }

    fn expression(&self, expression: &Expression<'a>) -> Encoded {
        Ok(match expression {
            Expression::ParenthesizedExpression(inner) => self.expression(&inner.expression)?,
            Expression::TSSatisfiesExpression(inner) => self.expression(&inner.expression)?,
            Expression::BooleanLiteral(literal) => format!(".lit (.bool {})", literal.value),
            Expression::NullLiteral(_) => ".lit .null".into(),
            Expression::NumericLiteral(literal) => format!(".lit (.num {})", number(literal.value)),
            Expression::StringLiteral(literal) => {
                if literal.lone_surrogates {
                    return self.reject(expression, "lone surrogate");
                }

                format!(".lit (.str {})", string(&literal.value))
            }
            Expression::Identifier(reference) => {
                match reference.name == "undefined" && self.is_global(reference) {
                    true => ".lit .undefined".into(),
                    false => format!(".ident {}", self.resolve(reference)?),
                }
            }
            Expression::ThisExpression(_) => ".«this»".into(),
            Expression::UnaryExpression(unary) => {
                let op = match unary.operator {
                    UnaryOperator::LogicalNot => ".not",
                    UnaryOperator::UnaryNegation => ".neg",
                    UnaryOperator::Typeof => ".typeof",
                    UnaryOperator::BitwiseNot => ".bitNot",
                    operator => return self.reject(expression, operator.as_str()),
                };

                format!(".unary {op} ({})", self.expression(&unary.argument)?)
            }
            Expression::BinaryExpression(binary) => {
                let Some(op) = binary_operator(binary.operator) else {
                    return self.reject(expression, binary.operator.as_str());
                };

                self.binary(op, &binary.left, &binary.right)?
            }
            Expression::LogicalExpression(logical) => self.binary(
                logical_operator(logical.operator),
                &logical.left,
                &logical.right,
            )?,
            Expression::ConditionalExpression(conditional) => format!(
                ".cond ({}) ({}) ({})",
                self.expression(&conditional.test)?,
                self.expression(&conditional.consequent)?,
                self.expression(&conditional.alternate)?
            ),
            Expression::AssignmentExpression(assignment) => {
                let operator = assignment.operator;
                let op = match operator {
                    AssignmentOperator::Assign => None,
                    _ => match (
                        operator.to_binary_operator().and_then(binary_operator),
                        operator.to_logical_operator(),
                    ) {
                        (Some(op), _) => Some(op),
                        (None, Some(logical)) => Some(logical_operator(logical)),
                        (None, None) => return self.reject(expression, operator.as_str()),
                    },
                };

                self.assignment(op, &assignment.left, &assignment.right)?
            }
            Expression::UpdateExpression(update) => {
                let inc = update.operator == UpdateOperator::Increment;
                let pre = update.prefix;

                match self.target(&update.argument)? {
                    Target::Identifier(name) => format!(".update {inc} {pre} {name}"),
                    Target::Member(object, key) => {
                        format!(".updateIndex {inc} {pre} ({object}) ({key})")
                    }
                }
            }
            Expression::StaticMemberExpression(member) if !member.optional => format!(
                ".member ({}) {}",
                self.expression(&member.object)?,
                string(&member.property.name)
            ),
            Expression::ComputedMemberExpression(member) if !member.optional => format!(
                ".index ({}) ({})",
                self.expression(&member.object)?,
                self.expression(&member.expression)?
            ),
            Expression::CallExpression(call) if !call.optional => format!(
                ".call ({}) {}",
                self.expression(&call.callee)?,
                self.arguments(&call.arguments)?
            ),
            Expression::NewExpression(new) => format!(
                ".new ({}) {}",
                self.expression(&new.callee)?,
                self.arguments(&new.arguments)?
            ),
            Expression::FunctionExpression(function) => {
                format!(".func ({})", self.function(function)?)
            }
            Expression::ArrowFunctionExpression(arrow) => format!(".func ({})", self.arrow(arrow)?),
            Expression::ClassExpression(class) => format!(".klass ({})", self.class(class)?),
            Expression::ArrayExpression(array) => {
                let mut elements = Vec::with_capacity(array.elements.len());

                for element in &array.elements {
                    let Some(expression) = element.as_expression() else {
                        return Err(self.unsupported(element, None));
                    };

                    elements.push(expression);
                }

                format!(".array {}", self.expressions(elements.into_iter())?)
            }
            Expression::ObjectExpression(object) => self.object(object)?,
            Expression::RegExpLiteral(literal) => format!(
                ".regex {} {}",
                string(&literal.regex.pattern.text),
                string(&literal.regex.flags.to_string())
            ),
            Expression::StaticMemberExpression(_)
            | Expression::ComputedMemberExpression(_)
            | Expression::CallExpression(_) => return self.reject(expression, "optional"),
            _ => return Err(self.unsupported(expression, None)),
        })
    }

    fn binary(&self, op: &str, left: &Expression<'a>, right: &Expression<'a>) -> Encoded {
        Ok(format!(
            ".binary {op} ({}) ({})",
            self.expression(left)?,
            self.expression(right)?
        ))
    }

    /// `x = e`, `o[k] = e`, and with a compound operator `op`, `x op= e` and `o[k] op= e`.
    fn assignment(
        &self,
        op: Option<&str>,
        target: &AssignmentTarget<'a>,
        value: &Expression<'a>,
    ) -> Encoded {
        let Some(simple) = target.as_simple_assignment_target() else {
            return Err(self.unsupported(target, None));
        };
        let target = self.target(simple)?;
        let value = self.expression(value)?;

        Ok(match (op, target) {
            (None, Target::Identifier(name)) => format!(".assign {name} ({value})"),
            (None, Target::Member(object, key)) => {
                format!(".assignIndex ({object}) ({key}) ({value})")
            }
            (Some(op), Target::Identifier(name)) => format!(".assignOp {op} {name} ({value})"),
            (Some(op), Target::Member(object, key)) => {
                format!(".assignOpIndex {op} ({object}) ({key}) ({value})")
            }
        })
    }

    /// An identifier or member target; `o.p` keys as the string literal `"p"`.
    fn target(&self, target: &SimpleAssignmentTarget<'a>) -> Result<Target, EncodeError> {
        Ok(match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                Target::Identifier(self.resolve(reference)?)
            }
            SimpleAssignmentTarget::StaticMemberExpression(member) => Target::Member(
                self.expression(&member.object)?,
                format!(".lit (.str {})", string(&member.property.name)),
            ),
            SimpleAssignmentTarget::ComputedMemberExpression(member) => Target::Member(
                self.expression(&member.object)?,
                self.expression(&member.expression)?,
            ),
            _ => return Err(self.unsupported(target, None)),
        })
    }

    fn object(&self, object: &oxc_ast::ast::ObjectExpression<'a>) -> Encoded {
        let mut properties = Vec::with_capacity(object.properties.len());

        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(inner) = property else {
                return Err(self.unsupported(property, None));
            };

            if inner.kind != PropertyKind::Init {
                return self.reject(property, "accessor");
            }

            let name = match &inner.key {
                PropertyKey::StaticIdentifier(name) if !inner.computed => name.name.as_str(),
                PropertyKey::StringLiteral(name) if !inner.computed && !name.lone_surrogates => {
                    name.value.as_str()
                }
                _ => return self.reject(property, "key"),
            };

            if name == "__proto__" {
                return self.reject(property, "__proto__");
            }

            properties.push(format!(
                "({}, {})",
                string(name),
                self.expression(&inner.value)?
            ));
        }

        Ok(format!(".object {}", list(properties)))
    }

    fn ty(&self, ty: &TSType<'a>) -> Encoded {
        Ok(match ty {
            TSType::TSAnyKeyword(_) | TSType::TSUnknownKeyword(_) => ".any".into(),
            TSType::TSUndefinedKeyword(_) => ".undefined".into(),
            TSType::TSNullKeyword(_) => ".null".into(),
            TSType::TSBooleanKeyword(_) => ".boolean".into(),
            TSType::TSNumberKeyword(_) => ".number".into(),
            TSType::TSStringKeyword(_) => ".string".into(),
            TSType::TSFunctionType(_) => ".func".into(),
            TSType::TSParenthesizedType(inner) => self.ty(&inner.type_annotation)?,
            TSType::TSArrayType(array) => format!(".array ({})", self.ty(&array.element_type)?),
            TSType::TSTypeReference(reference) => self.reference(ty, reference)?,
            TSType::TSTypeLiteral(literal) => {
                let mut fields = Vec::with_capacity(literal.members.len());

                for member in &literal.members {
                    let TSSignature::TSPropertySignature(signature) = member else {
                        return Err(self.unsupported(member, None));
                    };
                    let name = match &signature.key {
                        _ if signature.computed || signature.optional => None,
                        PropertyKey::StaticIdentifier(name) => Some(name.name.as_str()),
                        PropertyKey::StringLiteral(name) if !name.lone_surrogates => {
                            Some(name.value.as_str())
                        }
                        _ => None,
                    };
                    let (Some(name), Some(annotation)) = (name, &signature.type_annotation) else {
                        return self.reject(member, "property");
                    };

                    fields.push(format!(
                        "({}, {})",
                        string(name),
                        self.ty(&annotation.type_annotation)?
                    ));
                }

                format!(".object {}", list(fields))
            }
            _ => return Err(self.unsupported(ty, None)),
        })
    }

    /// `Array<T>`, `Map<K, V>` and `Set<T>` naming the global built-ins.
    fn reference(&self, ty: &TSType<'a>, reference: &TSTypeReference<'a>) -> Encoded {
        let TSTypeName::IdentifierReference(name) = &reference.type_name else {
            return Err(self.unsupported(ty, None));
        };

        if !self.is_global(name) {
            return self.reject(ty, "local type");
        }

        let arguments = reference
            .type_arguments
            .as_ref()
            .map_or(&[][..], |arguments| arguments.params.as_slice());
        let terms = arguments
            .iter()
            .map(|argument| Ok(format!("({})", self.ty(argument)?)))
            .collect::<Result<Vec<_>, EncodeError>>()?;

        Ok(match (name.name.as_str(), terms.as_slice()) {
            ("Array", [element]) => format!(".array {element}"),
            ("Set", [element]) => format!(".set {element}"),
            ("Map", [key, value]) => format!(".map {key} {value}"),
            _ => return self.reject(ty, "type reference"),
        })
    }
}

/// An encoded assignment or update target.
enum Target {
    /// A Lean string literal naming the variable.
    Identifier(String),
    /// The encoded object and key expressions.
    Member(String, String),
}

/// The Lean `BinOp` of a binary operator the model covers.
fn binary_operator(operator: BinaryOperator) -> Option<&'static str> {
    Some(match operator {
        BinaryOperator::Addition => ".add",
        BinaryOperator::Subtraction => ".sub",
        BinaryOperator::Multiplication => ".mul",
        BinaryOperator::Division => ".div",
        BinaryOperator::Remainder => ".mod",
        BinaryOperator::LessThan => ".lt",
        BinaryOperator::LessEqualThan => ".le",
        BinaryOperator::GreaterThan => ".gt",
        BinaryOperator::GreaterEqualThan => ".ge",
        BinaryOperator::StrictEquality => ".strictEq",
        BinaryOperator::StrictInequality => ".strictNe",
        BinaryOperator::BitwiseAnd => ".band",
        BinaryOperator::BitwiseOR => ".bor",
        BinaryOperator::BitwiseXOR => ".bxor",
        BinaryOperator::ShiftLeft => ".shl",
        BinaryOperator::ShiftRight => ".shr",
        BinaryOperator::ShiftRightZeroFill => ".ushr",
        _ => return None,
    })
}

/// The Lean `BinOp` of a logical operator.
fn logical_operator(operator: LogicalOperator) -> &'static str {
    match operator {
        LogicalOperator::And => ".and",
        LogicalOperator::Or => ".or",
        LogicalOperator::Coalesce => ".nullish",
    }
}

/// A Lean `Double` term for a binary64 value: a natural-number literal for an integer up to
/// `2^53`, else `.fin neg m e` with odd `m`, the exact value `(-1)^neg · m · 2^e`.
pub fn number(value: f64) -> String {
    if value.is_nan() {
        return ".nan".into();
    }

    if value.is_infinite() {
        return format!("(.inf {})", value < 0.0);
    }

    if value >= 0.0 && value.fract() == 0.0 && value <= 9_007_199_254_740_992.0 {
        return format!("{}", value as u64);
    }

    let bits = value.to_bits();
    let negative = bits >> 63 == 1;
    let biased = ((bits >> 52) & 0x7ff) as i64;
    let fraction = bits & ((1 << 52) - 1);
    let (mut mantissa, mut exponent) = match biased {
        0 => (fraction, -1074),
        _ => (fraction | 1 << 52, biased - 1075),
    };

    if mantissa == 0 {
        return format!("(.fin {negative} 0 (-1074))");
    }

    let zeros = mantissa.trailing_zeros();

    mantissa >>= zeros;
    exponent += i64::from(zeros);

    match exponent < 0 {
        true => format!("(.fin {negative} {mantissa} ({exponent}))"),
        false => format!("(.fin {negative} {mantissa} {exponent})"),
    }
}

/// The detail of the first set flag.
fn flag(flags: &[(bool, &'static str)]) -> Option<&'static str> {
    flags
        .iter()
        .find(|(set, _)| *set)
        .map(|(_, detail)| *detail)
}

/// A Lean list literal of already encoded terms.
fn list(terms: impl IntoIterator<Item = String>) -> String {
    let terms = terms.into_iter().collect::<Vec<_>>();

    format!("[{}]", terms.join(", "))
}

/// A Lean string literal.
pub fn string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);

    out.push('"');

    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            character if character.is_control() => {
                for unit in character.encode_utf16(&mut [0; 2]) {
                    out.push_str(&format!("\\u{unit:04X}"));
                }
            }
            character => out.push(character),
        }
    }

    out.push('"');

    out
}

#[cfg(test)]
#[path = "lean_syntax.test.rs"]
mod tests;

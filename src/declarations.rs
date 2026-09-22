use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use oxc_ast::ast::{
    ArrowFunctionExpression, BindingPattern, Class, ClassElement, ExportDefaultDeclarationKind,
    Expression, FormalParameter, FormalParameterRest, FormalParameters, Function,
    IdentifierReference, MethodDefinitionKind, ObjectProperty, PropertyKey, Statement,
    TSEnumDeclaration, TSEnumMember, TSInterfaceDeclaration, TSModuleReference, TSSignature,
    TSTypeAliasDeclaration, TSTypeName, TSTypeParameter, VariableDeclarationKind,
    VariableDeclarator,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::module_record::{
    ExportEntry, ExportExportName, ExportImportName, ExportLocalName, ImportImportName,
    ModuleRecord,
};
use oxc_syntax::scope::ScopeId;
use oxc_syntax::symbol::SymbolId;

use crate::project::{FileId, Project, Resolved, SourceFile};
use crate::syntax::unwrap;
use crate::tables::{MUTATORS, REFLECTIVE_WRITES};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Binding {
    Symbol { file: FileId, symbol: SymbolId },
}

#[derive(Clone, Copy, Debug)]
pub enum Declaration<'a> {
    Function {
        file: FileId,
        function: FunctionNode<'a>,
    },
    Variable {
        file: FileId,
        declarator: &'a VariableDeclarator<'a>,
        constant: bool,
    },
    Parameter {
        file: FileId,
        parameter: ParameterNode<'a>,
        function: FunctionNode<'a>,
    },
    Class {
        file: FileId,
        class: &'a Class<'a>,
    },
    Member {
        file: FileId,
        class: &'a Class<'a>,
        element: &'a ClassElement<'a>,
    },
    Enum {
        file: FileId,
        declaration: &'a TSEnumDeclaration<'a>,
    },
    EnumMember {
        file: FileId,
        member: &'a TSEnumMember<'a>,
    },
    Interface {
        file: FileId,
        declaration: &'a TSInterfaceDeclaration<'a>,
    },
    TypeAlias {
        file: FileId,
        declaration: &'a TSTypeAliasDeclaration<'a>,
    },
    TypeParameter {
        file: FileId,
        parameter: &'a TSTypeParameter<'a>,
    },
    Namespace {
        file: FileId,
    },
    Property {
        file: FileId,
        property: &'a ObjectProperty<'a>,
    },
    External,
}

#[derive(Clone, Copy, Debug)]
pub enum FunctionNode<'a> {
    Function(&'a Function<'a>),
    Arrow(&'a ArrowFunctionExpression<'a>),
    Construction(&'a Class<'a>),
}

impl FunctionNode<'_> {
    pub fn node_id(self) -> NodeId {
        match self {
            FunctionNode::Function(function) => function.node_id(),
            FunctionNode::Arrow(arrow) => arrow.node_id(),
            FunctionNode::Construction(class) => class.node_id(),
        }
    }
}

impl PartialEq for FunctionNode<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (FunctionNode::Function(left), FunctionNode::Function(right)) => {
                std::ptr::eq(*left, *right)
            }
            (FunctionNode::Arrow(left), FunctionNode::Arrow(right)) => std::ptr::eq(*left, *right),
            (FunctionNode::Construction(left), FunctionNode::Construction(right)) => {
                std::ptr::eq(*left, *right)
            }
            _ => false,
        }
    }
}

impl Eq for FunctionNode<'_> {}

impl Hash for FunctionNode<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            FunctionNode::Function(function) => std::ptr::hash(*function, state),
            FunctionNode::Arrow(arrow) => std::ptr::hash(*arrow, state),
            FunctionNode::Construction(class) => std::ptr::hash(*class, state),
        }
    }
}

pub fn parameters_of<'a>(function: FunctionNode<'a>) -> Option<&'a FormalParameters<'a>> {
    match function {
        FunctionNode::Function(inner) => Some(&inner.params),
        FunctionNode::Arrow(inner) => Some(&inner.params),
        FunctionNode::Construction(_) => None,
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ParameterNode<'a> {
    Formal(&'a FormalParameter<'a>),
    Rest(&'a FormalParameterRest<'a>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId {
    pub file: FileId,
    pub node: NodeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum SurfaceTarget {
    Node(FileId, NodeId),
    Module(FileId),
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TargetSet {
    pub known: Vec<FunctionId>,
    pub open: bool,
}

impl Default for TargetSet {
    fn default() -> Self {
        Self {
            known: Vec::new(),
            open: true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    Symbol(FileId, SymbolId),
    OpenSymbol(FileId, SymbolId),
    Node(FileId, NodeId),
    Namespace(FileId),
    External,
}

type GlobalBindings = HashMap<(FileId, String), Option<(FileId, SymbolId)>>;
type CallableBindings = HashMap<(FileId, NodeId), (Option<Target>, bool)>;
type BlockFunctions = HashMap<(ScopeId, String), Vec<NodeId>>;
type DeclarationSpans = Vec<(u32, u32, NodeId)>;
type SurfaceReference = (FileId, NodeId, bool);

#[derive(Default)]
struct Importers {
    bindings: HashMap<Binding, Vec<Binding>>,
    namespaces: HashMap<FileId, Vec<Binding>>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ResolutionStats {
    pub symbol_visits: usize,
    pub helper_visits: usize,
    pub write_reference_visits: usize,
    pub stack_peak: usize,
    pub span_index_visits: usize,
    pub construction_visits: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct ConstructionLineage {
    constructor: bool,
    initialized: bool,
}

enum ResolutionStep<'a> {
    Symbol(FileId, SymbolId),
    Finish(FileId, SymbolId, usize),
    Members(Vec<&'a str>),
    Open,
}

pub struct Declarations<'a> {
    followed: RefCell<HashMap<(FileId, String), Option<Target>>>,
    globals: RefCell<GlobalBindings>,
    resolving: RefCell<HashSet<(FileId, SymbolId)>>,
    callable: RefCell<CallableBindings>,
    symbols: RefCell<HashMap<(FileId, SymbolId), (Target, bool)>>,
    write_free: RefCell<HashMap<Binding, bool>>,
    surface_writes: RefCell<HashMap<Binding, Vec<(FileId, NodeId)>>>,
    surface_references: RefCell<HashMap<Binding, Vec<SurfaceReference>>>,
    importers: RefCell<Option<Importers>>,
    block_functions: RefCell<HashMap<FileId, BlockFunctions>>,
    declaration_spans: RefCell<HashMap<FileId, DeclarationSpans>>,
    assignments: RefCell<HashMap<FileId, Option<NodeId>>>,
    constructions: RefCell<HashMap<(FileId, NodeId), ConstructionLineage>>,
    resolution_epoch: Cell<usize>,
    resolution_stats: Cell<ResolutionStats>,
    module_records: Vec<&'a ModuleRecord<'a>>,
}

impl<'a> Declarations<'a> {
    pub fn new(project: &Project<'a>) -> Self {
        Declarations {
            followed: RefCell::new(HashMap::new()),
            globals: RefCell::new(HashMap::new()),
            resolving: RefCell::new(HashSet::new()),
            callable: RefCell::new(HashMap::new()),
            symbols: RefCell::new(HashMap::new()),
            write_free: RefCell::new(HashMap::new()),
            surface_writes: RefCell::new(HashMap::new()),
            surface_references: RefCell::new(HashMap::new()),
            importers: RefCell::new(None),
            block_functions: RefCell::new(HashMap::new()),
            declaration_spans: RefCell::new(HashMap::new()),
            assignments: RefCell::new(HashMap::new()),
            constructions: RefCell::new(HashMap::new()),
            resolution_epoch: Cell::new(0),
            resolution_stats: Cell::new(ResolutionStats::default()),
            module_records: project
                .files
                .iter()
                .map(|file| file.module_record)
                .collect(),
        }
    }

    pub(crate) fn callable_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> (Option<Declaration<'a>>, bool) {
        let key_of = |file, reference: &IdentifierReference<'a>| {
            self.symbol_of_reference(project, file, reference)
                .map(|(file, symbol)| {
                    (
                        file,
                        project
                            .file(file)
                            .semantic
                            .scoping()
                            .symbol_declaration(symbol),
                    )
                })
                .unwrap_or((file, reference.node_id()))
        };
        let key = key_of(file, reference);

        if let Some(cached) = self.callable.borrow().get(&key) {
            return (
                cached
                    .0
                    .and_then(|target| declaration_of_target(project, target)),
                cached.1,
            );
        }

        let mut current = (file, reference);
        let mut seen = HashSet::new();
        let mut path = Vec::new();
        let mut result = loop {
            let (file, reference) = current;
            let key = key_of(file, reference);

            if let Some((declaration, exact)) = self.callable.borrow().get(&key) {
                break (
                    declaration.and_then(|target| declaration_of_target(project, target)),
                    *exact,
                );
            }

            let declaration = self.of_reference(project, file, reference);
            let mut closed = true;

            if let Some(Binding::Symbol { file, symbol }) =
                self.binding_of_reference(project, file, reference)
            {
                if !seen.insert((file, symbol)) {
                    break (None, false);
                }

                closed &= self.is_write_free(project, Binding::Symbol { file, symbol })
                    && self.runtime_declarations_of(project, file, symbol).1;
            }

            path.push((key, closed));

            if !closed {
                break (None, false);
            }

            if self
                .symbol_of_reference(project, file, reference)
                .is_some_and(|key| {
                    self.symbols
                        .borrow()
                        .get(&key)
                        .is_some_and(|(_, open)| *open)
                })
            {
                if let Some((_, closed)) = path.last_mut() {
                    *closed = false;
                }
            }

            match declaration {
                Some(Declaration::Variable { declarator, .. })
                    if !matches!(declarator.id, BindingPattern::BindingIdentifier(_)) =>
                {
                    break (None, false)
                }
                Some(Declaration::Variable {
                    file,
                    declarator,
                    constant: true,
                }) => match declarator.init.as_ref().map(crate::syntax::unwrap) {
                    Some(Expression::Identifier(reference)) => current = (file, reference),
                    Some(expression)
                        if crate::syntax::member_expression_of(expression).is_some() =>
                    {
                        let member = crate::syntax::member_expression_of(expression).unwrap();

                        break (
                            self.member_of_receiver(project, file, member).or_else(|| {
                                self.namespace_target_of(project, file, expression)
                                    .and_then(|target| declaration_of_target(project, target))
                            }),
                            false,
                        );
                    }
                    _ => break (declaration, true),
                },
                Some(Declaration::Variable {
                    constant: false, ..
                }) => break (None, false),
                _ => break (declaration, true),
            }
        };

        for (key, closed) in path.into_iter().rev() {
            result.1 &= closed;

            self.callable
                .borrow_mut()
                .insert(key, (result.0.map(target_of_declaration), result.1));
        }

        result
    }

    pub fn of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<Declaration<'a>> {
        let (file, symbol) = self.symbol_of_reference(project, file, reference)?;
        let target = self.target_of_symbol(project, file, symbol);

        declaration_of_target(project, target)
    }

    pub(crate) fn runtime_candidates_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Vec<Declaration<'a>> {
        let Some(Binding::Symbol { file, symbol }) =
            self.binding_of_reference(project, file, reference)
        else {
            return Vec::new();
        };
        let (candidates, determined) = self.runtime_declarations_of(project, file, symbol);
        let selected = match determined {
            true => candidates.last().map_or(&[][..], std::slice::from_ref),
            false => &candidates[..],
        };

        selected
            .iter()
            .filter_map(|node| declaration_of_node(project, file, *node))
            .collect()
    }

    pub fn binding_of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<Binding> {
        let (file, symbol) = self.symbol_of_reference(project, file, reference)?;

        match self.target_of_symbol(project, file, symbol) {
            Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
                Some(Binding::Symbol { file, symbol })
            }
            _ => None,
        }
    }

    pub fn binding_of_access(
        &self,
        project: &Project<'a>,
        file: FileId,
        object: &Expression<'a>,
        name: &str,
    ) -> Option<Binding> {
        let owner = self.namespace_target_of(project, file, object)?;

        match self.member_target_of(project, owner, name)? {
            Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
                Some(Binding::Symbol { file, symbol })
            }
            _ => None,
        }
    }

    fn namespace_target_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        object: &Expression<'a>,
    ) -> Option<Target> {
        match object {
            Expression::ParenthesizedExpression(inner) => {
                self.namespace_target_of(project, file, &inner.expression)
            }
            Expression::Identifier(reference) => {
                let (target_file, symbol) = self.symbol_of_reference(project, file, reference)?;

                Some(self.target_of_symbol(project, target_file, symbol))
            }
            Expression::StaticMemberExpression(member) => {
                let owner = self.namespace_target_of(project, file, &member.object)?;

                self.member_target_of(project, owner, member.property.name.as_str())
            }
            _ => None,
        }
    }

    fn member_target_of(&self, project: &Project<'a>, owner: Target, name: &str) -> Option<Target> {
        match owner {
            Target::Namespace(namespace) => self.followed_export_of(project, namespace, name),
            Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
                let semantic = &project.file(file).semantic;
                let scoping = semantic.scoping();

                scoping.symbol_declarations(symbol).find_map(|node| {
                    match semantic.nodes().kind(node) {
                        AstKind::TSNamespaceDeclaration(namespace) => {
                            let scope = namespace.scope_id.get()?;

                            scoping
                                .get_binding(scope, name.into())
                                .map(|symbol| Target::Symbol(file, symbol))
                        }
                        _ => None,
                    }
                })
            }
            _ => None,
        }
    }

    fn merged_namespace_symbol_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<SymbolId> {
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();
        let scoping = semantic.scoping();
        let name = reference.name.as_str();

        nodes
            .ancestors(reference.node_id())
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::TSNamespaceDeclaration(enclosing) => {
                    let namespace = enclosing.id.symbol_id.get()?;

                    scoping
                        .symbol_declarations(namespace)
                        .find_map(|node| match nodes.kind(node) {
                            AstKind::TSNamespaceDeclaration(block) => {
                                let symbol =
                                    scoping.get_binding(block.scope_id.get()?, name.into())?;
                                let declaration = scoping.symbol_declaration(symbol);
                                let exported = nodes.ancestors(declaration).take(3).any(|parent| {
                                    matches!(parent.kind(), AstKind::ExportDeclaration(_))
                                });

                                exported.then_some(symbol)
                            }
                            _ => None,
                        })
                }
                _ => None,
            })
    }

    pub fn is_member_first_declared_by_interface(
        &self,
        project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
        name: &str,
    ) -> bool {
        let Some(symbol) = class.id.as_ref().and_then(|id| id.symbol_id.get()) else {
            return false;
        };
        let semantic = &project.file(file).semantic;

        semantic.scoping().symbol_declarations(symbol).any(|node| {
            match semantic.nodes().kind(node) {
                AstKind::TSInterfaceDeclaration(interface)
                    if interface.span.start < class.span.start =>
                {
                    interface.body.body.iter().any(|signature| {
                        let key = match signature {
                            TSSignature::TSPropertySignature(property) => &property.key,
                            TSSignature::TSMethodSignature(method) => &method.key,
                            _ => return false,
                        };

                        match key {
                            PropertyKey::StaticIdentifier(identifier) => identifier.name == name,
                            PropertyKey::StringLiteral(literal) => literal.value == name,
                            _ => false,
                        }
                    })
                }
                _ => false,
            }
        })
    }

    pub fn of_binding(&self, project: &Project<'a>, binding: Binding) -> Option<Declaration<'a>> {
        match binding {
            Binding::Symbol { file, symbol } => {
                let target = self.target_of_symbol(project, file, symbol);

                declaration_of_target(project, target)
            }
        }
    }

    pub fn of_type_name(
        &self,
        project: &Project<'a>,
        file: FileId,
        name: &TSTypeName<'a>,
    ) -> Option<Declaration<'a>> {
        match name {
            TSTypeName::IdentifierReference(reference) => {
                self.of_reference(project, file, reference)
            }
            TSTypeName::QualifiedName(qualified) => {
                match self.of_type_name(project, file, &qualified.left)? {
                    Declaration::Namespace { file: target } => self
                        .of_export(project, target, qualified.right.name.as_str())
                        .into_iter()
                        .next(),
                    Declaration::External => Some(Declaration::External),
                    _ => None,
                }
            }
            TSTypeName::ThisExpression(_) => None,
        }
    }

    pub fn of_export(
        &self,
        project: &Project<'a>,
        file: FileId,
        name: &str,
    ) -> Vec<Declaration<'a>> {
        self.followed_export_of(project, file, name)
            .map(|target| declarations_of_target(project, target))
            .unwrap_or_default()
    }

    pub fn exports_of(
        &self,
        project: &Project<'a>,
        file: FileId,
    ) -> Vec<(String, Vec<Declaration<'a>>)> {
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        let mut visited = HashSet::new();

        self.collect_export_names(project, file, true, &mut visited, &mut seen, &mut names);

        names
            .into_iter()
            .filter_map(|(name, provider)| {
                let target = self.followed_export_of(project, provider, &name)?;

                let declarations = declarations_of_target(project, target);

                (!declarations.is_empty()).then_some((name, declarations))
            })
            .collect()
    }

    pub(crate) fn surface_exports(
        &self,
        project: &Project<'a>,
        file: FileId,
    ) -> Vec<(String, Vec<SurfaceTarget>)> {
        let mut names = Vec::new();
        let mut pending = vec![(file, true)];
        let mut visited = HashSet::new();
        let mut seen = HashSet::new();

        while let Some((file, include_default)) = pending.pop() {
            if !visited.insert(file) {
                continue;
            }

            let record = self.module_records[file.0 as usize];
            let functions = exported_function_statements_of(project, file);
            let value_declarations: HashSet<_> = project
                .file(file)
                .program
                .body
                .iter()
                .filter_map(|statement| match statement {
                    Statement::ExportDeclaration(export)
                        if matches!(
                            export.declaration,
                            oxc_ast::ast::Declaration::ClassDeclaration(_)
                                | oxc_ast::ast::Declaration::FunctionDeclaration(_)
                                | oxc_ast::ast::Declaration::VariableDeclaration(_)
                                | oxc_ast::ast::Declaration::TSEnumDeclaration(_)
                                | oxc_ast::ast::Declaration::TSNamespaceDeclaration(_)
                        ) =>
                    {
                        Some(export.span)
                    }
                    _ => None,
                })
                .collect();
            let mut entries: Vec<_> = record
                .local_export_entries
                .iter()
                .chain(&record.indirect_export_entries)
                .filter(|entry| {
                    !entry.is_type || value_declarations.contains(&entry.statement_span)
                })
                .collect();

            entries.sort_by_key(|entry| {
                (!functions.contains(&entry.statement_span), entry.span.start)
            });

            for entry in entries {
                if let Some(name) = export_name_of(entry) {
                    if (include_default || name != "default") && seen.insert(name.to_string()) {
                        names.push((name.to_string(), file));
                    }
                }
            }

            for entry in record
                .star_export_entries
                .iter()
                .rev()
                .filter(|entry| !entry.is_type)
            {
                if let Some(request) = &entry.module_request {
                    if let Resolved::File(target) = project.resolve(file, request.name.as_str()) {
                        pending.push((target, false));
                    }
                }
            }
        }

        names
            .into_iter()
            .map(|(name, provider)| {
                if name == "default" {
                    if let Some(node) =
                        project
                            .file(provider)
                            .program
                            .body
                            .iter()
                            .find_map(|statement| match statement {
                                Statement::ExportDefaultDeclaration(export) => {
                                    Some(export.declaration.node_id())
                                }
                                _ => None,
                            })
                    {
                        return (name, vec![SurfaceTarget::Node(provider, node)]);
                    }
                }

                let targets = self
                    .surface_targets(project, self.followed_export_of(project, provider, &name));

                (name, targets)
            })
            .collect()
    }

    pub(crate) fn surface_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Vec<SurfaceTarget> {
        let target = self
            .symbol_of_reference(project, file, reference)
            .map(|(file, symbol)| self.target_of_symbol(project, file, symbol));

        self.surface_targets(project, target)
    }

    fn surface_targets(&self, project: &Project<'a>, target: Option<Target>) -> Vec<SurfaceTarget> {
        match target {
            Some(Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol)) => {
                let nodes = declaration_nodes_of(project, file, symbol);
                let implemented = nodes.iter().any(|node| matches!(project.file(file).semantic.nodes().kind(*node), AstKind::Function(function) if function.body.is_some()));

                nodes.into_iter().filter(|node| !implemented || !matches!(project.file(file).semantic.nodes().kind(*node), AstKind::Function(function) if function.body.is_none())).map(|node| SurfaceTarget::Node(file, node)).collect()
            }
            Some(Target::Node(file, node)) => vec![SurfaceTarget::Node(file, node)],
            Some(Target::Namespace(file)) => vec![SurfaceTarget::Module(file)],
            _ => vec![SurfaceTarget::Unresolved],
        }
    }

    pub(crate) fn executable_declaration(
        &self,
        project: &Project<'a>,
        declaration: Declaration<'a>,
    ) -> Declaration<'a> {
        if let Declaration::Function {
            file,
            function: FunctionNode::Function(function),
        } = declaration
        {
            if function.body.is_none() {
                if let Some(symbol) = function.id.as_ref().and_then(|id| id.symbol_id.get()) {
                    return declaration_of_target(project, Target::Symbol(file, symbol))
                        .unwrap_or(declaration);
                }
            }
        }

        declaration
    }

    pub fn function_of<'d>(
        &self,
        declaration: Declaration<'d>,
    ) -> Option<(FileId, FunctionNode<'d>)> {
        match declaration {
            Declaration::Function { file, function } => match function {
                FunctionNode::Function(inner) if inner.body.is_none() => None,
                _ => Some((file, function)),
            },
            Declaration::Variable {
                file, declarator, ..
            } => function_of_initializer(declarator.init.as_ref()).map(|function| (file, function)),
            Declaration::Member {
                file,
                class,
                element,
            } => match element {
                ClassElement::MethodDefinition(method) if method.value.body.is_some() => {
                    Some((file, FunctionNode::Function(&method.value)))
                }
                ClassElement::MethodDefinition(signature) if signature.value.body.is_none() => {
                    let name = signature.key.static_name()?;

                    class.body.body.iter().find_map(|element| match element {
                        ClassElement::MethodDefinition(method)
                            if method.value.body.is_some()
                                && method.r#static == signature.r#static
                                && method.kind == signature.kind
                                && method.key.static_name().as_deref() == Some(name.as_ref()) =>
                        {
                            Some((file, FunctionNode::Function(&method.value)))
                        }
                        _ => None,
                    })
                }
                ClassElement::PropertyDefinition(property) => {
                    function_of_initializer(property.value.as_ref())
                        .map(|function| (file, function))
                }
                ClassElement::AccessorProperty(property) => {
                    function_of_initializer(property.value.as_ref())
                        .map(|function| (file, function))
                }
                _ => None,
            },
            Declaration::Property { file, property } => {
                function_of_initializer(Some(&property.value)).map(|function| (file, function))
            }
            Declaration::Class { file, class } => {
                class.body.body.iter().find_map(|element| match element {
                    ClassElement::MethodDefinition(method)
                        if method.kind == MethodDefinitionKind::Constructor
                            && method.value.body.is_some() =>
                    {
                        Some((file, FunctionNode::Function(&method.value)))
                    }
                    _ => None,
                })
            }
            _ => None,
        }
    }

    pub fn construction_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Option<FunctionNode<'a>> {
        if class.declare || class.r#abstract {
            return None;
        }

        let lineage = self.construction_lineage_of(project, file, class);

        (!lineage.constructor && lineage.initialized).then_some(FunctionNode::Construction(class))
    }

    fn construction_lineage_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
    ) -> ConstructionLineage {
        let mut chain = Vec::new();
        let mut visiting = HashSet::new();
        let mut current = Some((file, class));
        let mut inherited = ConstructionLineage::default();
        let mut truncated = false;

        while let Some((file, class)) = current {
            let site = (file, class.node_id());

            if let Some(known) = self.constructions.borrow().get(&site) {
                inherited = *known;

                break;
            }

            if !visiting.insert(site) || chain.len() == MAXIMUM_LINEAGE {
                truncated = true;

                break;
            }

            let mut stats = self.resolution_stats.get();

            stats.construction_visits += 1;

            self.resolution_stats.set(stats);

            chain.push((site, own_construction_of(class)));

            current = class.heritage.as_ref().and_then(|heritage| {
                self.class_of_expression(project, file, unwrap(&heritage.expression))
            });
        }

        for (site, own) in chain.into_iter().rev() {
            inherited = ConstructionLineage {
                constructor: inherited.constructor || own.constructor,
                initialized: inherited.initialized || own.initialized,
            };

            if !truncated {
                self.constructions.borrow_mut().insert(site, inherited);
            }
        }

        inherited
    }

    fn symbol_of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<(FileId, SymbolId)> {
        let reference_id = reference.reference_id.get()?;

        if let Some(symbol) = project
            .file(file)
            .semantic
            .scoping()
            .get_reference(reference_id)
            .symbol_id()
        {
            return Some((file, symbol));
        }

        if let Some(symbol) = self.merged_namespace_symbol_of(project, file, reference) {
            return Some((file, symbol));
        }

        let name = reference.name.as_str();

        let key = (file, name.to_string());

        if let Some(found) = self.globals.borrow().get(&key) {
            return *found;
        }

        let mut answers = project.file(file).owners.iter().map(|owner| {
            let mut bindings = project
                .files
                .iter()
                .filter(|source| source.owners.contains(owner) && !is_module_file(source))
                .filter_map(|source| {
                    source
                        .semantic
                        .scoping()
                        .get_root_binding(name.into())
                        .map(|symbol| (source.id, symbol))
                });
            let first = bindings.next();

            if bindings.all(|binding| Some(binding) == first) {
                first
            } else {
                None
            }
        });
        let first = answers.next().flatten();
        let found = if answers.all(|answer| answer == first) {
            first
        } else {
            None
        };

        self.globals.borrow_mut().insert(key, found);

        found
    }

    pub fn resolution_stats(&self) -> ResolutionStats {
        self.resolution_stats.get()
    }

    pub(crate) fn is_write_free(&self, project: &Project<'a>, binding: Binding) -> bool {
        if let Some(found) = self.write_free.borrow().get(&binding) {
            return *found;
        }

        let Binding::Symbol { file, symbol } = binding;
        let mut stats = self.resolution_stats.get();
        let mut found = true;

        for reference in project
            .file(file)
            .semantic
            .scoping()
            .get_resolved_references(symbol)
        {
            stats.write_reference_visits = stats.write_reference_visits.saturating_add(1);
            found &= !reference.is_write();
        }

        self.resolution_stats.set(stats);
        self.write_free.borrow_mut().insert(binding, found);

        found
    }

    fn runtime_declarations_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        symbol: SymbolId,
    ) -> (Vec<NodeId>, bool) {
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();
        let scoping = semantic.scoping();
        let scope = scoping.symbol_scope_id(symbol);
        let mut declarations: Vec<NodeId> = scoping.symbol_declarations(symbol).collect();
        let mut hoisted = Vec::new();
        let mut initialized = Vec::new();
        let mut determined = true;

        declarations.sort_by_key(|node| nodes.kind(*node).span().start);

        for node in declarations {
            match nodes.kind(node) {
                AstKind::Function(function)
                    if function.is_declaration() && function.body.is_some() =>
                {
                    determined &= nodes.get_node(node).scope_id() == scope;

                    hoisted.push(node);
                }
                AstKind::VariableDeclarator(declarator) if declarator.init.is_some() => {
                    initialized.push(node);
                }
                _ => {}
            }
        }

        if hoisted.is_empty() {
            return (hoisted, true);
        }

        let blocks = self
            .block_functions_of(project, file)
            .get(&(scope, scoping.symbol_name(symbol).to_string()))
            .cloned()
            .unwrap_or_default();

        determined &= initialized.is_empty() && blocks.is_empty();

        hoisted.extend(initialized);
        hoisted.extend(blocks);

        (hoisted, determined)
    }

    fn block_functions_of(
        &self,
        project: &Project<'a>,
        file: FileId,
    ) -> std::cell::Ref<'_, BlockFunctions> {
        if !self.block_functions.borrow().contains_key(&file) {
            let semantic = &project.file(file).semantic;
            let scoping = semantic.scoping();
            let mut found: BlockFunctions = HashMap::new();

            for symbol in scoping.symbol_ids() {
                let node = scoping.symbol_declaration(symbol);
                let mut scope = scoping.symbol_scope_id(symbol);
                let flags = scoping.scope_flags(scope);

                if flags.is_var()
                    || flags.is_strict_mode()
                    || !matches!(semantic.nodes().kind(node), AstKind::Function(function) if function.is_declaration() && function.body.is_some())
                {
                    continue;
                }

                while let Some(parent) = scoping.scope_parent_id(scope) {
                    scope = parent;

                    if scoping.scope_flags(scope).is_var() {
                        break;
                    }
                }

                found
                    .entry((scope, scoping.symbol_name(symbol).to_string()))
                    .or_default()
                    .push(node);
            }

            self.block_functions.borrow_mut().insert(file, found);
        }

        std::cell::Ref::map(self.block_functions.borrow(), |files| &files[&file])
    }

    pub fn declaration_within(
        &self,
        project: &Project<'a>,
        file: FileId,
        start: u32,
        end: u32,
    ) -> Option<NodeId> {
        if !self.declaration_spans.borrow().contains_key(&file) {
            let mut stats = self.resolution_stats.get();
            let mut spans = Vec::new();

            for node in project.file(file).semantic.nodes().iter() {
                stats.span_index_visits = stats.span_index_visits.saturating_add(1);

                let kind = node.kind();

                if is_declaration_kind(&kind) {
                    let span = kind.span();

                    spans.push((span.start, span.end, node.id()));
                }
            }

            spans.sort_by_key(|(start, end, node)| (*start, std::cmp::Reverse(*end), *node));

            self.resolution_stats.set(stats);
            self.declaration_spans.borrow_mut().insert(file, spans);
        }

        let files = self.declaration_spans.borrow();
        let spans = &files[&file];
        let first = spans.partition_point(|(candidate, _, _)| *candidate < start);

        spans[first..]
            .iter()
            .take_while(|(candidate, _, _)| *candidate <= end)
            .find(|(_, candidate, _)| *candidate <= end)
            .map(|(_, _, node)| *node)
    }

    pub(crate) fn surface_writes_of(
        &self,
        project: &Project<'a>,
        binding: Binding,
    ) -> Vec<(FileId, NodeId)> {
        if let Some(found) = self.surface_writes.borrow().get(&binding) {
            return found.clone();
        }

        let mut writes = Vec::new();

        for (file, node, write) in self.surface_references_of(project, binding) {
            if write {
                writes.push((file, node));
            } else if let Some(written) =
                surface_write_of(project.file(file).semantic.nodes(), node)
            {
                writes.push((file, written));
            }
        }

        self.surface_writes
            .borrow_mut()
            .insert(binding, writes.clone());

        writes
    }

    pub(crate) fn surface_references_of(
        &self,
        project: &Project<'a>,
        binding: Binding,
    ) -> Vec<SurfaceReference> {
        if let Some(found) = self.surface_references.borrow().get(&binding) {
            return found.clone();
        }

        let Binding::Symbol { file, symbol } = binding;
        let scoping = project.file(file).semantic.scoping();
        let mut stats = self.resolution_stats.get();
        let mut found: Vec<_> = scoping
            .get_resolved_references(symbol)
            .filter(|reference| reference.is_value())
            .map(|reference| (file, reference.node_id(), reference.is_write()))
            .collect();
        let name = scoping.symbol_name(symbol);

        stats.write_reference_visits = stats.write_reference_visits.saturating_add(found.len());

        for source in &project.files {
            let scoping = source.semantic.scoping();
            let Some(references) = scoping.root_unresolved_references().get(name) else {
                continue;
            };

            for id in references.iter() {
                let reference = scoping.get_reference(*id);
                let node = reference.node_id();

                stats.write_reference_visits = stats.write_reference_visits.saturating_add(1);

                if !reference.is_value() {
                    continue;
                }

                if let AstKind::IdentifierReference(identifier) = source.semantic.nodes().kind(node)
                {
                    if self.symbol_of_reference(project, source.id, identifier)
                        == Some((file, symbol))
                    {
                        found.push((source.id, node, reference.is_write()));
                    }
                }
            }
        }

        self.resolution_stats.set(stats);
        self.surface_references
            .borrow_mut()
            .insert(binding, found.clone());

        found
    }

    pub(crate) fn importers_of(&self, project: &Project<'a>, binding: Binding) -> Vec<Binding> {
        if self.importers.borrow().is_none() {
            let mut importers = Importers::default();

            for source in &project.files {
                for entry in &source.module_record.import_entries {
                    if entry.is_type {
                        continue;
                    }

                    let Some(local) = source
                        .semantic
                        .scoping()
                        .get_root_binding(entry.local_name.name.as_str().into())
                    else {
                        continue;
                    };
                    let imported = Binding::Symbol {
                        file: source.id,
                        symbol: local,
                    };

                    match self.target_of_symbol(project, source.id, local) {
                        Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
                            importers
                                .bindings
                                .entry(Binding::Symbol { file, symbol })
                                .or_default()
                                .push(imported)
                        }
                        Target::Namespace(file) => {
                            importers.namespaces.entry(file).or_default().push(imported)
                        }
                        _ => {}
                    }
                }
            }

            *self.importers.borrow_mut() = Some(importers);
        }

        let importers = self.importers.borrow();
        let importers = importers.as_ref().expect("importers are indexed");
        let Binding::Symbol { file, .. } = binding;

        importers
            .bindings
            .get(&binding)
            .into_iter()
            .chain(importers.namespaces.get(&file))
            .flatten()
            .copied()
            .filter(|imported| *imported != binding)
            .collect()
    }

    fn target_of_symbol(&self, project: &Project<'a>, file: FileId, symbol: SymbolId) -> Target {
        let mut pending = vec![ResolutionStep::Symbol(file, symbol)];
        let mut owned = HashSet::new();
        let mut target = Target::External;
        let mut open = false;

        while let Some(step) = pending.pop() {
            let mut stats = self.resolution_stats.get();

            stats.stack_peak = stats.stack_peak.max(pending.len() + 1);

            self.resolution_stats.set(stats);

            match step {
                ResolutionStep::Symbol(file, symbol) => {
                    if let Some(cached) = self.symbols.borrow().get(&(file, symbol)) {
                        (target, open) = *cached;

                        continue;
                    }

                    if !self.resolving.borrow_mut().insert((file, symbol)) {
                        if !owned.contains(&(file, symbol)) {
                            self.resolution_epoch
                                .set(self.resolution_epoch.get().saturating_add(1));
                        }

                        target = Target::External;
                        open = true;

                        continue;
                    }

                    owned.insert((file, symbol));

                    stats.symbol_visits = stats.symbol_visits.saturating_add(1);

                    self.resolution_stats.set(stats);
                    pending.push(ResolutionStep::Finish(
                        file,
                        symbol,
                        self.resolution_epoch.get(),
                    ));

                    let semantic = &project.file(file).semantic;
                    let node = semantic.scoping().symbol_declaration(symbol);

                    if let AstKind::TSImportEqualsDeclaration(import) = semantic.nodes().kind(node)
                    {
                        let (base, names) =
                            self.import_equals_input(project, file, &import.module_reference);

                        if !names.is_empty() {
                            pending.push(ResolutionStep::Members(names));
                        }

                        match base {
                            Target::Symbol(file, symbol) => {
                                pending.push(ResolutionStep::Symbol(file, symbol))
                            }
                            other => {
                                target = other;
                                open = false;
                            }
                        }
                    } else {
                        target = self.target_of_symbol_inner(project, file, symbol);
                        open = matches!(target, Target::OpenSymbol(..));
                    }
                }
                ResolutionStep::Members(mut names) => {
                    let name = names.pop().expect("nonempty qualified name");

                    stats.helper_visits = stats.helper_visits.saturating_add(1);

                    self.resolution_stats.set(stats);

                    target = self
                        .member_target_of(project, target, name)
                        .unwrap_or(Target::External);

                    if !names.is_empty() {
                        pending.push(ResolutionStep::Members(names));
                    }

                    if let Target::Symbol(file, symbol) = target {
                        pending.push(ResolutionStep::Open);
                        pending.push(ResolutionStep::Symbol(file, symbol));
                    } else {
                        open = true;
                    }
                }
                ResolutionStep::Open => open = true,
                ResolutionStep::Finish(file, symbol, epoch) => {
                    self.resolving.borrow_mut().remove(&(file, symbol));
                    owned.remove(&(file, symbol));

                    if open {
                        if let Target::Symbol(file, symbol) = target {
                            target = Target::OpenSymbol(file, symbol);
                        }
                    }

                    if epoch == self.resolution_epoch.get() || target != Target::External {
                        self.symbols
                            .borrow_mut()
                            .insert((file, symbol), (target, open));
                    }
                }
            }
        }

        target
    }

    fn import_equals_input(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &'a TSModuleReference<'a>,
    ) -> (Target, Vec<&'a str>) {
        let mut names = Vec::new();
        let reference = match reference {
            TSModuleReference::IdentifierReference(reference) => reference.as_ref(),
            TSModuleReference::QualifiedName(name) => {
                names.push(name.right.name.as_str());

                let mut left = &name.left;

                while let TSTypeName::QualifiedName(name) = left {
                    names.push(name.right.name.as_str());

                    left = &name.left;
                }

                let TSTypeName::IdentifierReference(reference) = left else {
                    return (Target::External, names);
                };

                reference.as_ref()
            }
            TSModuleReference::ExternalModuleReference(external) => {
                let Resolved::File(file) =
                    project.resolve(file, external.expression.value.as_str())
                else {
                    return (Target::External, names);
                };

                return self.assignment_input(project, file);
            }
        };

        (
            self.symbol_of_reference(project, file, reference)
                .map(|(file, symbol)| Target::Symbol(file, symbol))
                .unwrap_or(Target::External),
            names,
        )
    }

    fn assignment_input(&self, project: &Project<'a>, file: FileId) -> (Target, Vec<&'a str>) {
        let cached = self.assignments.borrow().get(&file).copied();
        let assignment = cached.unwrap_or_else(|| {
            let mut stats = self.resolution_stats.get();
            let found = project
                .file(file)
                .program
                .body
                .iter()
                .find_map(|statement| {
                    stats.helper_visits = stats.helper_visits.saturating_add(1);

                    match statement {
                        Statement::TSExportAssignment(assignment) => Some(assignment.node_id()),
                        _ => None,
                    }
                });

            self.resolution_stats.set(stats);
            self.assignments.borrow_mut().insert(file, found);

            found
        });
        let Some(assignment) = assignment else {
            return (Target::Namespace(file), Vec::new());
        };
        let AstKind::TSExportAssignment(assignment) =
            project.file(file).semantic.nodes().kind(assignment)
        else {
            unreachable!()
        };
        let mut expression = crate::syntax::unwrap(&assignment.expression);
        let mut names = Vec::new();

        while let Expression::StaticMemberExpression(member) = expression {
            names.push(member.property.name.as_str());

            expression = crate::syntax::unwrap(&member.object);
        }

        let target = match expression {
            Expression::Identifier(reference) => self
                .symbol_of_reference(project, file, reference)
                .map(|(file, symbol)| Target::Symbol(file, symbol))
                .unwrap_or(Target::External),
            Expression::FunctionExpression(function) => Target::Node(file, function.node_id()),
            Expression::ArrowFunctionExpression(function) => Target::Node(file, function.node_id()),
            _ => Target::External,
        };

        (target, names)
    }

    fn target_of_symbol_inner(
        &self,
        project: &Project<'a>,
        file: FileId,
        symbol: SymbolId,
    ) -> Target {
        let semantic = &project.file(file).semantic;
        let node = semantic.scoping().symbol_declaration(symbol);
        let nodes = semantic.nodes();
        let imported = match nodes.kind(node) {
            AstKind::ImportSpecifier(specifier) => Some(specifier.imported.name().as_str()),
            AstKind::ImportDefaultSpecifier(_) => Some("default"),
            AstKind::ImportNamespaceSpecifier(_) => None,
            _ => return Target::Symbol(file, symbol),
        };
        let source = nodes
            .ancestors(node)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::ImportDeclaration(declaration) => Some(declaration.source.value.as_str()),
                _ => None,
            });
        let Some(source) = source else {
            return Target::External;
        };

        match (project.resolve(file, source), imported) {
            (Resolved::File(target), Some(name)) => self
                .followed_export_of(project, target, name)
                .unwrap_or(Target::External),
            (Resolved::File(target), None) => Target::Namespace(target),
            _ => Target::External,
        }
    }

    fn followed_export_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        name: &str,
    ) -> Option<Target> {
        let key = (file, name.to_string());

        if let Some(cached) = self.followed.borrow().get(&key) {
            return *cached;
        }

        let mut visited = HashSet::new();
        let epoch = self.resolution_epoch.get();
        let target = self.export_target_of(project, file, name, &mut visited);

        if epoch == self.resolution_epoch.get()
            || target.is_some_and(|target| target != Target::External)
        {
            self.followed.borrow_mut().insert(key, target);
        }

        target
    }

    fn export_target_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        name: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Option<Target> {
        if !visited.insert((file, name.to_string())) {
            return None;
        }

        let module_record = self.module_records[file.0 as usize];

        for entry in &module_record.local_export_entries {
            if export_name_of(entry) != Some(name) {
                continue;
            }

            return match &entry.local_name {
                ExportLocalName::Name(local) | ExportLocalName::Default(local) => {
                    let scoping = project.file(file).semantic.scoping();
                    let symbol = scoping.get_root_binding(local.name.as_str().into())?;

                    Some(self.target_of_symbol(project, file, symbol))
                }
                ExportLocalName::Null => anonymous_default_of(project, file, entry),
            };
        }

        for entry in &module_record.indirect_export_entries {
            if export_name_of(entry) != Some(name) {
                continue;
            }

            let specifier = entry.module_request.as_ref()?.name.as_str();

            return match project.resolve(file, specifier) {
                Resolved::File(target) => match &entry.import_name {
                    ExportImportName::All => Some(Target::Namespace(target)),
                    ExportImportName::Name(imported) => {
                        let imported =
                            imported_name_of(module_record, entry, imported.name.as_str());

                        self.export_target_of(project, target, imported, visited)
                    }
                    _ => None,
                },
                _ => Some(Target::External),
            };
        }

        if name == "default" {
            return None;
        }

        star_targets_of(project, module_record, file)
            .into_iter()
            .find_map(|target| self.export_target_of(project, target, name, visited))
    }

    fn collect_export_names(
        &self,
        project: &Project<'a>,
        file: FileId,
        include_default: bool,
        visited: &mut HashSet<FileId>,
        seen: &mut HashSet<String>,
        names: &mut Vec<(String, FileId)>,
    ) {
        if !visited.insert(file) {
            return;
        }

        let module_record = self.module_records[file.0 as usize];
        let functions = exported_function_statements_of(project, file);
        let mut entries: Vec<&ExportEntry<'_>> = module_record
            .local_export_entries
            .iter()
            .chain(&module_record.indirect_export_entries)
            .collect();

        entries.sort_by_key(|entry| (!functions.contains(&entry.statement_span), entry.span.start));

        for entry in entries {
            let Some(name) = export_name_of(entry) else {
                continue;
            };

            if (include_default || name != "default") && seen.insert(name.to_string()) {
                names.push((name.to_string(), file));
            }
        }

        for target in star_targets_of(project, module_record, file) {
            self.collect_export_names(project, target, false, visited, seen, names);
        }
    }
}

const MAXIMUM_LINEAGE: usize = 256;

fn own_construction_of(class: &Class<'_>) -> ConstructionLineage {
    let mut lineage = ConstructionLineage::default();

    for element in &class.body.body {
        match element {
            ClassElement::MethodDefinition(method)
                if method.kind == MethodDefinitionKind::Constructor =>
            {
                lineage.constructor = true;
            }
            ClassElement::PropertyDefinition(property) => {
                lineage.initialized |=
                    property.value.is_some() && !property.r#static && !property.declare;
            }
            ClassElement::AccessorProperty(property) => {
                lineage.initialized |= property.value.is_some() && !property.r#static;
            }
            _ => {}
        }
    }

    lineage
}

pub fn is_declaration_kind(kind: &AstKind<'_>) -> bool {
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
            | AstKind::AccessorProperty(_)
            | AstKind::ObjectProperty(_)
            | AstKind::TSEnumDeclaration(_)
            | AstKind::TSEnumMember(_)
            | AstKind::TSInterfaceDeclaration(_)
            | AstKind::TSTypeAliasDeclaration(_)
            | AstKind::TSTypeParameter(_)
    )
}

fn is_reflective_write(callee: &Expression<'_>) -> bool {
    matches!(
        crate::syntax::unwrap(callee),
        Expression::StaticMemberExpression(member)
            if matches!(crate::syntax::unwrap(&member.object), Expression::Identifier(owner) if owner.name == "Object" || owner.name == "Reflect")
                && REFLECTIVE_WRITES.contains(&member.property.name.as_str())
    )
}

pub(crate) fn surface_write_of(nodes: &AstNodes<'_>, reference: NodeId) -> Option<NodeId> {
    let mut current = reference;
    let mut member = false;

    loop {
        let span = nodes.kind(current).span();
        let parent = nodes.parent_id(current);
        let written = match nodes.kind(parent) {
            AstKind::ParenthesizedExpression(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSTypeAssertion(_) => {
                current = parent;

                continue;
            }
            AstKind::StaticMemberExpression(expression) if expression.object.span() == span => {
                if MUTATORS.contains(&expression.property.name.as_str())
                    && matches!(nodes.parent_kind(parent), AstKind::CallExpression(call) if call.callee.span() == expression.span)
                {
                    return Some(nodes.parent_id(parent));
                }

                member = true;
                current = parent;

                continue;
            }
            AstKind::ComputedMemberExpression(expression) if expression.object.span() == span => {
                member = true;
                current = parent;

                continue;
            }
            AstKind::CallExpression(call) => {
                call.arguments
                    .first()
                    .is_some_and(|argument| argument.span() == span)
                    && is_reflective_write(&call.callee)
            }
            AstKind::AssignmentExpression(assignment) => member && assignment.left.span() == span,
            AstKind::UpdateExpression(_)
            | AstKind::ArrayAssignmentTarget(_)
            | AstKind::AssignmentTargetRest(_) => member,
            AstKind::UnaryExpression(unary) => {
                member && unary.operator == oxc_syntax::operator::UnaryOperator::Delete
            }
            AstKind::AssignmentTargetWithDefault(target) => member && target.binding.span() == span,
            AstKind::AssignmentTargetPropertyProperty(property) => {
                member && property.binding.span() == span
            }
            AstKind::ForInStatement(statement) => member && statement.left.span() == span,
            AstKind::ForOfStatement(statement) => member && statement.left.span() == span,
            _ => false,
        };

        return written.then_some(parent);
    }
}

fn is_module_file(source: &SourceFile<'_>) -> bool {
    source.module_record.has_module_syntax
        || source.program.body.iter().any(|statement| match statement {
            Statement::TSImportEqualsDeclaration(declaration) => matches!(
                declaration.module_reference,
                TSModuleReference::ExternalModuleReference(_)
            ),
            Statement::TSExportAssignment(_) => true,
            _ => false,
        })
}

fn exported_function_statements_of(project: &Project<'_>, file: FileId) -> HashSet<Span> {
    project
        .file(file)
        .program
        .body
        .iter()
        .filter_map(|statement| match statement {
            Statement::ExportDeclaration(export)
                if matches!(
                    export.declaration,
                    oxc_ast::ast::Declaration::FunctionDeclaration(_)
                ) =>
            {
                Some(export.span)
            }
            Statement::ExportDefaultDeclaration(export)
                if matches!(
                    export.declaration,
                    ExportDefaultDeclarationKind::FunctionDeclaration(_)
                ) =>
            {
                Some(export.span)
            }
            _ => None,
        })
        .collect()
}

fn star_targets_of(
    project: &Project<'_>,
    module_record: &ModuleRecord<'_>,
    file: FileId,
) -> Vec<FileId> {
    module_record
        .star_export_entries
        .iter()
        .filter_map(|entry| entry.module_request.as_ref())
        .filter_map(
            |request| match project.resolve(file, request.name.as_str()) {
                Resolved::File(target) => Some(target),
                _ => None,
            },
        )
        .collect()
}

fn target_of_declaration(declaration: Declaration<'_>) -> Target {
    match declaration {
        Declaration::Function { file, function } => Target::Node(file, function.node_id()),
        Declaration::Variable {
            file, declarator, ..
        } => Target::Node(file, declarator.node_id()),
        Declaration::Parameter {
            file, parameter, ..
        } => Target::Node(
            file,
            match parameter {
                ParameterNode::Formal(parameter) => parameter.node_id(),
                ParameterNode::Rest(parameter) => parameter.node_id(),
            },
        ),
        Declaration::Class { file, class } => Target::Node(file, class.node_id()),
        Declaration::Member { file, element, .. } => Target::Node(file, element.node_id()),
        Declaration::Property { file, property } => Target::Node(file, property.node_id()),
        Declaration::Enum { file, declaration } => Target::Node(file, declaration.node_id()),
        Declaration::EnumMember { file, member } => Target::Node(file, member.node_id()),
        Declaration::Interface { file, declaration } => Target::Node(file, declaration.node_id()),
        Declaration::TypeAlias { file, declaration } => Target::Node(file, declaration.node_id()),
        Declaration::TypeParameter { file, parameter } => Target::Node(file, parameter.node_id()),
        Declaration::Namespace { file } => Target::Namespace(file),
        Declaration::External => Target::External,
    }
}

fn declaration_of_target<'a>(project: &Project<'a>, target: Target) -> Option<Declaration<'a>> {
    match target {
        Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
            let declarations = declaration_nodes_of(project, file, symbol);
            let node = declarations.iter().rev().copied().find(|node| matches!(project.file(file).semantic.nodes().kind(*node), AstKind::Function(function) if function.body.is_some() && function.is_declaration())).or_else(|| declarations.first().copied())?;

            declaration_of_node(project, file, node)
        }
        Target::Node(file, node) => declaration_of_node(project, file, node),
        Target::Namespace(file) => Some(Declaration::Namespace { file }),
        Target::External => Some(Declaration::External),
    }
}

fn declarations_of_target<'a>(project: &Project<'a>, target: Target) -> Vec<Declaration<'a>> {
    match target {
        Target::Symbol(file, symbol) | Target::OpenSymbol(file, symbol) => {
            declaration_nodes_of(project, file, symbol)
                .into_iter()
                .filter_map(|node| declaration_of_node(project, file, node))
                .collect()
        }
        other => declaration_of_target(project, other).into_iter().collect(),
    }
}

fn declaration_nodes_of(project: &Project<'_>, file: FileId, symbol: SymbolId) -> Vec<NodeId> {
    let semantic = &project.file(file).semantic;
    let nodes = semantic.nodes();
    let mut declarations: Vec<NodeId> = semantic.scoping().symbol_declarations(symbol).collect();

    declarations.sort_by_key(|node| {
        let kind = nodes.kind(*node);
        let function_declaration =
            matches!(kind, AstKind::Function(function) if function.is_declaration());

        (!function_declaration, kind.span().start)
    });

    declarations
}

pub(crate) fn declaration_of_node<'a>(
    project: &Project<'a>,
    file: FileId,
    node: NodeId,
) -> Option<Declaration<'a>> {
    let nodes = project.file(file).semantic.nodes();

    match nodes.kind(node) {
        AstKind::ObjectProperty(property) => Some(Declaration::Property { file, property }),
        kind @ (AstKind::MethodDefinition(_)
        | AstKind::PropertyDefinition(_)
        | AstKind::AccessorProperty(_)) => {
            let class = class_of_element_node(project, file, node)?;
            let span = kind.span();
            let element = class
                .body
                .body
                .iter()
                .find(|element| element.span() == span)?;

            Some(Declaration::Member {
                file,
                class,
                element,
            })
        }
        AstKind::Function(function) => Some(Declaration::Function {
            file,
            function: FunctionNode::Function(function),
        }),
        AstKind::VariableDeclarator(declarator) => {
            let constant = matches!(
                nodes.parent_kind(node),
                AstKind::VariableDeclaration(declaration) if declaration.kind == VariableDeclarationKind::Const
            );

            Some(Declaration::Variable {
                file,
                declarator,
                constant,
            })
        }
        AstKind::FormalParameter(parameter) => Some(Declaration::Parameter {
            file,
            parameter: ParameterNode::Formal(parameter),
            function: function_of_parameter(project, file, node)?,
        }),
        AstKind::FormalParameterRest(parameter) => Some(Declaration::Parameter {
            file,
            parameter: ParameterNode::Rest(parameter),
            function: function_of_parameter(project, file, node)?,
        }),
        AstKind::Class(class) => Some(Declaration::Class { file, class }),
        AstKind::TSEnumDeclaration(declaration) => Some(Declaration::Enum { file, declaration }),
        AstKind::TSEnumMember(member) => Some(Declaration::EnumMember { file, member }),
        AstKind::TSInterfaceDeclaration(declaration) => {
            Some(Declaration::Interface { file, declaration })
        }
        AstKind::TSTypeAliasDeclaration(declaration) => {
            Some(Declaration::TypeAlias { file, declaration })
        }
        AstKind::TSTypeParameter(parameter) => Some(Declaration::TypeParameter { file, parameter }),
        AstKind::ImportSpecifier(_)
        | AstKind::ImportDefaultSpecifier(_)
        | AstKind::ImportNamespaceSpecifier(_)
        | AstKind::TSImportEqualsDeclaration(_) => Some(Declaration::External),
        _ => None,
    }
}

fn class_of_element_node<'a>(
    project: &Project<'a>,
    file: FileId,
    element: NodeId,
) -> Option<&'a Class<'a>> {
    let nodes = project.file(file).semantic.nodes();

    nodes
        .ancestors(element)
        .find_map(|ancestor| match ancestor.kind() {
            AstKind::Class(class) => Some(class),
            _ => None,
        })
}

fn function_of_parameter<'a>(
    project: &Project<'a>,
    file: FileId,
    parameter: NodeId,
) -> Option<FunctionNode<'a>> {
    let nodes = project.file(file).semantic.nodes();
    let parameters = nodes.parent_id(parameter);

    match nodes.parent_kind(parameters) {
        AstKind::Function(function) => Some(FunctionNode::Function(function)),
        AstKind::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
        _ => None,
    }
}

pub(crate) fn function_of_initializer<'a>(
    initializer: Option<&'a Expression<'a>>,
) -> Option<FunctionNode<'a>> {
    match initializer? {
        Expression::FunctionExpression(function) if function.body.is_some() => {
            Some(FunctionNode::Function(function))
        }
        Expression::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
        _ => None,
    }
}

fn anonymous_default_of(
    project: &Project<'_>,
    file: FileId,
    entry: &ExportEntry<'_>,
) -> Option<Target> {
    let program = project.file(file).program;

    program.body.iter().find_map(|statement| match statement {
        Statement::ExportDefaultDeclaration(declaration)
            if declaration.span == entry.statement_span =>
        {
            match &declaration.declaration {
                ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
                    Some(Target::Node(file, function.node_id()))
                }
                ExportDefaultDeclarationKind::ClassDeclaration(class) => {
                    Some(Target::Node(file, class.node_id()))
                }
                _ => None,
            }
        }
        _ => None,
    })
}

fn export_name_of<'b>(entry: &'b ExportEntry<'_>) -> Option<&'b str> {
    match &entry.export_name {
        ExportExportName::Name(name) => Some(name.name.as_str()),
        ExportExportName::Default(_) => Some("default"),
        ExportExportName::Null => None,
    }
}

fn imported_name_of<'b>(
    module_record: &'b ModuleRecord<'_>,
    entry: &ExportEntry<'_>,
    imported: &'b str,
) -> &'b str {
    for import in &module_record.import_entries {
        if import.statement_span != entry.statement_span {
            continue;
        }

        match &import.import_name {
            ImportImportName::Default(_) if import.local_name.name.as_str() == imported => {
                return "default";
            }
            ImportImportName::Name(name) if name.name.as_str() == imported => return imported,
            _ => {}
        }
    }

    imported
}

pub(crate) fn element_name_of(element: &ClassElement<'_>) -> Option<String> {
    let key = match element {
        ClassElement::MethodDefinition(method) => &method.key,
        ClassElement::PropertyDefinition(property) => &property.key,
        ClassElement::AccessorProperty(accessor) => &accessor.key,
        _ => return None,
    };

    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.to_string()),
        PropertyKey::StringLiteral(literal) => Some(literal.value.to_string()),
        PropertyKey::PrivateIdentifier(identifier) => Some(format!("#{}", identifier.name)),
        _ => None,
    }
}

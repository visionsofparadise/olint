use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use oxc_ast::ast::{
    ArrowFunctionExpression, Class, ClassElement, ExportDefaultDeclarationKind, Expression,
    FormalParameter, FormalParameterRest, Function, IdentifierReference, MemberExpression,
    MethodDefinitionKind, PropertyKey, Statement, TSEnumDeclaration, TSEnumMember,
    TSInterfaceDeclaration, TSTypeAliasDeclaration, TSTypeName, TSTypeParameter,
    VariableDeclarationKind, VariableDeclarator,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::Span;
use oxc_syntax::module_record::{
    ExportEntry, ExportExportName, ExportImportName, ExportLocalName, ImportImportName,
    ModuleRecord,
};
use oxc_syntax::symbol::SymbolId;

use crate::project::{FileId, Project, Resolved};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Binding {
    Symbol {
        file: FileId,
        symbol: SymbolId,
    },
    Member {
        file: FileId,
        class: NodeId,
        element: u32,
    },
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
    External,
}

#[derive(Clone, Copy, Debug)]
pub enum FunctionNode<'a> {
    Function(&'a Function<'a>),
    Arrow(&'a ArrowFunctionExpression<'a>),
}

impl FunctionNode<'_> {
    pub fn node_id(self) -> NodeId {
        match self {
            FunctionNode::Function(function) => function.node_id(),
            FunctionNode::Arrow(arrow) => arrow.node_id(),
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
        }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    Symbol(FileId, SymbolId),
    Node(FileId, NodeId),
    Namespace(FileId),
    External,
}

pub struct Declarations<'a> {
    followed: RefCell<HashMap<(FileId, String), Option<Target>>>,
    member_writes: RefCell<HashMap<FileId, HashSet<String>>>,
    module_records: Vec<&'a ModuleRecord<'a>>,
}

impl<'a> Declarations<'a> {
    pub fn new(project: &Project<'a>) -> Self {
        Declarations {
            followed: RefCell::new(HashMap::new()),
            member_writes: RefCell::new(HashMap::new()),
            module_records: project
                .files
                .iter()
                .map(|file| file.module_record)
                .collect(),
        }
    }

    pub fn of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<Declaration<'a>> {
        let symbol = symbol_of_reference(project, file, reference)?;
        let target = self.target_of_symbol(project, file, symbol);

        declaration_of_target(project, target)
    }

    pub fn binding_of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &IdentifierReference<'a>,
    ) -> Option<Binding> {
        let symbol = symbol_of_reference(project, file, reference)?;

        match self.target_of_symbol(project, file, symbol) {
            Target::Symbol(file, symbol) => Some(Binding::Symbol { file, symbol }),
            _ => None,
        }
    }

    pub fn member_binding(
        &self,
        _project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
        name: &str,
    ) -> Option<Binding> {
        let element = element_index_of(class, name)?;

        Some(Binding::Member {
            file,
            class: class.node_id(),
            element,
        })
    }

    pub fn of_binding(&self, project: &Project<'a>, binding: Binding) -> Option<Declaration<'a>> {
        match binding {
            Binding::Symbol { file, symbol } => {
                let target = self.target_of_symbol(project, file, symbol);

                declaration_of_target(project, target)
            }
            Binding::Member {
                file,
                class,
                element,
            } => {
                let AstKind::Class(class) = project.file(file).semantic.nodes().kind(class) else {
                    return None;
                };
                let element = class.body.body.get(element as usize)?;

                Some(Declaration::Member {
                    file,
                    class,
                    element,
                })
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
                    Declaration::Namespace { file: target } => {
                        self.of_export(project, target, qualified.right.name.as_str())
                    }
                    Declaration::External => Some(Declaration::External),
                    _ => None,
                }
            }
            TSTypeName::ThisExpression(_) => None,
        }
    }

    pub fn member_of(
        &self,
        _project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
        name: &str,
    ) -> Option<Declaration<'a>> {
        let element = class
            .body
            .body
            .get(element_index_of(class, name)? as usize)?;

        Some(Declaration::Member {
            file,
            class,
            element,
        })
    }

    pub fn of_export(
        &self,
        project: &Project<'a>,
        file: FileId,
        name: &str,
    ) -> Option<Declaration<'a>> {
        let target = self.followed_export_of(project, file, name)?;

        declaration_of_target(project, target)
    }

    pub fn exports_of(
        &self,
        project: &Project<'a>,
        file: FileId,
    ) -> Vec<(String, Declaration<'a>)> {
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        let mut visited = HashSet::new();

        self.collect_export_names(project, file, true, &mut visited, &mut seen, &mut names);

        names
            .into_iter()
            .filter_map(|(name, provider)| {
                let target = self.followed_export_of(project, provider, &name)?;

                declaration_of_target(project, target).map(|declaration| (name, declaration))
            })
            .collect()
    }

    pub fn function_of(&self, declaration: Declaration<'a>) -> Option<(FileId, FunctionNode<'a>)> {
        match declaration {
            Declaration::Function { file, function } => match function {
                FunctionNode::Function(inner) if inner.body.is_none() => None,
                _ => Some((file, function)),
            },
            Declaration::Variable {
                file, declarator, ..
            } => function_of_initializer(declarator.init.as_ref()).map(|function| (file, function)),
            Declaration::Member { file, element, .. } => match element {
                ClassElement::MethodDefinition(method) if method.value.body.is_some() => {
                    Some((file, FunctionNode::Function(&method.value)))
                }
                ClassElement::PropertyDefinition(property) => {
                    function_of_initializer(property.value.as_ref())
                        .map(|function| (file, function))
                }
                _ => None,
            },
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

    pub fn is_written(&self, project: &Project<'a>, binding: Binding) -> bool {
        match binding {
            Binding::Symbol { file, symbol } => project
                .file(file)
                .semantic
                .scoping()
                .symbol_is_mutated(symbol),
            Binding::Member {
                file,
                class,
                element,
            } => {
                let AstKind::Class(class) = project.file(file).semantic.nodes().kind(class) else {
                    return false;
                };
                let Some(name) = class
                    .body
                    .body
                    .get(element as usize)
                    .and_then(element_name_of)
                else {
                    return false;
                };
                let mut member_writes = self.member_writes.borrow_mut();

                member_writes
                    .entry(file)
                    .or_insert_with(|| written_member_names_of(project, file))
                    .contains(&name)
            }
        }
    }

    fn target_of_symbol(&self, project: &Project<'a>, file: FileId, symbol: SymbolId) -> Target {
        let semantic = &project.file(file).semantic;
        let node = semantic.scoping().symbol_declaration(symbol);
        let nodes = semantic.nodes();
        let imported = match nodes.kind(node) {
            AstKind::ImportSpecifier(specifier) => Some(specifier.imported.name().as_str()),
            AstKind::ImportDefaultSpecifier(_) => Some("default"),
            AstKind::ImportNamespaceSpecifier(_) => None,
            AstKind::TSImportEqualsDeclaration(_) => return Target::External,
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
        let target = self.export_target_of(project, file, name, &mut visited);

        self.followed.borrow_mut().insert(key, target);

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

fn symbol_of_reference(
    project: &Project<'_>,
    file: FileId,
    reference: &IdentifierReference<'_>,
) -> Option<SymbolId> {
    let reference_id = reference.reference_id.get()?;

    project
        .file(file)
        .semantic
        .scoping()
        .get_reference(reference_id)
        .symbol_id()
}

fn declaration_of_target<'a>(project: &Project<'a>, target: Target) -> Option<Declaration<'a>> {
    match target {
        Target::Symbol(file, symbol) => {
            let node = project
                .file(file)
                .semantic
                .scoping()
                .symbol_declaration(symbol);

            declaration_of_node(project, file, node)
        }
        Target::Node(file, node) => declaration_of_node(project, file, node),
        Target::Namespace(file) => Some(Declaration::Namespace { file }),
        Target::External => Some(Declaration::External),
    }
}

fn declaration_of_node<'a>(
    project: &Project<'a>,
    file: FileId,
    node: NodeId,
) -> Option<Declaration<'a>> {
    let nodes = project.file(file).semantic.nodes();

    match nodes.kind(node) {
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

fn function_of_initializer<'a>(
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

fn element_name_of(element: &ClassElement<'_>) -> Option<String> {
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

fn element_index_of(class: &Class<'_>, name: &str) -> Option<u32> {
    class
        .body
        .body
        .iter()
        .position(|element| element_name_of(element).as_deref() == Some(name))
        .map(|index| index as u32)
}

fn written_member_names_of(project: &Project<'_>, file: FileId) -> HashSet<String> {
    project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .filter_map(|node| match node.kind() {
            AstKind::AssignmentExpression(assignment) => assignment.left.as_member_expression(),
            AstKind::UpdateExpression(update) => update.argument.as_member_expression(),
            _ => None,
        })
        .filter_map(this_member_name_of)
        .collect()
}

fn this_member_name_of(member: &MemberExpression<'_>) -> Option<String> {
    match member {
        MemberExpression::StaticMemberExpression(member)
            if matches!(member.object, Expression::ThisExpression(_)) =>
        {
            Some(member.property.name.to_string())
        }
        MemberExpression::PrivateFieldExpression(member)
            if matches!(member.object, Expression::ThisExpression(_)) =>
        {
            Some(format!("#{}", member.field.name))
        }
        _ => None,
    }
}

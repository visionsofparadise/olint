use oxc_ast::ast::{
    BindingPattern, Class, ClassElement, Expression, ForStatementLeft, FormalParameter,
    FormalParameterRest, MemberExpression, MethodDefinition, MethodDefinitionKind,
    ObjectExpression, ObjectProperty, ObjectPropertyKind, PropertyKey, PropertyKind,
    TSInterfaceDeclaration, TSLiteral, TSMethodSignatureKind, TSSignature, TSType,
    TSTypeAnnotation, TSTypeLiteral, TSTypeName, TSTypeReference, VariableDeclarator,
};
use oxc_ast::AstKind;
use oxc_syntax::operator::{BinaryOperator, LogicalOperator};

use crate::analysis::Analysis;
use crate::constants::{call_of, member_expression_of, unwrap};
use crate::declarations::{Declaration, FunctionNode, ParameterNode};
use crate::project::FileId;
use crate::tables::{KIND_OF_NAME, STRING_LINEAR, TYPED_ARRAYS};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    Array,
    Set,
    Map,
    String,
    RegExp,
    Other,
    #[default]
    Unknown,
}

impl Kind {
    pub fn rank(self) -> u8 {
        match self {
            Kind::Array => 6,
            Kind::Set | Kind::Map => 5,
            Kind::Unknown => 4,
            Kind::String => 3,
            Kind::RegExp => 2,
            Kind::Other => 1,
        }
    }

    pub fn join(self, other: Kind) -> Kind {
        if other.rank() > self.rank() {
            other
        } else {
            self
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeclaredType {
    pub kind: Kind,
    pub tuple: bool,
    pub closed: bool,
}

const MAXIMUM_DEPTH: u32 = 8;
const MAXIMUM_CONTAINER_DEPTH: u32 = 256;
const UNWRAPPED_TYPE_NAMES: &[&str] = &["Readonly", "Required", "Partial", "NonNullable"];
const STRING_TO_ARRAY_NAMES: &[&str] = &["split", "match"];
const NON_STRING_RESULTS: &[&str] = &[
    "split",
    "match",
    "matchAll",
    "search",
    "indexOf",
    "lastIndexOf",
    "includes",
    "startsWith",
    "endsWith",
    "localeCompare",
    "codePointAt",
];
const STRING_RESULTS: &[&str] = &["join", "toString", "toLowerCase", "toUpperCase", "trim"];

#[derive(Clone, Copy)]
enum Container<'a> {
    TypeLiteral(FileId, &'a TSTypeLiteral<'a>),
    Interface(FileId, &'a TSInterfaceDeclaration<'a>),
    Class(FileId, &'a Class<'a>),
    Object(FileId, &'a ObjectExpression<'a>),
}

#[derive(Clone, Copy)]
enum Member<'a> {
    Signature(FileId, &'a TSSignature<'a>),
    Method(FileId, &'a MethodDefinition<'a>),
    Field(FileId, Option<&'a TSType<'a>>, Option<&'a Expression<'a>>),
    Property(FileId, &'a ObjectProperty<'a>),
}

#[derive(Clone, Copy)]
enum Typing<'a> {
    Annotation(FileId, &'a TSType<'a>),
    Initializer(FileId, &'a Expression<'a>),
}

fn typing_of<'a>(
    file: FileId,
    annotation: Option<&'a TSType<'a>>,
    initializer: Option<&'a Expression<'a>>,
) -> Option<Typing<'a>> {
    match (annotation, initializer) {
        (Some(annotation), _) => Some(Typing::Annotation(file, annotation)),
        (None, Some(initializer)) => Some(Typing::Initializer(file, initializer)),
        (None, None) => None,
    }
}

fn binding_parts_of<'a>(
    declaration: &Declaration<'a>,
) -> Option<(FileId, Option<&'a TSType<'a>>, Option<&'a Expression<'a>>)> {
    if let Some((file, declarator, _)) = declarator_of_identifier(declaration) {
        return Some((
            file,
            annotation_of(&declarator.type_annotation),
            declarator.init.as_ref(),
        ));
    }

    if let Some((file, parameter)) = formal_parameter_of_identifier(declaration) {
        return Some((
            file,
            annotation_of(&parameter.type_annotation),
            parameter.initializer.as_deref(),
        ));
    }

    rest_parameter_of_identifier(declaration)
        .map(|(file, parameter)| (file, annotation_of(&parameter.type_annotation), None))
}

fn declared_type_of(kind: Kind) -> DeclaredType {
    DeclaredType {
        kind,
        tuple: false,
        closed: false,
    }
}

fn joined_type_of(parts: &[DeclaredType], closed_all: bool) -> DeclaredType {
    if parts.is_empty() {
        return DeclaredType::default();
    }

    let kind = parts
        .iter()
        .fold(Kind::Other, |joined, part| joined.join(part.kind));
    let closed = if closed_all {
        parts.iter().all(|part| part.closed)
    } else {
        parts.iter().any(|part| part.closed)
            && parts
                .iter()
                .all(|part| part.closed || part.kind == Kind::Unknown)
    };

    DeclaredType {
        kind,
        tuple: parts.iter().all(|part| part.tuple),
        closed,
    }
}

fn type_name_text_of<'a>(name: &TSTypeName<'a>) -> &'a str {
    match name {
        TSTypeName::IdentifierReference(reference) => reference.name.as_str(),
        TSTypeName::QualifiedName(qualified) => qualified.right.name.as_str(),
        TSTypeName::ThisExpression(_) => "",
    }
}

fn first_type_argument_of<'a>(reference: &'a TSTypeReference<'a>) -> Option<&'a TSType<'a>> {
    reference
        .type_arguments
        .as_ref()
        .and_then(|arguments| arguments.params.first())
}

fn annotation_of<'a>(
    annotation: &'a Option<oxc_allocator::Box<'a, TSTypeAnnotation<'a>>>,
) -> Option<&'a TSType<'a>> {
    annotation
        .as_ref()
        .map(|annotation| &annotation.type_annotation)
}

fn is_named_identifier(key: &PropertyKey<'_>, name: &str) -> bool {
    matches!(key, PropertyKey::StaticIdentifier(identifier) if identifier.name == name)
}

fn return_type_of_function_expression<'a>(
    expression: &'a Expression<'a>,
) -> Option<&'a TSType<'a>> {
    match expression {
        Expression::FunctionExpression(function) => annotation_of(&function.return_type),
        Expression::ArrowFunctionExpression(arrow) => annotation_of(&arrow.return_type),
        _ => None,
    }
}

pub(crate) fn is_identifier_pattern(pattern: &BindingPattern<'_>) -> bool {
    matches!(pattern, BindingPattern::BindingIdentifier(_))
}

pub(crate) fn declarator_of_identifier<'a>(
    declaration: &Declaration<'a>,
) -> Option<(FileId, &'a VariableDeclarator<'a>, bool)> {
    match *declaration {
        Declaration::Variable {
            file,
            declarator,
            constant,
        } if is_identifier_pattern(&declarator.id) => Some((file, declarator, constant)),
        _ => None,
    }
}

pub(crate) fn formal_parameter_of_identifier<'a>(
    declaration: &Declaration<'a>,
) -> Option<(FileId, &'a FormalParameter<'a>)> {
    match *declaration {
        Declaration::Parameter {
            file,
            parameter: ParameterNode::Formal(parameter),
            ..
        } if is_identifier_pattern(&parameter.pattern) => Some((file, parameter)),
        _ => None,
    }
}

fn rest_parameter_of_identifier<'a>(
    declaration: &Declaration<'a>,
) -> Option<(FileId, &'a FormalParameterRest<'a>)> {
    match *declaration {
        Declaration::Parameter {
            file,
            parameter: ParameterNode::Rest(parameter),
            ..
        } if is_identifier_pattern(&parameter.rest.argument) => Some((file, parameter)),
        _ => None,
    }
}

fn is_class_declaration(declaration: &Declaration<'_>) -> bool {
    matches!(declaration, Declaration::Class { class, .. } if class.is_declaration())
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn declared_type_of_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> DeclaredType {
        self.declared_type_of_nested_expression(file, expression, 0)
    }

    pub fn declared_type_of_type(&mut self, file: FileId, ty: &'a TSType<'a>) -> DeclaredType {
        self.declared_type_of_nested_type(file, ty, 0)
    }

    fn declaration_of_type_name(
        &self,
        file: FileId,
        name: &'a TSTypeName<'a>,
    ) -> Option<Declaration<'a>> {
        self.declarations.of_type_name(self.project, file, name)
    }

    fn is_global_type_name(&self, file: FileId, name: &TSTypeName<'a>) -> bool {
        match name {
            TSTypeName::IdentifierReference(reference) => {
                reference.reference_id.get().is_none_or(|reference_id| {
                    self.project
                        .file(file)
                        .semantic
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                        .is_none()
                })
            }
            TSTypeName::QualifiedName(qualified) => self.is_global_type_name(file, &qualified.left),
            TSTypeName::ThisExpression(_) => false,
        }
    }

    fn declaration_of_identifier(
        &self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<Declaration<'a>> {
        match expression {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            _ => None,
        }
    }

    fn declaration_of_heritage(
        &self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<Declaration<'a>> {
        match expression {
            Expression::StaticMemberExpression(member) => {
                match self.declaration_of_heritage(file, &member.object)? {
                    Declaration::Namespace { file: target } => self
                        .declarations
                        .of_export(self.project, target, member.property.name.as_str())
                        .into_iter()
                        .next(),
                    Declaration::External => Some(Declaration::External),
                    _ => None,
                }
            }
            _ => self.declaration_of_identifier(file, expression),
        }
    }

    fn declared_type_of_nested_type(
        &mut self,
        file: FileId,
        ty: &'a TSType<'a>,
        depth: u32,
    ) -> DeclaredType {
        if depth > MAXIMUM_DEPTH {
            return DeclaredType::default();
        }

        match ty {
            TSType::TSParenthesizedType(parenthesized) => {
                self.declared_type_of_nested_type(file, &parenthesized.type_annotation, depth + 1)
            }
            TSType::TSTypeOperatorType(operator) => {
                self.declared_type_of_nested_type(file, &operator.type_annotation, depth + 1)
            }
            TSType::TSTupleType(_) => DeclaredType {
                kind: Kind::Array,
                tuple: true,
                closed: false,
            },
            TSType::TSArrayType(_) => declared_type_of(Kind::Array),
            TSType::TSStringKeyword(_) | TSType::TSTemplateLiteralType(_) => {
                declared_type_of(Kind::String)
            }
            TSType::TSLiteralType(literal)
                if matches!(
                    literal.literal,
                    TSLiteral::StringLiteral(_) | TSLiteral::TemplateLiteral(_)
                ) =>
            {
                declared_type_of(Kind::String)
            }
            TSType::TSAnyKeyword(_) | TSType::TSUnknownKeyword(_) => DeclaredType::default(),
            TSType::TSObjectKeyword(_) => declared_type_of(Kind::Other),
            TSType::TSTypeLiteral(literal) => DeclaredType {
                kind: Kind::Other,
                tuple: false,
                closed: self.is_closed_container(Container::TypeLiteral(file, literal), depth + 1),
            },
            TSType::TSUnionType(union) => {
                let parts: Vec<DeclaredType> = union
                    .types
                    .iter()
                    .map(|part| self.declared_type_of_nested_type(file, part, depth + 1))
                    .collect();

                joined_type_of(&parts, true)
            }
            TSType::TSIntersectionType(intersection) => {
                let parts: Vec<DeclaredType> = intersection
                    .types
                    .iter()
                    .map(|part| self.declared_type_of_nested_type(file, part, depth + 1))
                    .collect();

                joined_type_of(&parts, false)
            }
            TSType::TSTypeReference(reference) => {
                self.declared_type_of_reference(file, reference, depth)
            }
            _ => declared_type_of(Kind::Other),
        }
    }

    fn declared_type_of_reference(
        &mut self,
        file: FileId,
        reference: &'a TSTypeReference<'a>,
        depth: u32,
    ) -> DeclaredType {
        let name = type_name_text_of(&reference.type_name);

        if let Some(kind) = named_kind_of(name) {
            return declared_type_of(kind);
        }

        if let Some(argument) = first_type_argument_of(reference) {
            if UNWRAPPED_TYPE_NAMES.contains(&name) {
                return self.declared_type_of_nested_type(file, argument, depth + 1);
            }

            if name == "Pick" || name == "Omit" {
                return DeclaredType {
                    kind: Kind::Other,
                    tuple: false,
                    closed: self
                        .declared_type_of_nested_type(file, argument, depth + 1)
                        .closed,
                };
            }
        }

        let Some(declaration) = self.declaration_of_type_name(file, &reference.type_name) else {
            return if self.is_global_type_name(file, &reference.type_name) {
                declared_type_of(Kind::Other)
            } else {
                DeclaredType::default()
            };
        };

        match declaration {
            Declaration::TypeAlias {
                file: target,
                declaration,
            } => self.declared_type_of_nested_type(target, &declaration.type_annotation, depth + 1),
            Declaration::Interface {
                file: target,
                declaration,
            } => DeclaredType {
                kind: Kind::Other,
                tuple: false,
                closed: self
                    .is_closed_container(Container::Interface(target, declaration), depth + 1),
            },
            Declaration::Class {
                file: target,
                class,
            } if class.is_declaration() => DeclaredType {
                kind: Kind::Other,
                tuple: false,
                closed: self.is_closed_container(Container::Class(target, class), depth + 1),
            },
            Declaration::Enum { .. } => DeclaredType {
                kind: Kind::Other,
                tuple: false,
                closed: true,
            },
            Declaration::TypeParameter {
                file: target,
                parameter,
            } => match &parameter.constraint {
                Some(constraint) => {
                    self.declared_type_of_nested_type(target, constraint, depth + 1)
                }
                None => DeclaredType::default(),
            },
            _ => DeclaredType::default(),
        }
    }

    fn is_closed_container(&mut self, container: Container<'a>, depth: u32) -> bool {
        if depth > MAXIMUM_DEPTH {
            return false;
        }

        match container {
            Container::Object(file, object) => {
                !object.properties.is_empty()
                    && object.properties.iter().all(|property| match property {
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            self.declared_type_of_nested_expression(
                                file,
                                &spread.argument,
                                depth + 1,
                            )
                            .closed
                        }
                        ObjectPropertyKind::ObjectProperty(_) => true,
                    })
            }
            Container::TypeLiteral(_, literal) => {
                !literal
                    .members
                    .iter()
                    .any(|member| matches!(member, TSSignature::TSIndexSignature(_)))
                    && !literal.members.is_empty()
            }
            Container::Interface(file, interface) => {
                if interface
                    .body
                    .body
                    .iter()
                    .any(|member| matches!(member, TSSignature::TSIndexSignature(_)))
                {
                    return false;
                }

                for heritage in &interface.extends {
                    let declaration = self.declaration_of_type_name(file, &heritage.type_name);

                    if !self.is_closed_heritage(declaration, depth) {
                        return false;
                    }
                }

                !interface.body.body.is_empty() || !interface.extends.is_empty()
            }
            Container::Class(file, class) => {
                if class
                    .body
                    .body
                    .iter()
                    .any(|element| matches!(element, ClassElement::TSIndexSignature(_)))
                {
                    return false;
                }

                if let Some(heritage) = &class.heritage {
                    let declaration = self.declaration_of_heritage(file, &heritage.expression);

                    if !self.is_closed_heritage(declaration, depth) {
                        return false;
                    }
                }

                for implemented in &class.implements {
                    let declaration = self.declaration_of_type_name(file, &implemented.expression);

                    if !self.is_closed_heritage(declaration, depth) {
                        return false;
                    }
                }

                !class.body.body.is_empty()
                    || class.heritage.is_some()
                    || !class.implements.is_empty()
            }
        }
    }

    fn is_closed_heritage(&mut self, declaration: Option<Declaration<'a>>, depth: u32) -> bool {
        match declaration {
            Some(Declaration::Interface { file, declaration }) => {
                self.is_closed_container(Container::Interface(file, declaration), depth + 1)
            }
            Some(Declaration::Class { file, class }) if class.is_declaration() => {
                self.is_closed_container(Container::Class(file, class), depth + 1)
            }
            Some(Declaration::TypeAlias { file, declaration }) => {
                self.declared_type_of_nested_type(file, &declaration.type_annotation, depth + 1)
                    .closed
            }
            _ => false,
        }
    }

    fn container_of_type(
        &mut self,
        file: FileId,
        ty: &'a TSType<'a>,
        depth: u32,
    ) -> Option<Container<'a>> {
        if depth > MAXIMUM_DEPTH {
            return None;
        }

        match ty {
            TSType::TSParenthesizedType(parenthesized) => {
                self.container_of_type(file, &parenthesized.type_annotation, depth + 1)
            }
            TSType::TSTypeLiteral(literal) => Some(Container::TypeLiteral(file, literal)),
            TSType::TSTypeReference(reference) => {
                let name = type_name_text_of(&reference.type_name);

                if UNWRAPPED_TYPE_NAMES.contains(&name) {
                    if let Some(argument) = first_type_argument_of(reference) {
                        return self.container_of_type(file, argument, depth + 1);
                    }
                }

                match self.declaration_of_type_name(file, &reference.type_name)? {
                    Declaration::TypeAlias {
                        file: target,
                        declaration,
                    } => self.container_of_type(target, &declaration.type_annotation, depth + 1),
                    Declaration::Interface {
                        file: target,
                        declaration,
                    } => Some(Container::Interface(target, declaration)),
                    Declaration::Class {
                        file: target,
                        class,
                    } if class.is_declaration() => Some(Container::Class(target, class)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn container_of_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: u32,
    ) -> Option<Container<'a>> {
        if depth > MAXIMUM_CONTAINER_DEPTH {
            return None;
        }

        let expression = unwrap(expression);

        if let Expression::ThisExpression(this) = expression {
            let nodes = self.project.file(file).semantic.nodes();

            return nodes
                .ancestors(this.node_id())
                .find_map(|ancestor| match ancestor.kind() {
                    AstKind::Class(class) => Some(Container::Class(file, class)),
                    _ => None,
                });
        }

        if let Expression::ObjectExpression(object) = expression {
            return Some(Container::Object(file, object));
        }

        if let Expression::NewExpression(new) = expression {
            let declaration = self.declaration_of_identifier(file, &new.callee)?;

            return match declaration {
                Declaration::Class {
                    file: target,
                    class,
                } if class.is_declaration() => Some(Container::Class(target, class)),
                _ => None,
            };
        }

        if let Expression::Identifier(reference) = expression {
            let declaration = self
                .declarations
                .of_reference(self.project, file, reference)?;

            return self.container_of_binding(declaration, depth);
        }

        if let Some(call) = call_of(expression) {
            let callee = unwrap(&call.callee);

            if let Expression::Identifier(reference) = callee {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference);
                let (target, return_type) = return_type_of_callee(declaration)?;

                return self.container_of_type(target, return_type, 0);
            }

            if let Some(MemberExpression::StaticMemberExpression(member)) =
                member_expression_of(callee)
            {
                let container = self.container_of_expression(file, &member.object, depth + 1);

                let (target, return_type) =
                    match member_of_container(container, member.property.name.as_str())? {
                        Member::Signature(target, TSSignature::TSMethodSignature(method))
                            if method.kind == TSMethodSignatureKind::Method =>
                        {
                            (target, annotation_of(&method.return_type)?)
                        }
                        Member::Method(target, method)
                            if method.kind == MethodDefinitionKind::Method =>
                        {
                            (target, annotation_of(&method.value.return_type)?)
                        }
                        Member::Property(target, property) if property.method => {
                            (target, return_type_of_function_expression(&property.value)?)
                        }
                        _ => return None,
                    };

                return self.container_of_type(target, return_type, 0);
            }

            return None;
        }

        if let Some(MemberExpression::StaticMemberExpression(member)) =
            member_expression_of(expression)
        {
            let container = self.container_of_expression(file, &member.object, depth + 1);

            let typing = match member_of_container(container, member.property.name.as_str())? {
                Member::Property(target, property)
                    if property.kind == PropertyKind::Init
                        && !property.method
                        && !property.shorthand =>
                {
                    Typing::Initializer(target, &property.value)
                }
                Member::Signature(target, TSSignature::TSPropertySignature(signature)) => {
                    Typing::Annotation(target, annotation_of(&signature.type_annotation)?)
                }
                Member::Field(target, annotation, initializer) => {
                    typing_of(target, annotation, initializer)?
                }
                _ => return None,
            };

            return self.container_of_typing(typing, depth);
        }

        None
    }

    fn container_of_typing(&mut self, typing: Typing<'a>, depth: u32) -> Option<Container<'a>> {
        match typing {
            Typing::Annotation(file, annotation) => self.container_of_type(file, annotation, 0),
            Typing::Initializer(file, initializer) => {
                self.container_of_expression(file, initializer, depth + 1)
            }
        }
    }

    fn container_of_binding(
        &mut self,
        declaration: Declaration<'a>,
        depth: u32,
    ) -> Option<Container<'a>> {
        let (file, annotation, initializer) = binding_parts_of(&declaration)?;

        self.container_of_typing(typing_of(file, annotation, initializer)?, depth)
    }

    fn declared_type_of_typing(&mut self, typing: Option<Typing<'a>>, depth: u32) -> DeclaredType {
        match typing {
            Some(Typing::Annotation(file, annotation)) => {
                self.declared_type_of_nested_type(file, annotation, depth + 1)
            }
            Some(Typing::Initializer(file, initializer)) => {
                self.declared_type_of_nested_expression(file, initializer, depth + 1)
            }
            None => DeclaredType::default(),
        }
    }

    fn declared_type_of_member(&mut self, member: Option<Member<'a>>, depth: u32) -> DeclaredType {
        let typing = match member {
            Some(Member::Property(file, property))
                if property.kind == PropertyKind::Init && !property.method =>
            {
                Some(Typing::Initializer(file, &property.value))
            }
            Some(Member::Property(file, property)) if property.kind == PropertyKind::Get => {
                return_type_of_function_expression(&property.value)
                    .map(|annotation| Typing::Annotation(file, annotation))
            }
            Some(Member::Signature(file, TSSignature::TSPropertySignature(signature))) => {
                annotation_of(&signature.type_annotation)
                    .map(|annotation| Typing::Annotation(file, annotation))
            }
            Some(Member::Signature(file, TSSignature::TSMethodSignature(method)))
                if method.kind == TSMethodSignatureKind::Get =>
            {
                annotation_of(&method.return_type)
                    .map(|annotation| Typing::Annotation(file, annotation))
            }
            Some(Member::Field(file, annotation, initializer)) => {
                typing_of(file, annotation, initializer)
            }
            Some(Member::Method(file, method)) if method.kind == MethodDefinitionKind::Get => {
                annotation_of(&method.value.return_type)
                    .map(|annotation| Typing::Annotation(file, annotation))
            }
            _ => None,
        };

        self.declared_type_of_typing(typing, depth)
    }

    fn return_type_of_member(&mut self, member: Option<Member<'a>>, depth: u32) -> DeclaredType {
        let return_type = match member {
            Some(Member::Signature(file, TSSignature::TSMethodSignature(method)))
                if method.kind == TSMethodSignatureKind::Method =>
            {
                annotation_of(&method.return_type).map(|ty| (file, ty))
            }
            Some(Member::Method(file, method)) if method.kind == MethodDefinitionKind::Method => {
                annotation_of(&method.value.return_type).map(|ty| (file, ty))
            }
            Some(Member::Property(file, property)) if property.method => {
                return_type_of_function_expression(&property.value).map(|ty| (file, ty))
            }
            Some(Member::Signature(file, TSSignature::TSPropertySignature(signature))) => {
                match annotation_of(&signature.type_annotation) {
                    Some(TSType::TSFunctionType(function)) => {
                        Some((file, &function.return_type.type_annotation))
                    }
                    _ => None,
                }
            }
            Some(Member::Field(file, annotation, initializer)) => match (annotation, initializer) {
                (Some(TSType::TSFunctionType(function)), _) => {
                    Some((file, &function.return_type.type_annotation))
                }
                (_, Some(value)) => return_type_of_function_expression(value).map(|ty| (file, ty)),
                _ => None,
            },
            Some(Member::Property(file, property))
                if property.kind == PropertyKind::Init && !property.shorthand =>
            {
                return_type_of_function_expression(&property.value).map(|ty| (file, ty))
            }
            _ => None,
        };

        self.declared_type_of_typing(
            return_type.map(|(file, annotation)| Typing::Annotation(file, annotation)),
            depth,
        )
    }

    fn declared_type_of_nested_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: u32,
    ) -> DeclaredType {
        if depth > MAXIMUM_DEPTH {
            return DeclaredType::default();
        }

        match expression {
            Expression::TSAsExpression(assertion) if !is_const_type(&assertion.type_annotation) => {
                return self.declared_type_of_nested_type(
                    file,
                    &assertion.type_annotation,
                    depth + 1,
                );
            }
            Expression::TSSatisfiesExpression(assertion)
                if !is_const_type(&assertion.type_annotation) =>
            {
                return self.declared_type_of_nested_type(
                    file,
                    &assertion.type_annotation,
                    depth + 1,
                );
            }
            _ => {}
        }

        let expression = unwrap(expression);

        match expression {
            Expression::ArrayExpression(array) => {
                return DeclaredType {
                    kind: Kind::Array,
                    tuple: !array.elements.iter().any(|element| element.is_spread()),
                    closed: false,
                };
            }
            Expression::StringLiteral(_) | Expression::TemplateLiteral(_) => {
                return declared_type_of(Kind::String);
            }
            Expression::RegExpLiteral(_) => return declared_type_of(Kind::RegExp),
            Expression::ObjectExpression(object) => {
                return DeclaredType {
                    kind: Kind::Other,
                    tuple: false,
                    closed: self.is_closed_container(Container::Object(file, object), depth + 1),
                };
            }
            Expression::NewExpression(new) => {
                if let Expression::Identifier(callee) = &new.callee {
                    if let Some(kind) = named_kind_of(callee.name.as_str()) {
                        return declared_type_of(kind);
                    }

                    return match self.declarations.of_reference(self.project, file, callee) {
                        Some(Declaration::Class {
                            file: target,
                            class,
                        }) if class.is_declaration() => DeclaredType {
                            kind: Kind::Other,
                            tuple: false,
                            closed: self
                                .is_closed_container(Container::Class(target, class), depth + 1),
                        },
                        _ => declared_type_of(Kind::Other),
                    };
                }
            }
            Expression::BinaryExpression(binary) if binary.operator == BinaryOperator::Addition => {
                let left = self.declared_type_of_nested_expression(file, &binary.left, depth + 1);
                let right = self.declared_type_of_nested_expression(file, &binary.right, depth + 1);

                return if left.kind == Kind::String || right.kind == Kind::String {
                    declared_type_of(Kind::String)
                } else {
                    DeclaredType::default()
                };
            }
            Expression::ConditionalExpression(conditional) => {
                let parts = [
                    self.declared_type_of_nested_expression(
                        file,
                        &conditional.consequent,
                        depth + 1,
                    ),
                    self.declared_type_of_nested_expression(
                        file,
                        &conditional.alternate,
                        depth + 1,
                    ),
                ];

                return joined_type_of(&parts, true);
            }
            Expression::LogicalExpression(logical)
                if matches!(
                    logical.operator,
                    LogicalOperator::Coalesce | LogicalOperator::Or
                ) =>
            {
                let parts = [
                    self.declared_type_of_nested_expression(file, &logical.left, depth + 1),
                    self.declared_type_of_nested_expression(file, &logical.right, depth + 1),
                ];

                return joined_type_of(&parts, true);
            }
            _ => {}
        }

        if let Some(call) = call_of(expression) {
            return self.declared_type_of_call(file, &call.callee, depth);
        }

        match member_expression_of(expression) {
            Some(MemberExpression::StaticMemberExpression(member)) => {
                let name = member.property.name.as_str();

                if name == "length" {
                    return declared_type_of(Kind::Other);
                }

                let container = self.container_of_expression(file, &member.object, depth + 1);
                let found = member_of_container(container, name);

                return self.declared_type_of_member(found, depth + 1);
            }
            Some(_) => return DeclaredType::default(),
            None => {}
        }

        if let Expression::Identifier(reference) = expression {
            let Some(declaration) = self
                .declarations
                .of_reference(self.project, file, reference)
            else {
                return DeclaredType::default();
            };

            return self.declared_type_of_binding(declaration, depth);
        }

        DeclaredType::default()
    }

    fn declared_type_of_call(
        &mut self,
        file: FileId,
        callee: &'a Expression<'a>,
        depth: u32,
    ) -> DeclaredType {
        let callee = unwrap(callee);

        if let Some(MemberExpression::StaticMemberExpression(member)) = member_expression_of(callee)
        {
            let method = member.property.name.as_str();
            let receiver = unwrap(&member.object);

            if let Expression::Identifier(identifier) = receiver {
                let text = identifier.name.as_str();

                if (text == "Object" || text == "Array")
                    && matches!(method, "keys" | "values" | "entries" | "from" | "of")
                {
                    return declared_type_of(Kind::Array);
                }

                if text == "JSON" && method == "stringify" {
                    return declared_type_of(Kind::String);
                }
            }

            let received = self.declared_type_of_nested_expression(file, receiver, depth + 1);

            if received.kind == Kind::String && STRING_TO_ARRAY_NAMES.contains(&method) {
                return declared_type_of(Kind::Array);
            }

            if received.kind == Kind::String
                && STRING_LINEAR.contains(&method)
                && !NON_STRING_RESULTS.contains(&method)
            {
                return declared_type_of(Kind::String);
            }

            if received.kind == Kind::Array && crate::tables::ARRAY_TO_ARRAY.contains(&method) {
                return declared_type_of(Kind::Array);
            }

            if STRING_RESULTS.contains(&method) {
                return declared_type_of(Kind::String);
            }

            let container = self.container_of_expression(file, receiver, depth + 1);
            let found = member_of_container(container, method);

            return self.return_type_of_member(found, depth + 1);
        }

        if let Expression::Identifier(reference) = callee {
            let declaration = self
                .declarations
                .of_reference(self.project, file, reference);

            return match return_type_of_callee(declaration) {
                Some((target, return_type)) => {
                    self.declared_type_of_nested_type(target, return_type, depth + 1)
                }
                None => DeclaredType::default(),
            };
        }

        DeclaredType::default()
    }

    fn declared_type_of_binding(
        &mut self,
        declaration: Declaration<'a>,
        depth: u32,
    ) -> DeclaredType {
        if let Some((target, annotation, initializer)) = binding_parts_of(&declaration) {
            if let Some(typing) = typing_of(target, annotation, initializer) {
                return self.declared_type_of_typing(Some(typing), depth);
            }

            let Some((_, declarator, _)) = declarator_of_identifier(&declaration) else {
                return DeclaredType::default();
            };
            let nodes = self.project.file(target).semantic.nodes();
            let declaration_node = nodes.parent_id(declarator.node_id());

            if let AstKind::ForOfStatement(statement) = nodes.parent_kind(declaration_node) {
                if matches!(statement.left, ForStatementLeft::VariableDeclaration(_)) {
                    let source = self.declared_type_of_nested_expression(
                        target,
                        &statement.right,
                        depth + 1,
                    );

                    return if source.kind == Kind::String {
                        declared_type_of(Kind::String)
                    } else {
                        DeclaredType::default()
                    };
                }
            }

            return DeclaredType::default();
        }

        match declaration {
            Declaration::Class { .. } if is_class_declaration(&declaration) => {
                declared_type_of(Kind::Other)
            }
            Declaration::Function {
                function: FunctionNode::Function(function),
                ..
            } if function.is_declaration() => declared_type_of(Kind::Other),
            Declaration::Enum { .. } => DeclaredType {
                kind: Kind::Other,
                tuple: false,
                closed: true,
            },
            _ => DeclaredType::default(),
        }
    }
}

fn named_kind_of(name: &str) -> Option<Kind> {
    KIND_OF_NAME
        .iter()
        .find(|(known, _)| *known == name)
        .map(|(_, kind)| *kind)
        .or_else(|| TYPED_ARRAYS.contains(&name).then_some(Kind::Array))
}

pub(crate) fn is_const_type(ty: &TSType<'_>) -> bool {
    matches!(ty, TSType::TSTypeReference(reference) if type_name_text_of(&reference.type_name) == "const")
}

fn return_type_of_callee<'a>(
    declaration: Option<Declaration<'a>>,
) -> Option<(FileId, &'a TSType<'a>)> {
    match declaration? {
        Declaration::Function {
            file,
            function: FunctionNode::Function(function),
        } => annotation_of(&function.return_type).map(|ty| (file, ty)),
        declaration => {
            let (file, declarator, _) = declarator_of_identifier(&declaration)?;

            return_type_of_function_expression(declarator.init.as_ref()?).map(|ty| (file, ty))
        }
    }
}

fn member_of_container<'a>(container: Option<Container<'a>>, name: &str) -> Option<Member<'a>> {
    match container? {
        Container::Object(file, object) => {
            object
                .properties
                .iter()
                .find_map(|property| match property {
                    ObjectPropertyKind::ObjectProperty(property)
                        if is_named_identifier(&property.key, name) =>
                    {
                        Some(Member::Property(file, property))
                    }
                    _ => None,
                })
        }
        Container::TypeLiteral(file, literal) => member_signature_of(file, &literal.members, name),
        Container::Interface(file, interface) => {
            member_signature_of(file, &interface.body.body, name)
        }
        Container::Class(file, class) => class.body.body.iter().find_map(|element| match element {
            ClassElement::MethodDefinition(method)
                if method.kind != MethodDefinitionKind::Constructor
                    && is_named_identifier(&method.key, name) =>
            {
                Some(Member::Method(file, method))
            }
            ClassElement::PropertyDefinition(property)
                if is_named_identifier(&property.key, name) =>
            {
                Some(Member::Field(
                    file,
                    annotation_of(&property.type_annotation),
                    property.value.as_ref(),
                ))
            }
            ClassElement::AccessorProperty(property)
                if is_named_identifier(&property.key, name) =>
            {
                Some(Member::Field(
                    file,
                    annotation_of(&property.type_annotation),
                    property.value.as_ref(),
                ))
            }
            _ => None,
        }),
    }
}

fn member_signature_of<'a>(
    file: FileId,
    signatures: &'a [TSSignature<'a>],
    name: &str,
) -> Option<Member<'a>> {
    signatures.iter().find_map(|signature| {
        let named = match signature {
            TSSignature::TSPropertySignature(property) => is_named_identifier(&property.key, name),
            TSSignature::TSMethodSignature(method) => is_named_identifier(&method.key, name),
            _ => false,
        };

        named.then_some(Member::Signature(file, signature))
    })
}

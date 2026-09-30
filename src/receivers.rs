use oxc_ast::ast::{
    ArrowFunctionExpression, Class, ClassElement, Expression, Function, IdentifierReference,
    MemberExpression, MethodDefinitionKind, ObjectExpression, ObjectPropertyKind, PropertyKey,
    ReturnStatement, TSType,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_syntax::scope::ScopeFlags;

use crate::declarations::{element_name_of, is_module_file, Declaration, Declarations};
use crate::declared_types::{declarator_of_identifier, formal_parameter_of_identifier};
use crate::project::{FileId, Project};
use crate::syntax::{member_name_of, unwrap, unwrap_to_cast};
use oxc_span::GetSpan;

const MAXIMUM_BASE_CLASSES: usize = 32;
const MAXIMUM_ALIASES: usize = 8;

/// Whether a function body returns a value, outside the functions nested in it.
#[derive(Default)]
struct ValueReturns {
    found: bool,
}

impl<'a> Visit<'a> for ValueReturns {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _arrow: &ArrowFunctionExpression<'a>) {}

    fn visit_return_statement(&mut self, statement: &ReturnStatement<'a>) {
        self.found |= statement.argument.is_some();
    }
}

/// Whether the constructor `class` declares returns a value: ECMA-262 §10.2.2 [[Construct]]
/// then yields that value when it is an object, in place of the instance the class built.
fn constructor_returns_value(class: &Class<'_>) -> bool {
    class.body.body.iter().any(|element| match element {
        ClassElement::MethodDefinition(method)
            if method.kind == MethodDefinitionKind::Constructor =>
        {
            let mut returns = ValueReturns::default();

            if let Some(body) = &method.value.body {
                returns.visit_function_body(body);
            }

            returns.found
        }
        _ => false,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Placement {
    Static,
    Instance,
    Either,
}

impl<'a> Declarations<'a> {
    pub fn member_of_receiver(
        &self,
        project: &Project<'a>,
        file: FileId,
        callee: &'a MemberExpression<'a>,
    ) -> Option<Declaration<'a>> {
        let name = member_name_of(callee)?;
        let object = unwrap_to_cast(callee.object());

        if let Expression::ThisExpression(_) = object {
            let Some(ThisOwner::Class {
                file: target,
                class,
                placement,
            }) = this_owner_of(project, file, member_node_id_of(callee))
            else {
                return None;
            };

            if self.is_member_first_declared_by_interface(project, target, class, &name) {
                return None;
            }

            return self.inherited_member_of(project, target, class, &name, placement);
        }

        if let Expression::NewExpression(new) = object {
            let (target, class) =
                self.class_of_expression(project, file, unwrap_to_cast(&new.callee))?;

            return self.inherited_member_of(project, target, class, &name, Placement::Instance);
        }

        let cast = match object {
            Expression::TSAsExpression(cast) => Some(&cast.type_annotation),
            Expression::TSTypeAssertion(cast) => Some(&cast.type_annotation),
            _ => None,
        };

        if let Some(cast) = cast {
            let (class_file, class) = self.class_of_type(project, file, cast)?;

            return self.inherited_member_of(
                project,
                class_file,
                class,
                &name,
                Placement::Instance,
            );
        }

        let Expression::Identifier(reference) = object else {
            return None;
        };

        if let Some((target, class)) = self.class_of_reference(project, file, reference) {
            return self.inherited_member_of(project, target, class, &name, Placement::Static);
        }

        let declaration = self.of_reference(project, file, reference)?;

        match declaration {
            Declaration::Namespace { file: target } => {
                return self.of_export(project, target, &name).into_iter().next();
            }
            Declaration::External => return Some(Declaration::External),
            _ => {}
        }

        if let Some((target, annotated)) = annotation_of(&declaration) {
            let (class_file, class) = self.class_of_type(project, target, annotated)?;

            return self.inherited_member_of(
                project,
                class_file,
                class,
                &name,
                Placement::Instance,
            );
        }

        let (target, declarator, constant) = declarator_of_identifier(&declaration)?;

        if !constant {
            return None;
        }

        match unwrap_to_cast(declarator.init.as_ref()?) {
            Expression::NewExpression(new) => {
                let (class_file, class) =
                    self.class_of_expression(project, target, unwrap_to_cast(&new.callee))?;

                self.inherited_member_of(project, class_file, class, &name, Placement::Instance)
            }
            Expression::ObjectExpression(object) => {
                let mut found = None;

                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::SpreadProperty(_) => found = None,
                        ObjectPropertyKind::ObjectProperty(property) => {
                            let named = !property.computed
                                && match &property.key {
                                    PropertyKey::StaticIdentifier(identifier) => {
                                        identifier.name == name.as_str()
                                    }
                                    PropertyKey::StringLiteral(literal) => {
                                        literal.value == name.as_str()
                                    }
                                    _ => false,
                                };

                            if named {
                                found = matches!(
                                    unwrap(&property.value),
                                    Expression::FunctionExpression(_)
                                        | Expression::ArrowFunctionExpression(_)
                                )
                                .then_some(Declaration::Property {
                                    file: target,
                                    property,
                                });
                            }
                        }
                    }
                }

                found
            }
            _ => None,
        }
    }

    /// Whether `member` reads exactly the class element `declaration` names on every value its
    /// receiver can hold. A declared type is structural (§2.5), so a conforming object literal or
    /// a subclass that redeclares the field can stand behind a receiver typed by the class; the
    /// element is exact only when the receiver is a construction of a known class, the class
    /// itself, `this` inside a class nothing can extend, or when the element is private, which
    /// no conforming value or subclass can redeclare. `this` in an exported class is the one
    /// unsound exception left open (see `is_exported_class`).
    pub(crate) fn is_exact_member(
        &self,
        project: &Project<'a>,
        file: FileId,
        member: &'a MemberExpression<'a>,
        declaration: &Declaration<'a>,
    ) -> bool {
        let Declaration::Member { element, .. } = *declaration else {
            return true;
        };

        if matches!(member, MemberExpression::PrivateFieldExpression(_)) {
            return true;
        }

        let object = unwrap_to_cast(member.object());
        let cast = matches!(
            object,
            Expression::TSAsExpression(_) | Expression::TSTypeAssertion(_)
        );

        if !cast && is_private_element(element) {
            return true;
        }

        let Some(name) = member_name_of(member) else {
            return false;
        };
        let exact = match object {
            Expression::ThisExpression(this) => {
                match this_owner_of(project, file, this.node_id()) {
                    Some(ThisOwner::Class {
                        file: target,
                        class,
                        placement: placement @ (Placement::Instance | Placement::Static),
                    }) if self.is_closed_class(project, target, class)
                        || is_exported_class(project, target, class) =>
                    {
                        Some((target, class, placement))
                    }
                    _ => None,
                }
            }
            Expression::NewExpression(new) => self
                .exact_class_of(project, file, unwrap_to_cast(&new.callee))
                .map(|(target, class)| (target, class, Placement::Instance)),
            Expression::Identifier(reference) => match self.exact_class_of(project, file, object) {
                Some((target, class)) => Some((target, class, Placement::Static)),
                None => self.constructed_class_of(project, file, reference),
            },
            _ => None,
        };

        exact.is_some_and(|(target, class, placement)| {
            (placement != Placement::Instance || self.constructs_itself(project, target, class))
                && matches!(
                    self.inherited_member_of(project, target, class, &name, placement),
                    Some(Declaration::Member { element: found, .. }) if std::ptr::eq(found, element)
                )
        })
    }

    /// Whether constructing `class` yields the instance it builds: neither its constructor nor
    /// any base constructor returns a value, since `new` yields a returned object in place of the
    /// instance and `super()` binds it as the derived class's `this`. An unresolved base may
    /// return anything.
    fn constructs_itself(&self, project: &Project<'a>, file: FileId, class: &'a Class<'a>) -> bool {
        let mut current = (file, class);

        for _ in 0..MAXIMUM_BASE_CLASSES {
            let (file, class) = current;

            if constructor_returns_value(class) {
                return false;
            }

            if class.heritage.is_none() {
                return true;
            }

            match self.base_class_of(project, file, class) {
                Some(base) => current = base,
                None => return false,
            }
        }

        false
    }

    /// The class a constant binding holds an instance of: `const x = new C()`.
    fn constructed_class_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> Option<(FileId, &'a Class<'a>, Placement)> {
        let declaration = self.of_reference(project, file, reference)?;
        let (target, declarator, constant) = declarator_of_identifier(&declaration)?;

        if !constant {
            return None;
        }

        let Expression::NewExpression(new) = unwrap_to_cast(declarator.init.as_ref()?) else {
            return None;
        };

        self.exact_class_of(project, target, unwrap_to_cast(&new.callee))
            .map(|(target, class)| (target, class, Placement::Instance))
    }

    /// The class an identifier denotes on every evaluation: a class binding nothing writes.
    fn exact_class_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<(FileId, &'a Class<'a>)> {
        let Expression::Identifier(reference) = expression else {
            return None;
        };
        let found = self.class_of_reference(project, file, reference)?;
        let written = self
            .binding_of_reference(project, file, reference)
            .is_none_or(|binding| !self.is_write_free(project, binding));

        (!written).then_some(found)
    }

    /// A class nothing can extend or reach as a value: a module-scoped declaration that is not
    /// exported and whose every value reference constructs it, in a file without direct eval.
    fn is_closed_class(&self, project: &Project<'a>, file: FileId, class: &'a Class<'a>) -> bool {
        let source = project.file(file);
        let semantic = &source.semantic;
        let nodes = semantic.nodes();
        let scoping = semantic.scoping();

        if !class.is_declaration()
            || class.declare
            || !is_module_file(source)
            || crate::values::has_direct_eval(semantic)
            || is_exported_class(project, file, class)
        {
            return false;
        }

        let Some(symbol) = class.id.as_ref().and_then(|id| id.symbol_id.get()) else {
            return false;
        };

        scoping
            .get_resolved_references(symbol)
            .filter(|reference| {
                !reference.flags().is_type() && !reference.flags().is_value_as_type()
            })
            .all(|reference| {
                let node = reference.node_id();

                matches!(
                    nodes.parent_kind(node),
                    AstKind::NewExpression(new) if new.callee.span() == nodes.kind(node).span()
                )
            })
    }

    fn inherited_member_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
        name: &str,
        placement: Placement,
    ) -> Option<Declaration<'a>> {
        let mut current = (file, class);

        for _ in 0..MAXIMUM_BASE_CLASSES {
            let (file, class) = current;
            let element = class.body.body.iter().find(|element| {
                let placed = match placement {
                    Placement::Static => is_static_element(element),
                    Placement::Instance => !is_static_element(element),
                    Placement::Either => true,
                };

                placed && element_name_of(element).as_deref() == Some(name)
            });

            if let Some(element) = element {
                return Some(Declaration::Member {
                    file,
                    class,
                    element,
                });
            }

            current = self.base_class_of(project, file, class)?;
        }

        None
    }

    pub(crate) fn base_class_of(
        &self,
        project: &Project<'a>,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Option<(FileId, &'a Class<'a>)> {
        let heritage = class.heritage.as_ref()?;
        let Expression::Identifier(base) = unwrap_to_cast(&heritage.expression) else {
            return None;
        };

        self.class_of_reference(project, file, base)
    }

    pub(crate) fn class_of_type(
        &self,
        project: &Project<'a>,
        file: FileId,
        annotated: &'a TSType<'a>,
    ) -> Option<(FileId, &'a Class<'a>)> {
        let mut current = (file, annotated);

        for _ in 0..MAXIMUM_ALIASES {
            let (file, annotated) = current;

            current = match annotated {
                TSType::TSParenthesizedType(parenthesized) => {
                    (file, &parenthesized.type_annotation)
                }
                TSType::TSTypeReference(type_reference) => {
                    match self.of_type_name(project, file, &type_reference.type_name)? {
                        Declaration::Class { file, class } => return Some((file, class)),
                        Declaration::TypeAlias { file, declaration } => {
                            (file, &declaration.type_annotation)
                        }
                        _ => return None,
                    }
                }
                _ => return None,
            };
        }

        None
    }

    fn class_of_reference(
        &self,
        project: &Project<'a>,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> Option<(FileId, &'a Class<'a>)> {
        match self.of_reference(project, file, reference)? {
            Declaration::Class { file, class } => Some((file, class)),
            declaration => {
                let (target, declarator, constant) = declarator_of_identifier(&declaration)?;

                match (constant, unwrap_to_cast(declarator.init.as_ref()?)) {
                    (true, Expression::ClassExpression(class)) => Some((target, class)),
                    _ => None,
                }
            }
        }
    }

    pub(crate) fn class_of_expression(
        &self,
        project: &Project<'a>,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<(FileId, &'a Class<'a>)> {
        match expression {
            Expression::Identifier(reference) => self.class_of_reference(project, file, reference),
            _ => None,
        }
    }
}

pub(crate) fn annotation_of<'a>(declaration: &Declaration<'a>) -> Option<(FileId, &'a TSType<'a>)> {
    declarator_of_identifier(declaration)
        .and_then(|(target, declarator, _)| {
            declarator
                .type_annotation
                .as_ref()
                .map(|annotation| (target, &annotation.type_annotation))
        })
        .or_else(|| {
            formal_parameter_of_identifier(declaration).and_then(|(target, parameter)| {
                parameter
                    .type_annotation
                    .as_ref()
                    .map(|annotation| (target, &annotation.type_annotation))
            })
        })
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum ThisOwner<'a> {
    Class {
        file: FileId,
        class: &'a Class<'a>,
        placement: Placement,
    },
    Object {
        file: FileId,
        object: &'a ObjectExpression<'a>,
    },
}

pub(crate) fn this_owner_of<'a>(
    project: &Project<'a>,
    file: FileId,
    node: oxc_semantic::NodeId,
) -> Option<ThisOwner<'a>> {
    let nodes = project.file(file).semantic.nodes();
    let mut placement = Placement::Either;

    for ancestor in nodes.ancestors(node) {
        match ancestor.kind() {
            AstKind::Class(class) => {
                return Some(ThisOwner::Class {
                    file,
                    class,
                    placement,
                })
            }
            AstKind::Function(_) => match nodes.parent_kind(ancestor.id()) {
                AstKind::MethodDefinition(method) if placement == Placement::Either => {
                    placement = placement_of(method.r#static);
                }
                AstKind::MethodDefinition(_) => {}
                AstKind::ObjectProperty(_) if placement == Placement::Either => {
                    let property = nodes.parent_id(ancestor.id());

                    return match nodes.parent_kind(property) {
                        AstKind::ObjectExpression(object) => {
                            Some(ThisOwner::Object { file, object })
                        }
                        _ => None,
                    };
                }
                _ => return None,
            },
            AstKind::PropertyDefinition(property) if placement == Placement::Either => {
                placement = placement_of(property.r#static);
            }
            AstKind::AccessorProperty(property) if placement == Placement::Either => {
                placement = placement_of(property.r#static);
            }
            AstKind::StaticBlock(_) if placement == Placement::Either => {
                placement = Placement::Static;
            }
            _ => {}
        }
    }

    None
}

fn placement_of(is_static: bool) -> Placement {
    if is_static {
        Placement::Static
    } else {
        Placement::Instance
    }
}

fn member_node_id_of(member: &MemberExpression<'_>) -> oxc_semantic::NodeId {
    match member {
        MemberExpression::StaticMemberExpression(member) => member.node_id(),
        MemberExpression::ComputedMemberExpression(member) => member.node_id(),
        MemberExpression::PrivateFieldExpression(member) => member.node_id(),
    }
}

// G22 left open: `this` in an exported class still folds, although a subclass outside the
// analysed sources can redeclare the field, because tests/integration/constants.rs
// (declared_types_casts_and_static_placement_decide_member_constants) pins it and stays
// unchanged until Matt approves.
fn is_exported_class(project: &Project<'_>, file: FileId, class: &Class<'_>) -> bool {
    matches!(
        project
            .file(file)
            .semantic
            .nodes()
            .parent_kind(class.node_id()),
        AstKind::ExportDeclaration(_) | AstKind::ExportDefaultDeclaration(_)
    )
}

fn is_private_element(element: &ClassElement<'_>) -> bool {
    let accessibility = match element {
        ClassElement::PropertyDefinition(property) => property.accessibility,
        ClassElement::AccessorProperty(property) => property.accessibility,
        ClassElement::MethodDefinition(method) => method.accessibility,
        _ => None,
    };

    accessibility == Some(oxc_ast::ast::TSAccessibility::Private)
}

pub(crate) fn is_static_element(element: &ClassElement<'_>) -> bool {
    match element {
        ClassElement::MethodDefinition(method) => method.r#static,
        ClassElement::PropertyDefinition(property) => property.r#static,
        ClassElement::AccessorProperty(property) => property.r#static,
        _ => false,
    }
}

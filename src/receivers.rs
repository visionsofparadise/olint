use oxc_ast::ast::{
    Class, ClassElement, Expression, IdentifierReference, MemberExpression, ObjectPropertyKind,
    PropertyKey, TSType,
};
use oxc_ast::AstKind;

use crate::constants::{member_name_of, unwrap, unwrap_to_cast};
use crate::declarations::{element_name_of, Declaration, Declarations};
use crate::declared_types::{declarator_of_identifier, formal_parameter_of_identifier};
use crate::project::{FileId, Project};

const MAXIMUM_BASE_CLASSES: usize = 32;
const MAXIMUM_ALIASES: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Placement {
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
            let (target, class, placement) = class_of_this(project, file, callee)?;

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

        let annotation = declarator_of_identifier(&declaration)
            .and_then(|(target, declarator, _)| {
                declarator
                    .type_annotation
                    .as_ref()
                    .map(|annotation| (target, &annotation.type_annotation))
            })
            .or_else(|| {
                formal_parameter_of_identifier(&declaration).and_then(|(target, parameter)| {
                    parameter
                        .type_annotation
                        .as_ref()
                        .map(|annotation| (target, &annotation.type_annotation))
                })
            });

        if let Some((target, annotated)) = annotation {
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

            let heritage = class.heritage.as_ref()?;
            let Expression::Identifier(base) = unwrap_to_cast(&heritage.expression) else {
                return None;
            };

            current = self.class_of_reference(project, file, base)?;
        }

        None
    }

    fn class_of_type(
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

    fn class_of_expression(
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

fn class_of_this<'a>(
    project: &Project<'a>,
    file: FileId,
    callee: &'a MemberExpression<'a>,
) -> Option<(FileId, &'a Class<'a>, Placement)> {
    let nodes = project.file(file).semantic.nodes();
    let mut placement = Placement::Either;

    for ancestor in nodes.ancestors(member_node_id_of(callee)) {
        match ancestor.kind() {
            AstKind::Class(class) => return Some((file, class, placement)),
            AstKind::Function(_) => match nodes.parent_kind(ancestor.id()) {
                AstKind::MethodDefinition(method) if placement == Placement::Either => {
                    placement = placement_of(method.r#static);
                }
                AstKind::MethodDefinition(_) => {}
                _ => return None,
            },
            AstKind::PropertyDefinition(property) if placement == Placement::Either => {
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

fn is_static_element(element: &ClassElement<'_>) -> bool {
    match element {
        ClassElement::MethodDefinition(method) => method.r#static,
        ClassElement::PropertyDefinition(property) => property.r#static,
        ClassElement::AccessorProperty(property) => property.r#static,
        _ => false,
    }
}

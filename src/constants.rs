use oxc_ast::ast::{
    Argument, ArrowFunctionExpression, ClassElement, Expression, Function, IdentifierReference,
    MemberExpression, ReturnStatement,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_semantic::NodeId;
use oxc_syntax::scope::ScopeFlags;

use crate::analysis::Analysis;
use crate::declarations::{Declaration, FunctionNode};
use crate::declared_types::declarator_of_identifier;
use crate::project::FileId;
use crate::syntax::{member_expression_of, unwrap_to_cast};
use crate::values::{Cardinality, Primitive};

#[path = "enum_values.rs"]
mod enum_values;
pub use enum_values::{evaluate_enum, EnumInitializer};

#[derive(Default)]
struct ReturnStatements {
    nodes: Vec<NodeId>,
}

impl<'a> Visit<'a> for ReturnStatements {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _arrow: &ArrowFunctionExpression<'a>) {}

    fn visit_return_statement(&mut self, statement: &ReturnStatement<'a>) {
        self.nodes.push(statement.node_id());
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn is_numeric_constant(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        if matches!(self.known_value(file, e).value.as_deref(), Ok(Primitive::Number(value)) if value.is_finite())
        {
            return true;
        }

        let Some(member) = member_expression_of(e) else {
            return false;
        };

        if let MemberExpression::StaticMemberExpression(access) = member {
            if access.property.name == "length" {
                return self.is_constant_sized(file, &access.object);
            }
        }

        false
    }

    pub fn is_constant_sized(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        self.cardinality_of(file, e) == Cardinality::Constant
    }

    pub(crate) fn is_constant_sized_argument(
        &mut self,
        file: FileId,
        argument: &'a Argument<'a>,
    ) -> bool {
        match argument {
            Argument::SpreadElement(_) => false,
            _ => argument
                .as_expression()
                .is_some_and(|argument| self.is_constant_sized(file, argument)),
        }
    }

    pub(crate) fn is_closed_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> bool {
        match argument {
            Argument::SpreadElement(_) => false,
            _ => argument
                .as_expression()
                .is_some_and(|argument| self.is_closed(file, argument)),
        }
    }

    pub(crate) fn is_constant_sized_reference(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> bool {
        self.declarations
            .of_reference(self.project, file, reference)
            .is_some_and(|declaration| self.declaration_is_constant_sized(declaration))
    }

    pub fn returns_constant_sized(&mut self, file: FileId, function: FunctionNode<'a>) -> bool {
        let body = match function {
            FunctionNode::Function(function) => match &function.body {
                Some(body) => body,
                None => return false,
            },
            FunctionNode::Arrow(arrow) => match arrow.get_expression() {
                Some(expression) => return self.is_constant_sized(file, expression),
                None => match arrow.get_function_body() {
                    Some(body) => body,
                    None => return false,
                },
            },
            FunctionNode::Construction(_) => return false,
        };
        let mut statements = ReturnStatements::default();

        statements.visit_function_body(body);

        let nodes = self.project.file(file).semantic.nodes();
        let returns: Vec<&'a ReturnStatement<'a>> = statements
            .nodes
            .iter()
            .filter_map(|node| match nodes.kind(*node) {
                AstKind::ReturnStatement(statement) => Some(statement),
                _ => None,
            })
            .collect();
        let mut constant = true;

        for statement in &returns {
            let returned = match &statement.argument {
                Some(argument) => self.is_constant_sized(file, argument),
                None => false,
            };

            if !returned {
                constant = false;
            }
        }

        constant && !returns.is_empty()
    }

    pub fn is_enum_object(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let declaration = match e {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            Expression::StaticMemberExpression(member) => match &member.object {
                Expression::Identifier(object) => {
                    match self.declarations.of_reference(self.project, file, object) {
                        Some(Declaration::Namespace { file: target }) => self
                            .declarations
                            .of_export(self.project, target, member.property.name.as_str())
                            .into_iter()
                            .next(),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        };

        match declaration {
            Some(declaration @ Declaration::Enum { .. }) => {
                self.declaration_has_constant_keys(declaration)
            }
            _ => false,
        }
    }

    pub(crate) fn declaration_of_access(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<Declaration<'a>> {
        self.declaration_of_access_at(file, member, 0)
    }

    fn declaration_of_access_at(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
        depth: usize,
    ) -> Option<Declaration<'a>> {
        if depth >= 64 {
            return None;
        }

        let (object, name) = match member {
            MemberExpression::StaticMemberExpression(access) => (
                &access.object,
                Some(std::borrow::Cow::Borrowed(access.property.name.as_str())),
            ),
            MemberExpression::ComputedMemberExpression(access) => (
                &access.object,
                self.known_key(file, &access.expression)
                    .ok()
                    .map(std::borrow::Cow::Owned),
            ),
            MemberExpression::PrivateFieldExpression(_) => {
                return self
                    .declarations
                    .member_of_receiver(self.project, file, member)
            }
        };

        if let Some(name) = name {
            let object = unwrap_to_cast(object);
            let enumeration = match object {
                Expression::Identifier(reference) => {
                    self.declarations
                        .of_reference(self.project, file, reference)
                }
                _ => member_expression_of(object)
                    .and_then(|inner| self.declaration_of_access_at(file, inner, depth + 1)),
            };

            if let Some(Declaration::Enum {
                file: target,
                declaration,
            }) = enumeration
            {
                let semantic = &self.project.file(target).semantic;
                let symbol = semantic
                    .scoping()
                    .get_binding(declaration.body.scope_id.get()?, name.as_ref().into())?;

                return match semantic
                    .nodes()
                    .kind(semantic.scoping().symbol_declaration(symbol))
                {
                    AstKind::TSEnumMember(member) => Some(Declaration::EnumMember {
                        file: target,
                        member,
                    }),
                    _ => None,
                };
            }
        }

        self.declarations
            .member_of_receiver(self.project, file, member)
    }
}

pub(crate) fn constant_initializer_of<'a>(
    declaration: Declaration<'a>,
) -> Option<(FileId, &'a Expression<'a>)> {
    if let Some((file, declarator, constant)) = declarator_of_identifier(&declaration) {
        return match (&declarator.init, constant) {
            (Some(initializer), true) => Some((file, initializer)),
            _ => None,
        };
    }

    match declaration {
        Declaration::Member {
            file,
            element: ClassElement::PropertyDefinition(property),
            ..
        } if property.readonly => property.value.as_ref().map(|value| (file, value)),
        _ => None,
    }
}

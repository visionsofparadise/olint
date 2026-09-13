use oxc_ast::ast::{
    Argument, ArrowFunctionExpression, AssignmentTarget, CallExpression, ClassElement, Expression,
    Function, IdentifierReference, MemberExpression, ReturnStatement, SimpleAssignmentTarget,
    TSEnumMemberName,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_semantic::NodeId;
use oxc_syntax::operator::UnaryOperator;
use oxc_syntax::scope::ScopeFlags;

use crate::analysis::Analysis;
use crate::declarations::{Declaration, FunctionNode};
use crate::declared_types::declarator_of_identifier;
use crate::project::FileId;
use crate::tables::{DERIVED_METHODS, OBJECT_KEYED, TYPED_ARRAYS};

pub fn unwrap<'a>(e: &'a Expression<'a>) -> &'a Expression<'a> {
    match e {
        Expression::ParenthesizedExpression(inner) => unwrap(&inner.expression),
        Expression::TSAsExpression(inner) => unwrap(&inner.expression),
        Expression::TSSatisfiesExpression(inner) => unwrap(&inner.expression),
        Expression::TSNonNullExpression(inner) => unwrap(&inner.expression),
        Expression::TSTypeAssertion(inner) => unwrap(&inner.expression),
        _ => e,
    }
}

pub(crate) fn call_of<'a>(e: &'a Expression<'a>) -> Option<&'a CallExpression<'a>> {
    match e {
        Expression::CallExpression(call) => Some(call),
        Expression::ChainExpression(chain) => match &chain.expression {
            oxc_ast::ast::ChainElement::CallExpression(call) => Some(call),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn member_expression_of<'a>(e: &'a Expression<'a>) -> Option<&'a MemberExpression<'a>> {
    match e {
        Expression::ChainExpression(chain) => chain.expression.as_member_expression(),
        _ => e.as_member_expression(),
    }
}

pub(crate) fn member_name_of(member: &MemberExpression<'_>) -> Option<String> {
    match member {
        MemberExpression::StaticMemberExpression(member) => Some(member.property.name.to_string()),
        MemberExpression::PrivateFieldExpression(member) => Some(format!("#{}", member.field.name)),
        MemberExpression::ComputedMemberExpression(_) => None,
    }
}

fn argument_expression_of<'a>(argument: Option<&'a Argument<'a>>) -> Option<&'a Expression<'a>> {
    argument?.as_expression()
}

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
        let e = unwrap(e);

        match e {
            Expression::NumericLiteral(_) => return true,
            Expression::UnaryExpression(unary)
                if matches!(
                    unary.operator,
                    UnaryOperator::UnaryPlus
                        | UnaryOperator::UnaryNegation
                        | UnaryOperator::LogicalNot
                        | UnaryOperator::BitwiseNot
                ) =>
            {
                return self.is_numeric_constant(file, &unary.argument);
            }
            Expression::UpdateExpression(update) if update.prefix => {
                return match &update.argument {
                    SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                        self.is_numeric_identifier(file, reference)
                    }
                    _ => false,
                };
            }
            Expression::BinaryExpression(binary) => {
                return self.is_numeric_constant(file, &binary.left)
                    && self.is_numeric_constant(file, &binary.right);
            }
            Expression::LogicalExpression(logical) => {
                return self.is_numeric_constant(file, &logical.left)
                    && self.is_numeric_constant(file, &logical.right);
            }
            Expression::SequenceExpression(sequence) => {
                return sequence
                    .expressions
                    .iter()
                    .all(|expression| self.is_numeric_constant(file, expression));
            }
            Expression::AssignmentExpression(assignment) => {
                return match &assignment.left {
                    AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                        self.is_numeric_identifier(file, reference)
                            && self.is_numeric_constant(file, &assignment.right)
                    }
                    _ => false,
                };
            }
            Expression::Identifier(reference) => {
                return self.is_numeric_identifier(file, reference)
            }
            _ => {}
        }

        let Some(member) = member_expression_of(e) else {
            return false;
        };

        if let MemberExpression::StaticMemberExpression(access) = member {
            if access.property.name == "length" {
                return self.is_constant_sized(file, &access.object);
            }
        }

        let declaration = self.declaration_of_access(file, member);

        self.is_numeric_declaration(declaration)
    }

    pub fn is_constant_sized(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let e = unwrap(e);

        match e {
            Expression::ArrayExpression(array) => {
                return array.elements.iter().all(|element| match element {
                    oxc_ast::ast::ArrayExpressionElement::SpreadElement(spread) => {
                        self.is_constant_sized(file, &spread.argument)
                    }
                    _ => true,
                });
            }
            Expression::ConditionalExpression(conditional) => {
                return self.is_constant_sized(file, &conditional.consequent)
                    && self.is_constant_sized(file, &conditional.alternate);
            }
            _ => {}
        }

        if let Some(call) = call_of(e) {
            if let Expression::StaticMemberExpression(callee) = &call.callee {
                let method = callee.property.name.as_str();

                if DERIVED_METHODS.contains(&method) && self.is_constant_sized(file, &callee.object)
                {
                    if method == "flatMap" {
                        return match argument_expression_of(call.arguments.first()) {
                            Some(Expression::FunctionExpression(function)) => {
                                self.returns_constant_sized(file, FunctionNode::Function(function))
                            }
                            Some(Expression::ArrowFunctionExpression(arrow)) => {
                                self.returns_constant_sized(file, FunctionNode::Arrow(arrow))
                            }
                            _ => false,
                        };
                    }

                    if method == "concat" {
                        return call.arguments.iter().all(|argument| {
                            argument
                                .as_expression()
                                .is_some_and(|argument| self.is_constant_sized(file, argument))
                        });
                    }

                    return true;
                }
            }
        }

        match e {
            Expression::StringLiteral(_) => return true,
            Expression::TemplateLiteral(template) if template.expressions.is_empty() => {
                return true
            }
            Expression::NewExpression(new) => {
                if let Expression::Identifier(callee) = &new.callee {
                    let name = callee.name.as_str();

                    if (TYPED_ARRAYS.contains(&name) || name == "Array")
                        && new.arguments.len() == 1
                        && argument_expression_of(new.arguments.first())
                            .is_some_and(|argument| self.is_numeric_constant(file, argument))
                    {
                        return true;
                    }
                }
            }
            _ => {}
        }

        let declaration = match e {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            _ => {
                member_expression_of(e).and_then(|member| self.declaration_of_access(file, member))
            }
        };

        if let Some(declaration) = declaration {
            if let Some((target, initializer)) = constant_initializer_of(declaration) {
                if self.is_constant_sized(target, initializer) {
                    return true;
                }
            }
        }

        if let Some(call) = call_of(e) {
            if let Expression::StaticMemberExpression(callee) = &call.callee {
                let keyed = matches!(&callee.object, Expression::Identifier(object) if object.name == "Object")
                    && OBJECT_KEYED.contains(&callee.property.name.as_str());

                if keyed {
                    if let Some(argument) = call.arguments.first() {
                        let Some(argument) = argument.as_expression() else {
                            return false;
                        };

                        return self.is_enum_object(file, argument)
                            || self.is_closed(file, argument)
                            || self.is_constant_sized(file, argument);
                    }
                }
            }
        }

        self.is_tuple(file, e)
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

    pub fn is_enum_object(&self, file: FileId, e: &'a Expression<'a>) -> bool {
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

        matches!(declaration, Some(Declaration::Enum { .. }))
    }

    fn is_numeric_identifier(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> bool {
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference);

        self.is_numeric_declaration(declaration)
    }

    fn is_numeric_declaration(&mut self, declaration: Option<Declaration<'a>>) -> bool {
        let Some(declaration) = declaration else {
            return false;
        };

        if let Declaration::EnumMember { .. } = declaration {
            return true;
        }

        match constant_initializer_of(declaration) {
            Some((target, initializer)) => self.is_numeric_constant(target, initializer),
            None => false,
        }
    }

    pub(crate) fn declaration_of_access(
        &self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<Declaration<'a>> {
        if let MemberExpression::StaticMemberExpression(access) = member {
            let object = unwrap(&access.object);
            let enumeration = match object {
                Expression::Identifier(reference) => {
                    self.declarations
                        .of_reference(self.project, file, reference)
                }
                _ => member_expression_of(object)
                    .and_then(|inner| self.declaration_of_access(file, inner)),
            };

            if let Some(Declaration::Enum {
                file: target,
                declaration,
            }) = enumeration
            {
                let name = access.property.name.as_str();

                return declaration
                    .body
                    .members
                    .iter()
                    .find(|enum_member| match &enum_member.id {
                        TSEnumMemberName::Identifier(identifier) => identifier.name == name,
                        TSEnumMemberName::String(literal)
                        | TSEnumMemberName::ComputedString(literal) => literal.value == name,
                        TSEnumMemberName::ComputedTemplateString(_) => false,
                    })
                    .map(|member| Declaration::EnumMember {
                        file: target,
                        member,
                    });
            }
        }

        self.declarations
            .member_of_receiver(self.project, file, member)
    }
}

fn constant_initializer_of<'a>(
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

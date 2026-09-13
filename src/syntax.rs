use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, FunctionBody, IdentifierReference,
    MemberExpression, Statement, TSType, TSTypeName,
};
use oxc_ast::AstKind;

use crate::declarations::FunctionNode;

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

pub(crate) fn unwrap_to_cast<'a>(e: &'a Expression<'a>) -> &'a Expression<'a> {
    match e {
        Expression::ParenthesizedExpression(inner) => unwrap_to_cast(&inner.expression),
        Expression::TSSatisfiesExpression(inner) => unwrap_to_cast(&inner.expression),
        Expression::TSNonNullExpression(inner) => unwrap_to_cast(&inner.expression),
        Expression::TSAsExpression(inner) if is_const_type(&inner.type_annotation) => {
            unwrap_to_cast(&inner.expression)
        }
        Expression::TSTypeAssertion(inner) if is_const_type(&inner.type_annotation) => {
            unwrap_to_cast(&inner.expression)
        }
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

#[derive(Clone, Copy)]
pub(crate) enum Root<'a> {
    Statement(&'a Statement<'a>),
    Expression(&'a Expression<'a>),
    Body(&'a FunctionBody<'a>),
}

pub(crate) fn body_root_of<'a>(function: FunctionNode<'a>) -> Option<Root<'a>> {
    match function {
        FunctionNode::Function(function) => function.body.as_deref().map(Root::Body),
        FunctionNode::Arrow(arrow) => Some(match &arrow.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Root::Body(body),
            body => Root::Expression(
                body.as_expression()
                    .expect("an arrow body is a block or an expression"),
            ),
        }),
    }
}

pub(crate) fn identifier_of<'a>(e: &'a Expression<'a>) -> Option<&'a IdentifierReference<'a>> {
    match e {
        Expression::Identifier(reference) => Some(reference),
        _ => None,
    }
}

pub(crate) fn collapsed_text_of(text: &str) -> String {
    let mut collapsed = String::with_capacity(text.len());
    let mut in_space = false;

    for character in text.chars() {
        if is_space(character) {
            if !in_space {
                collapsed.push(' ');
            }

            in_space = true;
        } else {
            collapsed.push(character);

            in_space = false;
        }
    }

    collapsed
}

pub(crate) fn compact_text_of(text: &str) -> String {
    text.chars()
        .filter(|character| !is_space(*character))
        .collect()
}

pub(crate) fn is_space(character: char) -> bool {
    (character.is_whitespace() && character != '\u{85}') || character == '\u{feff}'
}

pub fn is_iteration_kind(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::ForStatement(_)
            | AstKind::ForInStatement(_)
            | AstKind::ForOfStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
    )
}

pub(crate) fn loop_body_of<'a>(kind: AstKind<'a>) -> Option<&'a Statement<'a>> {
    match kind {
        AstKind::ForStatement(statement) => Some(&statement.body),
        AstKind::ForInStatement(statement) => Some(&statement.body),
        AstKind::ForOfStatement(statement) => Some(&statement.body),
        AstKind::WhileStatement(statement) => Some(&statement.body),
        AstKind::DoWhileStatement(statement) => Some(&statement.body),
        _ => None,
    }
}

pub(crate) fn is_identifier_pattern(pattern: &BindingPattern<'_>) -> bool {
    matches!(pattern, BindingPattern::BindingIdentifier(_))
}

pub(crate) fn is_const_type(ty: &TSType<'_>) -> bool {
    matches!(ty, TSType::TSTypeReference(reference) if matches!(&reference.type_name, TSTypeName::IdentifierReference(name) if name.name == "const"))
}

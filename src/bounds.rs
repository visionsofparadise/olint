use oxc_ast::ast::{
    AssignmentTarget, BindingPattern, Expression, ForStatement, ForStatementInit, Statement,
    StaticMemberExpression,
};
use oxc_ast::AstKind;
use oxc_ast_visit::Visit;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, UnaryOperator};

use crate::analysis::Analysis;
use crate::budgets::{is_less, sides_of, Subtree};
use crate::cost::Cost;
use crate::directives::PerfTag;
use crate::project::FileId;
use crate::syntax::{
    call_of, collapsed_text_of, compact_text_of, identifier_of, is_iteration_kind, loop_body_of,
    unwrap, Root,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bound {
    pub factor: Cost,
    pub why: Option<&'static str>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exit {
    Return,
    Throw,
    Break,
}

impl Exit {
    pub fn text(self) -> &'static str {
        match self {
            Exit::Return => "return",
            Exit::Throw => "throw",
            Exit::Break => "break",
        }
    }
}

pub fn loop_label(kind: AstKind<'_>) -> &'static str {
    match kind {
        AstKind::ForOfStatement(_) => "for-of",
        AstKind::ForInStatement(_) => "for-in",
        AstKind::ForStatement(_) => "for",
        AstKind::WhileStatement(_) => "while",
        _ => "do-while",
    }
}

pub fn short(text: &str) -> String {
    let collapsed = collapsed_text_of(text);

    if utf16_length_of(&collapsed) <= 40 {
        return collapsed;
    }

    let mut kept = String::new();
    let mut units = 0;

    for character in collapsed.chars() {
        units += character.len_utf16();

        if units > 37 {
            if units == 38 && character.len_utf16() == 2 {
                kept.push(char::REPLACEMENT_CHARACTER);
            }

            break;
        }

        kept.push(character);
    }

    kept.push_str("...");

    kept
}

pub(crate) fn utf16_length_of(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

fn is_multiplicative_operator(operator: BinaryOperator) -> bool {
    matches!(
        operator,
        BinaryOperator::Multiplication
            | BinaryOperator::Division
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::ShiftRightZeroFill
    )
}

fn is_multiplicative_assignment(operator: AssignmentOperator) -> bool {
    matches!(
        operator,
        AssignmentOperator::Multiplication
            | AssignmentOperator::Division
            | AssignmentOperator::ShiftLeft
            | AssignmentOperator::ShiftRight
            | AssignmentOperator::ShiftRightZeroFill
    )
}

enum AssignmentWrite<'a> {
    Geometric,
    Assign(&'a Expression<'a>),
    Other,
}

struct LoopVariable<'a> {
    name: &'a str,
    init: &'a Expression<'a>,
}

#[derive(Default)]
struct Names {
    names: Vec<String>,
}

impl<'a> Visit<'a> for Names {
    fn visit_identifier_reference(&mut self, reference: &oxc_ast::ast::IdentifierReference<'a>) {
        self.add(reference.name.as_str());
    }

    fn visit_binding_identifier(&mut self, identifier: &oxc_ast::ast::BindingIdentifier<'a>) {
        self.add(identifier.name.as_str());
    }

    fn visit_identifier_name(&mut self, identifier: &oxc_ast::ast::IdentifierName<'a>) {
        self.add(identifier.name.as_str());
    }

    fn visit_static_member_expression(&mut self, member: &StaticMemberExpression<'a>) {
        self.visit_expression(&member.object);
    }
}

impl Names {
    fn add(&mut self, name: &str) {
        if !self.names.iter().any(|known| known == name) {
            self.names.push(name.to_string());
        }
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn ends_in(&self, _file: FileId, statement: &'a Statement<'a>) -> Option<Exit> {
        exit_of(statement)
    }

    pub fn inside_loop(&self, file: FileId, node: NodeId) -> bool {
        let nodes = self.project.file(file).semantic.nodes();

        for ancestor in nodes.ancestors(node) {
            let kind = ancestor.kind();

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                return false;
            }

            if is_iteration_kind(&kind) {
                return true;
            }
        }

        false
    }

    pub fn bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Bound {
        let bound = self.inner_bound_of(file, loop_kind);

        if self.bound_seen.insert((file, loop_kind.node_id())) {
            let reason = match bound.why {
                Some(why) => why,
                None if bound.factor.log > 0 => "log",
                None => "N",
            };

            self.stats
                .count(&format!("loop {}: {}", loop_label(loop_kind), reason));
        }

        bound
    }

    fn inner_bound_of(&mut self, file: FileId, loop_kind: AstKind<'a>) -> Bound {
        if self.perf_tags(file, loop_kind).contains(&PerfTag::Bounded) {
            return constant_bound_of("@perf bounded");
        }

        let Some(body) = loop_body_of(loop_kind) else {
            return linear_bound_of();
        };

        if self.ends_in(file, body).is_some() {
            return constant_bound_of("single iteration");
        }

        match loop_kind {
            AstKind::ForOfStatement(statement) => {
                if self.is_constant_sized(file, &statement.right) {
                    constant_bound_of("constant collection")
                } else if self.is_share_sized(file, &statement.right) {
                    constant_bound_of("share of budget")
                } else {
                    linear_bound_of()
                }
            }
            AstKind::ForInStatement(statement) => {
                if self.is_constant_sized(file, &statement.right)
                    || self.is_closed(file, &statement.right)
                {
                    constant_bound_of("closed object type")
                } else {
                    linear_bound_of()
                }
            }
            AstKind::ForStatement(statement) => self.bound_of_for(file, statement),
            AstKind::WhileStatement(statement) => {
                self.bound_of_while(file, &statement.test, &statement.body)
            }
            AstKind::DoWhileStatement(statement) => {
                self.bound_of_while(file, &statement.test, &statement.body)
            }
            _ => linear_bound_of(),
        }
    }

    fn is_same_text(&self, file: FileId, left: &Expression<'_>, right: &Expression<'_>) -> bool {
        compact_text_of(self.text_of(file, left.span()))
            == compact_text_of(self.text_of(file, right.span()))
    }

    fn bound_of_for(&mut self, file: FileId, statement: &'a ForStatement<'a>) -> Bound {
        let variable = loop_variable_of(statement);

        if let Some(variable) = &variable {
            if self.is_multiplicative_update(file, statement.update.as_ref(), variable.name) {
                return Bound {
                    factor: Cost::LOG,
                    why: Some("geometric step"),
                };
            }
        }

        let condition = statement.test.as_ref().map(unwrap);

        if let (Some(variable), Some(Expression::BinaryExpression(binary))) = (&variable, condition)
        {
            let counter = identifier_of(unwrap(&binary.left));

            if is_less(binary.operator)
                && counter.is_some_and(|counter| counter.name == variable.name)
            {
                let bound = unwrap(&binary.right);

                if self.is_share_sized(file, bound) {
                    return constant_bound_of("share of budget");
                }

                if let Expression::BinaryExpression(sum) = bound {
                    if sum.operator == BinaryOperator::Addition
                        && ((self.is_same_text(file, &sum.left, variable.init)
                            && self.is_share_sized(file, &sum.right))
                            || (self.is_same_text(file, &sum.right, variable.init)
                                && self.is_share_sized(file, &sum.left)))
                    {
                        return constant_bound_of("share of budget");
                    }
                }
            }
        }

        if let Some(sides) = condition.and_then(sides_of) {
            let unwrapped = [sides.left.map(unwrap), Some(unwrap(sides.right))];

            for side in unwrapped.into_iter().flatten() {
                if self.is_numeric_constant(file, side) {
                    return constant_bound_of("constant bound");
                }
            }

            if let Some(variable) = &variable {
                let bound = unwrapped.into_iter().find(|side| {
                    !side
                        .and_then(identifier_of)
                        .is_some_and(|identifier| identifier.name == variable.name)
                });

                if let Some(Some(Expression::BinaryExpression(offset))) = bound {
                    if matches!(
                        offset.operator,
                        BinaryOperator::Addition | BinaryOperator::Subtraction
                    ) {
                        let left = unwrap(&offset.left);
                        let right = unwrap(&offset.right);

                        if (self.is_same_text(file, left, variable.init)
                            && self.is_numeric_constant(file, right))
                            || (self.is_same_text(file, right, variable.init)
                                && self.is_numeric_constant(file, left))
                        {
                            return constant_bound_of("constant offset from start");
                        }
                    }
                }
            }
        }

        linear_bound_of()
    }

    fn is_geometric(&mut self, file: FileId, value: &'a Expression<'a>, name: &str) -> bool {
        let value = unwrap(value);

        if let Expression::BinaryExpression(binary) = value {
            if is_multiplicative_operator(binary.operator) {
                return identifier_of(unwrap(&binary.left))
                    .is_some_and(|identifier| identifier.name == name)
                    && self.is_numeric_constant(file, &binary.right);
            }
        }

        if let Some(call) = call_of(value) {
            let callee = compact_text_of(self.text_of(file, call.callee.span()));

            if matches!(callee.as_str(), "Math.floor" | "Math.ceil" | "Math.trunc") {
                if let Some(argument) = call
                    .arguments
                    .first()
                    .and_then(|argument| argument.as_expression())
                {
                    return self.is_geometric(file, argument, name);
                }
            }
        }

        false
    }

    fn is_multiplicative_update(
        &mut self,
        file: FileId,
        e: Option<&'a Expression<'a>>,
        name: &str,
    ) -> bool {
        let Some(e) = e else {
            return false;
        };
        let Expression::AssignmentExpression(assignment) = unwrap(e) else {
            return false;
        };
        let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left else {
            return false;
        };

        if target.name != name {
            return false;
        }

        if is_multiplicative_assignment(assignment.operator) {
            return self.is_numeric_constant(file, &assignment.right);
        }

        if assignment.operator == AssignmentOperator::Assign {
            return self.is_geometric(file, &assignment.right, name);
        }

        false
    }

    fn assignments_of(
        &mut self,
        file: FileId,
        body: &'a Statement<'a>,
        names: &[String],
    ) -> Vec<AssignmentWrite<'a>> {
        let mut found = Vec::new();

        for kind in Subtree::of(Root::Statement(body), true, false) {
            match kind {
                AstKind::AssignmentExpression(assignment) => {
                    let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left
                    else {
                        continue;
                    };
                    let name = target.name.as_str();

                    if !names.iter().any(|known| known == name) {
                        continue;
                    }

                    let is_multiplicative = if is_multiplicative_assignment(assignment.operator) {
                        self.is_numeric_constant(file, &assignment.right)
                    } else if assignment.operator == AssignmentOperator::Assign {
                        self.is_geometric(file, &assignment.right, name)
                    } else {
                        false
                    };

                    if is_multiplicative {
                        found.push(AssignmentWrite::Geometric);
                    } else if assignment.operator == AssignmentOperator::Assign {
                        found.push(AssignmentWrite::Assign(&assignment.right));
                    } else {
                        found.push(AssignmentWrite::Other);
                    }
                }
                AstKind::UpdateExpression(update) => {
                    if let oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(
                        target,
                    ) = &update.argument
                    {
                        if names.iter().any(|known| known == target.name.as_str()) {
                            found.push(AssignmentWrite::Other);
                        }
                    }
                }
                AstKind::UnaryExpression(unary)
                    if matches!(
                        unary.operator,
                        UnaryOperator::UnaryPlus
                            | UnaryOperator::UnaryNegation
                            | UnaryOperator::LogicalNot
                            | UnaryOperator::BitwiseNot
                    ) =>
                {
                    if let Expression::Identifier(target) = &unary.argument {
                        if names.iter().any(|known| known == target.name.as_str()) {
                            found.push(AssignmentWrite::Other);
                        }
                    }
                }
                _ => {}
            }
        }

        found
    }

    fn midpoint_names_of(
        &self,
        file: FileId,
        body: &'a Statement<'a>,
        names: &[String],
    ) -> Vec<String> {
        let mut midpoints = Vec::new();

        for kind in Subtree::of(Root::Statement(body), true, false) {
            let AstKind::VariableDeclarator(declarator) = kind else {
                continue;
            };
            let (BindingPattern::BindingIdentifier(identifier), Some(initializer)) =
                (&declarator.id, &declarator.init)
            else {
                continue;
            };
            let text = compact_text_of(self.text_of(file, initializer.span()));
            let mentions = names
                .iter()
                .filter(|name| contains_word(&text, name))
                .count();

            if mentions >= 2 && (has_halving_shift(&text) || has_halving_division(&text)) {
                midpoints.push(identifier.name.to_string());
            }
        }

        midpoints
    }

    fn bound_of_while(
        &mut self,
        file: FileId,
        test: &'a Expression<'a>,
        body: &'a Statement<'a>,
    ) -> Bound {
        let condition = unwrap(test);
        let mut names = Names::default();

        names.visit_expression(condition);

        if names.names.is_empty() {
            return linear_bound_of();
        }

        let writes = self.assignments_of(file, body, &names.names);

        if writes.is_empty() {
            return linear_bound_of();
        }

        let midpoints = self.midpoint_names_of(file, body, &names.names);
        let is_midpoint = |name: &str| midpoints.iter().any(|known| known == name);
        let mut halving = true;

        for write in writes {
            let holds = match write {
                AssignmentWrite::Geometric => true,
                AssignmentWrite::Other => false,
                AssignmentWrite::Assign(value) => {
                    let value = unwrap(value);

                    if identifier_of(value).is_some_and(|identifier| is_midpoint(&identifier.name))
                    {
                        true
                    } else if let Some(sides) = sides_of(value) {
                        sides
                            .left
                            .map(unwrap)
                            .and_then(identifier_of)
                            .is_some_and(|identifier| is_midpoint(&identifier.name))
                            && self.is_numeric_constant(file, sides.right)
                    } else {
                        false
                    }
                }
            };

            if !holds {
                halving = false;

                break;
            }
        }

        if halving {
            Bound {
                factor: Cost::LOG,
                why: Some("halving"),
            }
        } else {
            linear_bound_of()
        }
    }
}

fn exit_of(statement: &Statement<'_>) -> Option<Exit> {
    match statement {
        Statement::ReturnStatement(_) => Some(Exit::Return),
        Statement::ThrowStatement(_) => Some(Exit::Throw),
        Statement::BreakStatement(_) => Some(Exit::Break),
        Statement::BlockStatement(block) => block.body.last().and_then(exit_of),
        Statement::IfStatement(statement) => {
            let consequent = exit_of(&statement.consequent);
            let alternate = statement.alternate.as_ref().and_then(exit_of);

            match (consequent, alternate) {
                (Some(first), Some(second)) if first == second => Some(first),
                (Some(_), Some(_)) => Some(Exit::Return),
                _ => None,
            }
        }
        _ => None,
    }
}

fn loop_variable_of<'a>(statement: &'a ForStatement<'a>) -> Option<LoopVariable<'a>> {
    match statement.init.as_ref()? {
        ForStatementInit::VariableDeclaration(declaration) => {
            let [declarator] = declaration.declarations.as_slice() else {
                return None;
            };
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                return None;
            };

            Some(LoopVariable {
                name: identifier.name.as_str(),
                init: declarator.init.as_ref()?,
            })
        }
        init => {
            let Expression::AssignmentExpression(assignment) = init.as_expression()? else {
                return None;
            };
            let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left else {
                return None;
            };

            (assignment.operator == AssignmentOperator::Assign).then_some(LoopVariable {
                name: target.name.as_str(),
                init: &assignment.right,
            })
        }
    }
}

fn constant_bound_of(why: &'static str) -> Bound {
    Bound {
        factor: Cost::ONE,
        why: Some(why),
    }
}

fn linear_bound_of() -> Bound {
    Bound {
        factor: Cost::N,
        why: None,
    }
}

fn is_word_character(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn is_boundary(text: &[u8], position: usize) -> bool {
    let left = position.checked_sub(1).map(|index| text[index]);
    let right = text.get(position).copied();
    let left_word = left.is_some_and(is_word_character);
    let right_word = right.is_some_and(is_word_character);

    left_word != right_word
}

fn contains_word(text: &str, word: &str) -> bool {
    if word.is_empty() {
        return false;
    }

    let bytes = text.as_bytes();

    text.match_indices(word)
        .any(|(start, _)| is_boundary(bytes, start) && is_boundary(bytes, start + word.len()))
}

fn has_halving_shift(text: &str) -> bool {
    let bytes = text.as_bytes();

    [">>>1", ">>1"].iter().any(|pattern| {
        text.match_indices(pattern).any(|(start, _)| {
            let end = start + pattern.len();

            !bytes.get(end).copied().is_some_and(is_word_character)
        })
    })
}

fn has_halving_division(text: &str) -> bool {
    let bytes = text.as_bytes();

    text.match_indices("/2")
        .any(|(start, _)| !bytes.get(start + 2).copied().is_some_and(is_word_character))
}

#[cfg(test)]
#[path = "bounds.test.rs"]
mod tests;

use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::analysis::Analysis;
use crate::cost::{Cost, Preference};
use crate::declarations::FunctionNode;
use crate::project::{FileId, Project};
use crate::syntax::collapsed_text_of;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PerfTag {
    Ignore,
    Hot,
    Cold,
    Bounded,
    Cost(String),
    Max(String),
}

const WORD_TAGS: &[(&str, PerfTag)] = &[
    ("ignore", PerfTag::Ignore),
    ("hot", PerfTag::Hot),
    ("cold", PerfTag::Cold),
    ("bounded", PerfTag::Bounded),
];

pub fn tags_in_comment(text: &str) -> Vec<PerfTag> {
    let mut tags = Vec::new();
    let mut position = 0;

    while let Some(found) = text[position..].find("@perf") {
        let start = position + found + "@perf".len();

        match tag_and_length_of(&text[start..]) {
            Some((tag, consumed)) => {
                if !tags.contains(&tag) {
                    tags.push(tag);
                }

                position = start + consumed;
            }
            None => position = start,
        }
    }

    tags
}

pub fn preference_of(tags: &[PerfTag]) -> Option<Preference> {
    if tags.contains(&PerfTag::Hot) {
        Some(Preference::Hot)
    } else if tags.contains(&PerfTag::Cold) {
        Some(Preference::Cold)
    } else {
        None
    }
}

pub fn cost_tag_of(tags: &[PerfTag]) -> Option<(Cost, String)> {
    tags.iter().find_map(|tag| match tag {
        PerfTag::Cost(text) => Cost::parse(text).map(|cost| (cost, text.clone())),
        _ => None,
    })
}

pub fn max_tag_of(tags: &[PerfTag]) -> Option<(Cost, String)> {
    tags.iter().find_map(|tag| match tag {
        PerfTag::Max(text) => Cost::parse(text).map(|cost| (cost, text.clone())),
        _ => None,
    })
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn perf_tags(&mut self, file: FileId, kind: AstKind<'a>) -> &[PerfTag] {
        let key = (file, kind.node_id());

        if !self.tag_cache.contains_key(&key) {
            let start = kind.span().start;
            let tags = if is_owner(self.project, file, key.1, start) {
                leading_tags_of(self.project, file, start)
            } else {
                Vec::new()
            };

            self.tag_cache.insert(key, tags);
        }

        &self.tag_cache[&key]
    }

    pub fn function_tags(&mut self, file: FileId, function: FunctionNode<'a>) -> Vec<PerfTag> {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let mut node = function.node_id();
        let is_expression = match function {
            FunctionNode::Arrow(_) => true,
            FunctionNode::Function(inner) => inner.is_expression(),
        };

        if is_expression
            && matches!(
                nodes.parent_kind(node),
                AstKind::VariableDeclarator(_)
                    | AstKind::PropertyDefinition(_)
                    | AstKind::AccessorProperty(_)
                    | AstKind::ObjectProperty(_)
            )
        {
            node = nodes.parent_id(node);
        }

        if let (AstKind::VariableDeclarator(_), AstKind::VariableDeclaration(declaration)) =
            (nodes.kind(node), nodes.parent_kind(node))
        {
            if declaration.declarations.len() == 1 {
                node = nodes.parent_id(node);
            }
        }

        if matches!(
            nodes.kind(node),
            AstKind::Function(_) | AstKind::VariableDeclaration(_) | AstKind::Class(_)
        ) && matches!(
            nodes.parent_kind(node),
            AstKind::ExportDeclaration(_) | AstKind::ExportDefaultDeclaration(_)
        ) {
            node = nodes.parent_id(node);
        }

        if matches!(nodes.kind(node), AstKind::Function(_))
            && matches!(nodes.parent_kind(node), AstKind::MethodDefinition(_))
        {
            node = nodes.parent_id(node);
        }

        let start = nodes.kind(node).span().start;

        while !is_owner(project, file, node, start) {
            node = nodes.parent_id(node);
        }

        leading_tags_of(project, file, start)
    }
}

fn is_owner(project: &Project<'_>, file: FileId, node: NodeId, start: u32) -> bool {
    let nodes = project.file(file).semantic.nodes();
    let parent = nodes.parent_id(node);

    parent == node
        || matches!(nodes.kind(parent), AstKind::Program(_))
        || nodes.kind(parent).span().start != start
}

fn leading_tags_of(project: &Project<'_>, file: FileId, start: u32) -> Vec<PerfTag> {
    let source = project.file(file);
    let comments = source.semantic.comments();
    let before = comments.partition_point(|comment| comment.span.end <= start);
    let mut gap_start = start as usize;
    let mut first = before;

    loop {
        gap_start = source.text[..gap_start]
            .trim_end_matches(is_trivia_space)
            .len();

        match first.checked_sub(1).map(|previous| &comments[previous]) {
            Some(comment) if comment.span.end as usize == gap_start => {
                gap_start = comment.span.start as usize;
                first -= 1;
            }
            _ => break,
        }
    }

    let mut collecting = gap_start == 0;
    let mut cursor = gap_start;
    let mut tags = Vec::new();

    for comment in &comments[first..before] {
        if source.text[cursor..comment.span.start as usize].contains(['\n', '\r']) {
            collecting = true;
        }

        cursor = comment.span.end as usize;

        if !collecting {
            continue;
        }

        for tag in tags_in_comment(comment.content_span().source_text(source.text)) {
            if !tags.contains(&tag) {
                tags.push(tag);
            }
        }
    }

    tags
}

fn is_trivia_space(character: char) -> bool {
    character.is_whitespace() || character == '\u{feff}'
}

fn tag_and_length_of(text: &str) -> Option<(PerfTag, usize)> {
    let trimmed = text.trim_start();
    let skipped = text.len() - trimmed.len();

    if skipped == 0 {
        return None;
    }

    for (word, tag) in WORD_TAGS {
        if let Some(rest) = trimmed.strip_prefix(word) {
            if !rest.starts_with(|character: char| {
                character.is_ascii_alphanumeric() || character == '_'
            }) {
                return Some((tag.clone(), skipped + word.len()));
            }
        }
    }

    if let Some(rest) = trimmed.strip_prefix("max") {
        let inner = rest.trim_start();
        let gap = rest.len() - inner.len();

        if gap > 0 {
            if let Some(length) = cost_length_of(inner) {
                let tag = PerfTag::Max(collapse_whitespace(&inner[..length]));

                return Some((tag, skipped + "max".len() + gap + length));
            }
        }
    }

    cost_length_of(trimmed).map(|length| {
        (
            PerfTag::Cost(collapse_whitespace(&trimmed[..length])),
            skipped + length,
        )
    })
}

fn cost_length_of(text: &str) -> Option<usize> {
    let rest = text.strip_prefix("O(")?;

    rest.find(')').map(|close| "O(".len() + close + 1)
}

fn collapse_whitespace(text: &str) -> String {
    collapsed_text_of(text)
}

#[cfg(test)]
#[path = "directives.test.rs"]
mod tests;

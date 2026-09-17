use std::collections::{HashMap, HashSet};

use crate::cost::Cost;
use crate::project::{FileId, Project};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceSpan {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnknownReason {
    Target,
    Effect,
    Multiplicity,
    Bound,
    Recurrence,
    UnsupportedSyntax,
    UnsupportedModel,
    Comparison,
    SizeRelation,
    ResourceExhaustion,
}

impl UnknownReason {
    pub fn text(self) -> &'static str {
        match self {
            Self::Target => "call target",
            Self::Effect => "effects",
            Self::Multiplicity => "invocation count",
            Self::Bound => "iteration bound",
            Self::Recurrence => "recurrence",
            Self::UnsupportedSyntax => "syntax",
            Self::UnsupportedModel => "operation model",
            Self::Comparison => "limit comparison",
            Self::SizeRelation => "input size relation",
            Self::ResourceExhaustion => "analysis resource limit",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Unknown {
    pub origin: SourceSpan,
    pub reason: UnknownReason,
    pub multiplicity: Option<Cost>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UnknownId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnknownNode {
    Origin(Unknown),
    Call {
        site: SourceSpan,
        child: UnknownId,
    },
    Scale {
        factor: Option<Cost>,
        child: UnknownId,
    },
    Join {
        children: Vec<UnknownId>,
    },
}

#[derive(Default)]
pub struct Unknowns {
    nodes: Vec<UnknownNode>,
    interned: HashMap<UnknownNode, UnknownId>,
}

impl Unknowns {
    pub fn node(&self, id: UnknownId) -> &UnknownNode {
        &self.nodes[id.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn insert(&mut self, node: UnknownNode) -> UnknownId {
        if let Some(id) = self.interned.get(&node) {
            return *id;
        }

        let id = UnknownId(u32::try_from(self.nodes.len()).expect("unknown arena fits u32"));

        self.nodes.push(node.clone());
        self.interned.insert(node, id);

        id
    }

    pub fn origin(&mut self, origin: SourceSpan, reason: UnknownReason) -> UnknownId {
        self.insert(UnknownNode::Origin(Unknown {
            origin,
            reason,
            multiplicity: Some(Cost::ONE),
        }))
    }

    pub fn join(&mut self, left: Option<UnknownId>, right: Option<UnknownId>) -> Option<UnknownId> {
        match (left, right) {
            (Some(left), Some(right)) if left != right => {
                let mut children = vec![left, right];

                children.sort();

                Some(self.insert(UnknownNode::Join { children }))
            }
            (Some(id), _) | (_, Some(id)) => Some(id),
            _ => None,
        }
    }

    pub fn scale(&mut self, child: Option<UnknownId>, factor: Option<Cost>) -> Option<UnknownId> {
        child.map(|child| match factor {
            Some(factor) if factor.is_one() => child,
            factor => self.insert(UnknownNode::Scale { factor, child }),
        })
    }

    pub fn called(&mut self, child: Option<UnknownId>, site: SourceSpan) -> Option<UnknownId> {
        child.map(|child| self.insert(UnknownNode::Call { site, child }))
    }

    pub fn semantic_key(&self, root: Option<UnknownId>) -> Vec<(UnknownId, Option<Cost>)> {
        let mut pending: Vec<_> = root.into_iter().map(|id| (id, Some(Cost::ONE))).collect();
        let mut visited = HashSet::new();
        let mut origins = Vec::new();

        while let Some((id, factor)) = pending.pop() {
            if !visited.insert((id, factor.clone())) {
                continue;
            }

            match self.node(id) {
                UnknownNode::Call { child, .. } => pending.push((*child, factor)),
                UnknownNode::Join { children } => {
                    pending.extend(children.iter().map(|id| (*id, factor.clone())))
                }
                UnknownNode::Scale {
                    child,
                    factor: next,
                } => pending.push((*child, multiply(factor, next.clone()))),
                UnknownNode::Origin(_) => origins.push((id, factor)),
            }
        }

        origins.sort_by_key(|(id, factor)| (*id, factor.as_ref().map(Cost::structural_key)));
        origins.dedup();

        origins
    }

    pub fn lines(&self, project: &Project<'_>, root: UnknownId) -> Vec<String> {
        self.lines_with(project, root, &|id| format!("size_{id}"))
    }

    pub fn lines_with(
        &self,
        project: &Project<'_>,
        root: UnknownId,
        name: &impl Fn(u64) -> String,
    ) -> Vec<String> {
        let mut pending = vec![(root, Some(Cost::ONE), Vec::<SourceSpan>::new())];
        let mut lines = Vec::new();
        let mut shown = HashSet::new();

        while let Some((id, factor, calls)) = pending.pop() {
            match self.node(id) {
                UnknownNode::Origin(unknown) => {
                    let factor = multiply(factor, unknown.multiplicity.clone());
                    let origin = unknown.origin;
                    let location = |span: SourceSpan| {
                        format!(
                            "{}:{} [{}..{}]",
                            project.file(span.file).relative,
                            project.line_of(span.file, span.start),
                            span.start,
                            span.end
                        )
                    };
                    let frequency = factor
                        .as_ref()
                        .map_or_else(|| "unknown".to_string(), |cost| cost.text_with(name));
                    let via = if calls.is_empty() {
                        String::new()
                    } else {
                        format!(
                            " via {}",
                            calls
                                .iter()
                                .copied()
                                .map(location)
                                .collect::<Vec<_>>()
                                .join(" -> ")
                        )
                    };
                    let line = format!(
                        "unknown {} at {}; multiplicity {frequency}{via}",
                        unknown.reason.text(),
                        location(origin)
                    );

                    if shown.insert(line.clone()) {
                        lines.push(line);
                    }
                }
                UnknownNode::Call { site, child } => {
                    let mut calls = calls;

                    calls.push(*site);
                    pending.push((*child, factor, calls));
                }
                UnknownNode::Scale {
                    factor: multiplier,
                    child,
                } => {
                    pending.push((*child, multiply(factor, multiplier.clone()), calls));
                }
                UnknownNode::Join { children } => {
                    for child in children.iter().rev() {
                        pending.push((*child, factor.clone(), calls.clone()));
                    }
                }
            }
        }

        lines
    }
}

fn multiply(left: Option<Cost>, right: Option<Cost>) -> Option<Cost> {
    let (left, right) = (left?, right?);

    left.multiply(&right).ok()
}

#[cfg(test)]
#[path = "unknowns.test.rs"]
mod tests;

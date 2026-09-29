use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::cost::Cost;
use crate::project::{FileId, Project};

#[path = "unknown_sets.rs"]
mod sets;

pub use sets::{Counts as SemanticSetStats, Error as SemanticError, Limits as SemanticLimits};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SemanticKeyId(sets::SetId);

struct SemanticFrame {
    id: UnknownId,
    factor: Option<Cost>,
    next: usize,
    joined: sets::SetId,
}

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
    ImplementationDefined,
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
            Self::ImplementationDefined => "implementation-defined work",
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
    semantic_sets: sets::Sets<(UnknownId, Option<Cost>)>,
    semantic_contexts: HashMap<(UnknownId, Option<Cost>), sets::SetId>,
    edges: usize,
}

impl Unknowns {
    pub fn edge_count(&self) -> usize {
        self.edges
    }

    pub fn semantic_context_count(&self) -> usize {
        self.semantic_contexts.len()
    }
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

        self.edges += match &node {
            UnknownNode::Origin(_) => 0,
            UnknownNode::Call { .. } | UnknownNode::Scale { .. } => 1,
            UnknownNode::Join { children } => children.len(),
        };

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

    pub fn semantic_stats(&self) -> SemanticSetStats {
        self.semantic_sets.counts()
    }

    pub fn set_semantic_limits(&mut self, limits: SemanticLimits) -> Result<(), SemanticError> {
        self.semantic_sets.set_limits(limits)
    }

    pub fn semantic_key(
        &mut self,
        root: Option<UnknownId>,
        work: &mut impl FnMut() -> bool,
    ) -> Result<SemanticKeyId, SemanticError> {
        let Some(root) = root else {
            return Ok(SemanticKeyId(sets::SetId::EMPTY));
        };

        if !work() {
            return Err(SemanticError::Resource);
        }

        let mut pending = vec![SemanticFrame {
            id: root,
            factor: Some(Cost::ONE),
            next: 0,
            joined: sets::SetId::EMPTY,
        }];
        let mut completed = None;

        while let Some(frame) = pending.last_mut() {
            if let Some(child) = completed.take() {
                frame.joined = if matches!(
                    self.nodes.get(frame.id.0 as usize),
                    Some(UnknownNode::Join { .. })
                ) {
                    self.semantic_sets.union(frame.joined, child, work)?
                } else {
                    child
                };
            }

            let context = (frame.id, frame.factor.clone());

            if frame.next == 0 {
                if !work() {
                    return Err(SemanticError::Resource);
                }

                if let Some(key) = self.semantic_contexts.get(&context).copied() {
                    pending.pop();

                    completed = Some(key);

                    continue;
                }
            }

            let node = self
                .nodes
                .get(frame.id.0 as usize)
                .ok_or(SemanticError::InvalidRoot)?;
            let child = match node {
                UnknownNode::Origin(_) => {
                    frame.joined = self.semantic_sets.singleton(context.clone(), work)?;

                    None
                }
                UnknownNode::Call { child, .. } if frame.next == 0 => {
                    Some((*child, frame.factor.clone()))
                }
                UnknownNode::Scale { child, factor } if frame.next == 0 => {
                    Some((*child, multiply(frame.factor.clone(), factor.clone())))
                }
                UnknownNode::Join { children } => children
                    .get(frame.next)
                    .map(|child| (*child, frame.factor.clone())),
                _ => None,
            };

            if let Some((id, factor)) = child {
                if !work() {
                    return Err(SemanticError::Resource);
                }

                frame.next += 1;

                pending.push(SemanticFrame {
                    id,
                    factor,
                    next: 0,
                    joined: sets::SetId::EMPTY,
                });
            } else {
                if !work() || self.semantic_contexts.len() >= 1_000_000 {
                    return Err(SemanticError::Resource);
                }

                let key = frame.joined;

                self.semantic_contexts.insert(context, key);
                pending.pop();

                completed = Some(key);
            }
        }

        Ok(SemanticKeyId(completed.expect("root evaluation completed")))
    }

    pub fn origins(&self, root: Option<UnknownId>) -> Vec<&Unknown> {
        let mut pending: Vec<_> = root.into_iter().collect();
        let mut visited = HashSet::new();
        let mut found = Vec::new();

        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }

            match self.node(id) {
                UnknownNode::Origin(unknown) => found.push(unknown),
                UnknownNode::Call { child, .. } | UnknownNode::Scale { child, .. } => {
                    pending.push(*child)
                }
                UnknownNode::Join { children } => pending.extend(children),
            }
        }

        found
    }

    pub fn lines(&self, project: &Project<'_>, root: UnknownId) -> Vec<String> {
        self.lines_with(project, root, &|id, out| write!(out, "size_{id}"))
    }

    pub fn lines_with(
        &self,
        project: &Project<'_>,
        root: UnknownId,
        name: &impl Fn(u64, &mut dyn std::fmt::Write) -> std::fmt::Result,
    ) -> Vec<String> {
        self.render_with(project, root, name, crate::trace::RenderBudget::default())
            .text
            .lines()
            .map(str::to_owned)
            .collect()
    }

    pub fn render_with(
        &self,
        project: &Project<'_>,
        root: UnknownId,
        name: &impl Fn(u64, &mut dyn std::fmt::Write) -> std::fmt::Result,
        budget: crate::trace::RenderBudget,
    ) -> UnknownRendered {
        let marker = crate::trace::TRUNCATION_MARKER;
        let Some(limit) = budget.bytes.checked_sub(marker.len()) else {
            return UnknownRendered {
                text: String::new(),
                truncated: true,
                stats: UnknownRenderStats::default(),
            };
        };
        let mut out = crate::trace::BoundedText {
            text: String::new(),
            limit,
            exhausted: false,
        };
        let mut stack = vec![UnknownFrame {
            id: root,
            factor: Some(Cost::ONE),
            path: None,
            next: 0,
            entered: false,
        }];
        let mut paths: Vec<CallPath> = Vec::new();
        let mut shown = HashSet::new();
        let mut stats = UnknownRenderStats::default();
        let mut truncated = false;

        while let Some(frame) = stack.last_mut() {
            if !frame.entered {
                if stats.visits >= budget.visits {
                    truncated = true;

                    break;
                }

                stats.visits += 1;
                frame.entered = true;
            }

            let Some(node) = self.nodes.get(frame.id.0 as usize) else {
                truncated = true;

                break;
            };
            let child = match node {
                UnknownNode::Origin(unknown) => {
                    let start = out.text.len();
                    let factor = multiply(frame.factor.clone(), unknown.multiplicity.clone());
                    let mut calls = Vec::new();
                    let mut path = frame.path;

                    while let Some(id) = path {
                        if calls.len() >= budget.depth {
                            truncated = true;

                            break;
                        }

                        calls.push(paths[id].site);

                        path = paths[id].parent;
                    }

                    if truncated {
                        break;
                    }

                    let result = (|| -> std::fmt::Result {
                        write!(out, "unknown {} at ", unknown.reason.text())?;
                        write_location(&mut out, project, unknown.origin)?;
                        out.write_str("; multiplicity ")?;

                        match factor {
                            Some(cost) => cost.write_with(&mut out, true, name)?,
                            None => out.write_str("unknown")?,
                        };

                        if !calls.is_empty() {
                            out.write_str(" via ")?;

                            for (index, site) in calls.iter().rev().enumerate() {
                                if index != 0 {
                                    out.write_str(" -> ")?;
                                }

                                write_location(&mut out, project, *site)?;
                            }
                        }

                        out.write_char('\n')
                    })();

                    if result.is_err() {
                        out.text.truncate(start);

                        truncated = true;

                        break;
                    }

                    if !shown.insert(out.text[start..].to_string()) {
                        out.text.truncate(start);
                    }

                    None
                }
                UnknownNode::Call { site, child } if frame.next == 0 => {
                    let depth = frame.path.map_or(1, |id| paths[id].depth + 1);

                    if depth > budget.depth || paths.len() >= budget.visits {
                        truncated = true;

                        break;
                    }

                    let id = paths.len();

                    paths.push(CallPath {
                        site: *site,
                        parent: frame.path,
                        depth,
                    });

                    stats.path_frames += 1;

                    Some((*child, frame.factor.clone(), Some(id)))
                }
                UnknownNode::Scale { factor, child } if frame.next == 0 => Some((
                    *child,
                    multiply(frame.factor.clone(), factor.clone()),
                    frame.path,
                )),
                UnknownNode::Join { children } => children
                    .get(frame.next)
                    .map(|child| (*child, frame.factor.clone(), frame.path)),
                _ => None,
            };

            if let Some((id, factor, path)) = child {
                frame.next += 1;
                stats.edges += 1;

                stack.push(UnknownFrame {
                    id,
                    factor,
                    path,
                    next: 0,
                    entered: false,
                });
            } else {
                stack.pop();
            }
        }

        if truncated {
            out.text.push_str(marker);
        }

        stats.bytes = out.text.len();

        UnknownRendered {
            text: out.text,
            truncated,
            stats,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UnknownRenderStats {
    pub visits: usize,
    pub edges: usize,
    pub path_frames: usize,
    pub bytes: usize,
}
pub struct UnknownRendered {
    pub text: String,
    pub truncated: bool,
    pub stats: UnknownRenderStats,
}
struct CallPath {
    site: SourceSpan,
    parent: Option<usize>,
    depth: usize,
}
struct UnknownFrame {
    id: UnknownId,
    factor: Option<Cost>,
    path: Option<usize>,
    next: usize,
    entered: bool,
}
fn write_location(
    out: &mut dyn Write,
    project: &Project<'_>,
    span: SourceSpan,
) -> std::fmt::Result {
    write!(
        out,
        "{}:{} [{}..{}]",
        project.file(span.file).relative,
        project.line_of(span.file, span.start),
        span.start,
        span.end
    )
}

fn multiply(left: Option<Cost>, right: Option<Cost>) -> Option<Cost> {
    let (left, right) = (left?, right?);

    left.multiply(&right).ok()
}

#[cfg(test)]
#[path = "unknowns.test.rs"]
mod tests;

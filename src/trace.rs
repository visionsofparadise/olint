use std::cell::Cell;
use std::collections::HashMap;
use std::fmt::{self, Write};

use crate::cost::Cost;
use crate::project::Site;
use crate::unknowns::SourceSpan;

pub const TRUNCATION_MARKER: &str = "... explanation truncated ...\n";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TraceId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraceNode {
    pub label: String,
    pub site: Site,
    pub cost: Cost,
    pub children: Vec<TraceId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TraceLayout {
    Factor { inner_children: u8 },
    Group,
    Sequence,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TraceKey {
    node: TraceNode,
    origin: Option<SourceSpan>,
    layout: TraceLayout,
}

#[derive(Clone, Copy, Debug)]
pub struct ArenaLimits {
    pub nodes: usize,
    pub edges: usize,
    pub children_per_node: usize,
    pub label_bytes_per_node: usize,
    pub label_bytes_total: usize,
}

impl Default for ArenaLimits {
    fn default() -> Self {
        Self {
            nodes: 1_000_000,
            edges: 2_000_000,
            children_per_node: 64,
            label_bytes_per_node: 4096,
            label_bytes_total: 64 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ArenaStats {
    pub nodes: usize,
    pub edges: usize,
    pub label_bytes: usize,
    pub insertion_attempts: usize,
    pub intern_hits: usize,
    pub shallow_key_edges: usize,
    pub node_reads: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceError {
    InvalidId,
    InvalidOrigin,
    InvalidLayout,
    Capacity,
}

pub struct TraceArena {
    records: Vec<TraceKey>,
    interned: HashMap<TraceKey, TraceId>,
    limits: ArenaLimits,
    stats: ArenaStats,
    node_reads: Cell<usize>,
}

impl Default for TraceArena {
    fn default() -> Self {
        Self::new(ArenaLimits::default())
    }
}

impl TraceArena {
    pub(crate) fn label_limit(&self) -> usize {
        self.limits.label_bytes_per_node
    }
    pub fn factor(
        &mut self,
        label: String,
        site: Site,
        origin: SourceSpan,
        cost: Cost,
        inner: Option<TraceId>,
        continuation: Option<TraceId>,
    ) -> Result<TraceId, TraceError> {
        self.factor_format(label, site, origin, cost, inner, continuation)
    }

    pub fn factor_format(
        &mut self,
        label: impl fmt::Display,
        site: Site,
        origin: SourceSpan,
        cost: Cost,
        inner: Option<TraceId>,
        continuation: Option<TraceId>,
    ) -> Result<TraceId, TraceError> {
        let mut text = BoundedText {
            text: String::new(),
            limit: self.limits.label_bytes_per_node,
            exhausted: false,
        };

        write!(text, "{label}").map_err(|_| TraceError::Capacity)?;

        self.insert(
            TraceNode {
                label: text.text,
                site,
                cost,
                children: inner.into_iter().chain(continuation).collect(),
            },
            Some(origin),
            TraceLayout::Factor {
                inner_children: u8::from(inner.is_some()),
            },
        )
    }

    pub fn group(
        &mut self,
        left: Option<TraceId>,
        right: Option<TraceId>,
    ) -> Result<Option<TraceId>, TraceError> {
        match (left, right) {
            (Some(left), Some(right)) if left != right => {
                let site = self
                    .records
                    .get(left.0 as usize)
                    .ok_or(TraceError::InvalidId)?
                    .node
                    .site;

                self.insert(
                    TraceNode {
                        label: String::new(),
                        site,
                        cost: Cost::ONE,
                        children: vec![left, right],
                    },
                    None,
                    TraceLayout::Sequence,
                )
                .map(Some)
            }
            (Some(id), _) | (_, Some(id)) => Ok(Some(id)),
            _ => Ok(None),
        }
    }
    pub fn new(limits: ArenaLimits) -> Self {
        Self {
            records: Vec::new(),
            interned: HashMap::new(),
            limits,
            stats: ArenaStats::default(),
            node_reads: Cell::new(0),
        }
    }

    pub fn stats(&self) -> ArenaStats {
        ArenaStats {
            node_reads: self.node_reads.get(),
            ..self.stats
        }
    }

    pub fn reset_node_reads(&self) {
        self.node_reads.set(0);
    }

    pub fn node(&self, id: TraceId) -> Result<&TraceNode, TraceError> {
        let record = self
            .records
            .get(id.0 as usize)
            .ok_or(TraceError::InvalidId)?;

        self.node_reads.set(
            self.node_reads
                .get()
                .checked_add(1)
                .ok_or(TraceError::Capacity)?,
        );

        Ok(&record.node)
    }

    pub fn origin(&self, id: TraceId) -> Result<Option<SourceSpan>, TraceError> {
        self.records
            .get(id.0 as usize)
            .map(|record| record.origin)
            .ok_or(TraceError::InvalidId)
    }

    pub fn layout(&self, id: TraceId) -> Result<TraceLayout, TraceError> {
        self.records
            .get(id.0 as usize)
            .map(|record| record.layout)
            .ok_or(TraceError::InvalidId)
    }

    pub fn insert(
        &mut self,
        node: TraceNode,
        origin: Option<SourceSpan>,
        layout: TraceLayout,
    ) -> Result<TraceId, TraceError> {
        self.stats.insertion_attempts = self
            .stats
            .insertion_attempts
            .checked_add(1)
            .ok_or(TraceError::Capacity)?;

        if node.children.len() > self.limits.children_per_node
            || node.label.len() > self.limits.label_bytes_per_node
        {
            return Err(TraceError::Capacity);
        }

        if origin.is_some_and(|origin| origin.file != node.site.file || origin.start > origin.end)
            || (call_label(&node.label) && origin.is_none())
        {
            return Err(TraceError::InvalidOrigin);
        }

        match layout {
            TraceLayout::Factor { inner_children }
                if inner_children > 1
                    || usize::from(inner_children) > node.children.len()
                    || node.children.len() > usize::from(inner_children) + 1 =>
            {
                return Err(TraceError::InvalidLayout);
            }
            TraceLayout::Group | TraceLayout::Sequence
                if !node.label.is_empty() || !node.cost.is_one() =>
            {
                return Err(TraceError::InvalidLayout);
            }
            _ => {}
        }

        if node
            .children
            .iter()
            .any(|id| id.0 as usize >= self.records.len())
        {
            return Err(TraceError::InvalidId);
        }

        self.stats.shallow_key_edges = self
            .stats
            .shallow_key_edges
            .checked_add(node.children.len())
            .ok_or(TraceError::Capacity)?;
        let key = TraceKey {
            node,
            origin,
            layout,
        };

        if let Some(id) = self.interned.get(&key) {
            self.stats.intern_hits = self
                .stats
                .intern_hits
                .checked_add(1)
                .ok_or(TraceError::Capacity)?;

            return Ok(*id);
        }

        let nodes = self
            .records
            .len()
            .checked_add(1)
            .ok_or(TraceError::Capacity)?;
        let edges = self
            .stats
            .edges
            .checked_add(key.node.children.len())
            .ok_or(TraceError::Capacity)?;
        let label_bytes = self
            .stats
            .label_bytes
            .checked_add(key.node.label.len())
            .ok_or(TraceError::Capacity)?;

        if nodes > self.limits.nodes
            || edges > self.limits.edges
            || label_bytes > self.limits.label_bytes_total
        {
            return Err(TraceError::Capacity);
        }

        let id = TraceId(u32::try_from(self.records.len()).map_err(|_| TraceError::Capacity)?);

        self.records.push(key.clone());
        self.interned.insert(key, id);

        self.stats.nodes = nodes;
        self.stats.edges = edges;
        self.stats.label_bytes = label_bytes;

        Ok(id)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RenderBudget {
    pub visits: usize,
    pub depth: usize,
    pub bytes: usize,
}

impl Default for RenderBudget {
    fn default() -> Self {
        Self {
            visits: 10_000,
            depth: 128,
            bytes: 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Truncation {
    Visits,
    Depth,
    Bytes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RenderError {
    Trace(TraceError),
    BudgetTooSmall,
    Formatter,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RenderStats {
    pub visits: usize,
    pub edges: usize,
    pub lines: usize,
    pub bytes: usize,
    pub peak_frames: usize,
}

#[derive(Debug)]
pub struct Rendered {
    pub text: String,
    pub truncated: Option<Truncation>,
    pub stats: RenderStats,
}

struct Frame {
    id: TraceId,
    depth: usize,
    next_child: usize,
    entered: bool,
    end_depth: usize,
}

impl Frame {
    fn new(id: TraceId, depth: usize) -> Self {
        Self {
            id,
            depth,
            next_child: 0,
            entered: false,
            end_depth: depth,
        }
    }
}

pub(crate) struct BoundedText {
    pub(crate) text: String,
    pub(crate) limit: usize,
    pub(crate) exhausted: bool,
}

impl Write for BoundedText {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if text.len() > self.limit - self.text.len() {
            self.exhausted = true;

            return Err(fmt::Error);
        }

        self.text.push_str(text);

        Ok(())
    }
}

fn call_label(label: &str) -> bool {
    ["call ", "new ", "recursive call ", "@perf "]
        .iter()
        .any(|prefix| label.starts_with(prefix))
}

fn spaces(out: &mut dyn Write, mut count: usize) -> fmt::Result {
    const SPACES: &str = "                                ";

    while count != 0 {
        let chunk = count.min(SPACES.len());

        out.write_str(&SPACES[..chunk])?;

        count -= chunk;
    }

    Ok(())
}

fn node_line(
    node: &TraceNode,
    depth: usize,
    out: &mut dyn Write,
    location: &impl Fn(Site, &mut dyn Write) -> fmt::Result,
    cost_text: &impl Fn(&Cost, bool, &mut dyn Write) -> fmt::Result,
) -> fmt::Result {
    let indentation = depth.checked_mul(4).ok_or(fmt::Error)?;
    let is_tag = node.label.starts_with("@perf ");
    let is_call = call_label(&node.label);
    let is_loop = ["for", "for-of", "for-in", "while", "do-while"]
        .iter()
        .any(|name| {
            node.label == *name
                || node
                    .label
                    .strip_prefix(name)
                    .is_some_and(|rest| rest.starts_with(' '))
        });
    let relation = if is_loop {
        "in loop"
    } else if is_tag {
        "reads as"
    } else if is_call {
        "calls"
    } else {
        "does"
    };
    let shown = ["call ", "new ", "recursive call "]
        .iter()
        .find_map(|prefix| node.label.strip_prefix(prefix))
        .unwrap_or(&node.label);

    spaces(out, indentation)?;
    write!(out, "{relation} {shown}")?;

    let width = 52 - indentation.min(32);

    spaces(out, width.saturating_sub(shown.encode_utf16().count()))?;
    out.write_char(' ')?;
    location(node.site, out)?;

    if !node.cost.is_one() {
        out.write_str(if is_call { "  = " } else { "  x " })?;
        cost_text(&node.cost, is_call, out)?;
    }

    out.write_char('\n')
}

pub fn render(
    arena: &TraceArena,
    root: TraceId,
    depth: usize,
    budget: RenderBudget,
    location: &impl Fn(Site, &mut dyn Write) -> fmt::Result,
    cost_text: &impl Fn(&Cost, bool, &mut dyn Write) -> fmt::Result,
) -> Result<Rendered, RenderError> {
    if root.0 as usize >= arena.records.len() {
        return Err(RenderError::Trace(TraceError::InvalidId));
    }

    let limit = budget
        .bytes
        .checked_sub(TRUNCATION_MARKER.len())
        .ok_or(RenderError::BudgetTooSmall)?;
    let mut out = BoundedText {
        text: String::new(),
        limit,
        exhausted: false,
    };
    let mut stack = vec![Frame::new(root, depth)];
    let mut stats = RenderStats {
        peak_frames: 1,
        ..RenderStats::default()
    };
    let mut truncated = None;

    while let Some(frame) = stack.last_mut() {
        if !frame.entered {
            if stats.visits == budget.visits {
                truncated = Some(Truncation::Visits);

                break;
            }

            if frame.depth > budget.depth || frame.depth.checked_mul(4).is_none() {
                truncated = Some(Truncation::Depth);

                break;
            }

            let node = arena.node(frame.id).map_err(RenderError::Trace)?;
            stats.visits += 1;
            frame.entered = true;

            if matches!(
                arena.records[frame.id.0 as usize].layout,
                TraceLayout::Factor { .. }
            ) {
                let start = out.text.len();

                if node_line(node, frame.depth, &mut out, location, cost_text).is_err() {
                    if !out.exhausted {
                        return Err(RenderError::Formatter);
                    }

                    out.text.truncate(start);

                    truncated = Some(Truncation::Bytes);

                    break;
                }

                stats.lines += 1;

                if !call_label(&node.label) && !node.cost.is_one() {
                    let Some(end_depth) = frame.depth.checked_add(1) else {
                        truncated = Some(Truncation::Depth);

                        break;
                    };
                    frame.end_depth = end_depth;
                }
            }
        }

        let record = &arena.records[frame.id.0 as usize];

        if let Some(child) = record.node.children.get(frame.next_child).copied() {
            let advances = match record.layout {
                TraceLayout::Group | TraceLayout::Sequence => false,
                TraceLayout::Factor { inner_children } => {
                    frame.next_child >= usize::from(inner_children)
                        && !call_label(&record.node.label)
                        && !record.node.cost.is_one()
                }
            };
            let Some(depth) = (if record.layout == TraceLayout::Sequence {
                Some(frame.end_depth)
            } else {
                frame.depth.checked_add(usize::from(advances))
            }) else {
                truncated = Some(Truncation::Depth);

                break;
            };
            frame.next_child += 1;
            stats.edges += 1;

            stack.push(Frame::new(child, depth));

            stats.peak_frames = stats.peak_frames.max(stack.len());
        } else {
            let finished = stack.pop().expect("active frame");

            if let Some(parent) = stack.last_mut() {
                let layout = arena.records[parent.id.0 as usize].layout;

                if layout == TraceLayout::Sequence
                    || matches!(layout,TraceLayout::Factor{inner_children} if parent.next_child>usize::from(inner_children))
                {
                    parent.end_depth = finished.end_depth;
                }
            }
        }
    }

    if truncated.is_some() {
        out.text.push_str(TRUNCATION_MARKER);
    }

    stats.bytes = out.text.len();

    Ok(Rendered {
        text: out.text,
        truncated,
        stats,
    })
}

#[cfg(test)]
#[path = "trace.test.rs"]
mod tests;

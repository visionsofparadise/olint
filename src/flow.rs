use std::borrow::Cow;

use oxc_ast::AstKind;
use oxc_cfg::BlockNodeId;
use oxc_semantic::{NodeId, Semantic};

use crate::project::FileId;
use crate::syntax::{is_iteration_kind, is_type_kind};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Completion {
    Normal,
    Return,
    Throw,
    Break(NodeId),
    Continue(NodeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FlowPointId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Region {
    Invocation(NodeId),
    ClassDefinition(NodeId),
    Construction(NodeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    Entry,
    Evaluate,
    ParameterDefault,
    LoopInitialize,
    LoopTest,
    LoopBody,
    LoopUpdate,
    Iterable,
    IterationNext,
    FinallyEntry,
    Exit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Guard {
    Always,
    Truthy(NodeId),
    Falsy(NodeId),
    Nullish(NodeId),
    NonNullish(NodeId),
    Undefined(NodeId),
    Defined(NodeId),
    Throws(NodeId),
    ReturnsNormally(NodeId),
    IterationAvailable(NodeId),
    IterationDone(NodeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompletionAction {
    Preserve,
    Produce(Completion),
    EnterFinally(Completion),
    Resume(Completion),
    Replace {
        pending: Completion,
        replacement: Completion,
    },
}

#[derive(Clone, Debug)]
pub struct FlowPoint {
    pub node: NodeId,
    pub region: Region,
    pub step: Step,
    pub cfg: BlockNodeId,
}

#[derive(Clone, Debug)]
pub struct FlowEdge {
    pub from: FlowPointId,
    pub to: FlowPointId,
    pub guard: Guard,
    pub action: CompletionAction,
}

#[derive(Clone, Copy, Debug)]
pub struct FlowExit {
    pub from: FlowPointId,
    pub completion: Completion,
}

#[derive(Clone, Debug)]
pub struct FlowSummary {
    pub file: FileId,
    pub function: NodeId,
    pub entry: FlowPointId,
    pub points: Vec<FlowPoint>,
    pub edges: Vec<FlowEdge>,
    pub exits: Vec<FlowExit>,
    pub node_visits: usize,
    pub sequence_port_visits: usize,
    pub construction_entries: Vec<(NodeId, FlowPointId)>,
    pub construction_exits: Vec<(NodeId, Vec<FlowExit>)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlowError {
    MissingCfg,
    InvalidSource,
    InvalidTarget(NodeId),
    Unsupported(NodeId),
    ResourceLimit,
}

#[derive(Default)]
struct Ports {
    normal: Vec<FlowExit>,
    abrupt: Vec<FlowExit>,
}

impl Ports {
    fn push(&mut self, exit: FlowExit) {
        if exit.completion == Completion::Normal {
            self.normal.push(exit);
        } else {
            self.abrupt.push(exit);
        }
    }
    fn extend(&mut self, exits: impl IntoIterator<Item = FlowExit>) {
        for exit in exits {
            self.push(exit);
        }
    }
    fn retain(&mut self, mut predicate: impl FnMut(&FlowExit) -> bool) {
        self.normal.retain(&mut predicate);
        self.abrupt.retain(predicate);
    }
}
impl From<Vec<FlowExit>> for Ports {
    fn from(exits: Vec<FlowExit>) -> Self {
        let mut result = Self::default();

        result.extend(exits);

        result
    }
}
impl IntoIterator for Ports {
    type Item = FlowExit;
    type IntoIter = std::iter::Chain<std::vec::IntoIter<FlowExit>, std::vec::IntoIter<FlowExit>>;
    fn into_iter(self) -> Self::IntoIter {
        self.normal.into_iter().chain(self.abrupt)
    }
}

struct Fragment {
    entry: FlowPointId,
    exits: Ports,
}

struct Builder<'s, 'a> {
    semantic: &'s Semantic<'a>,
    children: &'s [Vec<NodeId>],
    summary: FlowSummary,
    region: Region,
    limit: usize,
    depth: usize,
}

pub(crate) struct FlowIndex {
    children: Vec<Vec<NodeId>>,
}

impl FlowIndex {
    pub(crate) fn children_of(&self, node: NodeId) -> &[NodeId] {
        &self.children[node.index()]
    }

    pub(crate) fn new(semantic: &Semantic<'_>) -> Self {
        let mut children = vec![Vec::new(); semantic.nodes().len()];

        for (id, _) in semantic.nodes().iter_enumerated() {
            let parent = semantic.nodes().parent_id(id);

            if parent != id {
                children[parent.index()].push(id);
            }
        }

        Self { children }
    }
}

pub struct FlowContext<'s, 'a> {
    semantic: &'s Semantic<'a>,
    children: Cow<'s, [Vec<NodeId>]>,
    pub indexed_nodes: usize,
}

impl<'s, 'a> FlowContext<'s, 'a> {
    pub fn new(semantic: &'s Semantic<'a>) -> Result<Self, FlowError> {
        semantic.cfg().ok_or(FlowError::MissingCfg)?;

        let index = FlowIndex::new(semantic);

        Ok(Self {
            semantic,
            indexed_nodes: index.children.len(),
            children: Cow::Owned(index.children),
        })
    }
    pub(crate) fn from_index(semantic: &'s Semantic<'a>, index: &'s FlowIndex) -> Self {
        Self {
            semantic,
            indexed_nodes: index.children.len(),
            children: Cow::Borrowed(&index.children),
        }
    }
    pub fn build(&self, file: FileId, function: NodeId) -> Result<FlowSummary, FlowError> {
        self.build_with_limit(file, function, 20_000)
    }
    pub fn build_with_limit(
        &self,
        file: FileId,
        function: NodeId,
        limit: usize,
    ) -> Result<FlowSummary, FlowError> {
        let semantic = self.semantic;

        if function.index() >= semantic.nodes().len()
            || !matches!(
                semantic.nodes().kind(function),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            )
        {
            return Err(FlowError::InvalidTarget(function));
        }

        let children = &self.children;
        let mut builder = Builder {
            semantic,
            children,
            region: Region::Invocation(function),
            limit,
            depth: 0,
            summary: FlowSummary {
                file,
                function,
                entry: FlowPointId(0),
                points: Vec::new(),
                edges: Vec::new(),
                exits: Vec::new(),
                node_visits: 0,
                sequence_port_visits: 0,
                construction_entries: Vec::new(),
                construction_exits: Vec::new(),
            },
        };
        let entry = builder.point(function, Step::Entry)?;
        let body = builder.sequence(function, builder.children[function.index()].clone())?;

        builder.edge(entry, body.entry, Guard::Always, CompletionAction::Preserve);

        builder.summary.entry = entry;
        let mut pending = vec![entry];
        let mut reachable = std::collections::HashSet::new();
        let mut successors = vec![Vec::new(); builder.summary.points.len()];

        for edge in &builder.summary.edges {
            successors[edge.from.0].push(edge.to);
        }

        while let Some(point) = pending.pop() {
            if reachable.insert(point) {
                pending.extend(successors[point.0].iter().copied());
            }
        }

        builder.summary.exits = body
            .exits
            .into_iter()
            .filter(|exit| reachable.contains(&exit.from))
            .collect();

        Ok(builder.summary)
    }
}

impl<'s, 'a> Builder<'s, 'a> {
    fn control_target(
        &self,
        node: NodeId,
        label: Option<&str>,
        continuing: bool,
    ) -> Result<NodeId, FlowError> {
        control_target_of(self.semantic, node, label, continuing)
            .ok_or(FlowError::InvalidTarget(node))
    }

    fn point(&mut self, node: NodeId, step: Step) -> Result<FlowPointId, FlowError> {
        if self.summary.points.len() >= self.limit {
            return Err(FlowError::ResourceLimit);
        }

        let id = FlowPointId(self.summary.points.len());

        self.summary.points.push(FlowPoint {
            node,
            region: self.region,
            step,
            cfg: self.semantic.nodes().cfg_id(node),
        });

        Ok(id)
    }

    fn edge(&mut self, from: FlowPointId, to: FlowPointId, guard: Guard, action: CompletionAction) {
        self.summary.edges.push(FlowEdge {
            from,
            to,
            guard,
            action,
        });
    }

    fn atom(&mut self, node: NodeId, step: Step) -> Result<Fragment, FlowError> {
        let entry = self.point(node, step)?;

        Ok(Fragment {
            entry,
            exits: vec![FlowExit {
                from: entry,
                completion: Completion::Normal,
            }]
            .into(),
        })
    }

    fn append(&mut self, left: Fragment, right: Fragment) -> Fragment {
        let mut exits = Ports {
            normal: Vec::new(),
            abrupt: left.exits.abrupt,
        };
        let reaches = !left.exits.normal.is_empty();
        self.summary.sequence_port_visits += left.exits.normal.len();

        for exit in left.exits.normal {
            self.edge(
                exit.from,
                right.entry,
                Guard::Always,
                CompletionAction::Preserve,
            );
        }

        if reaches {
            exits.extend(right.exits);
        }

        Fragment {
            entry: left.entry,
            exits,
        }
    }

    fn sequence(&mut self, owner: NodeId, nodes: Vec<NodeId>) -> Result<Fragment, FlowError> {
        let mut result = self.atom(owner, Step::Entry)?;

        for node in nodes {
            if is_type_kind(self.semantic.nodes().kind(node).ty()) {
                continue;
            }

            let next = self.build(node)?;
            result = self.append(result, next);
        }

        Ok(result)
    }

    fn build(&mut self, node: NodeId) -> Result<Fragment, FlowError> {
        if self.depth >= 256 {
            return Err(FlowError::ResourceLimit);
        }

        self.summary.node_visits += 1;
        self.depth += 1;
        let result = self.build_inner(node);
        self.depth -= 1;

        result
    }

    fn build_inner(&mut self, node: NodeId) -> Result<Fragment, FlowError> {
        let kind = self.semantic.nodes().kind(node);

        match kind {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => {
                self.atom(node, Step::Evaluate)
            }
            AstKind::LogicalExpression(expr) => {
                use oxc_ast::ast::LogicalOperator;

                let left = self.build(expr.left.node_id())?;
                let right = self.build(expr.right.node_id())?;
                let (take, skip) = match expr.operator {
                    LogicalOperator::And => (
                        Guard::Truthy(expr.left.node_id()),
                        Guard::Falsy(expr.left.node_id()),
                    ),
                    LogicalOperator::Or => (
                        Guard::Falsy(expr.left.node_id()),
                        Guard::Truthy(expr.left.node_id()),
                    ),
                    LogicalOperator::Coalesce => (
                        Guard::Nullish(expr.left.node_id()),
                        Guard::NonNullish(expr.left.node_id()),
                    ),
                };

                self.branch(node, left, right, None, take, skip)
            }
            AstKind::IfStatement(stmt) => {
                let test = self.build(stmt.test.node_id())?;
                let yes = self.build(stmt.consequent.node_id())?;
                let no = stmt
                    .alternate
                    .as_ref()
                    .map(|other| self.build(other.node_id()))
                    .transpose()?;

                self.branch(
                    node,
                    test,
                    yes,
                    no,
                    Guard::Truthy(stmt.test.node_id()),
                    Guard::Falsy(stmt.test.node_id()),
                )
            }
            AstKind::ConditionalExpression(expr) => {
                let test = self.build(expr.test.node_id())?;
                let yes = self.build(expr.consequent.node_id())?;
                let no = self.build(expr.alternate.node_id())?;

                self.branch(
                    node,
                    test,
                    yes,
                    Some(no),
                    Guard::Truthy(expr.test.node_id()),
                    Guard::Falsy(expr.test.node_id()),
                )
            }
            AstKind::FormalParameter(param) => {
                let start = self.atom(node, Step::ParameterDefault)?;
                let defaults = if let Some(value) = &param.initializer {
                    let value = self.build(value.node_id())?;

                    self.branch(
                        node,
                        start,
                        value,
                        None,
                        Guard::Undefined(node),
                        Guard::Defined(node),
                    )?
                } else {
                    start
                };
                let pattern = self.build(param.pattern.node_id())?;

                Ok(self.append(defaults, pattern))
            }
            AstKind::AssignmentPattern(pattern) => {
                let start = self.atom(node, Step::ParameterDefault)?;
                let value = self.build(pattern.right.node_id())?;
                let conditional = self.branch(
                    node,
                    start,
                    value,
                    None,
                    Guard::Undefined(node),
                    Guard::Defined(node),
                )?;
                let left = self.build(pattern.left.node_id())?;

                Ok(self.append(conditional, left))
            }
            AstKind::ForStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
            | AstKind::ForOfStatement(_)
            | AstKind::ForInStatement(_) => {
                let phases = loop_phases_of(kind).ok_or(FlowError::Unsupported(node))?;

                self.loop_flow(node, &phases)
            }
            AstKind::LabeledStatement(stmt) => {
                let mut fragment = self.build(stmt.body.node_id())?;
                let after = self.point(node, Step::Exit)?;
                let mut reaches = false;

                fragment.exits.retain(|exit| {
                    if exit.completion == Completion::Break(node)
                        || exit.completion == Completion::Normal
                    {
                        self.edge(
                            exit.from,
                            after,
                            Guard::Always,
                            CompletionAction::Produce(Completion::Normal),
                        );

                        reaches = true;

                        false
                    } else {
                        true
                    }
                });

                if reaches {
                    fragment.exits.push(FlowExit {
                        from: after,
                        completion: Completion::Normal,
                    });
                }

                Ok(fragment)
            }
            AstKind::BreakStatement(stmt) => {
                let target = self.control_target(
                    node,
                    stmt.label.as_ref().map(|label| label.name.as_str()),
                    false,
                )?;

                self.abrupt(node, Completion::Break(target))
            }
            AstKind::ContinueStatement(stmt) => {
                let target = self.control_target(
                    node,
                    stmt.label.as_ref().map(|label| label.name.as_str()),
                    true,
                )?;

                self.abrupt(node, Completion::Continue(target))
            }
            AstKind::ReturnStatement(_) => self.abrupt(node, Completion::Return),
            AstKind::ThrowStatement(_) => self.abrupt(node, Completion::Throw),
            AstKind::TryStatement(stmt) => {
                let mut body = self.build(stmt.block.node_id())?;

                if let Some(handler) = &stmt.handler {
                    let catch = self.build(handler.node_id())?;
                    let mut caught = false;

                    body.exits.retain(|exit| {
                        if exit.completion == Completion::Throw {
                            caught = true;

                            self.edge(
                                exit.from,
                                catch.entry,
                                Guard::Always,
                                CompletionAction::Produce(Completion::Normal),
                            );

                            false
                        } else {
                            true
                        }
                    });

                    if caught {
                        body.exits.extend(catch.exits);
                    }
                }

                if let Some(finalizer) = &stmt.finalizer {
                    body = self.finalize(body, finalizer.node_id())?;
                }

                Ok(body)
            }
            AstKind::Class(class) => self.class_flow(node, class),
            AstKind::SwitchStatement(_)
            | AstKind::WithStatement(_)
            | AstKind::ChainExpression(_)
            | AstKind::TSEnumDeclaration(_)
            | AstKind::TSNamespaceDeclaration(_)
            | AstKind::TSExternalModuleDeclaration(_)
            | AstKind::TSImportEqualsDeclaration(_) => Err(FlowError::Unsupported(node)),
            AstKind::AssignmentExpression(assignment) if assignment.operator.is_logical() => {
                Err(FlowError::Unsupported(node))
            }
            _ => {
                let children = self.children[node.index()].clone();
                let fragment = self.sequence(node, children)?;

                if matches!(
                    kind,
                    AstKind::CallExpression(_)
                        | AstKind::NewExpression(_)
                        | AstKind::IdentifierReference(_)
                        | AstKind::ComputedMemberExpression(_)
                        | AstKind::StaticMemberExpression(_)
                        | AstKind::PrivateFieldExpression(_)
                        | AstKind::BinaryExpression(_)
                        | AstKind::UnaryExpression(_)
                        | AstKind::AssignmentExpression(_)
                        | AstKind::UpdateExpression(_)
                        | AstKind::AwaitExpression(_)
                        | AstKind::TaggedTemplateExpression(_)
                        | AstKind::SpreadElement(_)
                        | AstKind::ObjectPattern(_)
                        | AstKind::ArrayPattern(_)
                        | AstKind::ImportExpression(_)
                ) {
                    let point = self.point(node, Step::Evaluate)?;
                    let throw = self.point(node, Step::Exit)?;
                    let normal = self.point(node, Step::Exit)?;
                    let mut output = self.append(
                        fragment,
                        Fragment {
                            entry: point,
                            exits: Ports::default(),
                        },
                    );

                    self.edge(
                        point,
                        throw,
                        Guard::Throws(node),
                        CompletionAction::Produce(Completion::Throw),
                    );
                    self.edge(
                        point,
                        normal,
                        Guard::ReturnsNormally(node),
                        CompletionAction::Preserve,
                    );
                    output.exits.extend([
                        FlowExit {
                            from: throw,
                            completion: Completion::Throw,
                        },
                        FlowExit {
                            from: normal,
                            completion: Completion::Normal,
                        },
                    ]);

                    Ok(output)
                } else {
                    Ok(fragment)
                }
            }
        }
    }

    fn abrupt(&mut self, node: NodeId, completion: Completion) -> Result<Fragment, FlowError> {
        let mut result = self.sequence(node, self.children[node.index()].clone())?;

        for exit in std::mem::take(&mut result.exits.normal) {
            if exit.completion == Completion::Normal {
                let endpoint = self.point(node, Step::Exit)?;

                self.edge(
                    exit.from,
                    endpoint,
                    Guard::Always,
                    CompletionAction::Produce(completion),
                );
                result.exits.push(FlowExit {
                    from: endpoint,
                    completion,
                });
            }
        }

        Ok(result)
    }

    fn branch(
        &mut self,
        node: NodeId,
        test: Fragment,
        yes: Fragment,
        no: Option<Fragment>,
        take: Guard,
        skip: Guard,
    ) -> Result<Fragment, FlowError> {
        let after = self.point(node, Step::Exit)?;
        let mut exits = Vec::new();

        for exit in test.exits {
            if exit.completion == Completion::Normal {
                self.edge(exit.from, yes.entry, take, CompletionAction::Preserve);
                self.edge(
                    exit.from,
                    no.as_ref().map_or(after, |no| no.entry),
                    skip,
                    CompletionAction::Preserve,
                );
            } else {
                exits.push(exit);
            }
        }

        let mut reaches = no.is_none();

        for exit in yes
            .exits
            .into_iter()
            .chain(no.into_iter().flat_map(|no| no.exits))
        {
            if exit.completion == Completion::Normal {
                self.edge(exit.from, after, Guard::Always, CompletionAction::Preserve);

                reaches = true;
            } else {
                exits.push(exit);
            }
        }

        if reaches {
            exits.push(FlowExit {
                from: after,
                completion: Completion::Normal,
            });
        }

        Ok(Fragment {
            entry: test.entry,
            exits: exits.into(),
        })
    }

    fn loop_flow(&mut self, node: NodeId, phases: &LoopPhases) -> Result<Fragment, FlowError> {
        let iteration = phases.iterates();
        let test_after = phases.tested_after;
        let init = phases.initialize.or(phases.iterable);
        let test = if iteration {
            phases.binding
        } else {
            phases.test
        };
        let update = phases.update;
        let body = phases.body;

        let init_point = self.atom(
            node,
            if iteration {
                Step::Iterable
            } else {
                Step::LoopInitialize
            },
        )?;
        let init = if let Some(init) = init {
            let value = self.build(init)?;

            self.append(init_point, value)
        } else {
            init_point
        };
        let test_point = self.atom(
            node,
            if iteration {
                Step::IterationNext
            } else {
                Step::LoopTest
            },
        )?;
        let test_point = if iteration {
            self.possible_throw(node, test_point)?
        } else {
            test_point
        };
        let test_fragment = if !iteration {
            if let Some(test) = test {
                let value = self.build(test)?;

                self.append(test_point, value)
            } else {
                test_point
            }
        } else {
            test_point
        };
        let mut body_point = self.atom(node, Step::LoopBody)?;

        if iteration {
            if let Some(left) = test {
                let assignment = self.build(left)?;
                body_point = self.append(body_point, assignment);
            }
        }

        let body_fragment = self.build(body)?;
        let body_fragment = self.append(body_point, body_fragment);
        let update = if let Some(update) = update {
            let update_point = self.atom(node, Step::LoopUpdate)?;
            let value = self.build(update)?;

            Some(self.append(update_point, value))
        } else {
            None
        };
        let continue_target = update
            .as_ref()
            .map_or(test_fragment.entry, |update| update.entry);
        let after = self.point(node, Step::Exit)?;
        let mut exits = Vec::new();

        for exit in init.exits {
            if exit.completion == Completion::Normal {
                self.edge(
                    exit.from,
                    if test_after {
                        body_fragment.entry
                    } else {
                        test_fragment.entry
                    },
                    Guard::Always,
                    CompletionAction::Preserve,
                );
            } else {
                exits.push(exit);
            }
        }

        for exit in test_fragment.exits {
            if exit.completion == Completion::Normal {
                let condition = test.unwrap_or(node);
                let take = if iteration {
                    Guard::IterationAvailable(node)
                } else if test.is_some() {
                    Guard::Truthy(condition)
                } else {
                    Guard::Always
                };

                self.edge(
                    exit.from,
                    body_fragment.entry,
                    take,
                    CompletionAction::Preserve,
                );

                if iteration || test.is_some() {
                    self.edge(
                        exit.from,
                        after,
                        if iteration {
                            Guard::IterationDone(node)
                        } else {
                            Guard::Falsy(condition)
                        },
                        CompletionAction::Preserve,
                    );
                }
            } else {
                exits.push(exit);
            }
        }

        for exit in body_fragment.exits {
            match exit.completion {
                Completion::Normal | Completion::Continue(_)
                    if exit.completion == Completion::Normal
                        || exit.completion == Completion::Continue(node) =>
                {
                    self.edge(
                        exit.from,
                        continue_target,
                        Guard::Always,
                        CompletionAction::Produce(Completion::Normal),
                    )
                }
                Completion::Break(target) if target == node => self.edge(
                    exit.from,
                    after,
                    Guard::Always,
                    CompletionAction::Produce(Completion::Normal),
                ),
                _ => exits.push(exit),
            }
        }

        for exit in update.into_iter().flat_map(|update| update.exits) {
            if exit.completion == Completion::Normal {
                self.edge(
                    exit.from,
                    test_fragment.entry,
                    Guard::Always,
                    CompletionAction::Preserve,
                );
            } else {
                exits.push(exit);
            }
        }

        exits.push(FlowExit {
            from: after,
            completion: Completion::Normal,
        });

        Ok(Fragment {
            entry: init.entry,
            exits: exits.into(),
        })
    }

    fn finalize(&mut self, body: Fragment, finalizer: NodeId) -> Result<Fragment, FlowError> {
        let mut exits = Vec::new();
        let mut groups = Vec::<(Completion, Vec<FlowPointId>)>::new();

        for exit in body.exits {
            if let Some((_, sources)) = groups
                .iter_mut()
                .find(|(completion, _)| *completion == exit.completion)
            {
                sources.push(exit.from);
            } else {
                groups.push((exit.completion, vec![exit.from]));
            }
        }

        for (pending, sources) in groups {
            let entry = self.point(finalizer, Step::FinallyEntry)?;
            let cleanup = self.build(finalizer)?;

            for source in sources {
                self.edge(
                    source,
                    entry,
                    Guard::Always,
                    CompletionAction::EnterFinally(pending),
                );
            }

            self.edge(
                entry,
                cleanup.entry,
                Guard::Always,
                CompletionAction::Preserve,
            );

            for exit in cleanup.exits {
                let result = if exit.completion == Completion::Normal {
                    pending
                } else {
                    exit.completion
                };
                let endpoint = self.point(finalizer, Step::Exit)?;

                self.edge(
                    exit.from,
                    endpoint,
                    Guard::Always,
                    if exit.completion == Completion::Normal {
                        CompletionAction::Resume(pending)
                    } else {
                        CompletionAction::Replace {
                            pending,
                            replacement: result,
                        }
                    },
                );
                exits.push(FlowExit {
                    from: endpoint,
                    completion: result,
                });
            }
        }

        Ok(Fragment {
            entry: body.entry,
            exits: exits.into(),
        })
    }

    fn possible_throw(
        &mut self,
        node: NodeId,
        mut fragment: Fragment,
    ) -> Result<Fragment, FlowError> {
        let normal = self.point(node, Step::Exit)?;
        let throw = self.point(node, Step::Exit)?;
        let reaches = !fragment.exits.normal.is_empty();

        for exit in std::mem::take(&mut fragment.exits.normal) {
            self.edge(
                exit.from,
                normal,
                Guard::ReturnsNormally(node),
                CompletionAction::Preserve,
            );
            self.edge(
                exit.from,
                throw,
                Guard::Throws(node),
                CompletionAction::Produce(Completion::Throw),
            );
        }

        if reaches {
            fragment.exits.extend([
                FlowExit {
                    from: normal,
                    completion: Completion::Normal,
                },
                FlowExit {
                    from: throw,
                    completion: Completion::Throw,
                },
            ]);
        }

        Ok(fragment)
    }

    fn class_flow(
        &mut self,
        node: NodeId,
        class: &oxc_ast::ast::Class<'a>,
    ) -> Result<Fragment, FlowError> {
        if class.declare {
            return self.atom(node, Step::Evaluate);
        }

        let phases = class_phases_of(class);

        if let Some(decorated) = phases.decorated {
            return Err(FlowError::Unsupported(decorated));
        }

        let saved = self.region;
        self.region = Region::ClassDefinition(node);
        let mut definition = self.atom(node, Step::Entry)?;

        if let Some(base) = phases.heritage {
            let base = self.build(base)?;
            let base = self.possible_throw(node, base)?;
            definition = self.append(definition, base);
        }

        for (element, key) in phases.keys {
            let key = self.build(key)?;
            let key = self.possible_throw(element, key)?;
            definition = self.append(definition, key);
        }

        for (_, value) in phases.statics {
            let value = self.build(value)?;
            definition = self.append(definition, value);
        }

        self.region = Region::Construction(node);
        let instances = phases
            .instances
            .into_iter()
            .map(|(_, value)| value)
            .collect();
        let construction = self.sequence(node, instances)?;

        self.summary
            .construction_entries
            .push((node, construction.entry));
        self.summary
            .construction_exits
            .push((node, construction.exits.into_iter().collect()));

        self.region = saved;

        Ok(definition)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoopPhases {
    pub initialize: Option<NodeId>,
    pub iterable: Option<NodeId>,
    pub test: Option<NodeId>,
    pub binding: Option<NodeId>,
    pub update: Option<NodeId>,
    pub body: NodeId,
    pub tested_after: bool,
}

impl LoopPhases {
    pub fn iterates(&self) -> bool {
        self.iterable.is_some()
    }

    pub fn repeats(&self, node: NodeId) -> bool {
        [self.test, self.binding, self.update].contains(&Some(node))
    }
}

pub fn loop_phases_of(kind: AstKind<'_>) -> Option<LoopPhases> {
    let phases = |body: NodeId| LoopPhases {
        initialize: None,
        iterable: None,
        test: None,
        binding: None,
        update: None,
        body,
        tested_after: false,
    };

    match kind {
        AstKind::ForStatement(statement) => Some(LoopPhases {
            initialize: statement.init.as_ref().map(|init| init.node_id()),
            test: statement.test.as_ref().map(|test| test.node_id()),
            update: statement.update.as_ref().map(|update| update.node_id()),
            ..phases(statement.body.node_id())
        }),
        AstKind::WhileStatement(statement) => Some(LoopPhases {
            test: Some(statement.test.node_id()),
            ..phases(statement.body.node_id())
        }),
        AstKind::DoWhileStatement(statement) => Some(LoopPhases {
            test: Some(statement.test.node_id()),
            tested_after: true,
            ..phases(statement.body.node_id())
        }),
        AstKind::ForOfStatement(statement) => Some(LoopPhases {
            iterable: Some(statement.right.node_id()),
            binding: Some(statement.left.node_id()),
            ..phases(statement.body.node_id())
        }),
        AstKind::ForInStatement(statement) => Some(LoopPhases {
            iterable: Some(statement.right.node_id()),
            binding: Some(statement.left.node_id()),
            ..phases(statement.body.node_id())
        }),
        _ => None,
    }
}

fn enclosing_of(
    semantic: &Semantic<'_>,
    node: NodeId,
    mut selects: impl FnMut(NodeId, AstKind<'_>) -> Option<Option<NodeId>>,
) -> Option<NodeId> {
    for ancestor in semantic.nodes().ancestors(node) {
        let kind = ancestor.kind();

        if matches!(
            kind,
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
        ) {
            return None;
        }

        if let Some(selected) = selects(ancestor.id(), kind) {
            return selected;
        }
    }

    None
}

pub fn enclosing_iteration_of(semantic: &Semantic<'_>, node: NodeId) -> Option<NodeId> {
    enclosing_of(semantic, node, |ancestor, kind| {
        is_iteration_kind(&kind).then_some(Some(ancestor))
    })
}

pub fn control_target_of(
    semantic: &Semantic<'_>,
    node: NodeId,
    label: Option<&str>,
    continuing: bool,
) -> Option<NodeId> {
    match label {
        Some(label) => enclosing_of(semantic, node, |ancestor, kind| {
            let AstKind::LabeledStatement(statement) = kind else {
                return None;
            };

            if statement.label.name.as_str() != label {
                return None;
            }

            Some(match continuing {
                true => labelled_iteration_of(semantic, statement.body.node_id()),
                false => Some(ancestor),
            })
        }),
        None if continuing => enclosing_iteration_of(semantic, node),
        None => enclosing_of(semantic, node, |ancestor, kind| {
            (is_iteration_kind(&kind) || matches!(kind, AstKind::SwitchStatement(_)))
                .then_some(Some(ancestor))
        }),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resumption {
    Handler(NodeId),
    Finalizer(NodeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interception {
    pub statement: NodeId,
    pub resumption: Resumption,
}

pub fn interceptions_of(semantic: &Semantic<'_>, node: NodeId) -> Vec<Interception> {
    let nodes = semantic.nodes();
    let mut found = Vec::new();
    let mut child = node;
    let mut parent = nodes.parent_id(child);

    while parent != child {
        let kind = nodes.kind(parent);

        if matches!(
            kind,
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
        ) {
            break;
        }

        if let AstKind::TryStatement(statement) = kind {
            let handler = statement.handler.as_ref().map(|handler| handler.node_id());
            let guarded = statement.block.node_id() == child;
            let handled = handler == Some(child);

            if guarded {
                if let Some(handler) = handler {
                    found.push(Interception {
                        statement: parent,
                        resumption: Resumption::Handler(handler),
                    });
                }
            }

            if let Some(finalizer) = &statement.finalizer {
                if guarded || handled {
                    found.push(Interception {
                        statement: parent,
                        resumption: Resumption::Finalizer(finalizer.node_id()),
                    });
                }
            }
        }

        child = parent;
        parent = nodes.parent_id(child);
    }

    found
}

fn labelled_iteration_of(semantic: &Semantic<'_>, node: NodeId) -> Option<NodeId> {
    let mut labelled = node;

    while let AstKind::LabeledStatement(inner) = semantic.nodes().kind(labelled) {
        labelled = inner.body.node_id();
    }

    is_iteration_kind(&semantic.nodes().kind(labelled)).then_some(labelled)
}

pub fn completion_of(semantic: &Semantic<'_>, node: NodeId) -> Option<Completion> {
    let label_of =
        |name: Option<&oxc_ast::ast::LabelIdentifier<'_>>| name.map(|label| label.name.to_string());

    match semantic.nodes().kind(node) {
        AstKind::ReturnStatement(_) => Some(Completion::Return),
        AstKind::ThrowStatement(_) => Some(Completion::Throw),
        AstKind::BreakStatement(statement) => {
            let label = label_of(statement.label.as_ref());

            control_target_of(semantic, node, label.as_deref(), false).map(Completion::Break)
        }
        AstKind::ContinueStatement(statement) => {
            let label = label_of(statement.label.as_ref());

            control_target_of(semantic, node, label.as_deref(), true).map(Completion::Continue)
        }
        AstKind::BlockStatement(block) => block
            .body
            .last()
            .and_then(|statement| completion_of(semantic, statement.node_id())),
        AstKind::IfStatement(statement) => {
            let consequent = completion_of(semantic, statement.consequent.node_id())?;
            let alternate = completion_of(
                semantic,
                statement
                    .alternate
                    .as_ref()
                    .map(|alternate| alternate.node_id())?,
            )?;

            Some(nearer_completion_of(semantic, node, consequent, alternate))
        }
        _ => None,
    }
}

fn nearer_completion_of(
    semantic: &Semantic<'_>,
    node: NodeId,
    first: Completion,
    second: Completion,
) -> Completion {
    let target_of = |completion: Completion| match completion {
        Completion::Break(target) | Completion::Continue(target) => Some(target),
        _ => None,
    };
    let (left, right) = (target_of(first), target_of(second));

    if first == second {
        return first;
    }

    if left == right {
        return match (first, second) {
            (Completion::Continue(_), _) => first,
            (_, Completion::Continue(_)) => second,
            _ => first,
        };
    }

    for ancestor in semantic.nodes().ancestor_ids(node) {
        if Some(ancestor) == left {
            return first;
        }

        if Some(ancestor) == right {
            return second;
        }
    }

    first
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClassPhases {
    pub heritage: Option<NodeId>,
    pub keys: Vec<(NodeId, NodeId)>,
    pub statics: Vec<(NodeId, NodeId)>,
    pub instances: Vec<(NodeId, NodeId)>,
    pub decorated: Option<NodeId>,
}

pub fn class_phases_of(class: &oxc_ast::ast::Class<'_>) -> ClassPhases {
    use oxc_ast::ast::ClassElement;

    let mut phases = ClassPhases {
        heritage: class
            .heritage
            .as_ref()
            .map(|heritage| heritage.expression.node_id()),
        decorated: (!class.decorators.is_empty()).then(|| class.node_id()),
        ..ClassPhases::default()
    };

    for element in &class.body.body {
        let decorated_element = |decorators: &[oxc_ast::ast::Decorator<'_>]| {
            (!decorators.is_empty()).then(|| element.node_id())
        };
        let (decorated, key, value, is_static) = match element {
            ClassElement::PropertyDefinition(property)
                if property.declare || property.r#type.is_abstract() =>
            {
                continue
            }
            ClassElement::AccessorProperty(property) if property.r#type.is_abstract() => continue,
            ClassElement::PropertyDefinition(property) => (
                decorated_element(&property.decorators),
                property.computed.then_some(&property.key),
                property.value.as_ref().map(|value| value.node_id()),
                property.r#static,
            ),
            ClassElement::AccessorProperty(accessor) => (
                decorated_element(&accessor.decorators),
                accessor.computed.then_some(&accessor.key),
                accessor.value.as_ref().map(|value| value.node_id()),
                accessor.r#static,
            ),
            ClassElement::MethodDefinition(method) => (
                decorated_element(&method.decorators).or_else(|| {
                    method
                        .value
                        .params
                        .items
                        .iter()
                        .find(|parameter| !parameter.decorators.is_empty())
                        .map(|parameter| parameter.node_id())
                }),
                (method.computed && method.value.body.is_some()).then_some(&method.key),
                None,
                method.r#static,
            ),
            ClassElement::StaticBlock(block) => (None, None, Some(block.node_id()), true),
            ClassElement::TSIndexSignature(_) => continue,
        };

        if phases.decorated.is_none() {
            phases.decorated = decorated;
        }

        if let Some(key) = key {
            phases.keys.push((element.node_id(), key.node_id()));
        }

        match (value, is_static) {
            (Some(value), true) => phases.statics.push((element.node_id(), value)),
            (Some(value), false) => phases.instances.push((element.node_id(), value)),
            (None, _) => {}
        }
    }

    phases
}

#[cfg(test)]
#[path = "flow.test.rs"]
mod tests;

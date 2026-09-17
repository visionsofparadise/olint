use std::borrow::Cow;

use oxc_ast::AstKind;
use oxc_cfg::BlockNodeId;
use oxc_semantic::{NodeId, Semantic};

use crate::project::FileId;
use crate::syntax::is_type_kind;

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

struct Target {
    node: NodeId,
    label: Option<String>,
    iteration: Option<NodeId>,
    unlabelled_break: bool,
}

struct Builder<'s, 'a> {
    semantic: &'s Semantic<'a>,
    children: &'s [Vec<NodeId>],
    summary: FlowSummary,
    targets: Vec<Target>,
    region: Region,
    limit: usize,
    depth: usize,
}

pub(crate) struct FlowIndex {
    children: Vec<Vec<NodeId>>,
}

impl FlowIndex {
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
            targets: Vec::new(),
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
    fn iteration_flow(
        &mut self,
        node: NodeId,
        iterable: NodeId,
        binding: NodeId,
        body: NodeId,
    ) -> Result<Fragment, FlowError> {
        self.loop_flow(node, Some(iterable), Some(binding), None, body, false, true)
    }

    fn control_target(
        &self,
        node: NodeId,
        label: Option<&str>,
        continuing: bool,
    ) -> Result<NodeId, FlowError> {
        self.targets
            .iter()
            .rev()
            .find(|target| match label {
                Some(label) => target.label.as_deref() == Some(label),
                None if continuing => target.label.is_none() && target.iteration.is_some(),
                None => target.unlabelled_break,
            })
            .and_then(|target| {
                if continuing {
                    target.iteration
                } else {
                    Some(target.node)
                }
            })
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
            AstKind::ForStatement(stmt) => self.loop_flow(
                node,
                stmt.init.as_ref().map(|n| n.node_id()),
                stmt.test.as_ref().map(|n| n.node_id()),
                stmt.update.as_ref().map(|n| n.node_id()),
                stmt.body.node_id(),
                false,
                false,
            ),
            AstKind::WhileStatement(stmt) => self.loop_flow(
                node,
                None,
                Some(stmt.test.node_id()),
                None,
                stmt.body.node_id(),
                false,
                false,
            ),
            AstKind::DoWhileStatement(stmt) => self.loop_flow(
                node,
                None,
                Some(stmt.test.node_id()),
                None,
                stmt.body.node_id(),
                true,
                false,
            ),
            AstKind::ForOfStatement(stmt) => self.iteration_flow(
                node,
                stmt.right.node_id(),
                stmt.left.node_id(),
                stmt.body.node_id(),
            ),
            AstKind::ForInStatement(stmt) => self.iteration_flow(
                node,
                stmt.right.node_id(),
                stmt.left.node_id(),
                stmt.body.node_id(),
            ),
            AstKind::LabeledStatement(stmt) => {
                let body = stmt.body.node_id();
                let mut labelled_body = body;

                while let AstKind::LabeledStatement(inner) =
                    self.semantic.nodes().kind(labelled_body)
                {
                    labelled_body = inner.body.node_id();
                }

                let iteration = matches!(
                    self.semantic.nodes().kind(labelled_body),
                    AstKind::ForStatement(_)
                        | AstKind::WhileStatement(_)
                        | AstKind::DoWhileStatement(_)
                        | AstKind::ForOfStatement(_)
                        | AstKind::ForInStatement(_)
                )
                .then_some(labelled_body);

                self.targets.push(Target {
                    node,
                    label: Some(stmt.label.name.to_string()),
                    iteration,
                    unlabelled_break: false,
                });

                let mut fragment = self.build(body)?;

                self.targets.pop();

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

    #[allow(clippy::too_many_arguments)]
    fn loop_flow(
        &mut self,
        node: NodeId,
        init: Option<NodeId>,
        test: Option<NodeId>,
        update: Option<NodeId>,
        body: NodeId,
        test_after: bool,
        iteration: bool,
    ) -> Result<Fragment, FlowError> {
        self.targets.push(Target {
            node,
            label: None,
            iteration: Some(node),
            unlabelled_break: true,
        });

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

        self.targets.pop();

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

        let saved = self.region;
        self.region = Region::ClassDefinition(node);
        let mut definition = self.atom(node, Step::Entry)?;

        if !class.decorators.is_empty() {
            return Err(FlowError::Unsupported(node));
        }

        if let Some(base) = &class.heritage {
            let base = self.build(base.expression.node_id())?;
            let base = self.possible_throw(node, base)?;
            definition = self.append(definition, base);
        }

        let mut instances = Vec::new();
        let mut statics = Vec::new();

        for element in &class.body.body {
            use oxc_ast::ast::ClassElement;

            match element {
                ClassElement::PropertyDefinition(property) => {
                    if !property.decorators.is_empty() {
                        return Err(FlowError::Unsupported(element.node_id()));
                    }

                    if property.declare || property.r#type.is_abstract() {
                        continue;
                    }

                    if property.computed {
                        let key = self.build(property.key.node_id())?;
                        let key = self.possible_throw(element.node_id(), key)?;
                        definition = self.append(definition, key);
                    }

                    if let Some(value) = &property.value {
                        if property.r#static {
                            statics.push(value.node_id());
                        } else {
                            instances.push(value.node_id());
                        }
                    }
                }
                ClassElement::StaticBlock(block) => statics.push(block.node_id()),
                ClassElement::MethodDefinition(method) => {
                    if !method.decorators.is_empty() {
                        return Err(FlowError::Unsupported(element.node_id()));
                    }

                    if method.value.body.is_some() && method.computed {
                        let key = self.build(method.key.node_id())?;
                        let key = self.possible_throw(element.node_id(), key)?;
                        definition = self.append(definition, key);
                    }
                }
                _ => return Err(FlowError::Unsupported(element.node_id())),
            }
        }

        for value in statics {
            let value = self.build(value)?;
            definition = self.append(definition, value);
        }

        self.region = Region::Construction(node);
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

#[cfg(test)]
#[path = "flow.test.rs"]
mod tests;

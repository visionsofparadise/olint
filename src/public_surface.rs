use std::collections::{HashMap, HashSet};

use oxc_ast::ast::{
    Argument, AssignmentTarget, Class, ClassElement, Expression, ForStatementLeft, Function,
    IdentifierReference, ImportOrExportKind, ObjectPropertyKind, PropertyKey, PropertyKind,
    Statement, TSAccessibility, TSNamespaceDeclarationBody,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::symbol::SymbolId;

use crate::analysis::Analysis;
use crate::config::{validate_entries, Config, ConfigError};
use crate::declarations::{
    element_name_of, surface_write_of, Binding, Declaration, FunctionId, FunctionNode,
    SurfaceTarget,
};
use crate::directives::PerfTag;
use crate::effects::{value_flow_of, ValueFlow};
use crate::paths::relative_path_of;
use crate::project::{FileId, Resolved};
use crate::receivers::{this_owner_of, Placement, ThisOwner};
use crate::syntax::{member_expression_of, unwrap};
use crate::unknowns::{SourceSpan, UnknownReason};

use super::{ApplicableLimit, PublicFunction};

const MAXIMUM_RETURNED_DEPTH: usize = 8;

pub(super) struct Discovery<'a> {
    pub functions: Vec<PublicFunction<'a>>,
    pub issues: Vec<(SourceSpan, SourceSpan, UnknownReason)>,
}

enum Work {
    Enter(SurfaceTarget, SourceSpan),
    Leave(SurfaceTarget),
}

struct Walk<'w, 'p, 'a> {
    analysis: &'w mut Analysis<'p, 'a>,
    config: &'w Config,
    found: Discovery<'a>,
    positions: HashMap<(FileId, NodeId), usize>,
    pending: Vec<Work>,
    active: HashSet<SurfaceTarget>,
    visited: HashSet<SurfaceTarget>,
    entry_site: SourceSpan,
    entry: String,
    limits: Vec<ApplicableLimit>,
    remaining: usize,
}

pub(super) fn discover<'a>(
    analysis: &mut Analysis<'_, 'a>,
    config: &Config,
) -> Result<Discovery<'a>, ConfigError> {
    validate_entries(analysis.project, config)?;

    let mut walk = Walk {
        analysis,
        config,
        found: Discovery {
            functions: Vec::new(),
            issues: Vec::new(),
        },
        positions: HashMap::new(),
        pending: Vec::new(),
        active: HashSet::new(),
        visited: HashSet::new(),
        entry_site: SourceSpan {
            file: FileId(0),
            start: 0,
            end: 0,
        },
        entry: String::new(),
        limits: Vec::new(),
        remaining: 100_000,
    };

    for (path, limits) in &config.entrypoints {
        walk.entry = relative_path_of(&walk.analysis.project.root, path);

        if config.is_ignored(&walk.entry) {
            continue;
        }

        let file = walk
            .analysis
            .project
            .file_by_path(path)
            .expect("validated entry");
        walk.entry_site = walk.site(file, walk.analysis.project.file(file).program.node_id());
        walk.limits = limits
            .iter()
            .cloned()
            .map(|limit| ApplicableLimit {
                limit,
                entry: walk.entry.clone(),
            })
            .collect();

        walk.visited.clear();
        walk.active.clear();
        walk.push(SurfaceTarget::Module(file), walk.entry_site);
        walk.run();
    }

    Ok(walk.found)
}

fn hidden(accessibility: Option<TSAccessibility>, key: &PropertyKey<'_>) -> bool {
    matches!(
        accessibility,
        Some(TSAccessibility::Private | TSAccessibility::Protected)
    ) || matches!(key, PropertyKey::PrivateIdentifier(_))
}

fn is_module_exports(name: &str) -> bool {
    name == "module" || name == "exports"
}

fn accepts_descriptor(names: &mut HashMap<String, HashSet<u8>>, name: String, kind: u8) -> bool {
    let kinds = names.entry(name).or_default();

    if kinds.contains(&0) {
        return false;
    }

    if kind == 0 {
        let first = kinds.is_empty();

        kinds.insert(0);

        first
    } else {
        kinds.insert(kind)
    }
}

fn primitive_annotation(annotation: Option<&oxc_ast::ast::TSTypeAnnotation<'_>>) -> bool {
    annotation.is_some_and(|annotation| {
        matches!(
            annotation.type_annotation,
            oxc_ast::ast::TSType::TSNumberKeyword(_)
                | oxc_ast::ast::TSType::TSStringKeyword(_)
                | oxc_ast::ast::TSType::TSBooleanKeyword(_)
                | oxc_ast::ast::TSType::TSBigIntKeyword(_)
                | oxc_ast::ast::TSType::TSNullKeyword(_)
                | oxc_ast::ast::TSType::TSUndefinedKeyword(_)
                | oxc_ast::ast::TSType::TSVoidKeyword(_)
                | oxc_ast::ast::TSType::TSNeverKeyword(_)
        )
    })
}

impl<'a> Walk<'_, '_, 'a> {
    fn site(&self, file: FileId, node: NodeId) -> SourceSpan {
        let span = self
            .analysis
            .project
            .file(file)
            .semantic
            .nodes()
            .kind(node)
            .span();

        SourceSpan {
            file,
            start: span.start,
            end: span.end,
        }
    }

    fn issue(&mut self, site: SourceSpan, reason: UnknownReason) {
        let issue = (site, self.entry_site, reason);

        if !self.found.issues.contains(&issue) {
            self.found.issues.push(issue);
        }
    }

    fn push(&mut self, target: SurfaceTarget, site: SourceSpan) {
        if self.remaining == 0 {
            self.issue(site, UnknownReason::ResourceExhaustion);

            return;
        }

        self.remaining -= 1;

        self.pending.push(Work::Enter(target, site));
    }

    fn node(&mut self, file: FileId, node: NodeId) {
        self.push(SurfaceTarget::Node(file, node), self.site(file, node));
    }

    fn function(&mut self, file: FileId, function: FunctionNode<'a>) {
        if self
            .analysis
            .function_tags(file, function)
            .contains(&PerfTag::Ignore)
        {
            return;
        }

        let key = (file, function.node_id());

        if let Some(position) = self.positions.get(&key) {
            for limit in &self.limits {
                let limits = &mut self.found.functions[*position].limits;

                if !limits
                    .iter()
                    .any(|known| known.entry == limit.entry && known.limit.cost == limit.limit.cost)
                {
                    limits.push(limit.clone());
                }
            }
        } else {
            self.positions.insert(key, self.found.functions.len());
            self.found.functions.push(PublicFunction {
                file,
                function,
                limits: self.limits.clone(),
                own_limit: false,
            });
        }
    }

    fn run(&mut self) {
        while let Some(work) = self.pending.pop() {
            let (target, site) = match work {
                Work::Leave(target) => {
                    self.active.remove(&target);
                    self.visited.insert(target);

                    continue;
                }
                Work::Enter(target, site) => (target, site),
            };

            if target == SurfaceTarget::Unresolved {
                self.issue(site, UnknownReason::Target);

                continue;
            }

            if self.active.contains(&target) {
                if !matches!(target, SurfaceTarget::Module(_)) {
                    self.issue(site, UnknownReason::Target);
                }

                continue;
            }

            if self.visited.contains(&target) {
                continue;
            }

            let file = match target {
                SurfaceTarget::Node(file, _) | SurfaceTarget::Module(file) => file,
                SurfaceTarget::Unresolved => unreachable!(),
            };
            let source = self.analysis.project.file(file);

            if self.config.is_ignored(&source.relative)
                || (!self.config.explicit_entrypoints && self.analysis.project.is_test_path(file))
            {
                continue;
            }

            if !self.analysis.project.is_project_file(file)
                && matches!(target, SurfaceTarget::Module(_))
                && file == self.entry_site.file
            {
                continue;
            }

            self.active.insert(target);
            self.pending.push(Work::Leave(target));

            match target {
                SurfaceTarget::Module(file) => self.module(file),
                SurfaceTarget::Node(file, node) => self.visit(file, node),
                SurfaceTarget::Unresolved => unreachable!(),
            }
        }
    }

    fn module(&mut self, file: FileId) {
        let exports = self
            .analysis
            .declarations
            .surface_exports(self.analysis.project, file);
        let site = self.site(file, self.analysis.project.file(file).program.node_id());

        for (_, targets) in exports.into_iter().rev() {
            for target in targets.into_iter().rev() {
                self.push(target, site);
            }
        }

        for statement in self.analysis.project.file(file).program.body.iter().rev() {
            if let Statement::TSExportAssignment(export) = statement {
                self.node(file, export.expression.node_id());
            }

            if let Statement::ExportAllDeclaration(export) = statement {
                if export.export_kind == ImportOrExportKind::Value
                    && !matches!(
                        self.analysis
                            .project
                            .resolve(file, export.source.value.as_str()),
                        Resolved::File(_)
                    )
                {
                    self.issue(self.site(file, export.node_id()), UnknownReason::Target);
                }
            }
        }

        self.commonjs(file);
    }

    fn global(&self, file: FileId, expression: &Expression<'_>, name: &str) -> bool {
        matches!(unwrap(expression),Expression::Identifier(reference) if reference.name == name && self.analysis.project.file(file).semantic.scoping().get_reference(reference.reference_id()).symbol_id().is_none())
    }

    fn commonjs_target(&self, file: FileId, expression: &Expression<'_>) -> Option<String> {
        match unwrap(expression) {
            Expression::StaticMemberExpression(member)
                if self.global(file, &member.object, "module")
                    && member.property.name == "exports" =>
            {
                Some(String::new())
            }
            Expression::StaticMemberExpression(member)
                if self.global(file, &member.object, "exports")
                    || self.commonjs_target(file, &member.object).as_deref() == Some("") =>
            {
                Some(member.property.name.to_string())
            }
            Expression::ComputedMemberExpression(member)
                if self.global(file, &member.object, "exports")
                    || self.commonjs_target(file, &member.object).as_deref() == Some("") =>
            {
                Some(match unwrap(&member.expression) {
                    Expression::StringLiteral(key) => key.value.to_string(),
                    _ => "*".to_string(),
                })
            }
            _ => None,
        }
    }

    fn assignment_target(
        &self,
        file: FileId,
        target: &oxc_ast::ast::AssignmentTarget<'_>,
    ) -> Option<(String, bool)> {
        let (object, name) = match target {
            oxc_ast::ast::AssignmentTarget::StaticMemberExpression(member) => {
                (&member.object, member.property.name.to_string())
            }
            oxc_ast::ast::AssignmentTarget::ComputedMemberExpression(member) => (
                &member.object,
                match unwrap(&member.expression) {
                    Expression::StringLiteral(key) => key.value.to_string(),
                    _ => "*".to_string(),
                },
            ),
            _ => return None,
        };

        if self.global(file, object, "module") && name == "exports" {
            return Some((String::new(), false));
        }

        let alias = self.global(file, object, "exports");

        (alias || self.commonjs_target(file, object).as_deref() == Some(""))
            .then_some((name, alias))
    }

    fn commonjs(&mut self, file: FileId) {
        let mut values: Vec<(String, NodeId)> = Vec::new();
        let mut replaced = false;
        let mut handled = HashSet::new();

        for statement in &self.analysis.project.file(file).program.body {
            let Statement::ExpressionStatement(statement) = statement else {
                continue;
            };
            let Expression::AssignmentExpression(assignment) = unwrap(&statement.expression) else {
                continue;
            };
            let Some((name, alias)) = self.assignment_target(file, &assignment.left) else {
                continue;
            };

            handled.insert(assignment.node_id());

            if replaced && alias {
                continue;
            }

            if name == "*" || !assignment.operator.is_assign() {
                self.issue(self.site(file, assignment.node_id()), UnknownReason::Target);
                values.clear();

                continue;
            }

            if name.is_empty() {
                values.clear();

                replaced = true;

                if let Expression::ObjectExpression(object) = unwrap(&assignment.right) {
                    values = self.object_values(file, object);

                    values.reverse();

                    continue;
                }
            }

            if values.iter().any(|(key, _)| key.is_empty()) && !name.is_empty() {
                self.issue(self.site(file, assignment.node_id()), UnknownReason::Target);
                values.retain(|(key, _)| !key.is_empty());
            }

            values.retain(|(key, _)| key != &name);
            values.push((name, assignment.right.node_id()));
        }

        let mut pending: Vec<_> = self
            .analysis
            .project
            .file(file)
            .program
            .body
            .iter()
            .map(Statement::node_id)
            .collect();

        while let Some(node) = pending.pop() {
            if self.remaining == 0 {
                self.issue(self.site(file, node), UnknownReason::ResourceExhaustion);

                break;
            }

            self.remaining -= 1;

            match self.analysis.project.file(file).semantic.nodes().kind(node) {
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => {
                    continue
                }
                AstKind::AssignmentExpression(assignment)
                    if !handled.contains(&node)
                        && self.assignment_target(file, &assignment.left).is_some() =>
                {
                    self.issue(self.site(file, node), UnknownReason::Target);

                    if let Some((name, _)) = self.assignment_target(file, &assignment.left) {
                        if name.is_empty() || name == "*" {
                            values.clear();
                        } else {
                            values.retain(|(key, _)| key != &name && !key.is_empty());
                        }
                    }
                }
                _ => {}
            }

            pending.extend(self.analysis.project.file(file).children_of(node));
        }

        for (_, node) in values.into_iter().rev() {
            self.node(file, node);
        }
    }

    fn object_values(
        &mut self,
        file: FileId,
        object: &oxc_ast::ast::ObjectExpression<'_>,
    ) -> Vec<(String, NodeId)> {
        let mut names: HashMap<String, HashSet<u8>> = HashMap::new();
        let mut values = Vec::new();
        let mut spread = false;

        for property in object.properties.iter().rev() {
            match property {
                ObjectPropertyKind::SpreadProperty(property) => {
                    spread = true;

                    self.issue(self.site(file, property.node_id()), UnknownReason::Target);
                }
                ObjectPropertyKind::ObjectProperty(property) => {
                    let Some(name) = property.key.static_name() else {
                        self.issue(self.site(file, property.node_id()), UnknownReason::Target);

                        spread = true;

                        continue;
                    };
                    let name = name.into_owned();

                    if !accepts_descriptor(&mut names, name.clone(), property.kind as u8) {
                        continue;
                    }

                    if spread {
                        self.issue(self.site(file, property.node_id()), UnknownReason::Target);

                        continue;
                    }

                    values.push((name, property.value.node_id()));
                }
            }
        }

        values
    }

    fn surface_writes(&mut self, file: FileId, symbols: Vec<SymbolId>) {
        let project = self.analysis.project;
        let mut pending: Vec<(Binding, bool)> = symbols
            .into_iter()
            .map(|symbol| {
                let binding = Binding::Symbol { file, symbol };

                (binding, self.may_escape(binding))
            })
            .collect();
        let roots: HashSet<Binding> = pending.iter().map(|(binding, _)| *binding).collect();
        let mut scanned = HashSet::new();

        while let Some((binding, escaping)) = pending.pop() {
            if !scanned.insert(binding) {
                continue;
            }

            let writes = self
                .analysis
                .declarations
                .surface_writes_of(project, binding);

            for (file, write) in &writes {
                let rebinding = matches!(
                    project.file(*file).semantic.nodes().kind(*write),
                    AstKind::IdentifierReference(_)
                );

                if (!rebinding || roots.contains(&binding))
                    && self.may_install_callable(*file, *write)
                {
                    self.issue(self.site(*file, *write), UnknownReason::Target);
                }
            }

            for imported in self.analysis.declarations.importers_of(project, binding) {
                pending.push((imported, escaping));
            }

            for (file, node, write) in self
                .analysis
                .declarations
                .surface_references_of(project, binding)
            {
                if write {
                    continue;
                }

                match value_flow_of(project.file(file).semantic.nodes(), node) {
                    ValueFlow::Alias(target) => {
                        self.alias_bindings(file, target, escaping, &mut pending)
                    }
                    ValueFlow::Stored(assignment) if escaping => {
                        match self.stored_binding_of(file, assignment) {
                            Ok(Some(root)) => pending.push((root, escaping)),
                            Ok(None) => {}
                            Err(()) => {
                                self.issue(self.site(file, assignment), UnknownReason::Target)
                            }
                        }
                    }
                    ValueFlow::Argument(call, index)
                        if escaping && !writes.contains(&(file, call)) =>
                    {
                        self.argument_bindings(file, call, index, escaping, &mut pending)
                    }
                    ValueFlow::Receiver(call) if escaping && !writes.contains(&(file, call)) => {
                        self.receiver_writes(file, call, &mut HashSet::new())
                    }
                    ValueFlow::Escaped(site) if escaping => {
                        self.issue(self.site(file, site), UnknownReason::Target)
                    }
                    _ => {}
                }
            }
        }
    }

    fn receiver_writes(&mut self, file: FileId, call: NodeId, visited: &mut HashSet<FunctionId>) {
        let project = self.analysis.project;
        let AstKind::CallExpression(expression) = project.file(file).semantic.nodes().kind(call)
        else {
            return self.issue(self.site(file, call), UnknownReason::Target);
        };
        let targets = self.analysis.resolved_callee_of(file, expression).targets;

        if targets.open || targets.known.is_empty() {
            let inert = expression.arguments.iter().all(|argument| {
                argument.as_expression().is_some_and(|argument| {
                    self.analysis.is_non_callable_expression(file, argument)
                })
            });

            if !inert {
                self.issue(self.site(file, call), UnknownReason::Target);
            }
        }

        for target in targets.known {
            if !visited.insert(target) {
                continue;
            }

            let nodes = project.file(target.file).semantic.nodes();
            let span = nodes.kind(target.node).span();
            let receivers: Vec<NodeId> = nodes
                .iter()
                .filter(|node| {
                    matches!(node.kind(), AstKind::ThisExpression(_))
                        && span.contains_inclusive(node.kind().span())
                        && nodes
                            .ancestors(node.id())
                            .find(|ancestor| matches!(ancestor.kind(), AstKind::Function(_)))
                            .is_some_and(|owner| owner.id() == target.node)
                })
                .map(|node| node.id())
                .collect();

            for receiver in receivers {
                match value_flow_of(nodes, receiver) {
                    ValueFlow::Read => {}
                    ValueFlow::Member => {
                        if let Some(write) = surface_write_of(nodes, receiver) {
                            if self.may_install_callable(target.file, write) {
                                self.issue(self.site(target.file, write), UnknownReason::Target);
                            }
                        }
                    }
                    ValueFlow::Receiver(inner) => self.receiver_writes(target.file, inner, visited),
                    ValueFlow::Alias(site)
                    | ValueFlow::Stored(site)
                    | ValueFlow::Argument(site, _)
                    | ValueFlow::Escaped(site) => {
                        self.issue(self.site(target.file, site), UnknownReason::Target)
                    }
                }
            }
        }
    }

    fn may_escape(&self, binding: Binding) -> bool {
        match self
            .analysis
            .declarations
            .of_binding(self.analysis.project, binding)
        {
            Some(Declaration::Function { .. }) => false,
            Some(Declaration::Variable { declarator, .. }) => !matches!(
                declarator.init.as_ref().map(unwrap),
                Some(Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_))
            ),
            _ => true,
        }
    }

    fn alias_bindings(
        &mut self,
        file: FileId,
        target: NodeId,
        escaping: bool,
        pending: &mut Vec<(Binding, bool)>,
    ) {
        let project = self.analysis.project;
        let kind = project.file(file).semantic.nodes().kind(target);
        let assigned = match kind {
            AstKind::AssignmentExpression(assignment) => Some(&assignment.left),
            AstKind::AssignmentTargetWithDefault(default) => Some(&default.binding),
            _ => None,
        };

        if let Some(left) = assigned {
            return match left {
                AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                    self.alias_reference(file, target, reference, escaping, pending)
                }
                _ => self.issue(self.site(file, target), UnknownReason::Target),
            };
        }

        let identifiers = match kind {
            AstKind::VariableDeclarator(declarator) => declarator.id.get_binding_identifiers(),
            AstKind::ForOfStatement(statement) => match &statement.left {
                ForStatementLeft::VariableDeclaration(declaration) => declaration
                    .declarations
                    .iter()
                    .flat_map(|declarator| declarator.id.get_binding_identifiers())
                    .collect(),
                ForStatementLeft::AssignmentTargetIdentifier(reference) => {
                    return self.alias_reference(file, target, reference, escaping, pending)
                }
                _ => return self.issue(self.site(file, target), UnknownReason::Target),
            },
            AstKind::AssignmentTargetPropertyIdentifier(property) => {
                return self.alias_reference(file, target, &property.binding, escaping, pending)
            }
            _ => return self.issue(self.site(file, target), UnknownReason::Target),
        };

        for identifier in identifiers {
            pending.push((
                Binding::Symbol {
                    file,
                    symbol: identifier.symbol_id(),
                },
                escaping,
            ));
        }
    }

    fn alias_reference(
        &mut self,
        file: FileId,
        target: NodeId,
        reference: &IdentifierReference<'a>,
        escaping: bool,
        pending: &mut Vec<(Binding, bool)>,
    ) {
        match self.analysis.declarations.binding_of_reference(
            self.analysis.project,
            file,
            reference,
        ) {
            Some(binding) => pending.push((binding, escaping)),
            None => self.issue(self.site(file, target), UnknownReason::Target),
        }
    }

    fn stored_binding_of(&self, file: FileId, assignment: NodeId) -> Result<Option<Binding>, ()> {
        let project = self.analysis.project;
        let AstKind::AssignmentExpression(assignment) =
            project.file(file).semantic.nodes().kind(assignment)
        else {
            return Err(());
        };
        let mut object = assignment.left.as_member_expression().ok_or(())?.object();

        loop {
            match unwrap(object) {
                Expression::Identifier(reference) => {
                    return match self
                        .analysis
                        .declarations
                        .binding_of_reference(project, file, reference)
                    {
                        Some(binding) => Ok(Some(binding)),
                        None if is_module_exports(reference.name.as_str()) => Ok(None),
                        None => Err(()),
                    }
                }
                other => object = member_expression_of(other).ok_or(())?.object(),
            }
        }
    }

    fn argument_bindings(
        &mut self,
        file: FileId,
        call: NodeId,
        index: usize,
        escaping: bool,
        pending: &mut Vec<(Binding, bool)>,
    ) {
        let (targets, arguments) =
            match self.analysis.project.file(file).semantic.nodes().kind(call) {
                AstKind::CallExpression(expression) => (
                    self.analysis.resolved_callee_of(file, expression).targets,
                    &expression.arguments,
                ),
                AstKind::NewExpression(expression) => (
                    self.analysis.constructor_targets_of(file, expression),
                    &expression.arguments,
                ),
                _ => return,
            };
        let spread = arguments[..=index]
            .iter()
            .any(|argument| matches!(argument, Argument::SpreadElement(_)));

        if spread
            || targets.open
            || targets.known.is_empty()
            || targets
                .known
                .iter()
                .any(|target| self.analysis.dynamic_scope_of(target.file, target.node).1)
        {
            return self.issue(self.site(file, call), UnknownReason::Target);
        }

        for target in targets.known {
            let parameters = match self.analysis.function_at(target) {
                FunctionNode::Function(function) => &function.params,
                FunctionNode::Arrow(arrow) => &arrow.params,
            };
            let identifiers = match parameters.items.get(index) {
                Some(parameter) => parameter.pattern.get_binding_identifiers(),
                None => parameters
                    .rest
                    .iter()
                    .flat_map(|rest| rest.rest.argument.get_binding_identifiers())
                    .collect(),
            };

            for identifier in identifiers {
                pending.push((
                    Binding::Symbol {
                        file: target.file,
                        symbol: identifier.symbol_id(),
                    },
                    escaping,
                ));
            }
        }
    }

    fn may_install_callable(&mut self, file: FileId, write: NodeId) -> bool {
        let project = self.analysis.project;
        let nodes = project.file(file).semantic.nodes();
        let node = match nodes.kind(write) {
            AstKind::IdentifierReference(_) => nodes.parent_id(write),
            _ => write,
        };

        match nodes.kind(node) {
            AstKind::UpdateExpression(_) => false,
            AstKind::AssignmentExpression(assignment) if assignment.operator.is_assign() => !self
                .analysis
                .is_non_callable_expression(file, &assignment.right),
            AstKind::AssignmentExpression(assignment) => assignment.operator.is_logical(),
            AstKind::CallExpression(call) => {
                let Some(member) = call.callee.as_member_expression() else {
                    return true;
                };
                let reflective = matches!(unwrap(member.object()), Expression::Identifier(owner) if owner.name == "Object" || owner.name == "Reflect");
                let stored = &call.arguments[usize::from(reflective).min(call.arguments.len())..];

                !stored.iter().all(|argument| {
                    argument.as_expression().is_some_and(|expression| {
                        self.analysis.is_non_callable_expression(file, expression)
                    })
                })
            }
            _ => true,
        }
    }

    fn visit(&mut self, file: FileId, node: NodeId) {
        let kind = self.analysis.project.file(file).semantic.nodes().kind(node);
        let site = self.site(file, node);
        let symbols = match kind {
            AstKind::VariableDeclarator(declaration) => declaration
                .id
                .get_binding_identifiers()
                .into_iter()
                .map(|identifier| identifier.symbol_id())
                .collect(),
            AstKind::Function(function) => function
                .id
                .iter()
                .map(|identifier| identifier.symbol_id())
                .collect(),
            AstKind::Class(class) => class
                .id
                .iter()
                .map(|identifier| identifier.symbol_id())
                .collect(),
            AstKind::TSNamespaceDeclaration(namespace) => vec![namespace.id.symbol_id()],
            _ => Vec::new(),
        };

        self.surface_writes(file, symbols);

        match kind {
            AstKind::Function(function) => {
                if function.body.is_some() {
                    self.function(file, FunctionNode::Function(function));
                    self.function_results(file, function);
                } else {
                    self.issue(site, UnknownReason::Target);
                }
            }
            AstKind::ArrowFunctionExpression(function) => {
                self.function(file, FunctionNode::Arrow(function))
            }
            AstKind::VariableDeclarator(declaration) => match &declaration.init {
                Some(expression) => self.node(file, expression.node_id()),
                None if primitive_annotation(declaration.type_annotation.as_deref()) => {}
                None => self.issue(site, UnknownReason::Target),
            },
            AstKind::VariableDeclaration(declaration) => {
                for declarator in declaration.declarations.iter().rev() {
                    self.node(file, declarator.node_id());
                }
            }
            AstKind::IdentifierReference(reference) => {
                for target in self
                    .analysis
                    .declarations
                    .surface_reference(self.analysis.project, file, reference)
                    .into_iter()
                    .rev()
                {
                    self.push(target, site);
                }
            }
            AstKind::ObjectExpression(object) => {
                for (_, value) in self.object_values(file, object) {
                    self.node(file, value);
                }
            }
            AstKind::Class(class) => self.class(file, class),
            AstKind::ArrayExpression(array) => {
                for element in array.elements.iter().rev() {
                    if let Some(expression) = element.as_expression() {
                        self.node(file, expression.node_id());
                    } else if !matches!(element, oxc_ast::ast::ArrayExpressionElement::Elision(_)) {
                        self.issue(site, UnknownReason::Target);
                    }
                }
            }
            AstKind::TSNamespaceDeclaration(namespace) => match &namespace.body {
                TSNamespaceDeclarationBody::TSNamespaceDeclaration(inner) => {
                    self.node(file, inner.node_id())
                }
                TSNamespaceDeclarationBody::TSModuleBlock(block) => {
                    for statement in block.body.iter().rev() {
                        if let Statement::ExportDeclaration(export) = statement {
                            self.node(file, export.declaration.node_id());
                        }
                    }
                }
            },
            AstKind::ParenthesizedExpression(expression) => {
                self.node(file, expression.expression.node_id())
            }
            AstKind::TSAsExpression(expression) => self.node(file, expression.expression.node_id()),
            AstKind::TSSatisfiesExpression(expression) => {
                self.node(file, expression.expression.node_id())
            }
            AstKind::TSNonNullExpression(expression) => {
                self.node(file, expression.expression.node_id())
            }
            AstKind::TSTypeAssertion(expression) => {
                self.node(file, expression.expression.node_id())
            }
            AstKind::BooleanLiteral(_)
            | AstKind::NullLiteral(_)
            | AstKind::NumericLiteral(_)
            | AstKind::BigIntLiteral(_)
            | AstKind::StringLiteral(_)
            | AstKind::TemplateLiteral(_)
            | AstKind::UnaryExpression(_)
            | AstKind::BinaryExpression(_)
            | AstKind::TSInterfaceDeclaration(_)
            | AstKind::TSTypeAliasDeclaration(_)
            | AstKind::TSEnumDeclaration(_) => {}
            _ => self.issue(site, UnknownReason::Target),
        }
    }

    fn function_results(&mut self, file: FileId, function: &'a Function<'a>) {
        let nodes = self.analysis.project.file(file).semantic.nodes();
        let target = FunctionId {
            file,
            node: function.node_id(),
        };
        let getter = match nodes.parent_kind(function.node_id()) {
            AstKind::MethodDefinition(method) => method.kind.is_get(),
            AstKind::ObjectProperty(property) => property.kind == PropertyKind::Get,
            _ => false,
        };

        if getter {
            for value in self
                .analysis
                .returned_expressions_of(target)
                .into_iter()
                .rev()
            {
                self.surfaced_value(file, function.span, value, 0);
            }
        }

        self.receiver_installs(target, &mut HashSet::new());
    }

    fn surfaced_value(
        &mut self,
        file: FileId,
        scope: oxc_span::Span,
        value: &'a Expression<'a>,
        depth: usize,
    ) {
        if self.analysis.is_non_callable_expression(file, value) {
            return;
        }

        let local = match unwrap(value) {
            Expression::Identifier(reference) => matches!(
                self.analysis.declarations.of_reference(self.analysis.project, file, reference),
                Some(Declaration::Variable { file: owner, declarator, .. })
                    if owner == file && scope.contains_inclusive(declarator.span)
            )
            .then_some(reference),
            _ => None,
        };
        let Some(reference) = local else {
            return self.node(file, value.node_id());
        };

        match self.analysis.local_values_of(file, reference) {
            Some(values) if depth < MAXIMUM_RETURNED_DEPTH => {
                for (owner, value) in values {
                    self.surfaced_value(owner, scope, value, depth + 1);
                }
            }
            _ => self.issue(self.site(file, value.node_id()), UnknownReason::Target),
        }
    }

    fn receiver_installs(&mut self, function: FunctionId, visited: &mut HashSet<FunctionId>) {
        if !visited.insert(function) {
            return;
        }

        let file = function.file;
        let nodes = self.analysis.project.file(file).semantic.nodes();

        for receiver in self.analysis.receiver_nodes_of(function) {
            match value_flow_of(nodes, receiver) {
                ValueFlow::Member => {
                    if let Some(write) = surface_write_of(nodes, receiver) {
                        let scope = nodes.kind(function.node).span();

                        self.receiver_install(file, scope, receiver, write);
                    }
                }
                ValueFlow::Receiver(call) => {
                    let AstKind::CallExpression(expression) = nodes.kind(call) else {
                        continue;
                    };

                    for target in self
                        .analysis
                        .resolved_callee_of(file, expression)
                        .targets
                        .known
                    {
                        self.receiver_installs(target, visited);
                    }
                }
                ValueFlow::Alias(site) | ValueFlow::Stored(site) | ValueFlow::Argument(site, _) => {
                    self.issue(self.site(file, site), UnknownReason::Target)
                }
                ValueFlow::Read | ValueFlow::Escaped(_) => {}
            }
        }
    }

    fn receiver_install(
        &mut self,
        file: FileId,
        scope: oxc_span::Span,
        receiver: NodeId,
        write: NodeId,
    ) {
        if !self.may_install_callable(file, write) {
            return;
        }

        let project = self.analysis.project;
        let instance = matches!(
            this_owner_of(project, file, receiver),
            Some(ThisOwner::Class {
                placement: Placement::Instance,
                ..
            })
        );

        match project.file(file).semantic.nodes().kind(write) {
            AstKind::AssignmentExpression(assignment)
                if assignment.operator.is_assign() || assignment.operator.is_logical() =>
            {
                if !(instance && self.is_caller_value(file, &assignment.right)) {
                    self.surfaced_value(file, scope, &assignment.right, 0);
                }
            }
            AstKind::CallExpression(call)
                if instance
                    && call.arguments.iter().all(|argument| match argument {
                        Argument::SpreadElement(spread) => {
                            self.is_caller_value(file, &spread.argument)
                        }
                        argument => argument.as_expression().is_some_and(|argument| {
                            self.is_caller_value(file, argument)
                                || self.analysis.is_non_callable_expression(file, argument)
                        }),
                    }) => {}
            _ => self.issue(self.site(file, write), UnknownReason::Target),
        }
    }

    fn is_caller_value(&self, file: FileId, value: &Expression<'a>) -> bool {
        matches!(
            unwrap(value),
            Expression::Identifier(reference)
                if matches!(
                    self.analysis
                        .declarations
                        .of_reference(self.analysis.project, file, reference),
                    Some(Declaration::Parameter { .. })
                )
        )
    }

    fn class(&mut self, mut file: FileId, mut class: &'a Class<'a>) {
        let mut lineage = Vec::new();
        let mut visited = HashSet::new();
        let mut complete = true;

        loop {
            let site = self.site(file, class.node_id());

            if !visited.insert((file, class.node_id())) || lineage.len() == 256 {
                self.issue(site, UnknownReason::ResourceExhaustion);

                complete = false;

                break;
            }

            lineage.push((file, class, field_mask(class)));

            let Some(heritage) = &class.heritage else {
                break;
            };
            let Some((next_file, next_class)) = self.analysis.declarations.class_of_expression(
                self.analysis.project,
                file,
                unwrap(&heritage.expression),
            ) else {
                self.issue(site, UnknownReason::Target);

                complete = false;

                break;
            };
            file = next_file;
            class = next_class;
        }

        let instance_names: HashSet<_> = lineage
            .iter()
            .flat_map(|(_, _, mask)| {
                mask.fields
                    .iter()
                    .filter(|(placement, _)| !*placement)
                    .map(|(_, name)| name.clone())
            })
            .collect();
        let instance_fields = lineage.iter().any(|(_, _, mask)| mask.placement[0]);
        let opaque_instances = !complete || lineage.iter().any(|(_, _, mask)| mask.opaque[0]);
        let mut names = HashSet::new();
        let mut values = Vec::new();
        let mut opaque_names = [false; 2];
        let mut opaque_instance_values = false;
        let mut constructor_selected = false;

        for (file, class, mask) in lineage {
            let site = self.site(file, class.node_id());
            let mut own_names = HashSet::new();
            let mut descriptors = HashMap::new();
            let mut own_values = Vec::new();
            let mut later = [false; 2];
            let fields = &mask.fields;
            let mut field_placement = mask.placement;
            let mut opaque_fields = mask.opaque;
            field_placement[0] = instance_fields;
            opaque_fields[0] = opaque_instances;

            for element in class.body.body.iter().rev() {
                if let ClassElement::MethodDefinition(method) = element {
                    if method.kind.is_constructor() {
                        if !constructor_selected && method.value.body.is_some() {
                            constructor_selected = true;

                            if !hidden(method.accessibility, &method.key) {
                                own_values.push((file, method.value.node_id()));
                            }
                        } else if !constructor_selected && !hidden(method.accessibility,&method.key) && !class.body.body.iter().any(|element|matches!(element,ClassElement::MethodDefinition(candidate) if candidate.kind.is_constructor() && candidate.value.body.is_some())) {
                            self.issue(self.site(file,method.node_id()),UnknownReason::Target);
                        }

                        continue;
                    }
                }

                let Some(name) = element_name_of(element) else {
                    if !matches!(element, ClassElement::StaticBlock(_)) {
                        self.issue(site, UnknownReason::Target);
                    }

                    if let ClassElement::MethodDefinition(method) = element {
                        let index = usize::from(method.r#static);

                        if !later[index]
                            && !opaque_names[index]
                            && !field_placement[index]
                            && !hidden(method.accessibility, &method.key)
                            && method.value.body.is_some()
                        {
                            own_values.push((file, method.value.node_id()));
                        }

                        opaque_names[index] = true;
                        later[index] = true;
                    } else {
                        let placement = match element {
                            ClassElement::PropertyDefinition(property) => Some(property.r#static),
                            ClassElement::AccessorProperty(property) => Some(property.r#static),
                            _ => None,
                        };

                        if let Some(placement) = placement {
                            opaque_names[usize::from(placement)] = true;

                            if !placement {
                                opaque_instance_values = true;
                            }
                        }
                    }

                    continue;
                };
                let (is_static, inaccessible, value) = match element {
                    ClassElement::MethodDefinition(method) => (
                        method.r#static,
                        hidden(method.accessibility, &method.key),
                        Some(method.value.node_id()),
                    ),
                    ClassElement::PropertyDefinition(property) => (
                        property.r#static,
                        hidden(property.accessibility, &property.key),
                        property.value.as_ref().map(Expression::node_id),
                    ),
                    ClassElement::AccessorProperty(property) => (
                        property.r#static,
                        hidden(property.accessibility, &property.key),
                        property.value.as_ref().map(Expression::node_id),
                    ),
                    _ => continue,
                };
                let key = (is_static, name);
                let index = usize::from(is_static);
                later[index] = true;

                if names.contains(&key)
                    || (opaque_names[index]
                        && (is_static || matches!(element, ClassElement::MethodDefinition(_))))
                    || (!is_static
                        && !matches!(element, ClassElement::MethodDefinition(_))
                        && opaque_instance_values)
                    || (matches!(element, ClassElement::MethodDefinition(_))
                        && (fields.contains(&key)
                            || (!is_static && instance_names.contains(&key.1))
                            || opaque_fields[index]))
                {
                    continue;
                }

                own_names.insert(key.clone());

                if let ClassElement::MethodDefinition(method) = element {
                    if method.value.body.is_none() && class.body.body.iter().any(|other| matches!(other,ClassElement::MethodDefinition(candidate) if candidate.r#static == is_static && element_name_of(other) == Some(key.1.clone()) && candidate.value.body.is_some())) { continue; }
                }

                let kind = match element {
                    ClassElement::MethodDefinition(method) if method.kind.is_get() => 1,
                    ClassElement::MethodDefinition(method) if method.kind.is_set() => 2,
                    _ => 0,
                };

                if !accepts_descriptor(&mut descriptors, format!("{is_static}:{}", key.1), kind)
                    || inaccessible
                {
                    continue;
                }

                if let Some(value) = value {
                    own_values.push((file, value));
                } else if !match element {
                    ClassElement::PropertyDefinition(property) => {
                        primitive_annotation(property.type_annotation.as_deref())
                    }
                    ClassElement::AccessorProperty(property) => {
                        primitive_annotation(property.type_annotation.as_deref())
                    }
                    _ => false,
                } {
                    self.issue(self.site(file, element.node_id()), UnknownReason::Target);
                }
            }

            names.extend(own_names);
            values.extend(own_values.into_iter().rev());
        }

        for (file, value) in values.into_iter().rev() {
            self.node(file, value);
        }
    }
}

struct FieldMask {
    fields: HashSet<(bool, String)>,
    placement: [bool; 2],
    opaque: [bool; 2],
}

fn field_mask(class: &Class<'_>) -> FieldMask {
    let mut fields = HashSet::new();
    let mut field_placement = [false; 2];
    let mut opaque_fields = [false; 2];

    for element in &class.body.body {
        let placement = match element {
            ClassElement::PropertyDefinition(property)
                if matches!(property.key, PropertyKey::PrivateIdentifier(_)) =>
            {
                continue
            }
            ClassElement::PropertyDefinition(property) => property.r#static,
            ClassElement::AccessorProperty(property) => property.r#static,
            _ => continue,
        };
        field_placement[usize::from(placement)] = true;

        if let Some(name) = element_name_of(element) {
            fields.insert((placement, name));
        } else {
            opaque_fields[usize::from(placement)] = true;
        }
    }

    FieldMask {
        fields,
        placement: field_placement,
        opaque: opaque_fields,
    }
}

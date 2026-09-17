use std::collections::{HashMap, HashSet};

use oxc_ast::ast::{
    Class, ClassElement, Expression, ImportOrExportKind, ObjectPropertyKind, PropertyKey,
    Statement, TSAccessibility, TSNamespaceDeclarationBody,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::analysis::Analysis;
use crate::config::{validate_entries, Config, ConfigError};
use crate::declarations::{element_name_of, FunctionNode, SurfaceTarget};
use crate::directives::PerfTag;
use crate::paths::relative_path_of;
use crate::project::{FileId, Resolved};
use crate::syntax::unwrap;
use crate::unknowns::{SourceSpan, UnknownReason};

use super::{ApplicableLimit, PublicFunction};

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

    fn visit(&mut self, file: FileId, node: NodeId) {
        let kind = self.analysis.project.file(file).semantic.nodes().kind(node);
        let site = self.site(file, node);

        match kind {
            AstKind::Function(function) => {
                if function.body.is_some() {
                    self.function(file, FunctionNode::Function(function));
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

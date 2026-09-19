use std::collections::{HashMap, HashSet};

use oxc_ast::ast::{
    Argument, AssignmentTarget, CallExpression, Class, ClassElement, Expression,
    IdentifierReference, MemberExpression, MethodDefinitionKind, ObjectExpression,
    ObjectPropertyKind, PropertyKey, PropertyKind,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::constants::constant_initializer_of;
use crate::declarations::{element_name_of, Declaration, FunctionId, TargetSet};
use crate::declared_types::{declarator_of_identifier, Kind};
use crate::effects::{value_flow_of, ValueFlow};
use crate::project::FileId;
use crate::receivers::{annotation_of, this_owner_of, Placement, ThisOwner};
use crate::syntax::{member_expression_of, unwrap, unwrap_to_cast};
use crate::tables::{LINEAR_CONSTRUCTORS, REFLECTIVE_WRITES};

use super::ValueId;

pub(crate) const OUTSIDE_SOURCES_REPLACE_BUILTINS: bool = false;

const MAXIMUM_TARGET_DEPTH: usize = 24;
const MAXIMUM_LINEAGE: usize = 32;
const MAXIMUM_ALIAS_DEPTH: usize = 8;
const GLOBAL_OBJECTS: [&str; 4] = ["globalThis", "window", "self", "global"];
const INERT_CONSTRUCTORS: [&str; 7] = [
    "Object",
    "Array",
    "Date",
    "Error",
    "RegExp",
    "Promise",
    "ArrayBuffer",
];

type Site = (FileId, NodeId);
type ClassSite<'a> = (FileId, &'a Class<'a>);
pub(crate) type Valued<'a> = (FileId, &'a Expression<'a>);
pub(crate) type PrototypeMembers<'a> =
    HashMap<(usize, MemberKey), (Vec<Valued<'a>>, Vec<FunctionId>, bool)>;
type BuiltinKind = Option<Kind>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum MemberKey {
    Name(String),
    Symbol(Site),
    Index,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriteKind {
    Assigned,
    Removed,
    Defined,
    Prototype,
}

#[derive(Clone, Debug)]
struct Write {
    site: Site,
    key: Option<MemberKey>,
    kind: WriteKind,
}

#[derive(Clone, Debug, PartialEq)]
enum Owner {
    Value {
        value: ValueId,
        allocation: bool,
        shared: bool,
        kind: Kind,
        plain: bool,
    },
    ClassThis {
        class: Site,
        placement: Placement,
    },
    ObjectThis {
        object: Site,
    },
    Prototype {
        class: Site,
    },
    FunctionPrototype {
        function: Site,
    },
    Builtin {
        kind: BuiltinKind,
    },
    Global {
        name: String,
    },
}

#[derive(Default)]
struct Buckets {
    values: HashMap<(Option<MemberKey>, ValueId), Vec<usize>>,
    classes: HashMap<(Site, Option<MemberKey>), Vec<usize>>,
    objects: HashMap<(Site, Option<MemberKey>), Vec<usize>>,
    functions: HashMap<(Site, Option<MemberKey>), Vec<usize>>,
    wide: HashMap<Option<MemberKey>, Vec<usize>>,
    global: HashMap<(String, Option<MemberKey>), Vec<usize>>,
}

#[derive(Clone, Default)]
struct WideSummary {
    replaced: bool,
    known: Vec<FunctionId>,
    prototypes: Vec<usize>,
}

#[derive(Default)]
pub(crate) struct TargetIndex {
    indexed: bool,
    writes: Vec<Write>,
    owners: Vec<(Owner, bool)>,
    buckets: Buckets,
    returns: HashMap<Site, Vec<NodeId>>,
    receivers: HashMap<Site, Vec<NodeId>>,
    classes: Vec<Site>,
    lineages: HashMap<Site, Vec<Site>>,
    subclasses: Option<HashMap<Site, Vec<Site>>>,
    builtin_classes: Option<Vec<(Site, BuiltinKind)>>,
    dispatches: HashMap<Site, (Vec<FunctionId>, bool, bool)>,
    exhaustions: u64,
    exhausted_calls: HashSet<Site>,
    summaries: HashMap<(Option<MemberKey>, Kind, bool, bool), WideSummary>,
    prototypes: HashSet<(Site, MemberKey)>,
    exploring: HashSet<(usize, MemberKey)>,
    cuts: u64,
    prototype_owners: Vec<(ValueId, bool)>,
    replaced_globals: HashSet<String>,
    replaced_every_global: bool,
    rebound_functions: HashSet<Site>,
    rebound_every_function: bool,
    depth: usize,
}

#[derive(Clone, Copy)]
enum Origin<'a> {
    Object {
        file: FileId,
        object: &'a ObjectExpression<'a>,
    },
    Instance {
        file: FileId,
        class: &'a Class<'a>,
        exact: bool,
    },
    Constructor {
        file: FileId,
        class: &'a Class<'a>,
        exact: bool,
    },
    Function {
        function: Site,
    },
}

#[derive(Default)]
struct Receiver<'a> {
    origins: Vec<Origin<'a>>,
    values: Vec<ValueId>,
}

#[derive(Clone, Default)]
struct MemberValues<'a> {
    values: Vec<Valued<'a>>,
    functions: Vec<FunctionId>,
    replaced: bool,
    hits: Vec<usize>,
    lookups: usize,
    defined: usize,
    below: Vec<Site>,
}

enum KeySource<'a> {
    Known(MemberKey),
    Computed(FileId, &'a Expression<'a>),
}

pub(crate) struct MemberDispatch {
    pub(crate) known: Vec<FunctionId>,
    pub(crate) replaced: bool,
}

fn push_target(found: &mut TargetSet, target: FunctionId) {
    if !found.known.contains(&target) {
        found.known.push(target);
    }
}

fn push_function(found: &mut Vec<FunctionId>, target: FunctionId) {
    if !found.contains(&target) {
        found.push(target);
    }
}

fn push_value(values: &mut Vec<ValueId>, value: ValueId) {
    if !values.contains(&value) {
        values.push(value);
    }
}

fn is_unbound(scoping: &oxc_semantic::Scoping, reference: &IdentifierReference<'_>) -> bool {
    reference
        .reference_id
        .get()
        .is_none_or(|id| scoping.get_reference(id).symbol_id().is_none())
}

fn is_index_name(name: &str) -> bool {
    name.parse::<u32>()
        .is_ok_and(|index| index.to_string() == name)
}

fn global_owner_of(name: &str) -> String {
    match GLOBAL_OBJECTS.contains(&name) {
        true => "globalThis".to_string(),
        false => name.to_string(),
    }
}

fn global_name_of<'a>(
    scoping: &oxc_semantic::Scoping,
    expression: &'a Expression<'a>,
) -> Option<&'a str> {
    match unwrap(expression) {
        Expression::Identifier(reference) if is_unbound(scoping, reference) => {
            Some(reference.name.as_str())
        }
        Expression::StaticMemberExpression(member) => match unwrap(&member.object) {
            Expression::Identifier(owner)
                if is_unbound(scoping, owner) && GLOBAL_OBJECTS.contains(&owner.name.as_str()) =>
            {
                Some(member.property.name.as_str())
            }
            _ => None,
        },
        _ => None,
    }
}

fn builtin_kind_of(name: &str) -> BuiltinKind {
    match name {
        "Array" => Some(Kind::Array),
        "Set" => Some(Kind::Set),
        "Map" => Some(Kind::Map),
        "String" => Some(Kind::String),
        "RegExp" => Some(Kind::RegExp),
        "Object" => None,
        _ => Some(Kind::Other),
    }
}

fn affects(owner: BuiltinKind, receiver: Kind) -> bool {
    owner.is_none_or(|owner| receiver == Kind::Unknown || receiver == owner)
}

fn is_fresh_literal(expression: &Expression<'_>) -> bool {
    matches!(
        expression,
        Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::FunctionExpression(_)
            | Expression::ArrowFunctionExpression(_)
            | Expression::ClassExpression(_)
            | Expression::NewExpression(_)
            | Expression::StringLiteral(_)
            | Expression::NumericLiteral(_)
            | Expression::TemplateLiteral(_)
            | Expression::ThisExpression(_)
    )
}

fn is_builtin(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::Array | Kind::Set | Kind::Map | Kind::String | Kind::RegExp
    )
}

fn is_compatible(written: Kind, read: Kind) -> bool {
    matches!(written, Kind::Unknown | Kind::Other)
        || matches!(read, Kind::Unknown | Kind::Other)
        || written == read
}

fn reflective_name_of<'a>(callee: &'a Expression<'a>) -> Option<&'a str> {
    let Expression::StaticMemberExpression(member) = unwrap(callee) else {
        return None;
    };
    let Expression::Identifier(owner) = unwrap(&member.object) else {
        return None;
    };
    let name = member.property.name.as_str();

    ((owner.name == "Object" || owner.name == "Reflect") && REFLECTIVE_WRITES.contains(&name))
        .then_some(name)
}

fn is_object_create(scoping: &oxc_semantic::Scoping, callee: &Expression<'_>) -> bool {
    matches!(
        unwrap(callee),
        Expression::StaticMemberExpression(member)
            if member.property.name == "create"
                && matches!(unwrap(&member.object), Expression::Identifier(owner) if owner.name == "Object" && is_unbound(scoping, owner))
    )
}

fn key_source_of<'a>(file: FileId, member: &'a MemberExpression<'a>) -> KeySource<'a> {
    match member {
        MemberExpression::StaticMemberExpression(access) => {
            KeySource::Known(MemberKey::Name(access.property.name.to_string()))
        }
        MemberExpression::PrivateFieldExpression(access) => {
            KeySource::Known(MemberKey::Name(format!("#{}", access.field.name)))
        }
        MemberExpression::ComputedMemberExpression(access) => match unwrap(&access.expression) {
            Expression::StringLiteral(literal) => {
                KeySource::Known(MemberKey::Name(literal.value.to_string()))
            }
            _ => KeySource::Computed(file, &access.expression),
        },
    }
}

fn member_node_of(member: &MemberExpression<'_>) -> NodeId {
    match member {
        MemberExpression::StaticMemberExpression(access) => access.node_id(),
        MemberExpression::ComputedMemberExpression(access) => access.node_id(),
        MemberExpression::PrivateFieldExpression(access) => access.node_id(),
    }
}

fn placement_of_element(element: &ClassElement<'_>) -> Option<Placement> {
    let is_static = match element {
        ClassElement::MethodDefinition(method) if !method.kind.is_constructor() => method.r#static,
        ClassElement::PropertyDefinition(property) => property.r#static,
        ClassElement::AccessorProperty(property) => property.r#static,
        _ => return None,
    };

    Some(if is_static {
        Placement::Static
    } else {
        Placement::Instance
    })
}

fn element_key_expression<'a>(element: &'a ClassElement<'a>) -> Option<&'a PropertyKey<'a>> {
    match element {
        ClassElement::MethodDefinition(method) if method.computed => Some(&method.key),
        ClassElement::PropertyDefinition(property) if property.computed => Some(&property.key),
        ClassElement::AccessorProperty(property) if property.computed => Some(&property.key),
        _ => None,
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn callable_targets_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> TargetSet {
        let mut found = TargetSet {
            known: Vec::new(),
            open: false,
        };

        self.index_targets();
        self.collect_callable_targets(file, expression, &mut HashSet::new(), &mut found);

        found
    }

    pub(crate) fn member_dispatch_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> MemberDispatch {
        self.index_targets();

        let site = (file, member_node_of(member));

        if let Some((known, replaced, exhausted)) = self.values.targets.dispatches.get(&site) {
            let dispatch = MemberDispatch {
                known: known.clone(),
                replaced: *replaced,
            };

            self.values.targets.exhaustions += u64::from(*exhausted);

            return dispatch;
        }

        let Some(key) = self.member_key_of(file, member) else {
            return MemberDispatch {
                known: Vec::new(),
                replaced: false,
            };
        };
        let outermost = self.values.targets.depth == 0;
        let exhaustions = self.values.targets.exhaustions;
        let mut found = TargetSet {
            known: Vec::new(),
            open: true,
        };

        if !self.enter_targets() {
            self.leave_targets();

            return MemberDispatch {
                known: Vec::new(),
                replaced: true,
            };
        }

        let mut receiver = Receiver::default();

        self.collect_receiver(file, member.object(), &mut HashSet::new(), &mut receiver);

        let values = self.member_candidates_of(file, member.object(), &receiver, &key);
        let mut visited = HashSet::new();

        for function in values.functions {
            push_target(&mut found, function);
        }

        for (target, value) in values.values {
            self.collect_callable_targets(target, value, &mut visited, &mut found);
        }

        let replaced = values.replaced || OUTSIDE_SOURCES_REPLACE_BUILTINS || self.work_exhausted();

        self.leave_targets();

        if outermost && !self.work_exhausted() {
            let exhausted = self.values.targets.exhaustions > exhaustions;

            self.values
                .targets
                .dispatches
                .insert(site, (found.known.clone(), replaced, exhausted));
        }

        MemberDispatch {
            known: found.known,
            replaced,
        }
    }

    pub(crate) fn forget_dispatches(&mut self) {
        self.values.targets.dispatches.clear();
        self.values.targets.summaries.clear();
        self.values.targets.exhausted_calls.clear();
        self.prototype_members.clear();
        self.values.forget_sizes();
    }

    pub(crate) fn may_extend_inherited_keys(&mut self, kind: Kind) -> bool {
        self.index_targets();

        if OUTSIDE_SOURCES_REPLACE_BUILTINS || self.work_exhausted() {
            return true;
        }

        if let Some(extended) = self.values.sizes.inherited.get(&kind) {
            return *extended;
        }

        self.stats.count("sizes: inherited keys");

        let mut extended = false;

        for index in 0..self.values.targets.writes.len() {
            if !self.charge_work(Event::SizeStep, 1) {
                extended = true;

                break;
            }

            let write = &self.values.targets.writes[index];
            let (owner, _) = &self.values.targets.owners[index];

            extended |= !matches!(write.kind, WriteKind::Removed | WriteKind::Prototype)
                && match owner {
                    Owner::Builtin { kind: written } => match written {
                        None => true,
                        Some(written) => {
                            kind == Kind::Unknown || (kind != Kind::Other && *written == kind)
                        }
                    },
                    Owner::Value {
                        allocation,
                        kind: written,
                        ..
                    } => {
                        !allocation
                            && (kind == Kind::Unknown
                                || matches!(written, Kind::Unknown | Kind::Other)
                                || *written == kind)
                    }
                    _ => false,
                };

            if extended {
                break;
            }
        }

        self.values.sizes.inherited.insert(kind, extended);

        extended
    }

    pub(crate) fn builtin_members_replaced(&mut self, kind: Kind, names: &[&str]) -> bool {
        self.index_targets();

        if OUTSIDE_SOURCES_REPLACE_BUILTINS {
            return true;
        }

        let keys = names
            .iter()
            .map(|name| Some(MemberKey::Name((*name).to_string())))
            .chain(std::iter::once(None));
        let mut replaced = false;

        for key in keys {
            replaced |= self.wide_summary_of(key, kind, false, true).replaced;
        }

        replaced || self.work_exhausted()
    }

    pub(crate) fn target_exhaustions(&self) -> u64 {
        self.values.targets.exhaustions
    }

    pub(crate) fn mark_call_exhausted(&mut self, file: FileId, call: NodeId) {
        self.values.targets.exhausted_calls.insert((file, call));
    }

    pub(crate) fn is_call_exhausted(&self, file: FileId, call: NodeId) -> bool {
        self.values.targets.exhausted_calls.contains(&(file, call))
    }

    pub(crate) fn intrinsic_replaced_of(
        &mut self,
        file: FileId,
        callee: &'a Expression<'a>,
    ) -> bool {
        self.index_targets();

        match unwrap(callee) {
            Expression::Identifier(reference) => {
                if OUTSIDE_SOURCES_REPLACE_BUILTINS {
                    return true;
                }

                if !is_unbound(self.project.file(file).semantic.scoping(), reference) {
                    return false;
                }

                let name = reference.name.as_str();

                !self.global_values_of(name).is_empty()
                    || self.has_global_write("globalThis", None)
                    || self.has_global_write(name, None)
                    || self
                        .wide_summary_of(None, Kind::Unknown, true, true)
                        .replaced
            }
            other => match member_expression_of(other) {
                Some(member) => self.member_dispatch_of(file, member).replaced,
                None => false,
            },
        }
    }

    pub(crate) fn returned_expressions_of(
        &mut self,
        target: FunctionId,
    ) -> Vec<&'a Expression<'a>> {
        self.index_targets();

        if let AstKind::ArrowFunctionExpression(arrow) = self.kind_of_node(target.file, target.node)
        {
            if let Some(expression) = arrow.get_expression() {
                return vec![expression];
            }
        }

        let statements = self
            .values
            .targets
            .returns
            .get(&(target.file, target.node))
            .cloned()
            .unwrap_or_default();

        statements
            .into_iter()
            .filter_map(
                |statement| match self.kind_of_node(target.file, statement) {
                    AstKind::ReturnStatement(statement) => statement.argument.as_ref(),
                    _ => None,
                },
            )
            .collect()
    }

    pub(crate) fn receiver_nodes_of(&mut self, function: FunctionId) -> Vec<NodeId> {
        self.index_targets();

        self.values
            .targets
            .receivers
            .get(&(function.file, function.node))
            .cloned()
            .unwrap_or_default()
    }

    pub(crate) fn local_values_of(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> Option<Vec<Valued<'a>>> {
        let Some(Declaration::Variable {
            file: target,
            declarator,
            ..
        }) = self
            .declarations
            .of_reference(self.project, file, reference)
        else {
            return None;
        };

        if !matches!(
            declarator.id,
            oxc_ast::ast::BindingPattern::BindingIdentifier(_)
        ) {
            return None;
        }

        let nodes = self.project.file(target).semantic.nodes();
        let statement = nodes.parent_id(declarator.node_id());
        let plain = match nodes.kind(statement) {
            AstKind::VariableDeclaration(declaration) => {
                !declaration.declare
                    && !matches!(
                        nodes.parent_kind(statement),
                        AstKind::ForOfStatement(_) | AstKind::ForInStatement(_)
                    )
            }
            _ => false,
        };
        let mut values: Vec<Valued<'a>> = Vec::new();

        match &declarator.init {
            Some(init) => values.push((target, init)),
            None if plain => {}
            None => return None,
        }

        let (written, unresolved) = self.written_values_of(file, reference);

        if unresolved {
            return None;
        }

        values.extend(written);

        Some(values)
    }

    fn enter_targets(&mut self) -> bool {
        self.values.targets.depth += 1;

        let entered = self.values.targets.depth <= MAXIMUM_TARGET_DEPTH
            && self.charge_work(Event::DispatchStep, 1);

        self.values.targets.exhaustions += u64::from(!entered);

        entered
    }

    fn charge_dispatch(&mut self) -> bool {
        let charged = self.charge_work(Event::DispatchStep, 1);

        self.values.targets.exhaustions += u64::from(!charged);

        charged
    }

    fn leave_targets(&mut self) {
        self.values.targets.depth -= 1;
    }

    fn index_targets(&mut self) {
        if self.values.targets.indexed {
            return;
        }

        self.values.targets.indexed = true;

        let project = self.project;
        let mut pending: Vec<(Site, Option<KeySource<'a>>, WriteKind)> = Vec::new();

        for source in &project.files {
            let file = source.id;
            let nodes = source.semantic.nodes();
            let scoping = source.semantic.scoping();

            for node in nodes.iter() {
                let site = (file, node.id());

                match node.kind() {
                    AstKind::ReturnStatement(_) => {
                        if let Some(function) = nodes.ancestors(node.id()).find(|ancestor| {
                            matches!(
                                ancestor.kind(),
                                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
                            )
                        }) {
                            self.values
                                .targets
                                .returns
                                .entry((file, function.id()))
                                .or_default()
                                .push(node.id());
                        }
                    }
                    AstKind::ThisExpression(_) => {
                        if let Some(function) = nodes
                            .ancestors(node.id())
                            .find(|ancestor| {
                                matches!(ancestor.kind(), AstKind::Function(_) | AstKind::Class(_))
                            })
                            .filter(|ancestor| matches!(ancestor.kind(), AstKind::Function(_)))
                        {
                            self.values
                                .targets
                                .receivers
                                .entry((file, function.id()))
                                .or_default()
                                .push(node.id());
                        }
                    }
                    AstKind::Class(class) if class.heritage.is_some() => {
                        self.values.targets.classes.push(site)
                    }
                    AstKind::AssignmentExpression(assignment)
                        if assignment.operator.is_assign() || assignment.operator.is_logical() =>
                    {
                        match &assignment.left {
                            AssignmentTarget::AssignmentTargetIdentifier(reference)
                                if is_unbound(scoping, reference) =>
                            {
                                pending.push((
                                    site,
                                    Some(KeySource::Known(MemberKey::Name(
                                        reference.name.to_string(),
                                    ))),
                                    WriteKind::Assigned,
                                ));
                            }
                            left => {
                                if let Some(member) = left.as_member_expression() {
                                    let key = key_source_of(file, member);
                                    let kind = match &key {
                                        KeySource::Known(MemberKey::Name(name))
                                            if name == "__proto__" =>
                                        {
                                            WriteKind::Prototype
                                        }
                                        _ => WriteKind::Assigned,
                                    };

                                    pending.push((site, Some(key), kind));
                                }
                            }
                        }
                    }
                    AstKind::UnaryExpression(unary) if unary.operator == UnaryOperator::Delete => {
                        if let Some(member) = member_expression_of(unwrap(&unary.argument)) {
                            pending.push((
                                site,
                                Some(key_source_of(file, member)),
                                WriteKind::Removed,
                            ));
                        }
                    }
                    AstKind::CallExpression(call) => {
                        reflective_writes_of(file, call, site, &mut pending)
                    }
                    _ => {}
                }
            }
        }

        let mut writes = Vec::new();

        for (site, key, kind) in pending {
            let key = match key {
                Some(KeySource::Known(key)) => Some(key),
                Some(KeySource::Computed(file, expression)) => {
                    match self.member_key_of_expression(file, expression) {
                        Some(key) => Some(key),
                        None if self.is_numeric_key(file, expression, 0) => Some(MemberKey::Index),
                        None => None,
                    }
                }
                None => None,
            };

            let kind = match (self.kind_of_node(site.0, site.1), &key) {
                (AstKind::ObjectProperty(property), Some(MemberKey::Name(name)))
                    if name == "__proto__" =>
                {
                    if !property.computed {
                        continue;
                    }

                    WriteKind::Prototype
                }
                _ => kind,
            };

            writes.push(Write {
                site,
                key: match kind {
                    WriteKind::Prototype => None,
                    _ => key,
                },
                kind,
            });
        }

        let mut prototype_owners = Vec::new();
        let mut replaced_globals = HashSet::new();
        let mut replaced_every_global = false;
        let mut rebound_functions = HashSet::new();
        let mut rebound_every_function = false;
        let mut global_writes = Vec::new();

        for (index, write) in writes.iter().enumerate() {
            let file = write.site.0;

            match self.write_parts_of(write.site) {
                None => {
                    if let Some(MemberKey::Name(name)) = &write.key {
                        replaced_globals.insert(name.clone());
                    }
                }
                Some((object, value)) => {
                    if write.key == Some(MemberKey::Name("prototype".to_string()))
                        && write.kind != WriteKind::Removed
                    {
                        match self.function_candidates_of(file, object, 0) {
                            Some(functions) => rebound_functions.extend(functions),
                            None => rebound_every_function = true,
                        }
                    }

                    let replacing = write.kind != WriteKind::Prototype
                        && write.kind != WriteKind::Removed
                        && value.is_none_or(|value| self.may_be_callable(file, value));

                    if replacing && self.may_be_global_object(file, object, 0) {
                        global_writes.push(index);

                        match &write.key {
                            Some(MemberKey::Name(name)) => {
                                replaced_globals.insert(name.clone());
                            }
                            None => replaced_every_global = true,
                            _ => {}
                        }
                    }

                    if write.kind == WriteKind::Prototype {
                        let value = self.storage_value_of(file, object);
                        let shared =
                            !self.values.is_allocation(value) || self.escapes(file, unwrap(object));

                        prototype_owners.push((value, shared));
                    }
                }
            }
        }

        self.values.targets.prototype_owners = prototype_owners;
        self.values.targets.rebound_functions = rebound_functions;
        self.values.targets.rebound_every_function = rebound_every_function;
        self.values.targets.replaced_globals = replaced_globals;
        self.values.targets.replaced_every_global = replaced_every_global;

        let mut owners = Vec::with_capacity(writes.len());
        let mut buckets = Buckets::default();

        for (index, write) in writes.iter().enumerate() {
            let Some((object, value)) = self.write_parts_of(write.site) else {
                if let (AstKind::AssignmentExpression(assignment), Some(key)) =
                    (self.kind_of_node(write.site.0, write.site.1), &write.key)
                {
                    let MemberKey::Name(name) = key else {
                        continue;
                    };
                    let callable = self.may_be_callable(write.site.0, &assignment.right);

                    buckets
                        .global
                        .entry((global_owner_of(name), write.key.clone()))
                        .or_default()
                        .push(index);
                    owners.push((
                        Owner::Global {
                            name: global_owner_of(name),
                        },
                        callable,
                    ));
                } else {
                    owners.push((
                        Owner::Global {
                            name: String::new(),
                        },
                        false,
                    ));
                }

                continue;
            };
            let file = write.site.0;
            let owner = self.owner_of(file, object);
            let callable = match write.kind {
                WriteKind::Assigned => value.is_none_or(|value| self.may_be_callable(file, value)),
                WriteKind::Removed => false,
                WriteKind::Defined | WriteKind::Prototype => true,
            };

            if write.key.is_none() && !callable {
                owners.push((owner, false));

                continue;
            }

            let key = write.key.clone();

            match &owner {
                Owner::Value {
                    value,
                    allocation,
                    shared,
                    ..
                } => {
                    buckets
                        .values
                        .entry((key.clone(), *value))
                        .or_default()
                        .push(index);

                    if !*allocation || *shared {
                        buckets.wide.entry(key).or_default().push(index);
                    }
                }
                Owner::ClassThis { class, .. } | Owner::Prototype { class } => buckets
                    .classes
                    .entry((*class, key))
                    .or_default()
                    .push(index),
                Owner::ObjectThis { object } => buckets
                    .objects
                    .entry((*object, key))
                    .or_default()
                    .push(index),
                Owner::FunctionPrototype { function } => {
                    buckets
                        .functions
                        .entry((*function, key.clone()))
                        .or_default()
                        .push(index);
                    buckets.wide.entry(key).or_default().push(index);
                }
                Owner::Builtin { .. } => buckets.wide.entry(key).or_default().push(index),
                Owner::Global { name } => buckets
                    .global
                    .entry((name.clone(), key))
                    .or_default()
                    .push(index),
            }

            owners.push((owner, callable));
        }

        for index in global_writes {
            if !matches!(owners[index].0, Owner::Global { .. }) {
                buckets
                    .global
                    .entry(("globalThis".to_string(), writes[index].key.clone()))
                    .or_default()
                    .push(index);
            }
        }

        self.values.targets.writes = writes;
        self.values.targets.owners = owners;
        self.values.targets.buckets = buckets;
    }

    fn member_key_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<MemberKey> {
        match key_source_of(file, member) {
            KeySource::Known(key) => Some(key),
            KeySource::Computed(file, expression) => {
                self.member_key_of_expression(file, expression)
            }
        }
    }

    fn member_key_of_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<MemberKey> {
        if let Expression::Identifier(reference) = unwrap(expression) {
            if let Some(Declaration::Variable {
                file: target,
                declarator,
                constant: true,
            }) = self
                .declarations
                .of_reference(self.project, file, reference)
            {
                if let Some(Expression::CallExpression(call)) = declarator.init.as_ref().map(unwrap)
                {
                    if matches!(unwrap(&call.callee), Expression::Identifier(symbol) if symbol.name == "Symbol" && is_unbound(self.project.file(target).semantic.scoping(), symbol))
                    {
                        return Some(MemberKey::Symbol((target, declarator.node_id())));
                    }
                }
            }
        }

        if let Expression::TemplateLiteral(template) = unwrap(expression) {
            if template.expressions.is_empty() {
                return template
                    .quasis
                    .iter()
                    .map(|quasi| quasi.value.cooked.map(|cooked| cooked.to_string()))
                    .collect::<Option<String>>()
                    .map(MemberKey::Name);
            }
        }

        self.known_key(file, expression).ok().map(MemberKey::Name)
    }

    fn element_key_of(&mut self, file: FileId, element: &'a ClassElement<'a>) -> Option<MemberKey> {
        match element_key_expression(element) {
            Some(key) => match key.as_expression() {
                Some(expression) => self.member_key_of_expression(file, expression),
                None => key
                    .static_name()
                    .map(|name| MemberKey::Name(name.into_owned())),
            },
            None => element_name_of(element).map(MemberKey::Name),
        }
    }

    fn property_key_of(
        &mut self,
        file: FileId,
        property: &'a oxc_ast::ast::ObjectProperty<'a>,
    ) -> Option<MemberKey> {
        if !property.computed {
            return property
                .key
                .static_name()
                .map(|name| MemberKey::Name(name.into_owned()));
        }

        match property.key.as_expression() {
            Some(expression) => self.member_key_of_expression(file, expression),
            None => property
                .key
                .static_name()
                .map(|name| MemberKey::Name(name.into_owned())),
        }
    }

    fn is_numeric_key(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return false;
        }

        match unwrap(expression) {
            Expression::NumericLiteral(_) | Expression::UpdateExpression(_) => true,
            Expression::UnaryExpression(unary) => matches!(
                unary.operator,
                UnaryOperator::UnaryNegation | UnaryOperator::UnaryPlus | UnaryOperator::BitwiseNot
            ),
            Expression::BinaryExpression(binary) => match binary.operator {
                BinaryOperator::Addition => {
                    self.is_numeric_key(file, &binary.left, depth + 1)
                        && self.is_numeric_key(file, &binary.right, depth + 1)
                }
                operator => operator.is_arithmetic() || operator.is_bitwise(),
            },
            Expression::Identifier(reference) => {
                let Some(declaration) =
                    self.declarations
                        .of_reference(self.project, file, reference)
                else {
                    return false;
                };

                if let Declaration::Parameter {
                    file: target,
                    parameter: crate::declarations::ParameterNode::Formal(parameter),
                    function,
                } = declaration
                {
                    let (written, unresolved) = self.written_values_of(file, reference);

                    return !unresolved
                        && written
                            .into_iter()
                            .all(|(target, value)| self.is_numeric_key(target, value, depth + 1))
                        && self
                            .call_arguments_of(target, function, parameter)
                            .is_some_and(|arguments| {
                                arguments.into_iter().all(|argument| {
                                    argument.is_some_and(|(site, argument)| {
                                        self.is_numeric_key(site, argument, depth + 1)
                                    })
                                })
                            });
                }

                let Some((target, declarator, _)) = declarator_of_identifier(&declaration) else {
                    return false;
                };
                let Some(init) = &declarator.init else {
                    return false;
                };
                let (written, unresolved) = self.written_values_of(file, reference);

                !unresolved
                    && self.is_numeric_key(target, init, depth + 1)
                    && written
                        .into_iter()
                        .all(|(target, value)| self.is_numeric_key(target, value, depth + 1))
            }
            _ => false,
        }
    }

    fn collect_callable_targets(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        visited: &mut HashSet<Site>,
        found: &mut TargetSet,
    ) {
        let expression = unwrap(expression);

        if !visited.insert((file, expression.node_id())) {
            return;
        }

        if !self.enter_targets() {
            self.leave_targets();

            found.open = true;

            return;
        }

        match expression {
            Expression::FunctionExpression(function) if function.body.is_some() => push_target(
                found,
                FunctionId {
                    file,
                    node: function.node_id(),
                },
            ),
            Expression::ArrowFunctionExpression(arrow) => push_target(
                found,
                FunctionId {
                    file,
                    node: arrow.node_id(),
                },
            ),
            Expression::Identifier(reference) => {
                self.collect_reference_targets(file, reference, visited, found)
            }
            Expression::ConditionalExpression(conditional) => {
                self.collect_callable_targets(file, &conditional.consequent, visited, found);
                self.collect_callable_targets(file, &conditional.alternate, visited, found);
            }
            Expression::LogicalExpression(logical) => {
                self.collect_callable_targets(file, &logical.left, visited, found);
                self.collect_callable_targets(file, &logical.right, visited, found);
            }
            Expression::SequenceExpression(sequence) => match sequence.expressions.last() {
                Some(last) => self.collect_callable_targets(file, last, visited, found),
                None => found.open = true,
            },
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                self.collect_callable_targets(file, &assignment.right, visited, found)
            }
            Expression::CallExpression(call) => {
                let mut returned = Vec::new();

                found.open |= self.collect_returned(file, call, &mut returned);

                for (target, value) in returned {
                    self.collect_callable_targets(target, value, visited, found);
                }
            }
            Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::ClassExpression(_) => {}
            other => match member_expression_of(other) {
                Some(member) => {
                    for target in self.member_dispatch_of(file, member).known {
                        push_target(found, target);
                    }

                    found.open = true;
                }
                None => found.open |= !self.is_non_callable_expression(file, other),
            },
        }

        self.leave_targets();
    }

    fn collect_reference_targets(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
        visited: &mut HashSet<Site>,
        found: &mut TargetSet,
    ) {
        let project = self.project;
        let (declaration, closed) = self
            .declarations
            .callable_reference(project, file, reference);

        if closed {
            if let Some((target, function)) =
                declaration.and_then(|declaration| self.declarations.function_of(declaration))
            {
                return push_target(
                    found,
                    FunctionId {
                        file: target,
                        node: function.node_id(),
                    },
                );
            }
        }

        let Some(declaration) = self.declarations.of_reference(project, file, reference) else {
            if is_unbound(project.file(file).semantic.scoping(), reference) {
                for (target, value) in self.global_values_of(reference.name.as_str()) {
                    self.collect_callable_targets(target, value, visited, found);
                }
            }

            found.open = true;

            return;
        };

        match declaration {
            Declaration::Function { .. } => {
                let mut candidates = self
                    .declarations
                    .runtime_candidates_of(project, file, reference);

                if candidates.is_empty() {
                    candidates.push(declaration);
                }

                for candidate in candidates {
                    match candidate {
                        Declaration::Variable {
                            file: target,
                            declarator,
                            ..
                        } => match &declarator.init {
                            Some(init) => {
                                self.collect_callable_targets(target, init, visited, found)
                            }
                            None => found.open = true,
                        },
                        candidate => {
                            if let Some((target, function)) =
                                self.declarations.function_of(candidate)
                            {
                                push_target(
                                    found,
                                    FunctionId {
                                        file: target,
                                        node: function.node_id(),
                                    },
                                );
                            }
                        }
                    }
                }

                found.open |= !closed;
            }
            Declaration::Variable {
                file: target,
                declarator,
                constant,
            } => {
                match (&declarator.id, &declarator.init) {
                    (oxc_ast::ast::BindingPattern::BindingIdentifier(_), Some(init)) => {
                        self.collect_callable_targets(target, init, visited, found)
                    }
                    _ => found.open = true,
                }

                found.open |= !constant || !closed;
            }
            _ => found.open = true,
        }

        let (written, unresolved) = self.written_values_of(file, reference);

        found.open |= unresolved;

        for (target, value) in written {
            self.collect_callable_targets(target, value, visited, found);
        }
    }

    fn written_values_of(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
    ) -> (Vec<Valued<'a>>, bool) {
        let project = self.project;
        let Some(binding) = self
            .declarations
            .binding_of_reference(project, file, reference)
        else {
            return (Vec::new(), false);
        };
        let mut written = Vec::new();
        let mut unresolved = false;

        for (target, node, write) in self.declarations.surface_references_of(project, binding) {
            if !write {
                continue;
            }

            let nodes = project.file(target).semantic.nodes();
            let span = nodes.kind(node).span();

            match nodes.parent_kind(node) {
                AstKind::AssignmentExpression(assignment)
                    if assignment.left.span() == span
                        && (assignment.operator.is_assign()
                            || assignment.operator.is_logical()) =>
                {
                    written.push((target, &assignment.right))
                }
                AstKind::AssignmentExpression(_) | AstKind::UpdateExpression(_) => {}
                _ => unresolved = true,
            }
        }

        (written, unresolved)
    }

    fn global_values_of(&mut self, name: &str) -> Vec<Valued<'a>> {
        let key = Some(MemberKey::Name(name.to_string()));
        let mut indices = Vec::new();

        for owner in [global_owner_of(name), "globalThis".to_string()] {
            if let Some(found) = self
                .values
                .targets
                .buckets
                .global
                .get(&(owner.clone(), key.clone()))
            {
                indices.extend(found.iter().copied());
            }

            if owner == "globalThis" {
                break;
            }
        }

        indices.dedup();

        indices
            .into_iter()
            .filter_map(|index| {
                let (file, node) = self.values.targets.writes[index].site;

                match self.kind_of_node(file, node) {
                    AstKind::AssignmentExpression(assignment) => Some((file, &assignment.right)),
                    _ => None,
                }
            })
            .collect()
    }

    fn collect_returned(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        returned: &mut Vec<Valued<'a>>,
    ) -> bool {
        let targets = self.resolved_callee_of(file, call).targets;
        let mut open = targets.open;

        for target in targets.known {
            let deferred = match self.kind_of_node(target.file, target.node) {
                AstKind::Function(function) => function.r#async || function.generator,
                AstKind::ArrowFunctionExpression(arrow) => arrow.r#async,
                _ => true,
            };

            if deferred {
                open = true;

                continue;
            }

            for value in self.returned_expressions_of(target) {
                returned.push((target.file, value));
            }
        }

        open
    }

    fn collect_receiver(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        visited: &mut HashSet<Site>,
        receiver: &mut Receiver<'a>,
    ) {
        if !visited.insert((file, expression.node_id())) {
            return;
        }

        if self.enter_targets() {
            self.collect_receiver_within(file, expression, visited, receiver);
        }

        self.leave_targets();
    }

    fn collect_receiver_within(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        visited: &mut HashSet<Site>,
        receiver: &mut Receiver<'a>,
    ) {
        let project = self.project;
        let cast = match unwrap_to_cast(expression) {
            Expression::TSAsExpression(cast) => Some(&cast.type_annotation),
            Expression::TSTypeAssertion(cast) => Some(&cast.type_annotation),
            _ => None,
        };

        if let Some((target, class)) =
            cast.and_then(|annotation| self.declarations.class_of_type(project, file, annotation))
        {
            return receiver.origins.push(Origin::Instance {
                file: target,
                class,
                exact: false,
            });
        }

        let expression = unwrap(expression);

        if let Some(member) = member_expression_of(expression) {
            if let Some(function) = self.function_prototype_of(file, expression) {
                receiver.origins.push(Origin::Function { function });
            }

            if self.member_key_of(file, member) == Some(MemberKey::Name("prototype".to_string())) {
                for (target, class) in self.classes_of_expression(file, member.object(), 0) {
                    receiver.origins.push(Origin::Instance {
                        file: target,
                        class,
                        exact: false,
                    });
                }
            }
        }

        match expression {
            Expression::ObjectExpression(object) => {
                receiver.origins.push(Origin::Object { file, object })
            }
            Expression::NewExpression(new) => {
                let classes = self.classes_of_expression(file, &new.callee, 0);

                if classes.is_empty() {
                    if let Some(function) = self.constructor_function_of(file, &new.callee, 0) {
                        if !self.values.targets.rebound_every_function
                            && !self.values.targets.rebound_functions.contains(&function)
                        {
                            receiver.origins.push(Origin::Function { function });
                        }
                    }
                }

                for (target, class) in classes {
                    receiver.origins.push(Origin::Instance {
                        file: target,
                        class,
                        exact: true,
                    });
                }
            }
            Expression::ClassExpression(class) => receiver.origins.push(Origin::Constructor {
                file,
                class,
                exact: true,
            }),
            Expression::ThisExpression(this) => {
                match this_owner_of(project, file, this.node_id()) {
                    Some(ThisOwner::Class {
                        file,
                        class,
                        placement: Placement::Static,
                    }) => receiver.origins.push(Origin::Constructor {
                        file,
                        class,
                        exact: false,
                    }),
                    Some(ThisOwner::Class { file, class, .. }) => {
                        receiver.origins.push(Origin::Instance {
                            file,
                            class,
                            exact: false,
                        })
                    }
                    Some(ThisOwner::Object { file, object }) => {
                        receiver.origins.push(Origin::Object { file, object });

                        let value = self.values.allocation(self.source_span(file, object.span));

                        push_value(&mut receiver.values, value.value);
                    }
                    None => {}
                }
            }
            Expression::Identifier(reference) => {
                self.collect_reference_receiver(file, reference, visited, receiver)
            }
            Expression::ConditionalExpression(conditional) => {
                self.collect_receiver(file, &conditional.consequent, visited, receiver);
                self.collect_receiver(file, &conditional.alternate, visited, receiver);
            }
            Expression::LogicalExpression(logical) => {
                self.collect_receiver(file, &logical.left, visited, receiver);
                self.collect_receiver(file, &logical.right, visited, receiver);
            }
            Expression::SequenceExpression(sequence) => {
                if let Some(last) = sequence.expressions.last() {
                    self.collect_receiver(file, last, visited, receiver);
                }
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                self.collect_receiver(file, &assignment.right, visited, receiver)
            }
            Expression::CallExpression(call)
                if is_object_create(project.file(file).semantic.scoping(), &call.callee) =>
            {
                if let Some(prototype) = call.arguments.first().and_then(Argument::as_expression) {
                    self.collect_receiver(file, prototype, visited, receiver);
                }
            }
            Expression::CallExpression(call) => {
                let mut returned = Vec::new();

                self.collect_returned(file, call, &mut returned);

                for (target, value) in returned {
                    self.collect_receiver(target, value, visited, receiver);
                }
            }
            other => {
                if let Some(member) = member_expression_of(other) {
                    if let Some(key) = self.member_key_of(file, member) {
                        let mut owner = Receiver::default();

                        self.collect_receiver(file, member.object(), visited, &mut owner);

                        for (target, value) in self
                            .member_candidates_of(file, member.object(), &owner, &key)
                            .values
                        {
                            self.collect_receiver(target, value, visited, receiver);
                        }
                    }
                }
            }
        }

        let value = self.storage_value_of(file, expression);

        push_value(&mut receiver.values, value);
    }

    fn collect_reference_receiver(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
        visited: &mut HashSet<Site>,
        receiver: &mut Receiver<'a>,
    ) {
        let project = self.project;
        let Some(declaration) = self.declarations.of_reference(project, file, reference) else {
            return;
        };

        if let Declaration::Class { file, class } = declaration {
            return receiver.origins.push(Origin::Constructor {
                file,
                class,
                exact: true,
            });
        }

        if let Some((target, annotation)) = annotation_of(&declaration) {
            if let Some((target, class)) =
                self.declarations.class_of_type(project, target, annotation)
            {
                receiver.origins.push(Origin::Instance {
                    file: target,
                    class,
                    exact: false,
                });
            }
        }

        if let Some((target, declarator, constant)) = declarator_of_identifier(&declaration) {
            if let Some(init) = &declarator.init {
                self.collect_receiver(target, init, visited, receiver);
            }

            if !constant {
                for (target, value) in self.written_values_of(file, reference).0 {
                    self.collect_receiver(target, value, visited, receiver);
                }
            }
        }
    }

    fn member_candidates_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        receiver: &Receiver<'a>,
        key: &MemberKey,
    ) -> MemberValues<'a> {
        let mut found = self.member_candidates_raw_of(file, expression, receiver, key);

        for hit in std::mem::take(&mut found.hits) {
            let (values, functions, replaced) = self.prototype_members_of(hit, key);

            found.replaced |= replaced;

            found.values.extend(values);

            for function in functions {
                push_function(&mut found.functions, function);
            }
        }

        found
    }

    fn prototype_members_of(
        &mut self,
        start: usize,
        key: &MemberKey,
    ) -> (Vec<Valued<'a>>, Vec<FunctionId>, bool) {
        if let Some(found) = self.prototype_members.get(&(start, key.clone())) {
            return found.clone();
        }

        if self
            .values
            .targets
            .exploring
            .contains(&(start, key.clone()))
        {
            self.values.targets.cuts += 1;

            return (Vec::new(), Vec::new(), true);
        }

        let cuts = self.values.targets.cuts;
        let mut order = vec![start];
        let mut own: HashMap<usize, MemberValues<'a>> = HashMap::new();
        let mut position = 0;

        while position < order.len() {
            let write = order[position];

            position += 1;

            if !self.enter_targets() {
                self.leave_targets();

                own.insert(
                    write,
                    MemberValues {
                        replaced: true,
                        ..MemberValues::default()
                    },
                );

                continue;
            }

            self.values.targets.exploring.insert((write, key.clone()));

            let site = self.values.targets.writes[write].site;
            let mut members = match self.write_parts_of(site) {
                Some((_, Some(prototype))) => {
                    let mut receiver = Receiver::default();

                    self.collect_receiver(site.0, prototype, &mut HashSet::new(), &mut receiver);

                    self.member_candidates_raw_of(site.0, prototype, &receiver, key)
                }
                _ => MemberValues {
                    replaced: true,
                    ..MemberValues::default()
                },
            };

            members.replaced = true;

            for hit in &members.hits {
                if !order.contains(hit)
                    && !self.prototype_members.contains_key(&(*hit, key.clone()))
                {
                    order.push(*hit);
                }
            }

            own.insert(write, members);
            self.leave_targets();
        }

        let mut results = own.clone();
        let mut changed = true;

        while changed {
            changed = false;

            for write in &order {
                let hits = results[write].hits.clone();

                for hit in hits {
                    let (values, functions, replaced) = match results.get(&hit) {
                        Some(found) => (
                            found.values.clone(),
                            found.functions.clone(),
                            found.replaced,
                        ),
                        None => self
                            .prototype_members
                            .get(&(hit, key.clone()))
                            .cloned()
                            .unwrap_or((Vec::new(), Vec::new(), true)),
                    };
                    let target = results.get_mut(write).expect("explored write");

                    target.replaced |= replaced;

                    for value in values {
                        if !target.values.iter().any(|known| {
                            known.0 == value.0 && known.1.node_id() == value.1.node_id()
                        }) {
                            target.values.push(value);

                            changed = true;
                        }
                    }

                    for function in functions {
                        if !target.functions.contains(&function) {
                            target.functions.push(function);

                            changed = true;
                        }
                    }
                }
            }
        }

        for write in &order {
            self.values.targets.exploring.remove(&(*write, key.clone()));
        }

        let complete = self.values.targets.cuts == cuts;
        let result = results
            .get(&start)
            .map(|found| {
                (
                    found.values.clone(),
                    found.functions.clone(),
                    found.replaced,
                )
            })
            .unwrap_or((Vec::new(), Vec::new(), true));

        if complete {
            for (write, found) in results {
                self.prototype_members.insert(
                    (write, key.clone()),
                    (found.values, found.functions, found.replaced),
                );
            }
        }

        result
    }

    fn member_candidates_raw_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        receiver: &Receiver<'a>,
        key: &MemberKey,
    ) -> MemberValues<'a> {
        let mut found = MemberValues::default();

        for origin in &receiver.origins {
            if !self.charge_dispatch() {
                found.replaced = true;

                return found;
            }

            found.lookups += 1;

            match *origin {
                Origin::Object { file, object } => {
                    self.object_values_of(file, object, key, &mut found)
                }
                Origin::Instance { file, class, exact } => {
                    self.class_values_of(file, class, exact, Placement::Instance, key, &mut found)
                }
                Origin::Constructor { file, class, exact } => {
                    self.class_values_of(file, class, exact, Placement::Static, key, &mut found)
                }
                Origin::Function { function } => self.function_values_of(function, key, &mut found),
            }
        }

        self.collect_replacements(file, expression, receiver, key, &mut found);

        found
    }

    fn object_values_of(
        &mut self,
        file: FileId,
        object: &'a ObjectExpression<'a>,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let mut own = false;
        let mut prototype = None;

        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                continue;
            };
            let property_key = self.property_key_of(file, property);

            if !property.computed && property_key == Some(MemberKey::Name("__proto__".to_string()))
            {
                prototype = Some(&property.value);

                continue;
            }

            if property_key.as_ref() != Some(key) {
                continue;
            }

            if !own {
                found.defined += 1;
            }

            own = true;

            match property.kind {
                PropertyKind::Init => found.values.push((file, &property.value)),
                PropertyKind::Get => {
                    if let Expression::FunctionExpression(getter) = &property.value {
                        self.push_getter(
                            FunctionId {
                                file,
                                node: getter.node_id(),
                            },
                            found,
                        );
                    }
                }
                PropertyKind::Set => {}
            }
        }

        if let (false, Some(prototype)) = (own, prototype) {
            self.prototype_values_of(file, prototype, key, found);
        }
    }

    fn prototype_values_of(
        &mut self,
        file: FileId,
        prototype: &'a Expression<'a>,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let site = ((file, prototype.node_id()), key.clone());

        if self.values.targets.prototypes.contains(&site) {
            found.replaced = true;

            return;
        }

        if !self.enter_targets() {
            self.leave_targets();

            found.replaced = true;

            return;
        }

        self.values.targets.prototypes.insert(site.clone());

        let mut receiver = Receiver::default();

        self.collect_receiver(file, prototype, &mut HashSet::new(), &mut receiver);

        let inherited = self.member_candidates_of(file, prototype, &receiver, key);

        self.values.targets.prototypes.remove(&site);
        self.leave_targets();

        found.values.extend(inherited.values);

        found.replaced |= inherited.replaced;

        for function in inherited.functions {
            push_function(&mut found.functions, function);
        }
    }

    fn push_getter(&mut self, getter: FunctionId, found: &mut MemberValues<'a>) {
        push_function(&mut found.functions, getter);

        for value in self.returned_expressions_of(getter) {
            found.values.push((getter.file, value));
        }
    }

    fn class_values_of(
        &mut self,
        file: FileId,
        class: &'a Class<'a>,
        exact: bool,
        placement: Placement,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let mut classes = Vec::new();
        let lineage = self.lineage_of(file, class);

        for (position, candidate) in lineage.iter().enumerate() {
            if !self.elements_keyed(*candidate, key, placement).is_empty() {
                classes.push(*candidate);

                found.defined += 1;

                found.below.extend(
                    lineage[..position]
                        .iter()
                        .map(|(file, class)| (*file, class.node_id())),
                );

                break;
            }
        }

        if !exact {
            let subclasses = self.subclasses_of(file, class);

            found.below.extend(
                subclasses
                    .iter()
                    .map(|(file, class)| (*file, class.node_id())),
            );
            classes.extend(subclasses);
        }

        for candidate in classes {
            self.push_elements(candidate, key, placement, found);
        }
    }

    fn function_values_of(
        &mut self,
        function: Site,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let keyed = self
            .values
            .targets
            .buckets
            .functions
            .get(&(function, Some(key.clone())))
            .cloned()
            .unwrap_or_default();
        let unkeyed = self
            .values
            .targets
            .buckets
            .functions
            .get(&(function, None))
            .cloned()
            .unwrap_or_default();
        let defined = keyed
            .iter()
            .any(|index| self.values.targets.writes[*index].kind != WriteKind::Removed);

        for index in keyed {
            self.apply_write(index, found);
        }

        for index in unkeyed {
            if defined && self.values.targets.writes[index].kind == WriteKind::Prototype {
                continue;
            }

            self.apply_write(index, found);
        }

        found.defined += usize::from(defined);
    }

    fn elements_keyed(
        &mut self,
        (file, class): ClassSite<'a>,
        key: &MemberKey,
        placement: Placement,
    ) -> Vec<&'a ClassElement<'a>> {
        let mut found = Vec::new();

        for element in &class.body.body {
            if placement_of_element(element) == Some(placement)
                && self.element_key_of(file, element).as_ref() == Some(key)
            {
                found.push(element);
            }
        }

        found
    }

    fn push_elements(
        &mut self,
        (file, class): ClassSite<'a>,
        key: &MemberKey,
        placement: Placement,
        found: &mut MemberValues<'a>,
    ) {
        for element in self.elements_keyed((file, class), key, placement) {
            match element {
                ClassElement::MethodDefinition(method) if method.value.body.is_some() => {
                    let function = FunctionId {
                        file,
                        node: method.value.node_id(),
                    };

                    match method.kind {
                        MethodDefinitionKind::Method => {
                            push_function(&mut found.functions, function)
                        }
                        MethodDefinitionKind::Get => self.push_getter(function, found),
                        _ => {}
                    }
                }
                ClassElement::PropertyDefinition(property) => {
                    if let Some(value) = &property.value {
                        found.values.push((file, value));
                    }
                }
                ClassElement::AccessorProperty(property) => {
                    if let Some(value) = &property.value {
                        found.values.push((file, value));
                    }
                }
                _ => {}
            }
        }
    }

    fn classes_of_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Vec<ClassSite<'a>> {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return Vec::new();
        }

        let expression = unwrap(expression);

        if let Some(class) = self
            .declarations
            .class_of_expression(self.project, file, expression)
        {
            return vec![class];
        }

        match expression {
            Expression::ClassExpression(class) => vec![(file, class)],
            Expression::ConditionalExpression(conditional) => {
                let mut found =
                    self.classes_of_expression(file, &conditional.consequent, depth + 1);

                found.extend(self.classes_of_expression(file, &conditional.alternate, depth + 1));

                found
            }
            Expression::Identifier(reference) => {
                match self
                    .declarations
                    .of_reference(self.project, file, reference)
                    .and_then(constant_initializer_of)
                {
                    Some((target, init)) => self.classes_of_expression(target, init, depth + 1),
                    None => Vec::new(),
                }
            }
            Expression::CallExpression(call) => {
                let targets = self.resolved_callee_of(file, call).targets;
                let mut found = Vec::new();

                for target in targets.known {
                    let parameters = match self.kind_of_node(target.file, target.node) {
                        AstKind::Function(function) => &function.params,
                        AstKind::ArrowFunctionExpression(arrow) => &arrow.params,
                        _ => continue,
                    };

                    for value in self.returned_expressions_of(target) {
                        for (returned_file, returned) in
                            self.classes_of_expression(target.file, value, depth + 1)
                        {
                            found.push((returned_file, returned));

                            let Some(heritage) = &returned.heritage else {
                                continue;
                            };
                            let Expression::Identifier(base) = unwrap(&heritage.expression) else {
                                continue;
                            };
                            let position = parameters.items.iter().position(|parameter| {
                                matches!(&parameter.pattern, oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) if identifier.name == base.name)
                            });

                            if let Some(argument) = position
                                .and_then(|position| call.arguments.get(position))
                                .and_then(Argument::as_expression)
                            {
                                found.extend(self.classes_of_expression(file, argument, depth + 1));
                            }
                        }
                    }
                }

                found
            }
            _ => Vec::new(),
        }
    }

    fn lineage_sites_of(&mut self, file: FileId, class: &'a Class<'a>) -> Vec<Site> {
        let site = (file, class.node_id());

        if let Some(lineage) = self.values.targets.lineages.get(&site) {
            return lineage.clone();
        }

        let mut lineage = vec![site];
        let mut pending = vec![(file, class)];

        while let Some((file, class)) = pending.pop() {
            if lineage.len() >= MAXIMUM_LINEAGE {
                break;
            }

            let Some(heritage) = &class.heritage else {
                continue;
            };

            for (base_file, base) in self.classes_of_expression(file, &heritage.expression, 0) {
                let base_site = (base_file, base.node_id());

                if !lineage.contains(&base_site) {
                    lineage.push(base_site);
                    pending.push((base_file, base));
                }
            }
        }

        self.values.targets.lineages.insert(site, lineage.clone());

        lineage
    }

    fn lineage_of(&mut self, file: FileId, class: &'a Class<'a>) -> Vec<ClassSite<'a>> {
        let sites = self.lineage_sites_of(file, class);

        self.class_sites_of(sites)
    }

    fn class_sites_of(&self, sites: Vec<Site>) -> Vec<ClassSite<'a>> {
        sites
            .into_iter()
            .filter_map(|(file, node)| match self.kind_of_node(file, node) {
                AstKind::Class(class) => Some((file, class)),
                _ => None,
            })
            .collect()
    }

    fn subclasses_of(&mut self, file: FileId, class: &'a Class<'a>) -> Vec<ClassSite<'a>> {
        if self.values.targets.subclasses.is_none() {
            let mut subclasses: HashMap<Site, Vec<Site>> = HashMap::new();

            for (derived_file, node) in self.values.targets.classes.clone() {
                let AstKind::Class(derived) = self.kind_of_node(derived_file, node) else {
                    continue;
                };

                let lineage = self.lineage_sites_of(derived_file, derived);

                for (position, base) in lineage.iter().enumerate().skip(1) {
                    let children = subclasses.entry(*base).or_default();

                    for child in &lineage[..position] {
                        if !children.contains(child) {
                            children.push(*child);
                        }
                    }
                }
            }

            self.values.targets.subclasses = Some(subclasses);
        }

        let sites = self
            .values
            .targets
            .subclasses
            .as_ref()
            .and_then(|subclasses| subclasses.get(&(file, class.node_id())))
            .cloned()
            .unwrap_or_default();

        self.class_sites_of(sites)
    }

    fn builtin_classes_of(&mut self) -> Vec<(Site, BuiltinKind)> {
        if let Some(found) = &self.values.targets.builtin_classes {
            return found.clone();
        }

        let mut found = Vec::new();

        for (file, node) in self.values.targets.classes.clone() {
            let AstKind::Class(class) = self.kind_of_node(file, node) else {
                continue;
            };

            for (base_file, base) in self.lineage_of(file, class) {
                let builtin = base.heritage.as_ref().and_then(|heritage| {
                    global_name_of(
                        self.project.file(base_file).semantic.scoping(),
                        &heritage.expression,
                    )
                });

                if let Some(name) = builtin {
                    found.push(((file, node), builtin_kind_of(name)));

                    break;
                }
            }
        }

        self.values.targets.builtin_classes = Some(found.clone());

        found
    }

    fn write_parts_of(
        &self,
        (file, node): Site,
    ) -> Option<(&'a Expression<'a>, Option<&'a Expression<'a>>)> {
        let nodes = self.project.file(file).semantic.nodes();

        match self.kind_of_node(file, node) {
            AstKind::AssignmentExpression(assignment) => match &assignment.left {
                AssignmentTarget::AssignmentTargetIdentifier(_) => None,
                left => Some((
                    left.as_member_expression()?.object(),
                    Some(&assignment.right),
                )),
            },
            AstKind::UnaryExpression(unary) => Some((
                member_expression_of(unwrap(&unary.argument))?.object(),
                None,
            )),
            AstKind::ObjectProperty(property) => {
                let call = nodes
                    .ancestors(node)
                    .find_map(|ancestor| match ancestor.kind() {
                        AstKind::CallExpression(call) => Some(call),
                        _ => None,
                    })?;
                let object = call.arguments.first()?.as_expression()?;

                Some((
                    object,
                    (property.kind == PropertyKind::Init).then_some(&property.value),
                ))
            }
            AstKind::CallExpression(call) => {
                let object = call.arguments.first()?.as_expression()?;
                let value = match reflective_name_of(&call.callee) {
                    Some("setPrototypeOf") => {
                        call.arguments.get(1).and_then(Argument::as_expression)
                    }
                    _ => None,
                };

                Some((object, value))
            }
            _ => None,
        }
    }

    fn owner_of(&mut self, file: FileId, object: &'a Expression<'a>) -> Owner {
        let project = self.project;
        let scoping = project.file(file).semantic.scoping();

        if let Some(kind) = self.builtin_prototype_of(file, object, 0) {
            return Owner::Builtin { kind };
        }

        match unwrap(object) {
            Expression::ThisExpression(this) => {
                match this_owner_of(project, file, this.node_id()) {
                    Some(ThisOwner::Class {
                        file,
                        class,
                        placement,
                    }) => {
                        return Owner::ClassThis {
                            class: (file, class.node_id()),
                            placement,
                        }
                    }
                    Some(ThisOwner::Object { file, object }) => {
                        return Owner::ObjectThis {
                            object: (file, object.node_id()),
                        }
                    }
                    None => {}
                }
            }
            Expression::StaticMemberExpression(member) if member.property.name == "prototype" => {
                if let Some((target, class)) =
                    self.declarations
                        .class_of_expression(project, file, unwrap(&member.object))
                {
                    return Owner::Prototype {
                        class: (target, class.node_id()),
                    };
                }
            }
            other => {
                if let Some(name) = global_name_of(scoping, other) {
                    return Owner::Global {
                        name: global_owner_of(name),
                    };
                }
            }
        }

        let value = self.storage_value_of(file, object);
        let allocation =
            self.values.is_allocation(value) && !self.is_replaced_construction(file, object, 0);
        let shared = !allocation || self.escapes(file, unwrap(object));

        if let Some(function) = self.function_prototype_of(file, object) {
            return Owner::FunctionPrototype { function };
        }

        let kind = self.proven_kind_of(file, object, 0);
        let plain = kind == Kind::Other;

        Owner::Value {
            value,
            allocation,
            shared,
            kind,
            plain,
        }
    }

    fn function_prototype_of(&mut self, file: FileId, object: &'a Expression<'a>) -> Option<Site> {
        let member = member_expression_of(unwrap(object))?;

        if self.member_key_of(file, member) != Some(MemberKey::Name("prototype".to_string())) {
            return None;
        }

        let function = self.constructor_function_of(file, member.object(), 0)?;

        (!self.values.targets.rebound_every_function
            && !self.values.targets.rebound_functions.contains(&function))
        .then_some(function)
    }

    fn constructor_function_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Option<Site> {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return None;
        }

        let Expression::Identifier(reference) = unwrap(expression) else {
            return None;
        };
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference)?;

        match declaration {
            Declaration::Function {
                file: target,
                function: crate::declarations::FunctionNode::Function(function),
            } if function.body.is_some() && !function.declare => Some((target, function.node_id())),
            declaration => {
                let (target, init) = constant_initializer_of(declaration)?;

                self.constructor_function_of(target, init, depth + 1)
            }
        }
    }

    fn function_candidates_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Option<Vec<Site>> {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return None;
        }

        if let Some(function) = self.constructor_function_of(file, expression, 0) {
            return Some(vec![function]);
        }

        match unwrap(expression) {
            Expression::Identifier(reference)
                if is_unbound(self.project.file(file).semantic.scoping(), reference) =>
            {
                Some(Vec::new())
            }
            Expression::Identifier(reference) => {
                match self
                    .declarations
                    .of_reference(self.project, file, reference)?
                {
                    Declaration::Parameter {
                        file: target,
                        parameter: crate::declarations::ParameterNode::Formal(parameter),
                        function,
                    } => {
                        let mut found = Vec::new();

                        for (site, argument) in self
                            .call_arguments_of(target, function, parameter)?
                            .into_iter()
                            .flatten()
                        {
                            found.extend(self.function_candidates_of(site, argument, depth + 1)?);
                        }

                        Some(found)
                    }
                    Declaration::Class { .. } | Declaration::Function { .. } => Some(Vec::new()),
                    declaration => {
                        let (target, init) = constant_initializer_of(declaration)?;

                        self.function_candidates_of(target, init, depth + 1)
                    }
                }
            }
            literal if is_fresh_literal(literal) => Some(Vec::new()),
            _ => None,
        }
    }

    fn may_be_global_object(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return true;
        }

        let expression = unwrap(expression);

        match expression {
            Expression::Identifier(reference)
                if is_unbound(self.project.file(file).semantic.scoping(), reference) =>
            {
                GLOBAL_OBJECTS.contains(&reference.name.as_str())
            }
            Expression::Identifier(reference) => {
                let Some(declaration) =
                    self.declarations
                        .of_reference(self.project, file, reference)
                else {
                    return true;
                };

                if let Declaration::Parameter {
                    file: target,
                    parameter: crate::declarations::ParameterNode::Formal(parameter),
                    function,
                } = declaration
                {
                    return match self.call_arguments_of(target, function, parameter) {
                        Some(arguments) => {
                            arguments.into_iter().flatten().any(|(site, argument)| {
                                self.may_be_global_object(site, argument, depth + 1)
                            })
                        }
                        None => true,
                    };
                }

                match constant_initializer_of(declaration) {
                    Some((target, init)) => self.may_be_global_object(target, init, depth + 1),
                    None => {
                        let value = self.storage_value_of(file, expression);

                        !self.values.is_allocation(value)
                            && self.proven_kind_of(file, expression, 0) == Kind::Unknown
                    }
                }
            }
            literal if is_fresh_literal(literal) => false,
            other => {
                if member_expression_of(other).is_some_and(|member| {
                    self.member_key_of(file, member)
                        == Some(MemberKey::Name("prototype".to_string()))
                }) {
                    return false;
                }

                let value = self.storage_value_of(file, other);

                !self.values.is_allocation(value)
                    && self.proven_kind_of(file, other, 0) == Kind::Unknown
            }
        }
    }

    fn builtin_prototype_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Option<BuiltinKind> {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return None;
        }

        let scoping = self.project.file(file).semantic.scoping();

        match unwrap(expression) {
            Expression::Identifier(reference) => {
                let (target, init) = self
                    .declarations
                    .of_reference(self.project, file, reference)
                    .and_then(constant_initializer_of)?;

                self.builtin_prototype_of(target, init, depth + 1)
            }
            Expression::CallExpression(call) => {
                let Expression::StaticMemberExpression(member) = unwrap(&call.callee) else {
                    return None;
                };
                let reflective = matches!(unwrap(&member.object), Expression::Identifier(owner) if (owner.name == "Object" || owner.name == "Reflect") && is_unbound(scoping, owner));

                if !reflective || member.property.name != "getPrototypeOf" {
                    return None;
                }

                let argument = call.arguments.first()?.as_expression()?;

                Some(self.instance_kind_of(file, argument))
            }
            other => {
                let member = member_expression_of(other)?;

                match self.member_key_of(file, member)? {
                    MemberKey::Name(name) if name == "prototype" => {
                        global_name_of(scoping, member.object()).map(builtin_kind_of)
                    }
                    MemberKey::Name(name) if name == "__proto__" => {
                        Some(self.instance_kind_of(file, member.object()))
                    }
                    _ => None,
                }
            }
        }
    }

    fn is_replaced_construction(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return true;
        }

        match unwrap(expression) {
            Expression::NewExpression(new) => match unwrap(&new.callee) {
                Expression::Identifier(constructor)
                    if is_unbound(self.project.file(file).semantic.scoping(), constructor) =>
                {
                    self.values.targets.replaced_every_global
                        || self
                            .values
                            .targets
                            .replaced_globals
                            .contains(constructor.name.as_str())
                }
                _ => false,
            },
            Expression::Identifier(reference) => match self
                .declarations
                .of_reference(self.project, file, reference)
                .and_then(constant_initializer_of)
            {
                Some((target, init)) => self.is_replaced_construction(target, init, depth + 1),
                None => false,
            },
            _ => false,
        }
    }

    fn is_prototype_reassigned(&mut self, file: FileId, expression: &'a Expression<'a>) -> bool {
        if self.values.targets.prototype_owners.is_empty() {
            return false;
        }

        let value = self.storage_value_of(file, expression);
        let shared = !self.values.is_allocation(value) || self.escapes(file, expression);

        self.values
            .targets
            .prototype_owners
            .iter()
            .any(|(owner, owner_shared)| *owner == value || (shared && *owner_shared))
    }

    fn instance_kind_of(&mut self, file: FileId, expression: &'a Expression<'a>) -> BuiltinKind {
        match self.proven_kind_of(file, expression, 0) {
            Kind::Unknown | Kind::Other => None,
            kind => Some(kind),
        }
    }

    fn proven_kind_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Kind {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return Kind::Unknown;
        }

        match unwrap(expression) {
            Expression::ArrayExpression(_) => Kind::Array,
            Expression::StringLiteral(_) | Expression::TemplateLiteral(_) => Kind::String,
            Expression::RegExpLiteral(_) => Kind::RegExp,
            Expression::ObjectExpression(_) => Kind::Other,
            Expression::NewExpression(new) => match unwrap(&new.callee) {
                Expression::Identifier(constructor)
                    if is_unbound(self.project.file(file).semantic.scoping(), constructor)
                        && !self.values.targets.replaced_every_global
                        && !self
                            .values
                            .targets
                            .replaced_globals
                            .contains(constructor.name.as_str()) =>
                {
                    match constructor.name.as_str() {
                        "Array" => Kind::Array,
                        "Set" => Kind::Set,
                        "Map" => Kind::Map,
                        "RegExp" => Kind::RegExp,
                        _ => Kind::Unknown,
                    }
                }
                _ => Kind::Unknown,
            },
            Expression::Identifier(reference) => {
                if self.is_prototype_reassigned(file, unwrap(expression)) {
                    return Kind::Unknown;
                }

                let Some(declaration) =
                    self.declarations
                        .of_reference(self.project, file, reference)
                else {
                    return Kind::Unknown;
                };
                let mut values: Vec<Valued<'a>> = Vec::new();

                match declaration {
                    Declaration::Parameter {
                        file: target,
                        parameter: crate::declarations::ParameterNode::Formal(parameter),
                        function,
                    } => match self.call_arguments_of(target, function, parameter) {
                        Some(arguments) if !arguments.is_empty() => {
                            for argument in arguments {
                                match argument {
                                    Some(argument) => values.push(argument),
                                    None => return Kind::Unknown,
                                }
                            }
                        }
                        _ => return Kind::Unknown,
                    },
                    declaration => match declarator_of_identifier(&declaration) {
                        Some((target, declarator, _)) => match &declarator.init {
                            Some(init) => values.push((target, init)),
                            None => return Kind::Unknown,
                        },
                        None => return Kind::Unknown,
                    },
                }

                let (written, unresolved) = self.written_values_of(file, reference);

                if unresolved {
                    return Kind::Unknown;
                }

                values.extend(written);

                let mut proven = None;

                for (target, value) in values {
                    let kind = self.proven_kind_of(target, value, depth + 1);

                    if kind == Kind::Unknown || proven.is_some_and(|proven| proven != kind) {
                        return Kind::Unknown;
                    }

                    proven = Some(kind);
                }

                proven.unwrap_or(Kind::Unknown)
            }
            _ => Kind::Unknown,
        }
    }

    fn has_global_write(&self, name: &str, key: Option<MemberKey>) -> bool {
        self.values
            .targets
            .buckets
            .global
            .get(&(global_owner_of(name), key))
            .is_some_and(|indices| {
                indices
                    .iter()
                    .any(|index| self.values.targets.owners[*index].1)
            })
    }

    fn apply_write(&mut self, index: usize, found: &mut MemberValues<'a>) {
        let (_, callable) = self.values.targets.owners[index].clone();
        let write = self.values.targets.writes[index].clone();
        let Some((_, value)) = self.write_parts_of(write.site) else {
            if callable {
                found.replaced = true;
            }

            if let AstKind::AssignmentExpression(assignment) =
                self.kind_of_node(write.site.0, write.site.1)
            {
                found.values.push((write.site.0, &assignment.right));
            }

            return;
        };

        match write.kind {
            WriteKind::Prototype => {
                found.replaced = true;

                if value.is_some() && !found.hits.contains(&index) {
                    found.hits.push(index);
                }
            }
            _ => {
                found.replaced |= callable;

                if let Some(value) = value {
                    found.values.push((write.site.0, value));
                }
            }
        }
    }

    fn wide_summary_of(
        &mut self,
        written: Option<MemberKey>,
        kind: Kind,
        shared: bool,
        opaque: bool,
    ) -> WideSummary {
        let cache = (written.clone(), kind, shared, opaque);

        if let Some(summary) = self.values.targets.summaries.get(&cache) {
            return summary.clone();
        }

        let indices = self
            .values
            .targets
            .buckets
            .wide
            .get(&written)
            .cloned()
            .unwrap_or_default();
        let mut summary = WideSummary::default();
        let mut found = MemberValues::default();

        for index in indices {
            if !self.charge_dispatch() {
                summary.replaced = true;

                break;
            }

            let (owner, callable) = self.values.targets.owners[index].clone();
            let relevant = match owner {
                Owner::Builtin { kind: written } => affects(written, kind),
                Owner::FunctionPrototype { .. } => opaque && !is_builtin(kind),
                Owner::Value {
                    allocation: false,
                    kind: written,
                    plain,
                    ..
                } => is_compatible(written, kind) && !(plain && is_builtin(kind)),
                Owner::Value {
                    shared: true,
                    kind: written,
                    plain,
                    ..
                } => shared && is_compatible(written, kind) && !(plain && is_builtin(kind)),
                _ => false,
            };

            if !relevant {
                continue;
            }

            if self.values.targets.writes[index].kind == WriteKind::Prototype {
                summary.replaced = true;

                summary.prototypes.push(index);

                continue;
            }

            summary.replaced |= callable;

            if written.is_some() {
                self.apply_write(index, &mut found);
            }
        }

        let mut targets = TargetSet {
            known: found.functions,
            open: true,
        };
        let mut visited = HashSet::new();

        for (target, value) in found.values {
            self.collect_callable_targets(target, value, &mut visited, &mut targets);
        }

        summary.known = targets.known;

        self.values.targets.summaries.insert(cache, summary.clone());

        summary
    }

    fn collect_replacements(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        receiver: &Receiver<'a>,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let expression = unwrap(expression);
        let scoping = self.project.file(file).semantic.scoping();
        let global = global_name_of(scoping, expression).map(global_owner_of);
        let shared = receiver
            .values
            .iter()
            .any(|value| !self.values.is_allocation(*value))
            || self.escapes(file, expression);
        let kind = self.declared_type_of_expression(file, expression).kind;
        let mut written_keys = vec![Some(key.clone())];

        if matches!(key, MemberKey::Name(name) if is_index_name(name)) {
            written_keys.push(Some(MemberKey::Index));
        }

        written_keys.push(None);

        let mut indices = Vec::new();
        let mut classes: Vec<(Site, Placement)> = Vec::new();

        for origin in &receiver.origins {
            match *origin {
                Origin::Instance { file, class, exact }
                | Origin::Constructor { file, class, exact } => {
                    let placement = match origin {
                        Origin::Constructor { .. } => Placement::Static,
                        _ => Placement::Instance,
                    };
                    let mut related = self.lineage_sites_of(file, class);

                    if !exact {
                        related.extend(
                            self.subclasses_of(file, class)
                                .into_iter()
                                .map(|(file, class)| (file, class.node_id())),
                        );
                    }

                    for site in related {
                        if !classes.contains(&(site, placement)) {
                            classes.push((site, placement));
                        }
                    }
                }
                Origin::Object { .. } | Origin::Function { .. } => {}
            }
        }

        for written in &written_keys {
            let buckets = &self.values.targets.buckets;

            for value in &receiver.values {
                if let Some(found) = buckets.values.get(&(written.clone(), *value)) {
                    indices.extend(found.iter().copied());
                }
            }

            for origin in &receiver.origins {
                if let Origin::Object { file, object } = origin {
                    if let Some(found) = buckets
                        .objects
                        .get(&((*file, object.node_id()), written.clone()))
                    {
                        indices.extend(found.iter().copied());
                    }
                }
            }

            for (site, placement) in &classes {
                for index in buckets
                    .classes
                    .get(&(*site, written.clone()))
                    .into_iter()
                    .flatten()
                {
                    let matched = match &self.values.targets.owners[*index].0 {
                        Owner::ClassThis {
                            placement: written, ..
                        } => (*written == Placement::Static) == (*placement == Placement::Static),
                        Owner::Prototype { .. } => *placement == Placement::Instance,
                        _ => false,
                    };

                    if matched {
                        indices.push(*index);
                    }
                }
            }

            if let Some(found) = global
                .as_ref()
                .and_then(|global| buckets.global.get(&(global.clone(), written.clone())))
            {
                indices.extend(found.iter().copied());
            }
        }

        indices.sort_unstable();
        indices.dedup();

        for index in indices {
            if !self.charge_dispatch() {
                found.replaced = true;

                return;
            }

            self.apply_write(index, found);
        }

        if let Some(global) = &global {
            let namespace = self
                .values
                .targets
                .buckets
                .global
                .get(&(
                    "globalThis".to_string(),
                    Some(MemberKey::Name(global.clone())),
                ))
                .cloned()
                .unwrap_or_default();

            for index in namespace {
                if !self.charge_dispatch() {
                    found.replaced = true;

                    return;
                }

                found.replaced = true;

                let site = self.values.targets.writes[index].site;

                if let AstKind::AssignmentExpression(assignment) = self.kind_of_node(site.0, site.1)
                {
                    self.prototype_values_of(site.0, &assignment.right, key, found);
                }
            }

            found.replaced |= self.has_global_write("globalThis", None);
        }

        for written in written_keys {
            let summary = self.wide_summary_of(written, kind, shared, receiver.origins.is_empty());

            found.replaced |= summary.replaced;

            for function in summary.known {
                push_function(&mut found.functions, function);
            }

            for index in summary.prototypes {
                if !found.hits.contains(&index) {
                    found.hits.push(index);
                }
            }
        }

        if found.lookups > 0 && found.defined == found.lookups {
            let hits = std::mem::take(&mut found.hits);

            for hit in hits {
                let keep = match &self.values.targets.owners[hit].0 {
                    Owner::Value {
                        value,
                        allocation,
                        shared: written,
                        ..
                    } => receiver.values.contains(value) || ((!*allocation || *written) && shared),
                    Owner::ClassThis { .. } | Owner::ObjectThis { .. } => true,
                    Owner::Prototype { class } => found.below.contains(class),
                    Owner::FunctionPrototype { function } => found.below.contains(function),
                    Owner::Builtin { .. } | Owner::Global { .. } => false,
                };

                if keep {
                    found.hits.push(hit);
                }
            }
        }

        if shared || kind == Kind::Unknown {
            for ((class_file, node), builtin) in self.builtin_classes_of() {
                if !affects(builtin, kind) {
                    continue;
                }

                let AstKind::Class(class) = self.kind_of_node(class_file, node) else {
                    continue;
                };
                let before = found.functions.len() + found.values.len();

                self.push_elements((class_file, class), key, Placement::Instance, found);

                if found.functions.len() + found.values.len() > before {
                    found.replaced = true;
                }
            }
        }
    }

    fn escapes(&mut self, file: FileId, receiver: &'a Expression<'a>) -> bool {
        let project = self.project;
        let Expression::Identifier(reference) = receiver else {
            return false;
        };
        let Some(binding) = self
            .declarations
            .binding_of_reference(project, file, reference)
        else {
            return true;
        };

        self.declarations
            .surface_references_of(project, binding)
            .into_iter()
            .any(|(target, node, write)| {
                let nodes = project.file(target).semantic.nodes();

                !write
                    && match value_flow_of(nodes, node) {
                        ValueFlow::Argument(call, 0) => !matches!(
                            nodes.kind(call),
                            AstKind::CallExpression(call) if reflective_name_of(&call.callee).is_some()
                        ),
                        ValueFlow::Alias(_)
                        | ValueFlow::Stored(_)
                        | ValueFlow::Argument(..)
                        | ValueFlow::Escaped(_) => true,
                        ValueFlow::Read | ValueFlow::Member | ValueFlow::Receiver(_) => false,
                    }
            })
    }

    fn may_be_callable(&mut self, file: FileId, value: &'a Expression<'a>) -> bool {
        match unwrap(value) {
            Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::ClassExpression(_) => false,
            Expression::NewExpression(new) => !matches!(
                unwrap(&new.callee),
                Expression::Identifier(constructor)
                    if is_unbound(self.project.file(file).semantic.scoping(), constructor)
                        && (INERT_CONSTRUCTORS.contains(&constructor.name.as_str())
                            || LINEAR_CONSTRUCTORS.contains(&constructor.name.as_str()))
            ),
            other => !self.is_non_callable_expression(file, other),
        }
    }
}

fn reflective_writes_of<'a>(
    file: FileId,
    call: &'a CallExpression<'a>,
    site: Site,
    pending: &mut Vec<(Site, Option<KeySource<'a>>, WriteKind)>,
) {
    let Some(method) = reflective_name_of(&call.callee) else {
        return;
    };

    if call
        .arguments
        .first()
        .and_then(Argument::as_expression)
        .is_none()
    {
        return;
    }

    match method {
        "defineProperty" | "set" | "deleteProperty" => {
            let key = match call.arguments.get(1).and_then(Argument::as_expression) {
                Some(key) => match unwrap(key) {
                    Expression::StringLiteral(literal) => {
                        Some(KeySource::Known(MemberKey::Name(literal.value.to_string())))
                    }
                    _ => Some(KeySource::Computed(file, key)),
                },
                None => None,
            };
            let kind = match method {
                "deleteProperty" => WriteKind::Removed,
                _ => WriteKind::Defined,
            };

            pending.push((site, key, kind));
        }
        "assign" => {
            for source in &call.arguments[1..] {
                let Some(Expression::ObjectExpression(object)) = source.as_expression().map(unwrap)
                else {
                    pending.push((site, None, WriteKind::Defined));

                    continue;
                };

                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::ObjectProperty(property) => {
                            let key = match (property.computed, &property.key) {
                                (false, key) | (true, key @ PropertyKey::StringLiteral(_)) => {
                                    key.static_name().map(|name| {
                                        KeySource::Known(MemberKey::Name(name.into_owned()))
                                    })
                                }
                                (true, key) => key
                                    .as_expression()
                                    .map(|key| KeySource::Computed(file, key)),
                            };
                            let kind = match property.kind {
                                PropertyKind::Init => WriteKind::Assigned,
                                _ => WriteKind::Defined,
                            };

                            pending.push(((file, property.node_id()), key, kind));
                        }
                        ObjectPropertyKind::SpreadProperty(_) => {
                            pending.push((site, None, WriteKind::Defined))
                        }
                    }
                }
            }
        }
        "setPrototypeOf" => pending.push((site, None, WriteKind::Prototype)),
        _ => pending.push((site, None, WriteKind::Defined)),
    }
}

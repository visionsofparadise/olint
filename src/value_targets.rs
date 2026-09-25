use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, BindingProperty,
    CallExpression, Class, ClassElement, Expression, FormalParameter, IdentifierReference,
    MemberExpression, MethodDefinitionKind, ObjectExpression, ObjectPropertyKind, PropertyKey,
    PropertyKind,
};
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};

use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::constants::constant_initializer_of;
use crate::declarations::{
    element_name_of, parameters_of, Binding, Declaration, FunctionId, FunctionNode, ParameterNode,
    TargetSet,
};
use crate::declared_types::{declarator_of_identifier, Kind};
use crate::effects::{value_flow_of, ValueFlow};
use crate::invocations::{construction_context_of, ImplicitSite};
use crate::project::FileId;
use crate::receivers::{annotation_of, this_owner_of, Placement, ThisOwner};
use crate::syntax::{call_of, is_iteration_kind, member_expression_of, unwrap, unwrap_to_cast};
use crate::tables::{LINEAR_CONSTRUCTORS, REFLECTIVE_WRITES};

use super::{Definedness, ValueId};

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
pub(crate) type PrototypeMembers<'a> = HashMap<(usize, MemberKey), MemberValues<'a>>;
type BuiltinKind = Option<Kind>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum MemberKey {
    Name(String),
    Symbol(Site),
    WellKnown(String),
    Index,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Layer {
    Own,
    Prototype,
    Any,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriteKind {
    Assigned,
    Removed,
    Defined,
    Prototype,
}

#[derive(Clone, Copy)]
enum PatternSources<'a> {
    Initializer(&'a Expression<'a>),
    Parameter(FunctionNode<'a>, &'a FormalParameter<'a>),
}

#[derive(Clone, Debug)]
enum StepKey {
    Member(MemberKey),
    Element(usize),
}

#[derive(Clone, Debug)]
struct PatternStep<'a> {
    key: StepKey,
    default: Option<&'a Expression<'a>>,
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
    callables_open: bool,
    known: Vec<FunctionId>,
    getters: Vec<FunctionId>,
    setters: Vec<FunctionId>,
    accessors_open: bool,
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
    open_heritages: HashSet<Site>,
    bases: HashMap<Site, Vec<Site>>,
    removals: HashMap<Option<MemberKey>, Vec<usize>>,
    subclasses: Option<HashMap<Site, Vec<Site>>>,
    builtin_classes: Option<Vec<(Site, BuiltinKind)>>,
    dispatches: HashMap<Site, (Vec<FunctionId>, bool, bool)>,
    exhaustions: u64,
    exhausted_calls: HashSet<Site>,
    summaries: HashMap<(Option<MemberKey>, Kind, bool, bool), WideSummary>,
    linked: HashSet<(Site, MemberKey)>,
    exploring: HashSet<(usize, MemberKey)>,
    cuts: u64,
    prototype_owners: Vec<(ValueId, bool)>,
    replaced_globals: HashSet<String>,
    replaced_every_global: bool,
    rebound_functions: HashSet<Site>,
    rebound_every_function: bool,
    patterns: HashMap<(FileId, oxc_semantic::SymbolId), TargetSet>,
    parameter_classes: HashMap<Binding, (Vec<Site>, bool)>,
    plans: HashMap<Site, Rc<ConstructionPlan>>,
    accessor_keys: HashSet<Option<MemberKey>>,
    callable_keys: HashSet<Option<MemberKey>>,
    written_keys: HashSet<Option<MemberKey>>,
    invocations: HashMap<Binding, Option<Vec<Site>>>,
    primitive_bindings: HashMap<Binding, bool>,
    resolving_invocations: HashSet<Binding>,
    implicit: HashMap<(Site, ImplicitKey), (TargetSet, bool)>,
    extensible: HashMap<Site, bool>,
    closing: HashMap<FileId, Rc<HashSet<NodeId>>>,
    implicit_plans: HashMap<Site, Rc<Vec<ImplicitSite>>>,
    builtin_accessors: HashMap<Kind, bool>,
    resolving_patterns: HashSet<(FileId, oxc_semantic::SymbolId)>,
    pattern_cuts: u64,
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
    HomeClass {
        file: FileId,
        class: &'a Class<'a>,
        placement: Placement,
    },
    HomeObject {
        file: FileId,
        object: &'a ObjectExpression<'a>,
    },
}

#[derive(Default)]
struct Receiver<'a> {
    origins: Vec<Origin<'a>>,
    values: Vec<ValueId>,
    constrained: bool,
}

#[derive(Clone, Default)]
pub(crate) struct MemberValues<'a> {
    values: Vec<Valued<'a>>,
    functions: Vec<FunctionId>,
    getters: Vec<FunctionId>,
    setters: Vec<FunctionId>,
    replaced: bool,
    accessors_open: bool,
    hits: Vec<usize>,
    lookups: usize,
    defined: usize,
    below: Vec<Site>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ImplicitKey {
    Get,
    Set,
    Methods(Vec<MemberKey>),
    Returned(MemberKey),
    Member(MemberKey, bool),
    Construction,
}

#[derive(Clone, Copy)]
enum Descriptor<'a> {
    Absent,
    Unknown,
    Known {
        value: Option<&'a Expression<'a>>,
        getter: Option<&'a Expression<'a>>,
        setter: Option<&'a Expression<'a>>,
    },
}

enum KeySource<'a> {
    Known(MemberKey),
    Computed(FileId, &'a Expression<'a>),
}

pub(crate) struct MemberDispatch {
    pub(crate) known: Vec<FunctionId>,
    pub(crate) replaced: bool,
}

pub(crate) struct Construction<'a> {
    pub(crate) targets: TargetSet,
    pub(crate) implicit: Vec<(FileId, &'a Class<'a>)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Iteration {
    pub(crate) native: bool,
    pub(crate) asynchronous: bool,
    pub(crate) acquire: TargetSet,
    pub(crate) next: TargetSet,
    pub(crate) close: TargetSet,
}

#[derive(Debug, Default)]
pub(crate) struct ConstructionPlan {
    pub(crate) constructors: Vec<FunctionId>,
    pub(crate) initializers: Vec<Site>,
    pub(crate) owners: HashSet<Site>,
    pub(crate) open: bool,
}

impl<'a> MemberValues<'a> {
    fn absorb(&mut self, other: &MemberValues<'a>) -> bool {
        let before = self.counts_of();

        for value in &other.values {
            if !self
                .values
                .iter()
                .any(|known| known.0 == value.0 && known.1.node_id() == value.1.node_id())
            {
                self.values.push(*value);
            }
        }

        for (ours, theirs) in [
            (&mut self.functions, &other.functions),
            (&mut self.getters, &other.getters),
            (&mut self.setters, &other.setters),
        ] {
            for function in theirs {
                push_function(ours, *function);
            }
        }

        self.replaced |= other.replaced;
        self.accessors_open |= other.accessors_open;

        self.counts_of() != before
    }

    fn counts_of(&self) -> (usize, usize, usize, usize, bool, bool) {
        (
            self.values.len(),
            self.functions.len(),
            self.getters.len(),
            self.setters.len(),
            self.replaced,
            self.accessors_open,
        )
    }
}

impl Construction<'_> {
    pub(crate) fn into_targets(self) -> TargetSet {
        let mut targets = self.targets;

        targets.open |= !self.implicit.is_empty();

        targets
    }
}

pub(crate) fn protocol_key_of(name: &str) -> MemberKey {
    match name.strip_prefix("@@") {
        Some(symbol) => MemberKey::WellKnown(symbol.to_string()),
        None => MemberKey::Name(name.to_string()),
    }
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

fn closed_targets_of() -> TargetSet {
    TargetSet {
        known: Vec::new(),
        open: false,
    }
}

fn descriptor_value_of(descriptor: Descriptor<'_>) -> Option<&Expression<'_>> {
    match descriptor {
        Descriptor::Known { value, .. } => value,
        _ => None,
    }
}

fn is_unaliased_source(value: &Expression<'_>, key: &StepKey) -> bool {
    match (value, key) {
        (Expression::ObjectExpression(object), StepKey::Member(_)) => {
            object.properties.iter().all(|property| {
                matches!(
                    property,
                    ObjectPropertyKind::ObjectProperty(property)
                        if property.kind == PropertyKind::Init && !property.computed
                )
            })
        }
        (Expression::ArrayExpression(array), StepKey::Element(_)) => array
            .elements
            .iter()
            .all(|element| !matches!(element, ArrayExpressionElement::SpreadElement(_))),
        _ => false,
    }
}

fn is_unknown_prototype(prototype: &Expression<'_>, receiver: &Receiver<'_>) -> bool {
    receiver.origins.is_empty() && !matches!(unwrap(prototype), Expression::NullLiteral(_))
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

fn is_type_only_element(element: &ClassElement<'_>) -> bool {
    match element {
        ClassElement::MethodDefinition(method) => method.value.body.is_none(),
        ClassElement::PropertyDefinition(property) => {
            property.declare || property.r#type.is_abstract()
        }
        ClassElement::AccessorProperty(property) => property.r#type.is_abstract(),
        _ => false,
    }
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

    pub(crate) fn accessor_targets_of(
        &mut self,
        file: FileId,
        access: AstKind<'a>,
        setter: bool,
    ) -> TargetSet {
        self.index_targets();

        if self.values.targets.accessor_keys.is_empty() {
            return closed_targets_of();
        }

        let implicit = match setter {
            true => ImplicitKey::Set,
            false => ImplicitKey::Get,
        };

        self.implicit_targets_of((file, access.node_id()), implicit, |analysis| {
            analysis.accessor_targets_within(file, access, setter)
        })
    }

    pub(crate) fn protocol_targets_of(
        &mut self,
        file: FileId,
        receiver: &'a Expression<'a>,
        keys: &[MemberKey],
    ) -> TargetSet {
        self.index_targets();

        if !keys.iter().any(|key| self.may_implement(key)) {
            return closed_targets_of();
        }

        let implicit = ImplicitKey::Methods(keys.to_vec());

        self.implicit_targets_of((file, receiver.node_id()), implicit, |analysis| {
            analysis.protocol_targets_within(file, receiver, keys)
        })
    }

    pub(crate) fn merge_iterator_targets(
        &mut self,
        found: &mut TargetSet,
        incoming: TargetSet,
    ) -> bool {
        found.open |= incoming.open;

        if !self.charge_work(
            crate::analysis::work::Event::TraversalEdge,
            (found.known.len() + incoming.known.len()) as u64,
        ) {
            found.open = true;

            return false;
        }

        let mut seen: HashSet<FunctionId> = found.known.iter().copied().collect();

        found.known.extend(
            incoming
                .known
                .into_iter()
                .filter(|target| seen.insert(*target)),
        );

        true
    }

    pub(crate) fn iterator_accessors_on(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        key: MemberKey,
    ) -> TargetSet {
        let kind = self.iteration_kind_of(file, expression, 0);

        if is_builtin(kind)
            || self.is_intrinsic_iterator(file, expression)
            || self.is_generator_call(file, expression)
        {
            self.index_targets();

            if !self.may_access(Some(&key)) {
                return closed_targets_of();
            }

            let keyed = self.wide_summary_of(Some(key), kind, false, true);
            let any = self.wide_summary_of(None, kind, false, true);

            return TargetSet {
                known: keyed.getters,
                open: keyed.accessors_open || any.accessors_open,
            };
        }

        self.property_accessors_of((file, expression), key, false)
    }

    pub(crate) fn iterable_elements_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> (Vec<Valued<'a>>, bool) {
        if depth > MAXIMUM_ALIAS_DEPTH || !self.charge_dispatch() {
            return (Vec::new(), true);
        }

        if let Expression::ArrayExpression(array) = unwrap(expression) {
            if !self.charge_targets(array.elements.len() as u64) {
                return (Vec::new(), true);
            }

            let mut values = Vec::new();
            let mut open = false;

            for element in &array.elements {
                match element {
                    ArrayExpressionElement::SpreadElement(spread) => {
                        let (found, unresolved) =
                            self.iterable_elements_of(file, &spread.argument, depth + 1);

                        values.extend(found);

                        open |= unresolved;
                    }
                    _ => values.extend(element.as_expression().map(|value| (file, value))),
                }
            }

            return (values, open);
        }

        if let Some((source, value)) = self.constant_source_of(file, expression) {
            return self.iterable_elements_of(source, value, depth + 1);
        }

        self.property_values_of((file, expression), &MemberKey::Index)
    }

    pub(crate) fn entry_values_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        index: usize,
    ) -> (Vec<Valued<'a>>, bool) {
        if matches!(unwrap(expression), Expression::ArrayExpression(_)) {
            let found = self.literal_element_values_of(file, expression, index, 0);

            return (found.values, found.replaced || found.accessors_open);
        }

        self.property_values_of((file, expression), &MemberKey::Name(index.to_string()))
    }

    fn iterator_methods_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        keys: &[MemberKey],
    ) -> TargetSet {
        let kind = self.iteration_kind_of(file, expression, 0);
        let mut found = if is_builtin(kind) && !is_builtin(self.declared_kind_of(file, expression))
        {
            let mut found = closed_targets_of();

            for key in keys {
                let targets = self.wide_protocol_of(key, kind);

                if !self.merge_iterator_targets(&mut found, targets) {
                    break;
                }
            }

            found
        } else {
            self.protocol_targets_of(file, expression, keys)
        };
        let mut visited = HashSet::new();

        for key in keys {
            let getters = self.iterator_accessors_on(file, expression, key.clone());

            found.open |= getters.open;

            if !self.charge_work(
                crate::analysis::work::Event::TraversalEdge,
                (found.known.len() + getters.known.len()) as u64,
            ) {
                found.open = true;

                return found;
            }

            let excluded: HashSet<FunctionId> = getters.known.iter().copied().collect();

            found.known.retain(|target| !excluded.contains(target));

            for getter in getters.known {
                let returned = self.returned_expressions_of(getter);

                for value in returned {
                    if !self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                        found.open = true;

                        return found;
                    }

                    if !self.is_primitive_operand(getter.file, value) {
                        self.collect_callable_targets(getter.file, value, &mut visited, &mut found);
                    }
                }
            }
        }

        found
    }

    pub(crate) fn iteration_of(
        &mut self,
        file: FileId,
        iterable: &'a Expression<'a>,
        asynchronous: bool,
    ) -> Iteration {
        let acquire_keys = match asynchronous {
            true => vec![
                MemberKey::WellKnown("asyncIterator".to_string()),
                MemberKey::WellKnown("iterator".to_string()),
            ],
            false => vec![MemberKey::WellKnown("iterator".to_string())],
        };
        let site = (file, iterable.node_id());

        self.index_targets();

        let native = self.is_intrinsic_iterator(file, iterable)
            || is_builtin(self.iteration_kind_of(file, iterable, 0));

        if !["@@iterator", "@@asyncIterator", "next", "return"]
            .iter()
            .any(|name| self.may_implement(&protocol_key_of(name)))
        {
            return Iteration {
                native,
                asynchronous,
                acquire: closed_targets_of(),
                next: closed_targets_of(),
                close: closed_targets_of(),
            };
        }

        if self.is_generator_call(file, iterable) || self.is_intrinsic_iterator(file, iterable) {
            return Iteration {
                native,
                asynchronous,
                acquire: closed_targets_of(),
                next: self.intrinsic_protocol_of(site, "next"),
                close: self.intrinsic_protocol_of(site, "return"),
            };
        }

        let acquire = self.iterator_methods_of(file, iterable, &acquire_keys);

        if acquire.open {
            return Iteration {
                native: false,
                asynchronous,
                next: acquire.clone(),
                close: acquire.clone(),
                acquire,
            };
        }

        if acquire.known.is_empty() {
            let kind = self.iteration_kind_of(file, iterable, 0);

            if !is_builtin(kind) {
                return Iteration {
                    native,
                    asynchronous,
                    acquire,
                    next: closed_targets_of(),
                    close: closed_targets_of(),
                };
            }

            return Iteration {
                native,
                asynchronous,
                acquire,
                next: self.intrinsic_protocol_of(site, "next"),
                close: self.intrinsic_protocol_of(site, "return"),
            };
        }

        let [next, close] = ["next", "return"].map(|name| {
            let key = MemberKey::Name(name.to_string());

            self.implicit_targets_of(site, ImplicitKey::Returned(key.clone()), |analysis| {
                let mut found = closed_targets_of();

                for function in &acquire.known {
                    let targets =
                        analysis.returned_protocol_targets_of(*function, (file, iterable), &key);

                    found.open |= targets.open;

                    for known in targets.known {
                        push_target(&mut found, known);
                    }
                }

                found
            })
        });

        Iteration {
            native: false,
            asynchronous,
            acquire,
            next,
            close,
        }
    }

    pub(crate) fn construction_dispatch_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<TargetSet> {
        let object = unwrap(member.object());

        if !matches!(object, Expression::ThisExpression(_) | Expression::Super(_)) {
            return None;
        }

        let (class, placement) = construction_context_of(self.project, file, object.node_id())?;

        self.index_targets();

        Some(self.implicit_targets_of(
            (file, member_node_of(member)),
            ImplicitKey::Construction,
            |analysis| analysis.construction_dispatch_within(file, member, (class, placement)),
        ))
    }

    fn implicit_targets_of(
        &mut self,
        site: Site,
        implicit: ImplicitKey,
        resolve: impl FnOnce(&mut Self) -> TargetSet,
    ) -> TargetSet {
        let cache = (site, implicit);

        if let Some((targets, exhausted)) = self.values.targets.implicit.get(&cache) {
            let targets = targets.clone();

            self.values.targets.exhaustions += u64::from(*exhausted);

            return targets;
        }

        let outermost = self.values.targets.depth == 0;
        let exhaustions = self.values.targets.exhaustions;

        if !self.enter_targets() {
            self.leave_targets();

            return TargetSet {
                known: Vec::new(),
                open: true,
            };
        }

        let mut targets = resolve(self);

        targets.open |= self.work_exhausted();

        self.leave_targets();

        if outermost && !self.work_exhausted() {
            let exhausted = self.values.targets.exhaustions > exhaustions;

            self.values
                .targets
                .implicit
                .insert(cache, (targets.clone(), exhausted));
        }

        targets
    }

    fn implicit_receiver_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Receiver<'a> {
        let mut receiver = Receiver::default();

        self.collect_receiver(file, expression, &mut HashSet::new(), &mut receiver);

        receiver
    }

    fn is_defined_key(&self, keys: &HashSet<Option<MemberKey>>, key: &MemberKey) -> bool {
        keys.contains(&Some(key.clone())) || keys.contains(&None)
    }

    pub(crate) fn may_implement_any(&mut self, keys: &[MemberKey]) -> bool {
        self.index_targets();

        keys.iter().any(|key| self.may_implement(key))
    }

    pub(crate) fn may_access(&mut self, key: Option<&MemberKey>) -> bool {
        self.index_targets();

        match key {
            Some(key) => self.is_defined_key(&self.values.targets.accessor_keys, key),
            None => !self.values.targets.accessor_keys.is_empty(),
        }
    }

    pub(crate) fn member_key(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<MemberKey> {
        self.member_key_of(file, member)
    }

    pub(crate) fn expression_key(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<MemberKey> {
        match self.member_key_of_expression(file, expression) {
            Some(key) => Some(key),
            None if self.is_numeric_key(file, expression, 0) => Some(MemberKey::Index),
            None => None,
        }
    }

    pub(crate) fn property_key(
        &mut self,
        file: FileId,
        key: &'a PropertyKey<'a>,
        computed: bool,
    ) -> Option<MemberKey> {
        self.defined_key_of(file, key, computed)
    }

    pub(crate) fn implicit_plan(&self, site: Site) -> Option<Rc<Vec<ImplicitSite>>> {
        self.values.targets.implicit_plans.get(&site).cloned()
    }

    pub(crate) fn store_implicit_plan(&mut self, site: Site, plan: Rc<Vec<ImplicitSite>>) {
        self.values.targets.implicit_plans.insert(site, plan);
    }

    pub(crate) fn closes_early(&mut self, file: FileId, statement: NodeId) -> bool {
        if let Some(closing) = self.values.targets.closing.get(&file) {
            return closing.contains(&statement);
        }

        match self.closing_loops_of(file) {
            Some(closing) => {
                let closes = closing.contains(&statement);

                self.values.targets.closing.insert(file, Rc::new(closing));

                closes
            }
            None => true,
        }
    }

    fn closing_loops_of(&mut self, file: FileId) -> Option<HashSet<NodeId>> {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let scoping = project.file(file).semantic.scoping();
        let mut closing = HashSet::new();
        let mut escaped = HashSet::new();

        for node in nodes.iter() {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                return None;
            }

            self.stats.count("iterator exits: node");

            let (target, inclusive) = match node.kind() {
                AstKind::BreakStatement(statement) => match &statement.label {
                    Some(label) => (labeled_target_of(nodes, node.id(), &label.name), true),
                    None => (
                        nodes.ancestor_ids(node.id()).find(|ancestor| {
                            let kind = nodes.kind(*ancestor);

                            is_iteration_kind(&kind) || matches!(kind, AstKind::SwitchStatement(_))
                        }),
                        true,
                    ),
                },
                AstKind::ContinueStatement(statement) => match &statement.label {
                    Some(label) => (labeled_target_of(nodes, node.id(), &label.name), false),
                    None => continue,
                },
                kind if completes_normally(scoping, &kind) => continue,
                _ => (None, false),
            };
            let span = node.kind().span();

            for ancestor in nodes.ancestor_ids(node.id()) {
                self.stats.count("iterator exits: step");

                let kind = nodes.kind(ancestor);

                if Some(ancestor) == target {
                    if inclusive && matches!(kind, AstKind::ForOfStatement(_)) {
                        closing.insert(ancestor);
                    }

                    break;
                }

                if matches!(
                    kind,
                    AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_)
                ) {
                    break;
                }

                let AstKind::ForOfStatement(statement) = kind else {
                    continue;
                };

                if target.is_none() && escaped.contains(&ancestor) {
                    break;
                }

                if statement.body.span().contains_inclusive(span) {
                    closing.insert(ancestor);

                    if target.is_none() {
                        escaped.insert(ancestor);
                    }
                }
            }
        }

        Some(closing)
    }

    fn may_implement(&self, key: &MemberKey) -> bool {
        let targets = &self.values.targets;

        [
            &targets.accessor_keys,
            &targets.callable_keys,
            &targets.written_keys,
        ]
        .into_iter()
        .any(|keys| self.is_defined_key(keys, key))
    }

    fn accessor_targets_within(
        &mut self,
        file: FileId,
        access: AstKind<'a>,
        setter: bool,
    ) -> TargetSet {
        let (object, key) = match access {
            AstKind::StaticMemberExpression(member) => (
                &member.object,
                Some(MemberKey::Name(member.property.name.to_string())),
            ),
            AstKind::PrivateFieldExpression(member) => (
                &member.object,
                Some(MemberKey::Name(format!("#{}", member.field.name))),
            ),
            AstKind::ComputedMemberExpression(member) => {
                let key = match self.member_key_of_expression(file, &member.expression) {
                    Some(key) => Some(key),
                    None if self.is_numeric_key(file, &member.expression, 0) => {
                        Some(MemberKey::Index)
                    }
                    None => None,
                };

                (&member.object, key)
            }
            _ => return closed_targets_of(),
        };

        self.accessors_on(file, object, key, setter)
    }

    pub(crate) fn property_accessors_of(
        &mut self,
        (file, object): Valued<'a>,
        key: MemberKey,
        setter: bool,
    ) -> TargetSet {
        self.index_targets();

        if !self.is_defined_key(&self.values.targets.accessor_keys, &key) {
            return closed_targets_of();
        }

        let implicit = ImplicitKey::Member(key.clone(), setter);

        self.implicit_targets_of((file, object.node_id()), implicit, |analysis| {
            analysis.accessors_on(file, object, Some(key), setter)
        })
    }

    pub(crate) fn property_values_of(
        &mut self,
        (file, object): Valued<'a>,
        key: &MemberKey,
    ) -> (Vec<Valued<'a>>, bool) {
        self.index_targets();

        let receiver = self.implicit_receiver_of(file, object);
        let values = self.member_candidates_of(file, object, &receiver, key);

        (
            values.values,
            values.replaced || receiver.origins.is_empty() || receiver.constrained,
        )
    }

    pub(crate) fn proven_kind(&mut self, file: FileId, expression: &'a Expression<'a>) -> Kind {
        self.index_targets();

        self.proven_kind_of(file, expression, 0)
    }

    fn accessors_on(
        &mut self,
        file: FileId,
        object: &'a Expression<'a>,
        key: Option<MemberKey>,
        setter: bool,
    ) -> TargetSet {
        let kind = self.proven_kind_of(file, object, 0);
        let Some(key) = key else {
            return TargetSet {
                known: Vec::new(),
                open: match is_builtin(kind) {
                    true => self.builtin_accessors_defined(kind, None),
                    false => true,
                },
            };
        };

        if !self.is_defined_key(&self.values.targets.accessor_keys, &key) {
            return closed_targets_of();
        }

        let own = match &key {
            MemberKey::Index => true,
            MemberKey::Name(name) => name == "length" || is_index_name(name),
            _ => false,
        };

        if own && matches!(kind, Kind::Array | Kind::String) {
            return closed_targets_of();
        }

        let receiver = self.implicit_receiver_of(file, object);
        let values = self.member_candidates_of(file, object, &receiver, &key);
        let unresolved = receiver.origins.is_empty() || receiver.constrained;

        TargetSet {
            known: match setter {
                true => values.setters,
                false => values.getters,
            },
            open: values.accessors_open || (unresolved && !is_builtin(kind)),
        }
    }

    fn protocol_targets_within(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        keys: &[MemberKey],
    ) -> TargetSet {
        let receiver = self.implicit_receiver_of(file, expression);
        let coercing = keys
            .iter()
            .any(|key| matches!(key, MemberKey::WellKnown(name) if name == "toPrimitive"));
        let awaiting = keys
            .iter()
            .any(|key| matches!(key, MemberKey::Name(name) if name == "then"));
        let kind = match coercing {
            true => self.proven_kind_of(file, expression, 0),
            false => self.declared_kind_of(file, expression),
        };
        let intrinsic =
            is_builtin(kind) || (awaiting && self.is_intrinsic_promise(file, expression));
        let unresolved = (receiver.origins.is_empty() || receiver.constrained) && !intrinsic;
        let mut found = closed_targets_of();

        for key in keys {
            if !self.may_implement(key) {
                continue;
            }

            let values = self.member_candidates_of(file, expression, &receiver, key);

            self.absorb_callables(values, &mut found);

            found.open |= unresolved
                && (self.is_defined_key(&self.values.targets.callable_keys, key)
                    || self.is_defined_key(&self.values.targets.accessor_keys, key));
        }

        found
    }

    fn absorb_callables(&mut self, values: MemberValues<'a>, found: &mut TargetSet) {
        let mut visited = HashSet::new();

        found.open |= values.replaced;

        for function in values.functions {
            push_target(found, function);
        }

        for (target, value) in values.values {
            self.collect_callable_targets(target, value, &mut visited, found);
        }
    }

    fn returned_protocol_targets_of(
        &mut self,
        function: FunctionId,
        (file, iterable): Valued<'a>,
        key: &MemberKey,
    ) -> TargetSet {
        let (generator, asynchronous) = match self.kind_of_node(function.file, function.node) {
            AstKind::Function(inner) => (inner.generator, inner.r#async),
            AstKind::ArrowFunctionExpression(arrow) => (false, arrow.r#async),
            _ => (false, false),
        };

        if generator {
            return self.wide_protocol_of(key, Kind::Other);
        }

        if asynchronous {
            return closed_targets_of();
        }

        let mut found = closed_targets_of();

        for returned in self.returned_expressions_of(function) {
            if self.is_generator_call(function.file, returned)
                || self.is_intrinsic_iterator(function.file, returned)
            {
                let wide = self.wide_protocol_of(key, Kind::Other);

                found.open |= wide.open;

                for known in wide.known {
                    push_target(&mut found, known);
                }

                continue;
            }

            let (source, expression) = match unwrap(returned) {
                Expression::ThisExpression(_) => (file, iterable),
                _ => (function.file, returned),
            };
            let targets = self.iterator_methods_of(source, expression, std::slice::from_ref(key));

            found.open |= targets.open;

            for known in targets.known {
                push_target(&mut found, known);
            }
        }

        found
    }

    pub(crate) fn intrinsic_member_targets_of(
        &mut self,
        kind: Kind,
        name: &str,
    ) -> (TargetSet, TargetSet) {
        let key = protocol_key_of(name);

        self.index_targets();

        let mut methods = closed_targets_of();

        if self.may_implement(&key) {
            let keyed = self.wide_summary_of(Some(key.clone()), kind, false, true);
            let any = self.wide_summary_of(None, kind, false, true);

            methods.known = keyed.known;
            methods.open = keyed.callables_open || any.replaced || any.callables_open;
        }

        let accessors = if self.may_access(Some(&key)) {
            let keyed = self.wide_summary_of(Some(key), kind, false, true);
            let any = self.wide_summary_of(None, kind, false, true);

            TargetSet {
                known: keyed.getters,
                open: keyed.accessors_open || any.accessors_open,
            }
        } else {
            closed_targets_of()
        };

        (methods, accessors)
    }

    fn indexed_accessor_keys(&mut self) -> Vec<MemberKey> {
        self.index_targets();

        if !self.charge_targets(self.values.targets.accessor_keys.len() as u64) {
            return vec![MemberKey::Index];
        }

        let mut keys: Vec<_> = self
            .values
            .targets
            .accessor_keys
            .iter()
            .filter_map(|key| match key {
                Some(MemberKey::Index) => Some(MemberKey::Index),
                Some(MemberKey::Name(name)) if is_index_name(name) => {
                    Some(MemberKey::Name(name.clone()))
                }
                None => Some(MemberKey::Index),
                _ => None,
            })
            .collect();

        keys.sort_by(|left, right| match (left, right) {
            (MemberKey::Name(left), MemberKey::Name(right)) => left.cmp(right),
            (MemberKey::Index, MemberKey::Name(_)) => std::cmp::Ordering::Less,
            (MemberKey::Name(_), MemberKey::Index) => std::cmp::Ordering::Greater,
            _ => std::cmp::Ordering::Equal,
        });
        keys.dedup();

        keys
    }

    pub(crate) fn has_indexed_accessors(&mut self) -> bool {
        !self.indexed_accessor_keys().is_empty() || self.work_exhausted()
    }

    pub(crate) fn indexed_accessors_of(&mut self) -> TargetSet {
        let keys = self.indexed_accessor_keys();
        let mut found = closed_targets_of();

        for key in keys {
            let keyed = self.wide_summary_of(Some(key), Kind::Other, false, true);
            let any = self.wide_summary_of(None, Kind::Other, false, true);

            if !self.merge_iterator_targets(
                &mut found,
                TargetSet {
                    known: keyed.getters,
                    open: keyed.accessors_open || any.accessors_open,
                },
            ) {
                break;
            }
        }

        found.open |= self.work_exhausted();

        found
    }

    pub(crate) fn indexed_accessors_on(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> TargetSet {
        let keys = self.indexed_accessor_keys();
        let mut found = closed_targets_of();

        for key in keys {
            let targets = self.property_accessors_of((file, expression), key, false);

            if !self.merge_iterator_targets(&mut found, targets) {
                break;
            }
        }

        found.open |= self.work_exhausted();

        found
    }

    pub(crate) fn intrinsic_iterator_accessors_of(&mut self, name: &str) -> TargetSet {
        let key = MemberKey::Name(name.to_string());

        self.index_targets();

        if !self.may_access(Some(&key)) {
            return closed_targets_of();
        }

        let keyed = self.wide_summary_of(Some(key), Kind::Other, false, true);
        let any = self.wide_summary_of(None, Kind::Other, false, true);

        TargetSet {
            known: keyed.getters,
            open: keyed.accessors_open || any.accessors_open,
        }
    }

    pub(crate) fn intrinsic_protocol_of(&mut self, site: Site, name: &str) -> TargetSet {
        let key = MemberKey::Name(name.to_string());

        if !self.may_implement(&key) {
            return closed_targets_of();
        }

        self.implicit_targets_of(site, ImplicitKey::Returned(key.clone()), |analysis| {
            analysis.wide_protocol_of(&key, Kind::Other)
        })
    }

    fn wide_protocol_of(&mut self, key: &MemberKey, kind: Kind) -> TargetSet {
        let keyed = self.wide_summary_of(Some(key.clone()), kind, false, true);
        let any = self.wide_summary_of(None, kind, false, true);

        TargetSet {
            known: keyed.known,
            open: keyed.replaced || any.replaced,
        }
    }

    fn is_generator_call(&mut self, file: FileId, expression: &'a Expression<'a>) -> bool {
        let Some(call) = call_of(unwrap(expression)) else {
            return false;
        };
        let targets = self.resolved_callee_of(file, call).targets;

        !targets.open
            && !targets.known.is_empty()
            && targets.known.iter().all(|target| {
                matches!(self.kind_of_node(target.file, target.node), AstKind::Function(function) if function.generator)
            })
    }

    pub(crate) fn is_intrinsic_promise(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> bool {
        self.is_intrinsic_promise_at(file, expression, 0)
    }

    fn is_intrinsic_promise_at(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> bool {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return false;
        }

        if self.is_declared_promise(file, expression) {
            return true;
        }

        match unwrap(expression) {
            Expression::NewExpression(new) => self.is_global_promise(file, &new.callee),
            Expression::CallExpression(call) => match member_expression_of(unwrap(&call.callee)) {
                Some(member) if self.is_global_promise(file, member.object()) => true,
                Some(member)
                    if member
                        .static_property_name()
                        .is_some_and(|name| ["then", "catch", "finally"].contains(&name))
                        && self.is_intrinsic_promise_at(file, member.object(), depth + 1) =>
                {
                    true
                }
                _ => self.is_asynchronous_call(file, call),
            },
            Expression::Identifier(reference) => match self.local_values_of(file, reference) {
                Some(values) if !values.is_empty() => values
                    .into_iter()
                    .all(|(source, value)| self.is_intrinsic_promise_at(source, value, depth + 1)),
                _ => false,
            },
            _ => false,
        }
    }

    fn is_global_promise(&mut self, file: FileId, expression: &'a Expression<'a>) -> bool {
        let Expression::Identifier(reference) = unwrap(expression) else {
            return false;
        };

        reference.name == "Promise"
            && is_unbound(self.project.file(file).semantic.scoping(), reference)
            && !self.values.targets.replaced_every_global
            && !self.values.targets.replaced_globals.contains("Promise")
    }

    fn is_asynchronous_call(&mut self, file: FileId, call: &'a CallExpression<'a>) -> bool {
        let targets = self.resolved_callee_of(file, call).targets;

        !targets.open
            && !targets.known.is_empty()
            && targets.known.iter().all(|target| {
                match self.kind_of_node(target.file, target.node) {
                    AstKind::Function(function) => function.r#async && !function.generator,
                    AstKind::ArrowFunctionExpression(arrow) => arrow.r#async,
                    _ => false,
                }
            })
    }

    pub(crate) fn iteration_kind_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Kind {
        let site = (file, expression.node_id());

        if let Some(kind) = self.values.iteration_static.get(&site).copied() {
            return match self.charge_work(crate::analysis::work::Event::TraversalEdge, 1) {
                true => kind,
                false => Kind::Unknown,
            };
        }

        if depth > MAXIMUM_ALIAS_DEPTH || !self.charge_dispatch() {
            return Kind::Unknown;
        }

        let declared = match unwrap(expression) {
            Expression::ComputedMemberExpression(member)
                if self.is_numeric_key(file, &member.expression, 0) =>
            {
                self.declared_element_kind_of(file, &member.object)
            }
            _ => self.declared_kind_of(file, expression),
        };

        if is_builtin(declared) {
            self.values.iteration_static.insert(site, declared);

            return declared;
        }

        if matches!(unwrap(expression), Expression::ObjectExpression(_)) {
            self.values.iteration_static.insert(site, Kind::Other);

            return Kind::Other;
        }

        if matches!(unwrap(expression), Expression::ArrayExpression(_)) {
            self.values.iteration_static.insert(site, Kind::Array);

            return Kind::Array;
        }

        match unwrap(expression) {
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference);

                if let Some((source, value)) =
                    declaration.and_then(crate::constants::constant_initializer_of)
                {
                    let kind = self.iteration_kind_of(source, value, depth + 1);

                    if self
                        .values
                        .iteration_static
                        .contains_key(&(source, value.node_id()))
                        && !self.work_exhausted()
                    {
                        self.values.iteration_static.insert(site, kind);
                    }

                    return kind;
                }

                let values = match declaration {
                    Some(
                        declaration @ Declaration::Parameter {
                            file: target,
                            function,
                            parameter: crate::declarations::ParameterNode::Formal(parameter),
                            ..
                        },
                    ) => {
                        let Some(binding) = self.parameter_binding_of(declaration) else {
                            return Kind::Unknown;
                        };

                        if !self.is_parameter_unwritten(binding) {
                            return Kind::Unknown;
                        }

                        if let Some(kind) = self
                            .current_substitutions
                            .get(&binding)
                            .and_then(|facts| self.values.iteration_kinds.get(&facts.value.value))
                            .copied()
                        {
                            return kind;
                        }

                        let Some(arguments) = self.call_arguments_of(target, function, parameter)
                        else {
                            return Kind::Unknown;
                        };

                        if !self.charge_targets(arguments.len() as u64) {
                            return Kind::Unknown;
                        }

                        let Some(values) = arguments.into_iter().collect::<Option<Vec<_>>>() else {
                            return Kind::Unknown;
                        };

                        values
                    }
                    _ => self.local_values_of(file, reference).unwrap_or_default(),
                };

                if !self.charge_targets(values.len() as u64) {
                    return Kind::Unknown;
                }

                let mut known = None;

                for (source, value) in values {
                    let kind = self.iteration_kind_of(source, value, depth + 1);

                    if !is_builtin(kind) || known.is_some_and(|previous| previous != kind) {
                        return Kind::Unknown;
                    }

                    known = Some(kind);
                }

                known.unwrap_or(Kind::Unknown)
            }
            Expression::CallExpression(call) => {
                let Some(member) = member_expression_of(unwrap(&call.callee)) else {
                    return self.returned_iteration_kind_of(file, call, depth + 1);
                };
                let Some(MemberKey::Name(name)) = self.member_key_of(file, member) else {
                    return Kind::Unknown;
                };
                let kind = self.iteration_kind_of(file, member.object(), depth + 1);
                let returned = match (kind, name.as_str()) {
                    (
                        Kind::Array,
                        "slice" | "subarray" | "map" | "filter" | "flat" | "flatMap" | "concat"
                        | "toSorted" | "toReversed" | "toSpliced" | "with",
                    ) => Kind::Array,
                    (
                        Kind::String,
                        "slice" | "substring" | "substr" | "repeat" | "padStart" | "padEnd"
                        | "concat" | "replace" | "replaceAll" | "trim" | "trimStart" | "trimEnd"
                        | "toLowerCase" | "toUpperCase",
                    ) => Kind::String,
                    (Kind::String, "split") => Kind::Array,
                    _ => Kind::Unknown,
                };

                if !is_builtin(returned) {
                    return Kind::Unknown;
                }

                let dispatch = self.member_dispatch_of(file, member);

                match dispatch.known.is_empty()
                    && !dispatch.replaced
                    && !self.intrinsic_replaced_of(file, &call.callee)
                {
                    true => returned,
                    false => Kind::Unknown,
                }
            }
            _ => self.proven_kind_of(file, expression, depth + 1),
        }
    }

    fn returned_iteration_kind_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        depth: usize,
    ) -> Kind {
        let targets = self.resolved_callee_of(file, call).targets;

        if targets.open
            || targets.known.is_empty()
            || !self.charge_targets(targets.known.len() as u64)
        {
            return Kind::Unknown;
        }

        let mut known = None;

        for target in targets.known {
            if self.is_deferred_function(target) {
                return Kind::Unknown;
            }

            let returned = self.returned_expressions_of(target);

            if returned.is_empty() || !self.charge_targets(returned.len() as u64) {
                return Kind::Unknown;
            }

            for expression in returned {
                let kind = self.iteration_kind_of(target.file, expression, depth + 1);

                if !is_builtin(kind)
                    || self
                        .values
                        .iteration_static
                        .get(&(target.file, expression.node_id()))
                        != Some(&kind)
                    || known.is_some_and(|previous| previous != kind)
                {
                    return Kind::Unknown;
                }

                known = Some(kind);
            }
        }

        known.unwrap_or(Kind::Unknown)
    }

    fn is_intrinsic_iterator(&mut self, file: FileId, expression: &'a Expression<'a>) -> bool {
        let Some(call) = call_of(unwrap(expression)) else {
            return false;
        };
        let Some(member) = member_expression_of(unwrap(&call.callee)) else {
            return false;
        };
        let iterating = match self.member_key_of(file, member) {
            Some(MemberKey::Name(name)) => {
                matches!(name.as_str(), "values" | "keys" | "entries" | "matchAll")
            }
            Some(MemberKey::WellKnown(name)) => name == "iterator",
            _ => false,
        };

        if !iterating || !is_builtin(self.declared_kind_of(file, member.object())) {
            return false;
        }

        let dispatch = self.member_dispatch_of(file, member);

        dispatch.known.is_empty() && !dispatch.replaced
    }

    pub(crate) fn intrinsic_iteration_source_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Option<&'a Expression<'a>> {
        if !self.is_intrinsic_iterator(file, expression) {
            return None;
        }

        member_expression_of(unwrap(&call_of(unwrap(expression))?.callee))
            .map(|member| member.object())
    }

    fn construction_dispatch_within(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
        (class, placement): (&'a Class<'a>, Placement),
    ) -> TargetSet {
        let Some(key) = self.member_key_of(file, member) else {
            return TargetSet {
                known: Vec::new(),
                open: true,
            };
        };
        let object = unwrap(member.object());
        let mut receiver = Receiver::default();
        let class_value = self.values.allocation(self.source_span(file, class.span));
        let mut extensible = false;

        match (object, placement) {
            (Expression::Super(_), placement) => {
                receiver.origins.push(Origin::HomeClass {
                    file,
                    class,
                    placement,
                });

                if placement == Placement::Static {
                    push_value(&mut receiver.values, class_value.value);

                    extensible = self.is_class_surfaced(file, class);
                }
            }
            (_, Placement::Static) => {
                receiver.origins.push(Origin::Constructor {
                    file,
                    class,
                    exact: true,
                });
                push_value(&mut receiver.values, class_value.value);

                extensible = self.is_class_surfaced(file, class);
            }
            _ => {
                receiver.origins.push(Origin::Instance {
                    file,
                    class,
                    exact: false,
                });

                let value = self.storage_value_of(file, object);

                push_value(&mut receiver.values, value);

                extensible = self.is_class_extensible(file, class);
            }
        }

        let values = self.member_candidates_of(file, object, &receiver, &key);
        let mut found = closed_targets_of();

        self.absorb_callables(values, &mut found);

        found.open |= extensible;

        found
    }

    fn is_class_extensible(&mut self, file: FileId, class: &'a Class<'a>) -> bool {
        let site = (file, class.node_id());

        if let Some(extensible) = self.values.targets.extensible.get(&site) {
            return *extensible;
        }

        let extensible = self.class_extensibility_of(file, class);

        self.values.targets.extensible.insert(site, extensible);

        extensible
    }

    fn class_symbol_of(
        &self,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Result<oxc_semantic::SymbolId, bool> {
        let nodes = self.project.file(file).semantic.nodes();
        let symbol = match &class.id {
            Some(identifier) if class.is_declaration() => identifier.symbol_id.get(),
            _ => {
                let outer = crate::values::outermost_of(nodes, class.node_id());

                match nodes.parent_kind(outer) {
                    AstKind::NewExpression(new)
                        if new.callee.span() == nodes.kind(outer).span() =>
                    {
                        return Err(false)
                    }
                    AstKind::VariableDeclarator(declarator)
                        if matches!(nodes.parent_kind(declarator.node_id()), AstKind::VariableDeclaration(declaration) if declaration.kind.is_const())
                            && declarator.init.as_ref().map(GetSpan::span)
                                == Some(nodes.kind(outer).span()) =>
                    {
                        declarator
                            .id
                            .get_binding_identifier()
                            .and_then(|identifier| identifier.symbol_id.get())
                    }
                    _ => return Err(true),
                }
            }
        };

        symbol.ok_or(true)
    }

    fn is_class_surfaced(&self, file: FileId, class: &'a Class<'a>) -> bool {
        match self.class_symbol_of(file, class) {
            Ok(symbol) => {
                let declared = self
                    .project
                    .file(file)
                    .semantic
                    .scoping()
                    .symbol_declaration(symbol);

                self.is_surfaced_symbol(file, symbol, declared)
            }
            Err(fixed) => fixed,
        }
    }

    fn class_extensibility_of(&mut self, file: FileId, class: &'a Class<'a>) -> bool {
        let project = self.project;
        let symbol = match self.class_symbol_of(file, class) {
            Ok(symbol) => symbol,
            Err(fixed) => return fixed,
        };

        if self.is_class_surfaced(file, class) {
            return true;
        }

        let binding = Binding::Symbol { file, symbol };

        for (target, node, write) in self.declarations.surface_references_of(project, binding) {
            if !self.charge_dispatch() || write {
                return true;
            }

            let nodes = project.file(target).semantic.nodes();

            match value_flow_of(nodes, node) {
                ValueFlow::Read | ValueFlow::Member | ValueFlow::Receiver(_) => {}
                ValueFlow::Escaped(parent) if matches!(nodes.kind(parent), AstKind::Class(derived) if derived.heritage.as_ref().is_some_and(|heritage| heritage.expression.span() == nodes.kind(node).span())) =>
                    {}
                _ => return true,
            }
        }

        false
    }

    pub(crate) fn static_member_name_of(
        &mut self,
        file: FileId,
        member: &'a MemberExpression<'a>,
    ) -> Option<String> {
        match self.member_key_of(file, member)? {
            MemberKey::Name(name) => Some(name),
            _ => None,
        }
    }

    pub(crate) fn construction_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Construction<'a> {
        self.index_targets();

        let (classes, open) = self.class_candidates_of(file, expression, 0);
        let mut targets = match (classes.is_empty(), open) {
            (false, false) => TargetSet {
                known: Vec::new(),
                open: false,
            },
            (empty, _) => {
                let mut targets = self.callable_targets_of(file, expression);

                targets.open |= !empty;

                targets
            }
        };
        let implicit = self.split_class_constructors(classes, &mut targets);

        targets.open |= targets.known.is_empty() && implicit.is_empty();

        Construction { targets, implicit }
    }

    pub(crate) fn member_construction_of(
        &mut self,
        file: FileId,
        (callee, member): (&'a Expression<'a>, &'a MemberExpression<'a>),
        mut found: TargetSet,
    ) -> Construction<'a> {
        let dispatch = self.member_dispatch_of(file, member);
        let mut constructed = TargetSet {
            known: dispatch.known,
            open: dispatch.replaced,
        };

        self.index_targets();

        let (classes, _) = self.class_candidates_of(file, callee, 0);
        let implicit = self.split_class_constructors(classes, &mut constructed);

        for known in constructed.known {
            if !found.known.contains(&known) {
                found.known.push(known);

                found.open = true;
            }
        }

        found.open |= constructed.open || (found.known.is_empty() && implicit.is_empty());

        Construction {
            targets: found,
            implicit,
        }
    }

    pub(crate) fn base_construction_of(
        &mut self,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Construction<'a> {
        match &class.heritage {
            Some(heritage) => self.construction_of(file, &heritage.expression),
            None => Construction {
                targets: TargetSet {
                    known: Vec::new(),
                    open: false,
                },
                implicit: Vec::new(),
            },
        }
    }

    pub(crate) fn base_plan_of(
        &mut self,
        file: FileId,
        class: &'a Class<'a>,
    ) -> Rc<ConstructionPlan> {
        let site = (file, class.node_id());

        if let Some(plan) = self.values.targets.plans.get(&site) {
            return Rc::clone(plan);
        }

        let exhaustions = self.values.targets.exhaustions;
        let mut plan = ConstructionPlan::default();
        let mut visited = HashSet::from([site]);
        let mut pending = vec![(file, class)];

        while let Some((file, class)) = pending.pop() {
            let construction = self.base_construction_of(file, class);

            plan.open |= construction.targets.open;

            for known in construction.targets.known {
                if !self.charge_dispatch() {
                    plan.open = true;

                    break;
                }

                if !plan.constructors.contains(&known) {
                    plan.constructors.push(known);
                }
            }

            for (base_file, base) in construction.implicit {
                if !self.charge_dispatch() {
                    plan.open = true;

                    break;
                }

                let base_site = (base_file, base.node_id());

                if visited.insert(base_site) {
                    plan.initializers.push(base_site);
                    plan.owners.extend(self.owners_of(base_file, base_site.1));
                    pending.push((base_file, base));
                }
            }
        }

        let plan = Rc::new(plan);

        if exhaustions == self.values.targets.exhaustions {
            self.values.targets.plans.insert(site, Rc::clone(&plan));
        }

        plan
    }

    fn split_class_constructors(
        &mut self,
        classes: Vec<ClassSite<'a>>,
        found: &mut TargetSet,
    ) -> Vec<ClassSite<'a>> {
        let mut implicit: Vec<ClassSite<'a>> = Vec::new();

        for (target, class) in classes {
            match self.declarations.function_of(Declaration::Class {
                file: target,
                class,
            }) {
                Some((target, function)) => push_target(
                    found,
                    FunctionId {
                        file: target,
                        node: function.node_id(),
                    },
                ),
                None if !implicit.iter().any(|(known, candidate)| {
                    *known == target && candidate.node_id() == class.node_id()
                }) =>
                {
                    implicit.push((target, class))
                }
                None => {}
            }
        }

        implicit
    }

    pub(crate) fn forget_dispatches(&mut self) {
        self.values.targets.dispatches.clear();
        self.values.targets.summaries.clear();
        self.values.targets.exhausted_calls.clear();
        self.values.targets.patterns.clear();
        self.values.targets.parameter_classes.clear();
        self.values.targets.plans.clear();
        self.values.targets.implicit.clear();
        self.values.targets.extensible.clear();
        self.values.targets.closing.clear();
        self.values.targets.implicit_plans.clear();
        self.values.targets.builtin_accessors.clear();
        self.values.targets.invocations.clear();
        self.values.targets.primitive_bindings.clear();
        self.forget_constructions();
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
            .map(|name| Some(protocol_key_of(name)))
            .chain(std::iter::once(None));
        let mut replaced = false;

        for key in keys {
            replaced |= self.wide_summary_of(key, kind, false, true).replaced;
        }

        replaced || self.work_exhausted()
    }

    pub(crate) fn builtin_accessors_defined(&mut self, kind: Kind, name: Option<&str>) -> bool {
        self.index_targets();

        let Some(name) = name else {
            return !self.values.targets.accessor_keys.is_empty()
                && self.accessor_writes_reach(kind);
        };
        let key = protocol_key_of(name);

        if !self.is_defined_key(&self.values.targets.accessor_keys, &key) {
            return false;
        }

        if OUTSIDE_SOURCES_REPLACE_BUILTINS || self.work_exhausted() {
            return true;
        }

        [Some(key), None].into_iter().any(|written| {
            let summary = self.wide_summary_of(written, kind, false, true);

            !summary.getters.is_empty() || summary.accessors_open || !summary.prototypes.is_empty()
        })
    }

    pub(crate) fn holds_primitive(&mut self, file: FileId, operand: &'a Expression<'a>) -> bool {
        let binding = match unwrap(operand) {
            Expression::Identifier(reference) => {
                self.declarations
                    .binding_of_reference(self.project, file, reference)
            }
            _ => None,
        };
        let Some(binding) = binding else {
            return self.is_primitive_value(file, operand);
        };

        if let Some(primitive) = self.values.targets.primitive_bindings.get(&binding) {
            return *primitive;
        }

        let primitive = self.is_primitive_value(file, operand);

        self.values
            .targets
            .primitive_bindings
            .insert(binding, primitive);

        primitive
    }

    pub(crate) fn invocation_sites_of(
        &mut self,
        binding: Binding,
    ) -> Option<Vec<(FileId, &'a CallExpression<'a>)>> {
        let sites = match self.values.targets.invocations.get(&binding) {
            Some(sites) => sites.clone(),
            None => {
                if !self.values.targets.resolving_invocations.insert(binding) {
                    return None;
                }

                let exhaustions = self.values.targets.exhaustions;
                let sites = self.invocation_sites_within(binding);

                self.values.targets.resolving_invocations.remove(&binding);

                if exhaustions == self.values.targets.exhaustions {
                    self.values
                        .targets
                        .invocations
                        .insert(binding, sites.clone());
                }

                sites
            }
        }?;

        Some(
            sites
                .into_iter()
                .filter_map(|(file, node)| match self.kind_of_node(file, node) {
                    AstKind::CallExpression(call) => Some((file, call)),
                    _ => None,
                })
                .collect(),
        )
    }

    fn invocation_sites_within(&mut self, binding: Binding) -> Option<Vec<Site>> {
        let project = self.project;
        let mut sites = Vec::new();
        let mut visited = HashSet::from([binding]);
        let mut pending = vec![binding];

        while let Some(binding) = pending.pop() {
            for (target, node, write) in self.declarations.surface_references_of(project, binding) {
                if write || !self.charge_dispatch() {
                    return None;
                }

                let nodes = project.file(target).semantic.nodes();
                let span = nodes.kind(node).span();
                let AstKind::CallExpression(call) = nodes.parent_kind(node) else {
                    return None;
                };

                if call.callee.span() == span {
                    sites.push((target, call.node_id()));

                    continue;
                }

                let index = call
                    .arguments
                    .iter()
                    .position(|argument| argument.span() == span)?;
                let Expression::Identifier(callee) = unwrap(&call.callee) else {
                    return None;
                };
                let (declaration, closed) = self
                    .declarations
                    .callable_reference(project, target, callee);
                let (declared, function) = declaration
                    .filter(|_| closed)
                    .and_then(|declaration| self.declarations.function_of(declaration))?;
                let parameters = parameters_of(function)?;

                if call.arguments[..index]
                    .iter()
                    .any(|argument| matches!(argument, Argument::SpreadElement(_)))
                {
                    return None;
                }

                let Some(parameter) = parameters.items.get(index) else {
                    if parameters.rest.is_some() {
                        return None;
                    }

                    continue;
                };
                let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                    return None;
                };
                let forwarded = Binding::Symbol {
                    file: declared,
                    symbol: identifier.symbol_id.get()?,
                };

                if !self.is_parameter_unwritten(forwarded) {
                    return None;
                }

                if visited.insert(forwarded) {
                    pending.push(forwarded);
                }
            }
        }

        Some(sites)
    }

    fn accessor_writes_reach(&mut self, kind: Kind) -> bool {
        if let Some(reached) = self.values.targets.builtin_accessors.get(&kind) {
            return *reached;
        }

        let mut reached = OUTSIDE_SOURCES_REPLACE_BUILTINS;

        for index in 0..self.values.targets.writes.len() {
            if reached {
                break;
            }

            let write = &self.values.targets.writes[index];

            if write.kind != WriteKind::Defined
                || matches!(self.descriptor_of(write.site), Descriptor::Absent)
            {
                continue;
            }

            if !self.charge_dispatch() {
                reached = true;

                break;
            }

            reached = match self.values.targets.owners[index].0 {
                Owner::Builtin { kind: written } => affects(written, kind),
                Owner::FunctionPrototype { .. } => !is_builtin(kind),
                Owner::Value {
                    allocation: false,
                    kind: written,
                    plain,
                    ..
                }
                | Owner::Value {
                    shared: true,
                    kind: written,
                    plain,
                    ..
                } => is_compatible(written, kind) && !(plain && is_builtin(kind)),
                _ => false,
            };
        }

        if !reached {
            for ((file, node), builtin) in self.builtin_classes_of() {
                if !affects(builtin, kind) {
                    continue;
                }

                let AstKind::Class(class) = self.kind_of_node(file, node) else {
                    continue;
                };

                reached |= class.body.body.iter().any(|element| {
                    matches!(element, ClassElement::MethodDefinition(method) if matches!(method.kind, MethodDefinitionKind::Get | MethodDefinitionKind::Set))
                });
            }
        }

        if !self.work_exhausted() {
            self.values.targets.builtin_accessors.insert(kind, reached);
        }

        reached
    }

    pub(crate) fn target_exhaustions(&self) -> u64 {
        self.values.targets.exhaustions
    }

    pub(crate) fn constant_source_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
    ) -> Option<Valued<'a>> {
        let Expression::Identifier(reference) = unwrap(value) else {
            return None;
        };

        self.declarations
            .of_reference(self.project, file, reference)
            .and_then(constant_initializer_of)
    }

    pub(crate) fn charge_targets(&mut self, amount: u64) -> bool {
        let charged = self.charge_work(Event::DispatchStep, amount);

        self.values.targets.exhaustions += u64::from(!charged);

        charged
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
        let mut definitions: Vec<(Site, bool)> = Vec::new();

        for source in &project.files {
            let file = source.id;
            let nodes = source.semantic.nodes();
            let scoping = source.semantic.scoping();

            for node in nodes.iter() {
                let site = (file, node.id());

                match node.kind() {
                    AstKind::ObjectProperty(property) => match property.kind {
                        PropertyKind::Get | PropertyKind::Set => definitions.push((site, true)),
                        PropertyKind::Init => definitions.push((site, false)),
                    },
                    AstKind::MethodDefinition(method) if method.value.body.is_some() => {
                        match method.kind {
                            MethodDefinitionKind::Get | MethodDefinitionKind::Set => {
                                definitions.push((site, true))
                            }
                            MethodDefinitionKind::Method => definitions.push((site, false)),
                            MethodDefinitionKind::Constructor => {}
                        }
                    }
                    AstKind::PropertyDefinition(property) if property.value.is_some() => {
                        definitions.push((site, false))
                    }
                    AstKind::AccessorProperty(property) if property.value.is_some() => {
                        definitions.push((site, false))
                    }
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
                    self.expression_key(file, expression)
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
            let callable = match (write.kind, self.descriptor_of(write.site)) {
                (WriteKind::Assigned, _) => {
                    value.is_none_or(|value| self.may_be_callable(file, value))
                }
                (WriteKind::Removed, _) => false,
                (
                    WriteKind::Defined,
                    Descriptor::Known {
                        value: described,
                        getter,
                        ..
                    },
                ) => [described, getter]
                    .into_iter()
                    .flatten()
                    .any(|value| self.may_be_callable(file, value)),
                (WriteKind::Defined | WriteKind::Prototype, _) => true,
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

        let mut removals: HashMap<Option<MemberKey>, Vec<usize>> = HashMap::new();

        for (index, write) in writes.iter().enumerate() {
            if write.kind == WriteKind::Removed {
                removals.entry(write.key.clone()).or_default().push(index);
            }
        }

        let mut accessor_keys = HashSet::new();
        let mut callable_keys = HashSet::new();

        for ((file, node), accessor) in definitions {
            let (key, value) = match self.kind_of_node(file, node) {
                AstKind::ObjectProperty(property) => (
                    self.property_key_of(file, property),
                    (property.kind == PropertyKind::Init).then_some(&property.value),
                ),
                AstKind::MethodDefinition(method) => (
                    self.defined_key_of(file, &method.key, method.computed),
                    None,
                ),
                AstKind::PropertyDefinition(property) => (
                    self.defined_key_of(file, &property.key, property.computed),
                    property.value.as_ref(),
                ),
                AstKind::AccessorProperty(property) => (
                    self.defined_key_of(file, &property.key, property.computed),
                    property.value.as_ref(),
                ),
                _ => continue,
            };

            if value.is_some_and(|value| !self.may_be_callable(file, value)) {
                continue;
            }

            match accessor {
                true => accessor_keys.insert(key),
                false => callable_keys.insert(key),
            };
        }

        let mut written_keys = HashSet::new();

        for (index, write) in writes.iter().enumerate() {
            if write.kind == WriteKind::Defined
                && !matches!(self.descriptor_of(write.site), Descriptor::Absent)
            {
                accessor_keys.insert(write.key.clone());
            }

            if write.kind != WriteKind::Removed && owners[index].1 {
                written_keys.insert(write.key.clone());
            }
        }

        self.values.targets.accessor_keys = accessor_keys;
        self.values.targets.callable_keys = callable_keys;
        self.values.targets.written_keys = written_keys;
        self.values.targets.removals = removals;
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
        if let Expression::SequenceExpression(sequence) = unwrap(expression) {
            return self.member_key_of_expression(file, sequence.expressions.last()?);
        }

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

        if let Expression::StaticMemberExpression(member) = unwrap(expression) {
            let scoping = self.project.file(file).semantic.scoping();

            if matches!(unwrap(&member.object), Expression::Identifier(symbol) if symbol.name == "Symbol" && is_unbound(scoping, symbol))
            {
                return Some(MemberKey::WellKnown(member.property.name.to_string()));
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

    fn defined_key_of(
        &mut self,
        file: FileId,
        key: &'a PropertyKey<'a>,
        computed: bool,
    ) -> Option<MemberKey> {
        match key {
            PropertyKey::PrivateIdentifier(identifier) => {
                Some(MemberKey::Name(format!("#{}", identifier.name)))
            }
            _ if computed => key
                .as_expression()
                .and_then(|expression| self.member_key_of_expression(file, expression)),
            _ => key
                .static_name()
                .map(|name| MemberKey::Name(name.into_owned())),
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
                    (BindingPattern::BindingIdentifier(_), Some(init)) => {
                        self.collect_callable_targets(target, init, visited, found)
                    }
                    (pattern, Some(init)) => self.collect_pattern_targets(
                        (file, reference),
                        (target, pattern),
                        PatternSources::Initializer(init),
                        found,
                    ),
                    _ => found.open = true,
                }

                found.open |= !constant || !closed;
            }
            Declaration::Parameter {
                file: target,
                parameter: ParameterNode::Formal(parameter),
                function,
            } if !matches!(parameter.pattern, BindingPattern::BindingIdentifier(_)) => self
                .collect_pattern_targets(
                    (file, reference),
                    (target, &parameter.pattern),
                    PatternSources::Parameter(function, parameter),
                    found,
                ),
            Declaration::Parameter {
                file: target,
                parameter: ParameterNode::Formal(parameter),
                function,
            } => self.collect_parameter_targets(
                (file, reference),
                (target, function, parameter),
                found,
            ),
            _ => found.open = true,
        }

        let (written, unresolved) = self.written_values_of(file, reference);

        found.open |= unresolved;

        for (target, value) in written {
            self.collect_callable_targets(target, value, visited, found);
        }
    }

    fn collect_pattern_targets(
        &mut self,
        (file, reference): (FileId, &'a IdentifierReference<'a>),
        (target, pattern): (FileId, &'a BindingPattern<'a>),
        sources: PatternSources<'a>,
        found: &mut TargetSet,
    ) {
        found.open = true;

        let Some(Binding::Symbol {
            file: declared,
            symbol,
        }) = self
            .declarations
            .binding_of_reference(self.project, file, reference)
        else {
            return;
        };

        if declared != target {
            return;
        }

        self.collect_binding_targets((declared, symbol), found, |analysis| {
            let sources = match sources {
                PatternSources::Initializer(init) => vec![(target, init)],
                PatternSources::Parameter(function, parameter) => {
                    analysis.parameter_sources_of((target, function), parameter)
                }
            };
            let mut resolved = TargetSet {
                known: Vec::new(),
                open: true,
            };

            analysis.resolve_pattern(
                (target, pattern),
                symbol,
                sources,
                &mut HashSet::new(),
                &mut resolved,
            );

            resolved
        });
    }

    fn collect_parameter_targets(
        &mut self,
        (file, reference): (FileId, &'a IdentifierReference<'a>),
        (target, function, parameter): (FileId, FunctionNode<'a>, &'a FormalParameter<'a>),
        found: &mut TargetSet,
    ) {
        let binding = self
            .declarations
            .binding_of_reference(self.project, file, reference)
            .filter(|binding| self.is_parameter_unwritten(*binding));
        let Some(Binding::Symbol {
            file: declared,
            symbol,
        }) = binding
        else {
            found.open = true;

            return;
        };

        self.collect_binding_targets((declared, symbol), found, |analysis| {
            let mut resolved = TargetSet {
                known: Vec::new(),
                open: analysis
                    .call_arguments_of(target, function, parameter)
                    .is_none(),
            };
            let mut visited = HashSet::new();

            for (source, value) in analysis.parameter_sources_of((target, function), parameter) {
                analysis.collect_callable_targets(source, value, &mut visited, &mut resolved);
            }

            resolved
        });
    }

    fn parameter_sources_of(
        &mut self,
        (target, function): (FileId, FunctionNode<'a>),
        parameter: &'a FormalParameter<'a>,
    ) -> Vec<Valued<'a>> {
        parameter
            .initializer
            .iter()
            .map(|initializer| (target, &**initializer))
            .chain(
                self.local_call_arguments_of((target, function), parameter)
                    .unwrap_or_default()
                    .into_iter()
                    .flatten(),
            )
            .collect()
    }

    fn collect_binding_targets(
        &mut self,
        binding: (FileId, oxc_semantic::SymbolId),
        found: &mut TargetSet,
        resolve: impl FnOnce(&mut Self) -> TargetSet,
    ) {
        if let Some(cached) = self.values.targets.patterns.get(&binding) {
            found.open |= cached.open;

            for known in cached.known.clone() {
                push_target(found, known);
            }

            return;
        }

        if !self.values.targets.resolving_patterns.insert(binding) {
            self.values.targets.pattern_cuts += 1;
            found.open = true;

            return;
        }

        let cuts = self.values.targets.pattern_cuts;
        let exhaustions = self.values.targets.exhaustions;
        let resolved = resolve(self);

        self.values.targets.resolving_patterns.remove(&binding);

        if self.values.targets.pattern_cuts == cuts
            && self.values.targets.exhaustions == exhaustions
            && !self.work_exhausted()
        {
            self.values
                .targets
                .patterns
                .insert(binding, resolved.clone());
        }

        found.open |= resolved.open;

        for known in resolved.known {
            push_target(found, known);
        }
    }

    pub(crate) fn pattern_argument_targets_of(
        &mut self,
        file: FileId,
        pattern: &'a BindingPattern<'a>,
        symbol: oxc_semantic::SymbolId,
        sources: Vec<Valued<'a>>,
    ) -> TargetSet {
        let mut resolved = TargetSet {
            known: Vec::new(),
            open: true,
        };

        self.index_targets();
        self.resolve_pattern(
            (file, pattern),
            symbol,
            sources,
            &mut HashSet::new(),
            &mut resolved,
        );

        resolved
    }

    fn resolve_pattern(
        &mut self,
        (target, pattern): (FileId, &'a BindingPattern<'a>),
        symbol: oxc_semantic::SymbolId,
        sources: Vec<Valued<'a>>,
        visited: &mut HashSet<Site>,
        resolved: &mut TargetSet,
    ) {
        let steps = self.pattern_steps_of(target, pattern, symbol);
        let Some((last, steps)) = steps.as_ref().and_then(|steps| steps.split_last()) else {
            return;
        };
        let mut values = sources;
        let mut fresh = true;

        for step in steps {
            let mut next = Vec::new();
            let mut supplied = fresh && !values.is_empty();

            for (source, value) in values {
                let members = self.pattern_members_of(source, value, step, fresh);

                supplied &= self.supplies_step(value, step, &members);

                next.extend(members.values);
            }

            if !supplied {
                next.extend(step.default.map(|default| (target, default)));
            }

            values = next;
            fresh = false;
        }

        let mut supplied = fresh && !values.is_empty();

        for (source, value) in values {
            let members = self.pattern_members_of(source, value, last, fresh);

            supplied &= self.supplies_step(value, last, &members);

            for function in members.functions {
                push_target(resolved, function);
            }

            for (member, value) in members.values {
                self.collect_callable_targets(member, value, visited, resolved);
            }
        }

        if let (false, Some(default)) = (supplied, last.default) {
            self.collect_callable_targets(target, default, visited, resolved);
        }
    }

    fn supplies_step(
        &mut self,
        value: &'a Expression<'a>,
        step: &PatternStep<'a>,
        members: &MemberValues<'a>,
    ) -> bool {
        if members.replaced
            || members.accessors_open
            || !members.below.is_empty()
            || members.lookups == 0
            || members.defined != members.lookups
            || !members.getters.is_empty()
            || members.values.is_empty()
        {
            return false;
        }

        if !is_unaliased_source(unwrap(value), &step.key) {
            return false;
        }

        members
            .values
            .iter()
            .all(|(file, value)| self.definedness_of(*file, value) == Definedness::Defined)
    }

    fn pattern_members_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        step: &PatternStep<'a>,
        fresh: bool,
    ) -> MemberValues<'a> {
        if !self.charge_dispatch() {
            return MemberValues {
                replaced: true,
                ..MemberValues::default()
            };
        }

        let key = match &step.key {
            StepKey::Member(key) => key,
            StepKey::Element(index) => return self.element_values_of(file, value, *index, fresh),
        };
        let mut receiver = Receiver::default();

        self.collect_receiver(file, value, &mut HashSet::new(), &mut receiver);

        self.member_candidates_of(file, value, &receiver, key)
    }

    fn element_values_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        index: usize,
        fresh: bool,
    ) -> MemberValues<'a> {
        let mut found = self.literal_element_values_of(file, value, index, 0);

        if fresh && matches!(unwrap(value), Expression::ArrayExpression(_)) {
            return found;
        }

        let key = MemberKey::Name(index.to_string());
        let mut receiver = Receiver::default();

        self.collect_receiver(file, value, &mut HashSet::new(), &mut receiver);

        let written = self.member_candidates_of(file, value, &receiver, &key);

        found.absorb(&written);

        found
    }

    fn literal_element_values_of(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        index: usize,
        depth: usize,
    ) -> MemberValues<'a> {
        let unknown = MemberValues {
            replaced: true,
            lookups: 1,
            ..MemberValues::default()
        };

        if depth > MAXIMUM_ALIAS_DEPTH || !self.charge_dispatch() {
            return unknown;
        }

        match unwrap(value) {
            Expression::ArrayExpression(array) => {
                let elements = &array.elements;

                if elements
                    .iter()
                    .take(index + 1)
                    .any(|element| matches!(element, ArrayExpressionElement::SpreadElement(_)))
                {
                    return unknown;
                }

                let aliased = depth > 0;
                let Some(element) = elements
                    .get(index)
                    .and_then(|element| element.as_expression())
                else {
                    return MemberValues {
                        replaced: aliased,
                        lookups: 1,
                        ..MemberValues::default()
                    };
                };

                MemberValues {
                    values: vec![(file, element)],
                    replaced: aliased,
                    lookups: 1,
                    defined: 1,
                    ..MemberValues::default()
                }
            }
            _ => match self.constant_source_of(file, value) {
                Some((target, initializer)) => {
                    self.literal_element_values_of(target, initializer, index, depth + 1)
                }
                None => unknown,
            },
        }
    }

    fn pattern_steps_of(
        &mut self,
        file: FileId,
        pattern: &'a BindingPattern<'a>,
        symbol: oxc_semantic::SymbolId,
    ) -> Option<Vec<PatternStep<'a>>> {
        match pattern {
            BindingPattern::AssignmentPattern(assignment) => {
                self.pattern_steps_of(file, &assignment.left, symbol)
            }
            BindingPattern::ObjectPattern(object) => {
                for property in &object.properties {
                    let Some(mut steps) = self.pattern_steps_of(file, &property.value, symbol)
                    else {
                        continue;
                    };
                    let default = match &property.value {
                        BindingPattern::AssignmentPattern(assignment) => Some(&assignment.right),
                        _ => None,
                    };

                    steps.insert(
                        0,
                        PatternStep {
                            key: StepKey::Member(self.binding_property_key_of(file, property)?),
                            default,
                        },
                    );

                    return Some(steps);
                }

                None
            }
            BindingPattern::BindingIdentifier(identifier) => {
                (identifier.symbol_id.get() == Some(symbol)).then(Vec::new)
            }
            BindingPattern::ArrayPattern(array) => {
                for (index, element) in array.elements.iter().enumerate() {
                    let Some(element) = element else {
                        continue;
                    };
                    let Some(mut steps) = self.pattern_steps_of(file, element, symbol) else {
                        continue;
                    };
                    let default = match element {
                        BindingPattern::AssignmentPattern(assignment) => Some(&assignment.right),
                        _ => None,
                    };

                    steps.insert(
                        0,
                        PatternStep {
                            key: StepKey::Element(index),
                            default,
                        },
                    );

                    return Some(steps);
                }

                None
            }
        }
    }

    fn binding_property_key_of(
        &mut self,
        file: FileId,
        property: &'a BindingProperty<'a>,
    ) -> Option<MemberKey> {
        match (property.computed, property.key.as_expression()) {
            (true, Some(expression)) => self.member_key_of_expression(file, expression),
            _ => property
                .key
                .static_name()
                .map(|name| MemberKey::Name(name.into_owned())),
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
            receiver.constrained = true;

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
            Expression::Super(node) => match this_owner_of(project, file, node.node_id()) {
                Some(ThisOwner::Class {
                    file,
                    class,
                    placement,
                }) => {
                    let placements = match placement {
                        Placement::Either => vec![Placement::Instance, Placement::Static],
                        placement => vec![placement],
                    };

                    for placement in placements {
                        receiver.origins.push(Origin::HomeClass {
                            file,
                            class,
                            placement,
                        });
                    }

                    if placement != Placement::Instance {
                        let value = self.values.allocation(self.source_span(file, class.span));

                        push_value(&mut receiver.values, value.value);
                    }
                }
                Some(ThisOwner::Object { file, object }) => {
                    receiver.origins.push(Origin::HomeObject { file, object });

                    let value = self.values.allocation(self.source_span(file, object.span));

                    push_value(&mut receiver.values, value.value);
                }
                None => {}
            },
            Expression::ThisExpression(this) => {
                receiver.constrained |=
                    construction_context_of(project, file, this.node_id()).is_none();

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
            receiver.constrained |= declarator_of_identifier(&declaration)
                .is_none_or(|(_, declarator, _)| declarator.init.is_none());

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
            let inherited = self.prototype_members_of(hit, key);

            found.absorb(&inherited);
        }

        found
    }

    fn prototype_members_of(&mut self, start: usize, key: &MemberKey) -> MemberValues<'a> {
        let unknown = MemberValues {
            replaced: true,
            accessors_open: true,
            ..MemberValues::default()
        };

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

            return unknown;
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

                own.insert(write, unknown.clone());

                continue;
            }

            self.values.targets.exploring.insert((write, key.clone()));

            let site = self.values.targets.writes[write].site;
            let mut members = match self.write_parts_of(site) {
                Some((_, Some(prototype))) => {
                    let mut receiver = Receiver::default();

                    self.collect_receiver(site.0, prototype, &mut HashSet::new(), &mut receiver);

                    let mut members =
                        self.member_candidates_raw_of(site.0, prototype, &receiver, key);

                    members.accessors_open |= is_unknown_prototype(prototype, &receiver);

                    members
                }
                _ => unknown.clone(),
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
                    let inherited = match results.get(&hit) {
                        Some(found) => found.clone(),
                        None => self
                            .prototype_members
                            .get(&(hit, key.clone()))
                            .cloned()
                            .unwrap_or_else(|| unknown.clone()),
                    };
                    let target = results.get_mut(write).expect("explored write");

                    changed |= target.absorb(&inherited);
                }
            }
        }

        for write in &order {
            self.values.targets.exploring.remove(&(*write, key.clone()));
        }

        let complete = self.values.targets.cuts == cuts;
        let result = results.get(&start).cloned().unwrap_or(unknown);

        if complete {
            for (write, found) in results {
                self.prototype_members.insert((write, key.clone()), found);
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
                Origin::Instance { file, class, exact } => self.class_values_of(
                    (file, class),
                    (exact, false),
                    Placement::Instance,
                    key,
                    &mut found,
                ),
                Origin::Constructor { file, class, exact } => self.class_values_of(
                    (file, class),
                    (exact, false),
                    Placement::Static,
                    key,
                    &mut found,
                ),
                Origin::HomeClass {
                    file,
                    class,
                    placement,
                } => self.class_values_of((file, class), (true, true), placement, key, &mut found),
                Origin::HomeObject { file, object } => {
                    self.home_object_values_of(file, object, key, &mut found)
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
        let mut copied = Vec::new();

        if !self.charge_targets(object.properties.len() as u64) {
            found.replaced = true;

            return;
        }

        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                if let ObjectPropertyKind::SpreadProperty(spread) = property {
                    copied.push(&spread.argument);
                }

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
                PropertyKind::Set => {
                    if let Expression::FunctionExpression(setter) = &property.value {
                        push_function(
                            &mut found.setters,
                            FunctionId {
                                file,
                                node: setter.node_id(),
                            },
                        );
                    }
                }
            }
        }

        for source in copied {
            self.linked_values_of(file, source, key, found);
        }

        if let (false, Some(prototype)) = (own, prototype) {
            self.linked_values_of(file, prototype, key, found);
        }
    }

    fn linked_values_of(
        &mut self,
        file: FileId,
        linked: &'a Expression<'a>,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let site = ((file, linked.node_id()), key.clone());

        if self.values.targets.linked.contains(&site) {
            found.replaced = true;

            return;
        }

        if !self.enter_targets() {
            self.leave_targets();

            found.replaced = true;

            return;
        }

        self.values.targets.linked.insert(site.clone());

        let mut receiver = Receiver::default();

        self.collect_receiver(file, linked, &mut HashSet::new(), &mut receiver);

        let inherited = self.member_candidates_of(file, linked, &receiver, key);

        self.values.targets.linked.remove(&site);
        self.leave_targets();

        found.absorb(&inherited);

        found.accessors_open |= is_unknown_prototype(linked, &receiver);
    }

    fn push_getter(&mut self, getter: FunctionId, found: &mut MemberValues<'a>) {
        push_function(&mut found.functions, getter);
        push_function(&mut found.getters, getter);

        for value in self.returned_expressions_of(getter) {
            found.values.push((getter.file, value));
        }
    }

    fn home_object_values_of(
        &mut self,
        file: FileId,
        object: &'a ObjectExpression<'a>,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                continue;
            };

            if !property.computed
                && self.property_key_of(file, property)
                    == Some(MemberKey::Name("__proto__".to_string()))
            {
                self.linked_values_of(file, &property.value, key, found);
            }
        }
    }

    fn class_values_of(
        &mut self,
        (file, class): ClassSite<'a>,
        (exact, inherited): (bool, bool),
        placement: Placement,
        key: &MemberKey,
        found: &mut MemberValues<'a>,
    ) {
        let root = (file, class);
        let mut classes: Vec<(ClassSite<'a>, Layer)> = Vec::new();
        let mut prototype = true;

        self.lineage_sites_of(file, class);

        if placement == Placement::Instance && !inherited {
            let (owners, exposed) =
                self.defining_classes_of(root, (key, placement, Layer::Own), false, found);

            prototype = exposed;

            classes.extend(owners.into_iter().map(|site| (site, Layer::Own)));
        }

        if prototype {
            let layer = match placement {
                Placement::Instance => Layer::Prototype,
                _ => Layer::Any,
            };
            let (owners, _) =
                self.defining_classes_of(root, (key, placement, layer), inherited, found);

            classes.extend(owners.into_iter().map(|site| (site, layer)));
        }

        found.defined += usize::from(!classes.is_empty());

        if !exact {
            let subclasses = self.subclasses_of(file, class);

            found.below.extend(
                subclasses
                    .iter()
                    .map(|(file, class)| (*file, class.node_id())),
            );
            classes.extend(subclasses.into_iter().map(|site| (site, Layer::Any)));
        }

        for (candidate, layer) in classes {
            self.push_elements(candidate, key, placement, layer, found);
        }
    }

    fn defining_classes_of(
        &mut self,
        root: ClassSite<'a>,
        (key, placement, layer): (&MemberKey, Placement, Layer),
        inherited: bool,
        found: &mut MemberValues<'a>,
    ) -> (Vec<ClassSite<'a>>, bool) {
        let mut defining = Vec::new();
        let mut passed = Vec::new();
        let mut visited = HashSet::new();
        let mut exposed = false;
        let mut pending = vec![root];

        while let Some(candidate) = pending.pop() {
            let site = (candidate.0, candidate.1.node_id());

            if !visited.insert(site) {
                continue;
            }

            let skipped = inherited && site == (root.0, root.1.node_id());
            let continues = if !skipped
                && !self
                    .elements_keyed(candidate, key, placement, layer)
                    .is_empty()
            {
                defining.push(candidate);

                self.may_remove_member(candidate, key, placement, layer)
            } else {
                true
            };

            if !continues {
                continue;
            }

            passed.push(site);

            found.replaced |= self.is_open_heritage(candidate);

            let bases = self.bases_of(site);

            exposed |= bases.is_empty();

            pending.extend(bases);
        }

        if layer != Layer::Own && !defining.is_empty() {
            found.below.extend(passed);
        }

        (defining, exposed)
    }

    fn bases_of(&self, site: Site) -> Vec<ClassSite<'a>> {
        let bases = self
            .values
            .targets
            .bases
            .get(&site)
            .cloned()
            .unwrap_or_default();

        self.class_sites_of(bases)
    }

    fn is_open_heritage(&self, (file, class): ClassSite<'a>) -> bool {
        self.values
            .targets
            .open_heritages
            .contains(&(file, class.node_id()))
    }

    fn may_remove_member(
        &mut self,
        (file, class): ClassSite<'a>,
        key: &MemberKey,
        placement: Placement,
        layer: Layer,
    ) -> bool {
        let site = (file, class.node_id());
        let mut written_keys = vec![Some(key.clone()), None];

        if matches!(key, MemberKey::Name(name) if is_index_name(name)) {
            written_keys.push(Some(MemberKey::Index));
        }

        let indices: Vec<usize> = written_keys
            .iter()
            .filter_map(|written| self.values.targets.removals.get(written))
            .flatten()
            .copied()
            .collect();

        for index in indices {
            if !self.charge_dispatch() {
                return true;
            }

            let removed = match &self.values.targets.owners[index].0 {
                Owner::Prototype { class } => {
                    *class == site && placement == Placement::Instance && layer != Layer::Own
                }
                Owner::ClassThis {
                    class,
                    placement: written,
                } => {
                    *class == site
                        && match placement {
                            Placement::Instance => {
                                layer == Layer::Own && *written != Placement::Static
                            }
                            _ => *written != Placement::Instance,
                        }
                }
                Owner::Value {
                    allocation, shared, ..
                } => layer == Layer::Own || !*allocation || *shared,
                _ => false,
            };

            if removed {
                return true;
            }
        }

        false
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
        layer: Layer,
    ) -> Vec<&'a ClassElement<'a>> {
        let mut found = Vec::new();

        for element in &class.body.body {
            let own = matches!(element, ClassElement::PropertyDefinition(_));
            let layered = match layer {
                Layer::Own => own,
                Layer::Prototype => !own,
                Layer::Any => true,
            };

            if layered
                && (class.declare || !is_type_only_element(element))
                && placement_of_element(element) == Some(placement)
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
        layer: Layer,
        found: &mut MemberValues<'a>,
    ) {
        for element in self.elements_keyed((file, class), key, placement, layer) {
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
                        MethodDefinitionKind::Set => push_function(&mut found.setters, function),
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
        self.class_candidates_of(file, expression, depth).0
    }

    fn class_candidates_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> (Vec<ClassSite<'a>>, bool) {
        if depth > MAXIMUM_ALIAS_DEPTH {
            return (Vec::new(), true);
        }

        let expression = unwrap(expression);

        if let Some(class) = self
            .declarations
            .class_of_expression(self.project, file, expression)
        {
            let Expression::Identifier(reference) = expression else {
                return (vec![class], false);
            };
            let rebound = self
                .declarations
                .binding_of_reference(self.project, file, reference)
                .is_some_and(|binding| !self.declarations.is_write_free(self.project, binding));

            if !rebound {
                return (vec![class], false);
            }

            let (written, unresolved) = self.written_values_of(file, reference);
            let (mut found, open) = self.class_candidates_among(written, depth);

            found.insert(0, class);

            return (found, open || unresolved);
        }

        match expression {
            Expression::ClassExpression(class) => (vec![(file, class)], false),
            Expression::ConditionalExpression(conditional) => self.class_candidates_among(
                vec![
                    (file, &conditional.consequent),
                    (file, &conditional.alternate),
                ],
                depth,
            ),
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference);

                if let Some((target, init)) = declaration.and_then(constant_initializer_of) {
                    return self.class_candidates_of(target, init, depth + 1);
                }

                if let Some(Declaration::Parameter {
                    file: target,
                    parameter: ParameterNode::Formal(parameter),
                    function,
                }) = declaration
                {
                    return self.parameter_class_candidates_of(
                        (file, reference),
                        (target, function, parameter),
                        depth,
                    );
                }

                match declaration.and_then(|_| self.local_values_of(file, reference)) {
                    Some(values) => self.class_candidates_among(values, depth),
                    None => (Vec::new(), true),
                }
            }
            Expression::CallExpression(call) => {
                let targets = self.resolved_callee_of(file, call).targets;
                let mut found = Vec::new();
                let mut open = targets.open;

                for target in targets.known {
                    let parameters = match self.kind_of_node(target.file, target.node) {
                        AstKind::Function(function) => &function.params,
                        AstKind::ArrowFunctionExpression(arrow) => &arrow.params,
                        _ => continue,
                    };

                    for value in self.returned_expressions_of(target) {
                        let (returned_classes, returned_open) =
                            self.class_candidates_of(target.file, value, depth + 1);

                        open |= returned_open;

                        for (returned_file, returned) in returned_classes {
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

                (found, open)
            }
            other => {
                let Some(member) = member_expression_of(other) else {
                    return (Vec::new(), true);
                };
                let Some(key) = self.member_key_of(file, member) else {
                    return (Vec::new(), true);
                };
                let mut receiver = Receiver::default();

                if !self.enter_targets() {
                    self.leave_targets();

                    return (Vec::new(), true);
                }

                self.collect_receiver(file, member.object(), &mut HashSet::new(), &mut receiver);

                let values = self.member_candidates_of(file, member.object(), &receiver, &key);
                let (found, open) = self.class_candidates_among(values.values, depth);

                self.leave_targets();

                (found, open || values.replaced)
            }
        }
    }

    fn parameter_class_candidates_of(
        &mut self,
        (file, reference): (FileId, &'a IdentifierReference<'a>),
        (target, function, parameter): (FileId, FunctionNode<'a>, &'a FormalParameter<'a>),
        depth: usize,
    ) -> (Vec<ClassSite<'a>>, bool) {
        let binding = self
            .declarations
            .binding_of_reference(self.project, file, reference)
            .filter(|_| matches!(parameter.pattern, BindingPattern::BindingIdentifier(_)))
            .filter(|binding| self.is_parameter_unwritten(*binding));
        let Some(binding) = binding else {
            return (Vec::new(), true);
        };

        if let Some((sites, open)) = self.values.targets.parameter_classes.get(&binding) {
            let open = *open;

            return (self.class_sites_of(sites.clone()), open);
        }

        let exhaustions = self.values.targets.exhaustions;
        let open = self
            .call_arguments_of(target, function, parameter)
            .is_none();
        let sources = self.parameter_sources_of((target, function), parameter);
        let charged = sources.iter().all(|_| self.charge_dispatch());

        if !charged {
            return (Vec::new(), true);
        }

        let (found, sources_open) = self.class_candidates_among(sources, depth);
        let open = open || sources_open;

        if depth == 0 && exhaustions == self.values.targets.exhaustions {
            let sites = found
                .iter()
                .map(|(file, class)| (*file, class.node_id()))
                .collect();

            self.values
                .targets
                .parameter_classes
                .insert(binding, (sites, open));
        }

        (found, open)
    }

    fn class_candidates_among(
        &mut self,
        values: Vec<Valued<'a>>,
        depth: usize,
    ) -> (Vec<ClassSite<'a>>, bool) {
        let mut found: Vec<ClassSite<'a>> = Vec::new();
        let mut open = false;

        for (target, value) in values {
            let (classes, value_open) = self.class_candidates_of(target, value, depth + 1);

            open |= value_open;

            for class in classes {
                if !found
                    .iter()
                    .any(|(file, known)| *file == class.0 && known.node_id() == class.1.node_id())
                {
                    found.push(class);
                }
            }
        }

        (found, open)
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
                self.values
                    .targets
                    .open_heritages
                    .insert((file, class.node_id()));
                self.values.targets.open_heritages.extend(
                    pending
                        .iter()
                        .map(|(file, class): &ClassSite<'a>| (*file, class.node_id())),
                );

                break;
            }

            let Some(heritage) = &class.heritage else {
                continue;
            };
            let (bases, open) = self.class_candidates_of(file, &heritage.expression, 0);
            let builtin = global_name_of(
                self.project.file(file).semantic.scoping(),
                &heritage.expression,
            )
            .is_some();

            if open && !builtin {
                self.values
                    .targets
                    .open_heritages
                    .insert((file, class.node_id()));
            }

            self.values.targets.bases.insert(
                (file, class.node_id()),
                bases
                    .iter()
                    .map(|(base_file, base)| (*base_file, base.node_id()))
                    .collect(),
            );

            for (base_file, base) in bases {
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
                let value = match reflective_name_of(&call.callee) {
                    Some("defineProperties") => {
                        descriptor_value_of(self.descriptor_of((file, node)))
                    }
                    _ => (property.kind == PropertyKind::Init).then_some(&property.value),
                };

                Some((object, value))
            }
            AstKind::CallExpression(call) => {
                let object = call.arguments.first()?.as_expression()?;
                let value = match reflective_name_of(&call.callee) {
                    Some("setPrototypeOf") => {
                        call.arguments.get(1).and_then(Argument::as_expression)
                    }
                    Some("defineProperty") => descriptor_value_of(self.descriptor_of((file, node))),
                    _ => None,
                };

                Some((object, value))
            }
            _ => None,
        }
    }

    fn descriptor_of(&self, (file, node): Site) -> Descriptor<'a> {
        let nodes = self.project.file(file).semantic.nodes();
        let descriptor = match self.kind_of_node(file, node) {
            AstKind::CallExpression(call)
                if reflective_name_of(&call.callee) == Some("defineProperty") =>
            {
                call.arguments.get(2).and_then(Argument::as_expression)
            }
            AstKind::ObjectProperty(property) => {
                let defining = nodes
                    .ancestors(node)
                    .find_map(|ancestor| match ancestor.kind() {
                        AstKind::CallExpression(call) => Some(call),
                        _ => None,
                    });

                match defining.is_some_and(|call| {
                    reflective_name_of(&call.callee) == Some("defineProperties")
                }) {
                    true => Some(&property.value),
                    false => return Descriptor::Absent,
                }
            }
            _ => return Descriptor::Absent,
        };
        let Some(Expression::ObjectExpression(object)) = descriptor.map(unwrap) else {
            return Descriptor::Unknown;
        };
        let mut value = None;
        let mut getter = None;
        let mut setter = None;

        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                return Descriptor::Unknown;
            };

            if property.computed || property.kind != PropertyKind::Init {
                return Descriptor::Unknown;
            }

            match property.key.static_name().as_deref() {
                Some("value") => value = Some(&property.value),
                Some("get") => getter = Some(&property.value),
                Some("set") => setter = Some(&property.value),
                Some(_) => {}
                None => return Descriptor::Unknown,
            }
        }

        Descriptor::Known {
            value,
            getter,
            setter,
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
            Expression::AwaitExpression(awaited) => {
                let kind = self.proven_kind_of(file, &awaited.argument, depth + 1);

                match is_builtin(kind) && !self.builtin_members_replaced(kind, &["then"]) {
                    true => kind,
                    false => Kind::Unknown,
                }
            }
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
                found.accessors_open |= value.is_none();

                if value.is_some() && !found.hits.contains(&index) {
                    found.hits.push(index);
                }
            }
            kind => {
                found.replaced |= callable;

                if let Some(value) = value {
                    found.values.push((write.site.0, value));
                }

                if kind == WriteKind::Defined {
                    match self.descriptor_of(write.site) {
                        Descriptor::Known { getter, setter, .. } => {
                            let file = write.site.0;

                            if let Some(getter) = getter {
                                let targets = self.accessor_functions_of(file, getter);

                                found.accessors_open |= targets.open;

                                for known in targets.known {
                                    self.push_getter(known, found);
                                }
                            }

                            if let Some(setter) = setter {
                                let targets = self.accessor_functions_of(file, setter);

                                found.accessors_open |= targets.open;

                                for known in targets.known {
                                    push_function(&mut found.setters, known);
                                }
                            }
                        }
                        Descriptor::Unknown => found.accessors_open = true,
                        Descriptor::Absent => {}
                    }
                }
            }
        }
    }

    fn accessor_functions_of(&mut self, file: FileId, value: &'a Expression<'a>) -> TargetSet {
        let mut found = closed_targets_of();

        if self.may_be_callable(file, value) {
            self.collect_callable_targets(file, value, &mut HashSet::new(), &mut found);
        }

        found
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
                summary.callables_open = true;

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
                summary.callables_open = true;

                summary.prototypes.push(index);

                continue;
            }

            summary.replaced |= callable;

            if callable && written.is_some() {
                let site = self.values.targets.writes[index].site;
                let supplied = self
                    .write_parts_of(site)
                    .is_some_and(|(_, value)| value.is_some());
                let getter = matches!(
                    self.descriptor_of(site),
                    Descriptor::Known {
                        getter: Some(_),
                        ..
                    }
                );

                summary.callables_open |= !supplied && !getter;
            }

            if written.is_some() {
                self.apply_write(index, &mut found);
            } else if self.values.targets.writes[index].kind == WriteKind::Defined
                && !matches!(
                    self.descriptor_of(self.values.targets.writes[index].site),
                    Descriptor::Absent
                )
            {
                summary.accessors_open = true;
            }
        }

        summary.getters = std::mem::take(&mut found.getters);
        summary.setters = std::mem::take(&mut found.setters);
        summary.accessors_open |= found.accessors_open;

        let mut targets = TargetSet {
            known: found.functions,
            open: summary.callables_open || summary.accessors_open,
        };
        let mut visited = HashSet::new();

        for (target, value) in found.values {
            self.collect_callable_targets(target, value, &mut visited, &mut targets);
        }

        summary.callables_open |= targets.open;
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
            let (file, class, exact, placement) = match *origin {
                Origin::Instance { file, class, exact } => {
                    (file, class, exact, Placement::Instance)
                }
                Origin::Constructor { file, class, exact } => {
                    (file, class, exact, Placement::Static)
                }
                Origin::HomeClass {
                    file,
                    class,
                    placement,
                } => (file, class, true, placement),
                Origin::Object { .. } | Origin::Function { .. } | Origin::HomeObject { .. } => {
                    continue
                }
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
                    self.linked_values_of(site.0, &assignment.right, key, found);
                }
            }

            found.replaced |= self.has_global_write("globalThis", None);
        }

        for written in written_keys {
            let summary = self.wide_summary_of(written, kind, shared, receiver.origins.is_empty());

            found.replaced |= summary.replaced;
            found.accessors_open |= summary.accessors_open;

            for function in summary.known {
                push_function(&mut found.functions, function);
            }

            for getter in summary.getters {
                push_function(&mut found.getters, getter);
            }

            for setter in summary.setters {
                push_function(&mut found.setters, setter);
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

                self.push_elements(
                    (class_file, class),
                    key,
                    Placement::Instance,
                    Layer::Any,
                    found,
                );

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

                property_writes_of(file, (site, object), false, pending);
            }
        }
        "setPrototypeOf" => pending.push((site, None, WriteKind::Prototype)),
        "defineProperties" => {
            let Some(Expression::ObjectExpression(object)) = call
                .arguments
                .get(1)
                .and_then(Argument::as_expression)
                .map(unwrap)
            else {
                return pending.push((site, None, WriteKind::Defined));
            };

            property_writes_of(file, (site, object), true, pending);
        }
        _ => pending.push((site, None, WriteKind::Defined)),
    }
}

fn property_writes_of<'a>(
    file: FileId,
    (site, object): (Site, &'a ObjectExpression<'a>),
    defining: bool,
    pending: &mut Vec<(Site, Option<KeySource<'a>>, WriteKind)>,
) {
    for property in &object.properties {
        match property {
            ObjectPropertyKind::ObjectProperty(property) => {
                let key = match (property.computed, &property.key) {
                    (false, key) | (true, key @ PropertyKey::StringLiteral(_)) => key
                        .static_name()
                        .map(|name| KeySource::Known(MemberKey::Name(name.into_owned()))),
                    (true, key) => key
                        .as_expression()
                        .map(|key| KeySource::Computed(file, key)),
                };
                let kind = match (defining, property.kind) {
                    (false, PropertyKind::Init) => WriteKind::Assigned,
                    _ => WriteKind::Defined,
                };

                pending.push(((file, property.node_id()), key, kind));
            }
            ObjectPropertyKind::SpreadProperty(_) => pending.push((site, None, WriteKind::Defined)),
        }
    }
}

fn labeled_target_of(
    nodes: &oxc_semantic::AstNodes<'_>,
    node: NodeId,
    label: &str,
) -> Option<NodeId> {
    nodes
        .ancestor_ids(node)
        .find_map(|ancestor| match nodes.kind(ancestor) {
            AstKind::LabeledStatement(statement) if statement.label.name == label => {
                Some(statement.body.node_id())
            }
            _ => None,
        })
}

fn completes_normally(scoping: &oxc_semantic::Scoping, kind: &AstKind<'_>) -> bool {
    if crate::syntax::is_type_kind(kind.ty()) {
        return true;
    }

    match kind {
        AstKind::BlockStatement(_)
        | AstKind::EmptyStatement(_)
        | AstKind::ExpressionStatement(_)
        | AstKind::IfStatement(_)
        | AstKind::SwitchStatement(_)
        | AstKind::SwitchCase(_)
        | AstKind::LabeledStatement(_)
        | AstKind::LabelIdentifier(_)
        | AstKind::ForStatement(_)
        | AstKind::WhileStatement(_)
        | AstKind::DoWhileStatement(_)
        | AstKind::DebuggerStatement(_)
        | AstKind::VariableDeclaration(_)
        | AstKind::BindingIdentifier(_)
        | AstKind::NumericLiteral(_)
        | AstKind::StringLiteral(_)
        | AstKind::BooleanLiteral(_)
        | AstKind::NullLiteral(_)
        | AstKind::BigIntLiteral(_)
        | AstKind::ParenthesizedExpression(_)
        | AstKind::SequenceExpression(_)
        | AstKind::ConditionalExpression(_)
        | AstKind::LogicalExpression(_)
        | AstKind::Function(_)
        | AstKind::ArrowFunctionExpression(_) => true,
        AstKind::TemplateLiteral(template) => template.expressions.is_empty(),
        AstKind::TemplateElement(_) => true,
        AstKind::UnaryExpression(unary) => matches!(
            unary.operator,
            UnaryOperator::Void | UnaryOperator::LogicalNot | UnaryOperator::Typeof
        ),
        AstKind::VariableDeclarator(declarator) => {
            matches!(declarator.id, BindingPattern::BindingIdentifier(_))
        }
        AstKind::IdentifierReference(reference) => !is_unbound(scoping, reference),
        AstKind::AssignmentExpression(assignment) => {
            assignment.operator.is_assign()
                && matches!(
                    assignment.left,
                    AssignmentTarget::AssignmentTargetIdentifier(_)
                )
        }
        _ => false,
    }
}

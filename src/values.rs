use std::collections::HashMap;
use std::rc::Rc;

use oxc_allocator::GetAddress;
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, BindingPattern, CallExpression, Class,
    ClassElement, Expression, IdentifierReference, MemberExpression, SimpleAssignmentTarget,
};
use oxc_ast::AstKind;
use oxc_semantic::{NodeId, Semantic};
use oxc_syntax::operator::{LogicalOperator, UnaryOperator};

use crate::analysis::{work::Event, Analysis};
use crate::budgets::Subtree;
use crate::constants::{constant_initializer_of, evaluate_enum};
use crate::declarations::{Declaration, FunctionNode};
use crate::project::FileId;
use crate::syntax::{is_iteration_kind, member_expression_of, unwrap, Root};
use crate::unknowns::UnknownReason;

#[path = "primitive_values.rs"]
mod primitive;

#[path = "value_sizes.rs"]
mod sizes;

#[path = "value_targets.rs"]
mod targets;
pub use primitive::{
    CertifiedValues, Failure, Limits, Primitive, PrimitiveAdapter, ValueResult, Work,
};
pub use sizes::Cardinality;
pub(crate) use sizes::{is_direct_call, outermost_of};
pub(crate) use targets::{
    protocol_key_of, Construction, ConstructionPlan, Iteration, MemberKey, PrototypeMembers,
};

use crate::cost::{Cost, CostError, Domain, Part, Preference};
use crate::declarations::TargetSet;
use crate::summaries::SummaryId;
use crate::unknowns::SourceSpan;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SizeId {
    pub origin: SourceSpan,
    pub quantity: SizeQuantity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SizeQuantity {
    Length,
    Keys,
    Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueFacts {
    pub value: ValueId,
    pub size: Option<Cost>,
    pub targets: TargetSet,
    pub latent: Option<SummaryId>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Definedness {
    Undefined,
    Defined,
    #[default]
    Unknown,
}

const MAXIMUM_DEFINEDNESS_DEPTH: usize = 8;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgumentFacts {
    pub value: ValueFacts,
    pub callback: Option<Part>,
    pub preference: Preference,
    pub definedness: Definedness,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Size {
    pub length: Cost,
    pub element: Cost,
    pub exceeds: bool,
    pub length_resolved: bool,
    pub element_resolved: bool,
}

const MAXIMUM_PRODUCED_DEPTH: usize = 16;

const PRESERVING_METHODS: [&str; 10] = [
    "filter",
    "slice",
    "sort",
    "toSorted",
    "reverse",
    "toReversed",
    "fill",
    "copyWithin",
    "with",
    "splice",
];

fn size_sum_of(sizes: [&Cost; 2]) -> Result<Cost, CostError> {
    let mut terms: Vec<Cost> = sizes
        .into_iter()
        .filter(|size| size.constant_of().is_none())
        .cloned()
        .collect();

    terms.dedup();

    match terms.len() {
        0 => Ok(Cost::ONE),
        1 => Ok(terms.remove(0)),
        _ => Cost::maximum(terms),
    }
}

fn size_product_of(left: &Cost, right: &Cost) -> Result<(Cost, bool), CostError> {
    match (left.constant_of(), right.constant_of()) {
        (Some(_), Some(_)) => Ok((Cost::ONE, false)),
        (Some(_), None) => Ok((right.clone(), false)),
        (None, Some(_)) => Ok((left.clone(), false)),
        (None, None) => Ok((left.multiply(right)?, true)),
    }
}

impl Size {
    pub fn constant() -> Size {
        Size {
            element: Cost::ONE,
            ..Size::sized(Cost::ONE)
        }
    }

    pub fn sized(length: Cost) -> Size {
        Size {
            length,
            element: Cost::N,
            exceeds: false,
            length_resolved: true,
            element_resolved: true,
        }
    }

    pub fn unresolved() -> Size {
        Size::sized(Cost::N).unresolved_length()
    }

    pub fn unresolved_length(self) -> Size {
        Size {
            length_resolved: false,
            ..self
        }
    }

    pub fn combined(self, other: &Size) -> Size {
        match (
            size_sum_of([&self.length, &other.length]),
            size_sum_of([&self.element, &other.element]),
        ) {
            (Ok(length), Ok(element)) => Size {
                length,
                element,
                exceeds: self.exceeds || other.exceeds,
                length_resolved: self.length_resolved && other.length_resolved,
                element_resolved: self.element_resolved && other.element_resolved,
            },
            _ => Size::unresolved(),
        }
    }

    pub fn flattened(self) -> Size {
        match size_product_of(&self.length, &self.element) {
            Ok((length, product)) => Size {
                length,
                element: Cost::N,
                exceeds: self.exceeds || product,
                length_resolved: self.length_resolved && self.element_resolved,
                element_resolved: true,
            },
            Err(_) => Size::unresolved(),
        }
    }

    pub fn producing(self, result: &Size) -> Size {
        match size_product_of(&self.length, &result.length) {
            Ok((length, product)) => Size {
                length,
                element: result.element.clone(),
                exceeds: self.exceeds || result.exceeds || product,
                length_resolved: self.length_resolved && result.length_resolved,
                element_resolved: result.element_resolved,
            },
            Err(_) => Size::unresolved(),
        }
    }

    pub fn repeated(self, count: &Size) -> Size {
        match size_product_of(&self.length, &count.length) {
            Ok((length, product)) => Size {
                length,
                exceeds: self.exceeds || count.exceeds || product,
                length_resolved: self.length_resolved && count.length_resolved,
                ..self
            },
            Err(_) => Size::unresolved(),
        }
    }

    pub fn containing(self, result: &Size) -> Size {
        Size {
            element: result.length.clone(),
            element_resolved: result.length_resolved,
            ..self
        }
    }
}

pub const RECURRENCE_BASE: u64 = u64::MAX - 1;
pub const RECURRENCE_FLOOR: u64 =
    RECURRENCE_BASE - (crate::recurrences::MAXIMUM_RECURRENCE_MEMBERS as u64);

#[derive(Default)]
pub struct Values {
    origins: HashMap<SourceSpan, ValueId>,
    spans: HashMap<ValueId, SourceSpan>,
    allocations: std::collections::HashSet<ValueId>,
    callbacks: HashMap<usize, ValueId>,
    undefined: Option<ValueId>,
    next_value: u32,
    quantities: HashMap<(ValueId, SizeQuantity), u64>,
    labels: Vec<String>,
    primitive_limits: Limits,
    primitive_files: HashMap<FileId, PrimitiveFile>,
    targets: targets::TargetIndex,
    sizes: sizes::SizeMemory,
    iteration_kinds: HashMap<ValueId, crate::declared_types::Kind>,
    iteration_static: HashMap<(FileId, NodeId), crate::declared_types::Kind>,
}

#[derive(Clone, Debug)]
pub struct KnownValue {
    pub evaluation: NodeId,
    pub value: Result<Rc<Primitive>, Failure>,
}

#[derive(Default)]
struct PrimitiveFile {
    work: Work,
    values: HashMap<NodeId, KnownValue>,
    active: std::collections::HashSet<NodeId>,
    enums: HashMap<NodeId, Result<(), Failure>>,
    members: HashMap<NodeId, Result<Rc<Primitive>, Failure>>,
}

impl Failure {
    pub fn unknown_reason(self) -> UnknownReason {
        match self {
            Self::NodeLimit | Self::DepthLimit | Self::PayloadLimit => {
                UnknownReason::ResourceExhaustion
            }
            Self::UncertifiedReference => UnknownReason::SizeRelation,
            Self::Unsupported | Self::LoneSurrogate => UnknownReason::UnsupportedModel,
        }
    }
}

impl Values {
    pub(crate) fn remember_iteration_kind(
        &mut self,
        value: ValueId,
        kind: crate::declared_types::Kind,
    ) {
        self.iteration_kinds
            .entry(value)
            .and_modify(|known| {
                if *known != kind {
                    *known = crate::declared_types::Kind::Unknown;
                }
            })
            .or_insert(kind);
    }

    pub(crate) fn forget_iteration_kinds(&mut self) {
        self.iteration_kinds.clear();
        self.iteration_static.clear();
    }

    pub fn set_primitive_limits(&mut self, limits: Limits) -> bool {
        if !self.primitive_files.is_empty() {
            return false;
        }

        self.primitive_limits = limits;

        true
    }

    pub fn primitive_work(&self, file: FileId) -> Work {
        self.primitive_files
            .get(&file)
            .map_or(Work::default(), |state| state.work)
    }

    fn evaluate_with<'a, T>(
        &mut self,
        file: FileId,
        semantic: &Semantic<'a>,
        operation: impl FnOnce(&mut PrimitiveAdapter<'_, 'a>) -> T,
    ) -> T {
        let state = self.primitive_files.entry(file).or_default();
        let mut adapter = PrimitiveAdapter::new(semantic, self.primitive_limits);
        adapter.work = state.work;
        let result = operation(&mut adapter);
        state.work = adapter.work;

        result
    }
    pub fn quantity(
        &mut self,
        value: ValueId,
        quantity: SizeQuantity,
        label: String,
    ) -> Result<Cost, CostError> {
        let next = u64::try_from(self.labels.len()).map_err(|_| CostError::Resource)?;
        let id = *self.quantities.entry((value, quantity)).or_insert_with(|| {
            self.labels.push(label);

            next
        });

        Ok(Cost::dimension(id, Domain::Size))
    }

    pub fn label(&self, id: u64) -> String {
        if id == u64::MAX {
            return "N".into();
        }

        if id >= RECURRENCE_FLOOR {
            return "recursion".into();
        }

        self.labels
            .get(id as usize)
            .cloned()
            .unwrap_or_else(|| format!("size_{id}"))
    }

    pub fn write_label(&self, id: u64, out: &mut dyn std::fmt::Write) -> std::fmt::Result {
        if id == u64::MAX {
            return out.write_str("N");
        }

        if id >= RECURRENCE_FLOOR {
            return out.write_str("recursion");
        }

        match self.labels.get(id as usize) {
            Some(label) => out.write_str(label),
            None => write!(out, "size_{id}"),
        }
    }

    pub fn prefer_length_label(&mut self, value: ValueId) {
        if let Some(id) = self.quantities.get(&(value, SizeQuantity::Value)) {
            let label = &mut self.labels[*id as usize];

            if !label.ends_with(".length") {
                label.push_str(".length");
            }
        }
    }

    pub(crate) fn callback(&mut self, descriptor: usize) -> ValueFacts {
        let value = if let Some(value) = self.callbacks.get(&descriptor) {
            *value
        } else {
            let value = ValueId(self.next_value);
            self.next_value = self
                .next_value
                .checked_add(1)
                .expect("callback value arena fits u32");

            self.callbacks.insert(descriptor, value);

            value
        };

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }

    pub(crate) fn undefined(&mut self) -> ValueFacts {
        let value = match self.undefined {
            Some(value) => value,
            None => {
                let value = ValueId(self.next_value);
                self.next_value = self
                    .next_value
                    .checked_add(1)
                    .expect("value arena fits u32");
                self.undefined = Some(value);

                value
            }
        };

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }

    pub fn allocation(&mut self, origin: SourceSpan) -> ValueFacts {
        let facts = self.at(origin);

        self.allocations.insert(facts.value);

        facts
    }

    pub fn origin_of_value(&self, value: ValueId) -> Option<SourceSpan> {
        self.spans.get(&value).copied()
    }

    pub(crate) fn forget_sizes(&mut self) {
        self.sizes = sizes::SizeMemory::default();
    }

    pub fn is_allocation(&self, value: ValueId) -> bool {
        self.allocations.contains(&value)
    }

    pub fn may_alias(&self, left: ValueId, right: ValueId) -> bool {
        left == right || !(self.is_allocation(left) && self.is_allocation(right))
    }

    pub fn at(&mut self, origin: SourceSpan) -> ValueFacts {
        let value = if let Some(value) = self.origins.get(&origin) {
            *value
        } else {
            let value = ValueId(self.next_value);
            self.next_value = self
                .next_value
                .checked_add(1)
                .expect("value arena fits u32");

            self.origins.insert(origin, value);
            self.spans.insert(value, origin);

            value
        };

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn stable_initializer_of(
        &mut self,
        declaration: Declaration<'a>,
    ) -> Option<(FileId, &'a Expression<'a>)> {
        let (file, initializer) = constant_initializer_of(declaration)?;

        let Declaration::Member { class, element, .. } = declaration else {
            return Some((file, initializer));
        };
        let ClassElement::PropertyDefinition(property) = element else {
            return Some((file, initializer));
        };
        let key = property.key.static_name()?;

        (!reassigns_key(class, key.as_ref())).then_some((file, initializer))
    }

    pub(crate) fn definedness_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Definedness {
        self.definedness_at(file, e, 0)
    }

    fn definedness_at(&mut self, file: FileId, e: &'a Expression<'a>, depth: usize) -> Definedness {
        if depth >= MAXIMUM_DEFINEDNESS_DEPTH {
            return Definedness::Unknown;
        }

        let e = unwrap(e);
        let found = match e {
            Expression::Identifier(reference) => {
                let Some(declaration) =
                    self.declarations
                        .of_reference(self.project, file, reference)
                else {
                    return match reference.name == "undefined" {
                        true => Definedness::Undefined,
                        false => Definedness::Unknown,
                    };
                };

                if let Some(binding) = self.parameter_binding_of(declaration) {
                    let written = !self.is_parameter_unwritten(binding);

                    return match self.current_substitutions.get(&binding) {
                        Some(facts) if !written => facts.definedness,
                        _ => Definedness::Unknown,
                    };
                }

                if matches!(
                    declaration,
                    Declaration::Function { .. } | Declaration::Class { .. }
                ) && self
                    .declarations
                    .callable_reference(self.project, file, reference)
                    .1
                {
                    return Definedness::Defined;
                }

                match self.stable_initializer_of(declaration) {
                    Some((target, initializer)) => {
                        self.definedness_at(target, initializer, depth + 1)
                    }
                    None => Definedness::Unknown,
                }
            }
            Expression::UnaryExpression(unary) if unary.operator == UnaryOperator::Void => {
                Definedness::Undefined
            }
            Expression::UnaryExpression(_)
            | Expression::BinaryExpression(_)
            | Expression::UpdateExpression(_)
            | Expression::BooleanLiteral(_)
            | Expression::NullLiteral(_)
            | Expression::NumericLiteral(_)
            | Expression::BigIntLiteral(_)
            | Expression::RegExpLiteral(_)
            | Expression::StringLiteral(_)
            | Expression::TemplateLiteral(_)
            | Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::FunctionExpression(_)
            | Expression::ArrowFunctionExpression(_)
            | Expression::ClassExpression(_)
            | Expression::NewExpression(_) => Definedness::Defined,
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                self.definedness_at(file, &assignment.right, depth + 1)
            }
            Expression::SequenceExpression(sequence) => match sequence.expressions.last() {
                Some(last) => self.definedness_at(file, last, depth + 1),
                None => Definedness::Unknown,
            },
            Expression::ConditionalExpression(conditional) => {
                let consequent = self.definedness_at(file, &conditional.consequent, depth + 1);
                let alternate = self.definedness_at(file, &conditional.alternate, depth + 1);

                match consequent == alternate {
                    true => consequent,
                    false => Definedness::Unknown,
                }
            }
            Expression::LogicalExpression(logical) => {
                let right = self.definedness_at(file, &logical.right, depth + 1);

                match logical.operator {
                    LogicalOperator::And => {
                        let left = self.definedness_at(file, &logical.left, depth + 1);

                        match self.truthiness_at(file, &logical.left, depth + 1) {
                            Some(true) => right,
                            Some(false) => left,
                            None if left == Definedness::Defined
                                && right == Definedness::Defined =>
                            {
                                Definedness::Defined
                            }
                            None => Definedness::Unknown,
                        }
                    }
                    LogicalOperator::Or | LogicalOperator::Coalesce => match right {
                        Definedness::Defined => Definedness::Defined,
                        _ => Definedness::Unknown,
                    },
                }
            }
            _ => Definedness::Unknown,
        };

        if found != Definedness::Unknown {
            return found;
        }

        match self.known_value_at(file, e, depth).value.as_deref() {
            Ok(Primitive::Undefined) => Definedness::Undefined,
            Ok(_) => Definedness::Defined,
            Err(_) => Definedness::Unknown,
        }
    }

    fn truthiness_at(&mut self, file: FileId, e: &'a Expression<'a>, depth: usize) -> Option<bool> {
        match unwrap(e) {
            e if e.is_function() => Some(true),
            Expression::ObjectExpression(_)
            | Expression::ArrayExpression(_)
            | Expression::ClassExpression(_)
            | Expression::NewExpression(_)
            | Expression::RegExpLiteral(_) => Some(true),
            e if depth < MAXIMUM_DEFINEDNESS_DEPTH => self
                .known_value_at(file, e, depth)
                .value
                .ok()
                .map(|value| primitive::truthy(&value)),
            _ => None,
        }
    }

    pub fn known_value(&mut self, file: FileId, expression: &'a Expression<'a>) -> KnownValue {
        self.known_value_at(file, expression, 0)
    }

    pub fn known_key(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
    ) -> Result<String, Failure> {
        self.known_key_at(file, expression, 0)
    }

    fn known_key_at(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Result<String, Failure> {
        let value = self.known_value_at(file, expression, depth).value?;

        self.values
            .evaluate_with(file, &self.project.file(file).semantic, |adapter| {
                adapter.property_key(&value)
            })
    }

    fn known_value_at(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> KnownValue {
        let semantic = &self.project.file(file).semantic;
        let node = expression.node_id();
        let unavailable = |error| KnownValue {
            evaluation: node,
            value: Err(error),
        };

        if !PrimitiveAdapter::new(semantic, self.values.primitive_limits)
            .owns_node(node, expression.address())
        {
            return unavailable(Failure::UncertifiedReference);
        }

        if let Some(cached) = self
            .values
            .primitive_files
            .get(&file)
            .and_then(|state| state.values.get(&node))
        {
            return cached.clone();
        }

        if depth >= self.values.primitive_limits.depth {
            return unavailable(Failure::DepthLimit);
        }

        if let Err(error) = self
            .values
            .evaluate_with(file, semantic, |adapter| adapter.visit_container())
        {
            return unavailable(error);
        }

        if !self
            .values
            .primitive_files
            .get_mut(&file)
            .unwrap()
            .active
            .insert(node)
        {
            return unavailable(Failure::UncertifiedReference);
        }

        let value = self.primitive_expression(file, expression, depth + 1);
        let result = KnownValue {
            evaluation: node,
            value,
        };
        let state = self.values.primitive_files.get_mut(&file).unwrap();

        state.active.remove(&node);
        state.values.insert(node, result.clone());

        result
    }

    fn primitive_expression(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Result<Rc<Primitive>, Failure> {
        let semantic = &self.project.file(file).semantic;

        match expression {
            Expression::ParenthesizedExpression(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::TSAsExpression(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::TSSatisfiesExpression(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::TSTypeAssertion(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::TSNonNullExpression(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::TSInstantiationExpression(value) => {
                return self.known_value_at(file, &value.expression, depth).value
            }
            Expression::Identifier(reference) => {
                let declaration = self
                    .declarations
                    .of_reference(self.project, file, reference)
                    .ok_or(Failure::UncertifiedReference)?;

                return self.primitive_declaration(declaration, depth);
            }
            Expression::UnaryExpression(value) if value.operator != UnaryOperator::Void => {
                let argument = self.known_value_at(file, &value.argument, depth).value?;

                return self
                    .values
                    .evaluate_with(file, semantic, |adapter| {
                        let argument = adapter.copy_value(&argument)?;

                        adapter.unary(value.operator, argument)
                    })
                    .map(Rc::new);
            }
            Expression::BinaryExpression(value) => {
                let left = self.known_value_at(file, &value.left, depth).value?;
                let right = self.known_value_at(file, &value.right, depth).value?;

                return self
                    .values
                    .evaluate_with(file, semantic, |adapter| {
                        let left = adapter.copy_value(&left)?;
                        let right = adapter.copy_value(&right)?;

                        adapter.binary(value.operator, left, right)
                    })
                    .map(Rc::new);
            }
            Expression::SequenceExpression(value) => {
                return self
                    .known_value_at(
                        file,
                        value.expressions.last().ok_or(Failure::Unsupported)?,
                        depth,
                    )
                    .value
            }
            Expression::LogicalExpression(value) => {
                let left = self.known_value_at(file, &value.left, depth).value?;
                let take = match value.operator {
                    LogicalOperator::Coalesce => {
                        matches!(&*left, Primitive::Null | Primitive::Undefined)
                    }
                    LogicalOperator::And => primitive::truthy(&left),
                    LogicalOperator::Or => !primitive::truthy(&left),
                };

                return if take {
                    self.known_value_at(file, &value.right, depth).value
                } else {
                    Ok(left)
                };
            }
            _ => {}
        }

        if let Some(member) = member_expression_of(expression) {
            let (object, key) = match member {
                MemberExpression::StaticMemberExpression(access) => (
                    &access.object,
                    std::borrow::Cow::Borrowed(access.property.name.as_str()),
                ),
                MemberExpression::ComputedMemberExpression(access) => (
                    &access.object,
                    std::borrow::Cow::Owned(self.known_key_at(file, &access.expression, depth)?),
                ),
                MemberExpression::PrivateFieldExpression(_) => return Err(Failure::Unsupported),
            };

            if key == "length" {
                match self.primitive_length(file, object, depth) {
                    Ok(length) => return Ok(Rc::new(Primitive::Number(length))),
                    Err(
                        error @ (Failure::NodeLimit | Failure::DepthLimit | Failure::PayloadLimit),
                    ) => return Err(error),
                    Err(_) => {}
                }
            }

            let declaration = self
                .declaration_of_access(file, member)
                .ok_or(Failure::UncertifiedReference)?;

            return self.primitive_declaration(declaration, depth);
        }

        self.values
            .evaluate_with(file, semantic, |adapter| {
                adapter
                    .evaluate(expression, &CertifiedValues::new(semantic))
                    .value
            })
            .map(Rc::new)
    }

    fn primitive_length(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Result<f64, Failure> {
        if depth >= self.values.primitive_limits.depth {
            return Err(Failure::DepthLimit);
        }

        self.values
            .evaluate_with(file, &self.project.file(file).semantic, |adapter| {
                adapter.visit_container()
            })?;

        if let Expression::ArrayExpression(array) = expression {
            self.values
                .evaluate_with(file, &self.project.file(file).semantic, |adapter| {
                    for _ in &array.elements {
                        adapter.visit_container()?;
                    }

                    Ok(())
                })?;

            if array.elements.iter().all(|element| {
                !matches!(
                    element,
                    oxc_ast::ast::ArrayExpressionElement::SpreadElement(_)
                )
            }) {
                return Ok(array.elements.len() as f64);
            }
        }

        if let Expression::Identifier(reference) = expression {
            if let Some(declaration) = self
                .declarations
                .of_reference(self.project, file, reference)
            {
                if let Some((target, initializer)) = self.stable_initializer_of(declaration) {
                    if self.declaration_has_exact_size(declaration) {
                        return self.primitive_length(target, initializer, depth + 1);
                    }
                }
            }
        }

        match &*self.known_value_at(file, expression, depth).value? {
            Primitive::String(value) => Ok(value.encode_utf16().count() as f64),
            _ => Err(Failure::Unsupported),
        }
    }

    fn primitive_declaration(
        &mut self,
        declaration: Declaration<'a>,
        depth: usize,
    ) -> Result<Rc<Primitive>, Failure> {
        if let Declaration::EnumMember { file, member } = declaration {
            let semantic = &self.project.file(file).semantic;
            let enumeration = semantic
                .nodes()
                .ancestors(member.node_id())
                .take(3)
                .find_map(|node| match node.kind() {
                    AstKind::TSEnumDeclaration(declaration) => Some(declaration),
                    _ => None,
                })
                .ok_or(Failure::UncertifiedReference)?;
            let id = enumeration.node_id();

            if !self
                .values
                .primitive_files
                .get(&file)
                .is_some_and(|state| state.enums.contains_key(&id))
            {
                let evaluated = self.values.evaluate_with(file, semantic, |adapter| {
                    evaluate_enum(semantic, enumeration, adapter)
                });
                let state = self.values.primitive_files.get_mut(&file).unwrap();
                let status = match evaluated {
                    Ok(members) => {
                        for member in members {
                            state
                                .members
                                .insert(member.member, member.value.map(Rc::new));
                        }

                        Ok(())
                    }
                    Err(error) => Err(error),
                };

                state.enums.insert(id, status);
            }

            let state = &self.values.primitive_files[&file];

            state.enums[&id]?;

            return state
                .members
                .get(&member.node_id())
                .cloned()
                .unwrap_or(Err(Failure::UncertifiedReference));
        }

        let (file, initializer) = self
            .stable_initializer_of(declaration)
            .ok_or(Failure::UncertifiedReference)?;

        self.known_value_at(file, initializer, depth).value
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn collection_size_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Size {
        self.collection_size_at(file, e, 0)
    }

    pub(crate) fn iterable_size_at(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        depth: usize,
    ) -> Size {
        if depth > MAXIMUM_PRODUCED_DEPTH || !self.charge_work(Event::SizeStep, 1) {
            return Size::unresolved();
        }

        let iteration = self.iteration_of(file, expression, false);

        if self.has_native_iteration(file, expression, &iteration) {
            return self.collection_size_at(file, expression, depth + 1);
        }

        match self.iteration_count_at(file, expression, &iteration, depth + 1) {
            Some(count) => Size {
                exceeds: true,
                element_resolved: false,
                ..Size::sized(count)
            },
            None => Size::unresolved(),
        }
    }

    pub(crate) fn produced_size_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Size> {
        self.produced_size_at(file, e, 0)
    }

    pub(crate) fn collection_size_at(
        &mut self,
        file: FileId,
        e: &'a Expression<'a>,
        depth: usize,
    ) -> Size {
        match self.produced_size_at(file, e, depth) {
            Some(size) => size,
            None => self.input_size_of(file, e),
        }
    }

    fn input_size_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Size {
        let length = match self.is_constant_sized(file, e) {
            true => Cost::ONE,
            false => self.parameter_size_of(file, e).unwrap_or(Cost::N),
        };
        let element = match self.has_primitive_elements(file, e) {
            true => Cost::ONE,
            false => Cost::N,
        };

        Size {
            element,
            ..Size::sized(length)
        }
    }

    fn produced_size_at(
        &mut self,
        file: FileId,
        e: &'a Expression<'a>,
        depth: usize,
    ) -> Option<Size> {
        if depth > MAXIMUM_PRODUCED_DEPTH || !self.charge_work(Event::SizeStep, 1) {
            return Some(Size::unresolved());
        }

        match unwrap(e) {
            Expression::ArrayExpression(array) => Some(self.literal_size_of(file, array, depth)),
            Expression::ConditionalExpression(conditional) => {
                let consequent = self.produced_size_at(file, &conditional.consequent, depth + 1);
                let alternate = self.produced_size_at(file, &conditional.alternate, depth + 1);

                if consequent.is_none() && alternate.is_none() {
                    return None;
                }

                let consequent = match consequent {
                    Some(size) => size,
                    None => self.input_size_of(file, &conditional.consequent),
                };
                let alternate = match alternate {
                    Some(size) => size,
                    None => self.input_size_of(file, &conditional.alternate),
                };

                Some(consequent.combined(&alternate))
            }
            Expression::NewExpression(new) => {
                if self.intrinsic_replaced_of(file, &new.callee) {
                    return None;
                }

                let model = self.construction_model_of(file, new)?;
                let site = self.construction_site_of(file, new);

                self.output_size_of(&site, model, depth)
            }
            Expression::CallExpression(call) => self.call_size_of(file, call, depth),
            Expression::Identifier(reference) => self.holder_size_of(file, reference, depth),
            _ => None,
        }
    }

    fn literal_size_of(
        &mut self,
        file: FileId,
        array: &'a ArrayExpression<'a>,
        depth: usize,
    ) -> Size {
        let mut size = Size::constant();

        for element in &array.elements {
            let part = match element {
                ArrayExpressionElement::SpreadElement(spread) => {
                    self.iterable_size_at(file, &spread.argument, depth + 1)
                }
                ArrayExpressionElement::Elision(_) => continue,
                element => self.element_size_of(file, element.as_expression(), depth),
            };

            size = size.combined(&part);
        }

        size
    }

    fn element_size_of(
        &mut self,
        file: FileId,
        element: Option<&'a Expression<'a>>,
        depth: usize,
    ) -> Size {
        match element {
            Some(element) => {
                Size::constant().containing(&self.collection_size_at(file, element, depth + 1))
            }
            None => Size::unresolved(),
        }
    }

    fn holder_size_of(
        &mut self,
        file: FileId,
        reference: &'a IdentifierReference<'a>,
        depth: usize,
    ) -> Option<Size> {
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference)?;

        if !matches!(declaration, Declaration::Variable { .. }) {
            return None;
        }

        let (target, initializer) = constant_initializer_of(declaration)?;
        let held = initializer.node_id();
        let produced = self.produced_size_at(target, initializer, depth + 1);
        let primitive = produced.is_some() && self.is_primitive_operand(target, initializer);

        match self.holder_growth_of(declaration, primitive) {
            sizes::Growth::Stable => produced,
            sizes::Growth::Unstable => None,
            sizes::Growth::Sites { calls, open } => {
                let mut size = match produced {
                    Some(size) => size,
                    None => self.input_size_of(target, initializer),
                };

                for call in calls {
                    let grown = self.growth_size_of(target, call, held, depth);

                    size = size.combined(&grown);
                }

                Some(match open {
                    true => size.unresolved_length(),
                    false => size,
                })
            }
        }
    }

    fn growth_size_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        held: NodeId,
        depth: usize,
    ) -> Size {
        let mut increment = Size::constant();

        for argument in &call.arguments {
            let part = match argument {
                Argument::SpreadElement(spread) => {
                    self.iterable_size_at(file, &spread.argument, depth + 1)
                }
                argument => self.element_size_of(file, argument.as_expression(), depth),
            };

            increment = increment.combined(&part);
        }

        match self.growth_visits_of(file, call.node_id(), held, depth) {
            Some(visits) => increment.repeated(&visits),
            None => increment.unresolved_length(),
        }
    }

    fn growth_visits_of(
        &mut self,
        file: FileId,
        site: NodeId,
        held: NodeId,
        depth: usize,
    ) -> Option<Size> {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let enclosing: std::collections::HashSet<NodeId> = nodes
            .ancestors(held)
            .map(|ancestor| ancestor.id())
            .collect();
        let mut visits = Size::constant();

        for ancestor in nodes.ancestors(site) {
            if enclosing.contains(&ancestor.id()) {
                break;
            }

            if !is_iteration_kind(&ancestor.kind()) {
                continue;
            }

            let factor = self.bound_of(file, ancestor.kind()).factor()?.clone();
            let produced = match ancestor.kind() {
                AstKind::ForOfStatement(statement) => {
                    self.produced_size_at(file, &statement.right, depth + 1)
                }
                _ => None,
            };

            visits = match produced {
                Some(size) if !size.length_resolved => return None,
                Some(size) if size.exceeds => visits.repeated(&size),
                _ => visits.repeated(&Size::sized(factor)),
            };
        }

        visits.length_resolved.then_some(visits)
    }

    pub(crate) fn count_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Cost> {
        if self.is_numeric_constant(file, e) {
            return Some(Cost::ONE);
        }

        if let Some(size) = self.parameter_size_of(file, e) {
            return Some(size);
        }

        match unwrap(e) {
            Expression::StaticMemberExpression(member) if member.property.name == "length" => {
                let size = self.collection_size_of(file, &member.object);

                size.length_resolved.then_some(size.length)
            }
            _ => None,
        }
    }

    pub(crate) fn result_size_of(
        &mut self,
        file: FileId,
        callback: Option<&'a Argument<'a>>,
        element: &Cost,
        depth: usize,
    ) -> Size {
        let Some(callback) = callback.and_then(Argument::as_expression) else {
            return Size::unresolved();
        };

        if depth > MAXIMUM_PRODUCED_DEPTH {
            return Size::unresolved();
        }

        let targets = self.callable_targets_of(file, callback);

        if targets.open || targets.known.is_empty() {
            return Size::unresolved();
        }

        let mut size: Option<Size> = None;

        for target in targets.known {
            let function = self.function_at(target);
            let deferred = match function {
                FunctionNode::Function(function) => function.r#async || function.generator,
                FunctionNode::Arrow(arrow) => arrow.r#async,
                FunctionNode::Construction(_) => false,
            };
            let returned = match deferred {
                true => Vec::new(),
                false => self.returned_expressions_of(target),
            };
            let mut found = Size::constant();

            for expression in returned {
                let part = if is_first_parameter(
                    self.project.file(target.file).semantic.scoping(),
                    function,
                    expression,
                ) {
                    Size::sized(element.clone())
                } else if self.is_primitive_operand(target.file, expression) {
                    Size::constant()
                } else {
                    self.collection_size_at(target.file, expression, depth + 1)
                };

                found = found.combined(&part);
            }

            size = Some(match size {
                Some(size) => size.combined(&found),
                None => found,
            });
        }

        size.unwrap_or_else(Size::unresolved)
    }

    fn parameter_size_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Cost> {
        let Expression::Identifier(reference) = unwrap(e) else {
            return None;
        };
        let declaration = self
            .declarations
            .of_reference(self.project, file, reference)?;
        let binding = self.parameter_binding_of(declaration)?;

        if !self.is_parameter_unwritten(binding) {
            return None;
        }

        self.current_substitutions.get(&binding)?.value.size.clone()
    }

    pub(crate) fn array_method_size_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        receiver: &'a Expression<'a>,
        method: &str,
        depth: usize,
    ) -> Option<Size> {
        let source = self.collection_size_at(file, receiver, depth + 1);

        match method {
            "map" => {
                let result =
                    self.result_size_of(file, call.arguments.first(), &source.element, depth + 1);

                Some(source.containing(&result))
            }
            "toSpliced" => {
                let mut size = source;

                for argument in call.arguments.iter().skip(2) {
                    let part = match argument {
                        Argument::SpreadElement(spread) => {
                            self.iterable_size_at(file, &spread.argument, depth + 1)
                        }
                        _ => Size::constant(),
                    };

                    size = size.combined(&part);
                }

                Some(size)
            }
            method if PRESERVING_METHODS.contains(&method) => Some(source),
            _ => None,
        }
    }
}

fn is_first_parameter(
    scoping: &oxc_semantic::Scoping,
    function: FunctionNode<'_>,
    expression: &Expression<'_>,
) -> bool {
    let parameters = match function {
        FunctionNode::Function(function) => &function.params,
        FunctionNode::Arrow(arrow) => &arrow.params,
        FunctionNode::Construction(_) => return false,
    };
    let Some(BindingPattern::BindingIdentifier(first)) =
        parameters.items.first().map(|parameter| &parameter.pattern)
    else {
        return false;
    };
    let Expression::Identifier(reference) = unwrap(expression) else {
        return false;
    };

    reference
        .reference_id
        .get()
        .and_then(|id| scoping.get_reference(id).symbol_id())
        .is_some_and(|symbol| first.symbol_id.get() == Some(symbol))
}

fn reassigns_key(class: &Class<'_>, key: &str) -> bool {
    class.body.body.iter().any(|element| {
        let kinds = match element {
            ClassElement::MethodDefinition(method) => match &method.value.body {
                Some(body) => Subtree::of(Root::Body(body), false, false),
                None => Vec::new(),
            },
            ClassElement::PropertyDefinition(property) => match &property.value {
                Some(value) => Subtree::of(Root::Expression(value), false, false),
                None => Vec::new(),
            },
            ClassElement::StaticBlock(block) => block
                .body
                .iter()
                .flat_map(|statement| Subtree::of(Root::Statement(statement), false, false))
                .collect(),
            _ => Vec::new(),
        };

        kinds.into_iter().any(|kind| writes_key(kind, key))
    })
}

fn writes_key(kind: AstKind<'_>, key: &str) -> bool {
    let target = match kind {
        AstKind::AssignmentExpression(assignment) => assignment.left.as_simple_assignment_target(),
        AstKind::UpdateExpression(update) => Some(&update.argument),
        AstKind::UnaryExpression(unary) if unary.operator == UnaryOperator::Delete => {
            return member_expression_of(unwrap(&unary.argument))
                .is_some_and(|member| member.static_property_name().is_none_or(|name| name == key))
        }
        _ => return false,
    };

    match target {
        Some(SimpleAssignmentTarget::ComputedMemberExpression(member)) => {
            member.static_property_name().is_none_or(|name| name == key)
        }
        Some(SimpleAssignmentTarget::StaticMemberExpression(member)) => member.property.name == key,
        Some(SimpleAssignmentTarget::PrivateFieldExpression(member)) => member.field.name == key,
        _ => false,
    }
}

#[cfg(test)]
#[path = "values.test.rs"]
mod tests;

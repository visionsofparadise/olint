use std::collections::HashMap;
use std::rc::Rc;

use oxc_allocator::GetAddress;
use oxc_ast::ast::{Expression, MemberExpression};
use oxc_ast::AstKind;
use oxc_semantic::{NodeId, Semantic};
use oxc_syntax::operator::{LogicalOperator, UnaryOperator};

use crate::analysis::Analysis;
use crate::constants::{constant_initializer_of, evaluate_enum};
use crate::declarations::Declaration;
use crate::project::FileId;
use crate::syntax::member_expression_of;
use crate::unknowns::UnknownReason;

#[path = "primitive_values.rs"]
mod primitive;
pub use primitive::{
    CertifiedValues, Failure, Limits, Primitive, PrimitiveAdapter, ValueResult, Work,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgumentFacts {
    pub value: ValueFacts,
    pub callback: Option<Part>,
    pub preference: Preference,
}

#[derive(Default)]
pub struct Values {
    origins: HashMap<SourceSpan, ValueId>,
    allocations: std::collections::HashSet<ValueId>,
    callbacks: HashMap<usize, ValueId>,
    next_value: u32,
    quantities: HashMap<(ValueId, SizeQuantity), u64>,
    labels: Vec<String>,
    primitive_limits: Limits,
    primitive_files: HashMap<FileId, PrimitiveFile>,
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

        self.labels
            .get(id as usize)
            .cloned()
            .unwrap_or_else(|| format!("size_{id}"))
    }

    pub fn write_label(&self, id: u64, out: &mut dyn std::fmt::Write) -> std::fmt::Result {
        if id == u64::MAX {
            return out.write_str("N");
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

    pub fn allocation(&mut self, origin: SourceSpan) -> ValueFacts {
        let facts = self.at(origin);

        self.allocations.insert(facts.value);

        facts
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
            if let Some((target, initializer)) = self
                .declarations
                .of_reference(self.project, file, reference)
                .and_then(constant_initializer_of)
            {
                return self.primitive_length(target, initializer, depth + 1);
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

        let (file, initializer) =
            constant_initializer_of(declaration).ok_or(Failure::UncertifiedReference)?;

        self.known_value_at(file, initializer, depth).value
    }
}

#[cfg(test)]
#[path = "values.test.rs"]
mod tests;

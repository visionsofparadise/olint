use std::{borrow::Cow, collections::HashMap};

use oxc_allocator::{Address, Allocator, GetAddress, GetAllocator};
use oxc_ast::{
    ast::*,
    builder::{AstBuilder, GetAstBuilder},
};
use oxc_ecmascript::{
    constant_evaluation::{
        binary_operation_evaluate_value, ConstantEvaluation, ConstantEvaluationCtx,
    },
    side_effects::{MayHaveSideEffectsContext, PropertyReadSideEffects},
    ConstantValue, GlobalContext, ToBoolean, ToJsString,
};
use oxc_semantic::{NodeId, Semantic, SymbolId};
use oxc_span::SPAN;

pub type Primitive = ConstantValue<'static>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Failure {
    Unsupported,
    UncertifiedReference,
    LoneSurrogate,
    NodeLimit,
    DepthLimit,
    PayloadLimit,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub nodes: usize,
    pub depth: usize,
    pub value_bytes: usize,
    pub cumulative_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            nodes: 4096,
            depth: 64,
            value_bytes: 16384,
            cumulative_bytes: 1_048_576,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Work {
    pub node_visits: usize,
    pub reserved_bytes: usize,
    pub primitive_operations: usize,
}

#[derive(Clone, Debug)]
pub struct ValueResult {
    pub evaluation: NodeId,
    pub value: Result<Primitive, Failure>,
}

pub struct CertifiedValues<'s, 'a> {
    semantic: &'s Semantic<'a>,
    pub symbols: HashMap<SymbolId, Primitive>,
    pub members: HashMap<(SymbolId, String), SymbolId>,
}

impl<'s, 'a> CertifiedValues<'s, 'a> {
    pub fn new(semantic: &'s Semantic<'a>) -> Self {
        Self {
            semantic,
            symbols: HashMap::new(),
            members: HashMap::new(),
        }
    }
}

pub struct PrimitiveAdapter<'s, 'a> {
    semantic: &'s Semantic<'a>,
    limits: Limits,
    pub work: Work,
}

struct Operation<'a> {
    builder: AstBuilder<'a>,
}

fn owned(value: ConstantValue<'_>) -> Primitive {
    match value {
        ConstantValue::String(value) => ConstantValue::String(Cow::Owned(value.into_owned())),
        ConstantValue::Number(value) => ConstantValue::Number(value),
        ConstantValue::BigInt(value) => ConstantValue::BigInt(value),
        ConstantValue::Boolean(value) => ConstantValue::Boolean(value),
        ConstantValue::Null => ConstantValue::Null,
        ConstantValue::Undefined => ConstantValue::Undefined,
    }
}

impl<'a> GetAllocator<'a> for Operation<'a> {
    fn allocator(&self) -> &'a Allocator {
        self.builder.allocator()
    }
}
impl<'a> GetAstBuilder<'a> for Operation<'a> {
    type Builder = AstBuilder<'a>;
    fn builder(&self) -> &Self::Builder {
        &self.builder
    }
}
impl<'a> GlobalContext<'a> for Operation<'a> {
    fn is_global_reference(&self, _: &IdentifierReference<'a>) -> bool {
        false
    }
}
impl<'a> MayHaveSideEffectsContext<'a> for Operation<'a> {
    fn annotations(&self) -> bool {
        false
    }
    fn manual_pure_functions(&self, _: &Expression) -> bool {
        false
    }
    fn property_read_side_effects(&self) -> PropertyReadSideEffects {
        PropertyReadSideEffects::All
    }
    fn unknown_global_side_effects(&self) -> bool {
        true
    }
}
impl<'a> ConstantEvaluationCtx<'a> for Operation<'a> {}

fn payload(value: &Primitive) -> usize {
    match value {
        ConstantValue::String(value) => value.len(),
        ConstantValue::BigInt(value) => usize::try_from(value.bits()).unwrap_or(usize::MAX),
        _ => 32,
    }
}

impl<'s, 'a> PrimitiveAdapter<'s, 'a> {
    pub(crate) fn owns_semantic(&self, semantic: &Semantic<'a>) -> bool {
        std::ptr::eq(self.semantic, semantic)
    }

    pub(crate) fn owns_node(&self, node: NodeId, address: Address) -> bool {
        node.index() < self.semantic.nodes().len()
            && self.semantic.nodes().kind(node).address() == address
    }
    pub fn new(semantic: &'s Semantic<'a>, limits: Limits) -> Self {
        Self {
            semantic,
            limits,
            work: Work::default(),
        }
    }

    pub(crate) fn visit_container(&mut self) -> Result<(), Failure> {
        if self.work.node_visits >= self.limits.nodes {
            return Err(Failure::NodeLimit);
        }

        self.work.node_visits += 1;

        Ok(())
    }

    pub(crate) fn reserve_name(&mut self, length: usize) -> Result<(), Failure> {
        self.reserve(length)
    }
    pub(crate) fn copy_value(&mut self, value: &Primitive) -> Result<Primitive, Failure> {
        self.copy(value)
    }

    pub(crate) fn closed_initializer(
        &mut self,
        expression: &Expression<'a>,
    ) -> Result<bool, Failure> {
        match self.closed_inner(expression, 0) {
            Ok(()) => Ok(true),
            Err(Failure::Unsupported) => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn closed_inner(&mut self, expression: &Expression<'a>, depth: usize) -> Result<(), Failure> {
        if depth >= self.limits.depth {
            return Err(Failure::DepthLimit);
        }

        self.visit_container()?;

        match expression {
            Expression::NumericLiteral(_)
            | Expression::StringLiteral(_)
            | Expression::BigIntLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::NullLiteral(_)
            | Expression::Identifier(_) => Ok(()),
            Expression::ParenthesizedExpression(value) => {
                self.closed_inner(&value.expression, depth + 1)
            }
            Expression::TSAsExpression(value) => self.closed_inner(&value.expression, depth + 1),
            Expression::TSSatisfiesExpression(value) => {
                self.closed_inner(&value.expression, depth + 1)
            }
            Expression::TSTypeAssertion(value) => self.closed_inner(&value.expression, depth + 1),
            Expression::TSNonNullExpression(value) => {
                self.closed_inner(&value.expression, depth + 1)
            }
            Expression::TSInstantiationExpression(value) => {
                self.closed_inner(&value.expression, depth + 1)
            }
            Expression::UnaryExpression(value) if value.operator != UnaryOperator::Delete => {
                self.closed_inner(&value.argument, depth + 1)
            }
            Expression::BinaryExpression(value) => {
                self.closed_inner(&value.left, depth + 1)?;

                self.closed_inner(&value.right, depth + 1)
            }
            Expression::StaticMemberExpression(value) => {
                self.closed_inner(&value.object, depth + 1)
            }
            Expression::ComputedMemberExpression(value) => {
                self.closed_inner(&value.object, depth + 1)?;

                self.closed_inner(&value.expression, depth + 1)
            }
            _ => Err(Failure::Unsupported),
        }
    }

    fn reserve(&mut self, result_bound: usize) -> Result<(), Failure> {
        if result_bound > self.limits.value_bytes {
            return Err(Failure::PayloadLimit);
        }

        let reservation = result_bound.checked_mul(16).ok_or(Failure::PayloadLimit)?;
        let total = self
            .work
            .reserved_bytes
            .checked_add(reservation)
            .ok_or(Failure::PayloadLimit)?;

        if total > self.limits.cumulative_bytes {
            return Err(Failure::PayloadLimit);
        }

        self.work.reserved_bytes = total;

        Ok(())
    }

    pub fn evaluate(
        &mut self,
        expression: &Expression<'a>,
        certified: &CertifiedValues<'_, 'a>,
    ) -> ValueResult {
        ValueResult {
            evaluation: expression.node_id(),
            value: if self.owns_semantic(certified.semantic)
                && self.owns_node(expression.node_id(), expression.address())
            {
                self.evaluate_inner(expression, certified, 0)
            } else {
                Err(Failure::UncertifiedReference)
            },
        }
    }

    fn copy(&mut self, value: &Primitive) -> Result<Primitive, Failure> {
        self.reserve(payload(value))?;

        Ok(value.clone())
    }

    fn symbol_of(&self, identifier: &IdentifierReference<'a>) -> Option<SymbolId> {
        identifier
            .reference_id
            .get()
            .and_then(|id| self.semantic.scoping().get_reference(id).symbol_id())
    }

    fn evaluate_inner(
        &mut self,
        expression: &Expression<'a>,
        certified: &CertifiedValues<'_, 'a>,
        depth: usize,
    ) -> Result<Primitive, Failure> {
        if depth >= self.limits.depth {
            return Err(Failure::DepthLimit);
        }

        if self.work.node_visits >= self.limits.nodes {
            return Err(Failure::NodeLimit);
        }

        self.work.node_visits += 1;
        let next = depth + 1;

        match expression {
            Expression::ParenthesizedExpression(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::TSAsExpression(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::TSSatisfiesExpression(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::TSTypeAssertion(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::TSNonNullExpression(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::TSInstantiationExpression(value) => {
                self.evaluate_inner(&value.expression, certified, next)
            }
            Expression::NumericLiteral(value) => Ok(ConstantValue::Number(value.value)),
            Expression::BooleanLiteral(value) => Ok(ConstantValue::Boolean(value.value)),
            Expression::NullLiteral(_) => Ok(ConstantValue::Null),
            Expression::StringLiteral(value) => {
                if value.lone_surrogates {
                    return Err(Failure::LoneSurrogate);
                }

                self.reserve(value.value.len())?;

                Ok(ConstantValue::String(Cow::Owned(value.value.to_string())))
            }
            Expression::BigIntLiteral(value) => {
                self.reserve(
                    value
                        .value
                        .len()
                        .checked_mul(4)
                        .ok_or(Failure::PayloadLimit)?,
                )?;

                let allocator = Allocator::default();
                let context = Operation {
                    builder: AstBuilder::new(&allocator),
                };

                expression
                    .evaluate_value(&context)
                    .map(owned)
                    .ok_or(Failure::Unsupported)
            }
            Expression::Identifier(identifier) => {
                let symbol = self
                    .symbol_of(identifier)
                    .ok_or(Failure::UncertifiedReference)?;

                self.copy(
                    certified
                        .symbols
                        .get(&symbol)
                        .ok_or(Failure::UncertifiedReference)?,
                )
            }
            Expression::UnaryExpression(value) if value.operator == UnaryOperator::Void => {
                Ok(ConstantValue::Undefined)
            }
            Expression::UnaryExpression(value) => {
                let argument = self.evaluate_inner(&value.argument, certified, next)?;

                self.unary(value.operator, argument)
            }
            Expression::BinaryExpression(value) => {
                let left = self.evaluate_inner(&value.left, certified, next)?;
                let right = self.evaluate_inner(&value.right, certified, next)?;

                self.binary(value.operator, left, right)
            }
            Expression::SequenceExpression(value) => self.evaluate_inner(
                value.expressions.last().ok_or(Failure::Unsupported)?,
                certified,
                next,
            ),
            Expression::LogicalExpression(value) => {
                let left = self.evaluate_inner(&value.left, certified, next)?;
                let take = match value.operator {
                    LogicalOperator::Coalesce => {
                        matches!(left, ConstantValue::Null | ConstantValue::Undefined)
                    }
                    LogicalOperator::And => truthy(&left),
                    LogicalOperator::Or => !truthy(&left),
                };

                if take {
                    self.evaluate_inner(&value.right, certified, next)
                } else {
                    Ok(left)
                }
            }
            Expression::StaticMemberExpression(value) => {
                self.member(&value.object, value.property.name.as_str(), certified, next)
            }
            Expression::ComputedMemberExpression(value) => {
                let key = self.evaluate_inner(&value.expression, certified, next)?;
                let key = self.property_key(&key)?;

                self.member(&value.object, &key, certified, next)
            }
            _ => Err(Failure::Unsupported),
        }
    }

    fn member(
        &mut self,
        object: &Expression<'a>,
        key: &str,
        certified: &CertifiedValues<'_, 'a>,
        depth: usize,
    ) -> Result<Primitive, Failure> {
        if let Expression::Identifier(identifier) = object {
            if let Some(symbol) = self.symbol_of(identifier) {
                self.reserve(key.len())?;

                if let Some(member) = certified.members.get(&(symbol, key.to_owned())) {
                    return self.copy(
                        certified
                            .symbols
                            .get(member)
                            .ok_or(Failure::UncertifiedReference)?,
                    );
                }
            }
        }

        if key == "length" {
            if let ConstantValue::String(value) = self.evaluate_inner(object, certified, depth)? {
                return Ok(ConstantValue::Number(value.encode_utf16().count() as f64));
            }
        }

        Err(Failure::Unsupported)
    }

    pub(crate) fn unary(
        &mut self,
        operator: UnaryOperator,
        value: Primitive,
    ) -> Result<Primitive, Failure> {
        if operator == UnaryOperator::Delete {
            return Err(Failure::Unsupported);
        }

        self.reserve(payload(&value).saturating_add(32))?;

        self.work.primitive_operations += 1;
        let allocator = Allocator::default();
        let context = Operation {
            builder: AstBuilder::new(&allocator),
        };
        let argument = literal(&value, &context);
        let expression = Expression::new_unary_expression(SPAN, operator, argument, &context);

        expression
            .evaluate_value(&context)
            .map(owned)
            .ok_or(Failure::Unsupported)
    }

    pub(crate) fn binary(
        &mut self,
        operator: BinaryOperator,
        left: Primitive,
        right: Primitive,
    ) -> Result<Primitive, Failure> {
        if matches!(operator, BinaryOperator::In | BinaryOperator::Instanceof) {
            return Err(Failure::Unsupported);
        }

        self.reserve(
            payload(&left)
                .saturating_add(payload(&right))
                .saturating_add(64),
        )?;

        self.work.primitive_operations += 1;
        let allocator = Allocator::default();
        let context = Operation {
            builder: AstBuilder::new(&allocator),
        };
        let left = literal(&left, &context);
        let right = literal(&right, &context);

        binary_operation_evaluate_value(operator, &left, &right, &context)
            .map(owned)
            .ok_or(Failure::Unsupported)
    }

    pub fn property_key(&mut self, value: &Primitive) -> Result<String, Failure> {
        self.reserve(payload(value).saturating_add(32))?;

        let allocator = Allocator::default();
        let context = Operation {
            builder: AstBuilder::new(&allocator),
        };

        value
            .to_js_string(&context)
            .map(Cow::into_owned)
            .ok_or(Failure::Unsupported)
    }
}

fn literal<'a>(value: &Primitive, context: &Operation<'a>) -> Expression<'a> {
    match value {
        ConstantValue::Number(value) => {
            Expression::new_numeric_literal(SPAN, *value, None, NumberBase::Float, context)
        }
        ConstantValue::String(value) => Expression::new_string_literal(
            SPAN,
            context.allocator().alloc_str(value),
            None,
            context,
        ),
        ConstantValue::BigInt(value) => Expression::new_big_int_literal(
            SPAN,
            context.allocator().alloc_str(&value.to_string()),
            None,
            BigintBase::Decimal,
            context,
        ),
        ConstantValue::Boolean(value) => Expression::new_boolean_literal(SPAN, *value, context),
        ConstantValue::Null => Expression::new_null_literal(SPAN, context),
        ConstantValue::Undefined => Expression::new_unary_expression(
            SPAN,
            UnaryOperator::Void,
            Expression::new_numeric_literal(SPAN, 0.0, None, NumberBase::Decimal, context),
            context,
        ),
    }
}

pub(crate) fn truthy(value: &Primitive) -> bool {
    let allocator = Allocator::default();
    let context = Operation {
        builder: AstBuilder::new(&allocator),
    };

    value.to_boolean(&context).expect("primitive truth value")
}

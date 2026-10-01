use crate::derivation::{DerivationArena, DerivationId};
use crate::flow::Completion;
use crate::project::Site;
use crate::trace::{TraceArena, TraceId};
use crate::unknowns::{SourceSpan, UnknownId, UnknownReason, Unknowns};

use std::collections::BTreeMap;
use std::sync::Arc;

const MAX_DEPTH: usize = 64;
const MAX_PARSE_DEPTH: usize = MAX_DEPTH * 8;
const MAX_NODES: usize = 4096;
const MAX_PARSE_NODES: usize = MAX_NODES * 4;
const MAX_TEXT: usize = 65536;
const MAX_REDUCED_TERMS: usize = MAX_DEPTH;
const PROOF_CREDITS_PER_NODE: usize = MAX_NODES * MAX_DEPTH * 32;
const COMPARISON_CREDITS: usize = PROOF_CREDITS_PER_NODE * 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Domain {
    PositiveReal,
    Size,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Expression {
    Constant(u64),
    LegacyN,
    LegacyLog,
    LegacyNLog,
    Name(Arc<str>),
    Dimension { id: u64, domain: Domain },
    Sum(Arc<[Expression]>),
    Product(Arc<[Expression]>),
    Maximum(Arc<[Expression]>),
    Log(Arc<Expression>),
    Power(Arc<Expression>, Arc<Expression>),
    Ratio(Arc<Expression>, Arc<Expression>),
    Factorial(Arc<Expression>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CostComparison {
    Within,
    Exceeds,
    Inconclusive,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CostError {
    Syntax(usize),
    Overflow,
    Resource,
    Domain,
    UnknownName(String),
    UnresolvedQuantity(String),
    InvalidRoot,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Cost(Expression);
impl Default for Cost {
    fn default() -> Self {
        Self::ONE
    }
}
impl Cost {
    pub const ONE: Self = Self(Expression::ONE);
    pub const N: Self = Self(Expression::N);
    pub const LOG: Self = Self(Expression::LOG);
    pub const N_LOG_N: Self = Self(Expression::N_LOG_N);
    pub fn constant(value: u64) -> Self {
        Self(Expression::Constant(value))
    }
    pub fn dimension(id: u64, domain: Domain) -> Self {
        Self(Expression::dimension(id, domain))
    }
    pub fn is_one(&self) -> bool {
        self.0.is_one()
    }
    /// Whether the cost is a logarithm of one quantity.
    pub fn is_logarithm(&self) -> bool {
        matches!(self.0, Expression::Log(_) | Expression::LegacyLog)
    }
    pub(crate) fn has_polynomial_log_growth(&self, envelope: &Self) -> bool {
        envelope_growth(&self.0, &envelope.0)
            .is_some_and(|(polynomial, logarithmic)| polynomial >= 1 && logarithmic >= 1)
    }
    pub fn multiply(&self, other: &Self) -> Result<Self, CostError> {
        self.0.multiply(&other.0).map(Self)
    }
    pub fn sum(values: Vec<Self>) -> Result<Self, CostError> {
        Expression::sum(values.into_iter().map(|value| value.0).collect()).map(Self)
    }
    pub fn product(values: Vec<Self>) -> Result<Self, CostError> {
        Expression::product(values.into_iter().map(|value| value.0).collect()).map(Self)
    }
    pub fn maximum(values: Vec<Self>) -> Result<Self, CostError> {
        Expression::maximum(values.into_iter().map(|value| value.0).collect()).map(Self)
    }
    pub fn power(base: Self, exponent: Self) -> Result<Self, CostError> {
        Expression::power(base.0, exponent.0).map(Self)
    }
    pub fn ratio(numerator: Self, denominator: Self) -> Result<Self, CostError> {
        Expression::ratio(numerator.0, denominator.0).map(Self)
    }
    pub fn logarithm(argument: Self) -> Result<Self, CostError> {
        Expression::logarithm(argument.0).map(Self)
    }
    pub fn factorial(argument: Self) -> Result<Self, CostError> {
        Expression::factorial(argument.0).map(Self)
    }
    pub fn parse(text: &str) -> Result<Self, CostError> {
        Expression::parse(text).map(Self)
    }
    pub fn bind(
        &self,
        resolve: &impl Fn(&str) -> Option<Self>,
        roots: &[Self],
    ) -> Result<Self, CostError> {
        let roots: Vec<_> = roots.iter().map(|value| value.0.clone()).collect();

        self.0
            .bind(&|name| resolve(name).map(|value| value.0), &roots)
            .map(Self)
    }
    pub fn compare(&self, limit: &Self) -> CostComparison {
        self.0.compare(&limit.0)
    }
    pub fn text(&self) -> String {
        self.0.text()
    }
    pub fn text_with(&self, name: &impl Fn(u64) -> String) -> String {
        self.0.text_with(name)
    }
    pub fn write_with(
        &self,
        out: &mut dyn std::fmt::Write,
        full: bool,
        name: &impl Fn(u64, &mut dyn std::fmt::Write) -> std::fmt::Result,
    ) -> std::fmt::Result {
        if full {
            out.write_str("O(")?;
        }

        if self.0.check_budget().is_err() {
            out.write_str("unknown")?;
        } else {
            self.0.write_inner(out, name)?;
        }

        if full {
            out.write_char(')')?;
        }

        Ok(())
    }
    pub fn structural_key(&self) -> String {
        self.0.structural_key()
    }

    pub(crate) fn constant_of(&self) -> Option<u64> {
        match self.0 {
            Expression::Constant(value) => Some(value),
            _ => None,
        }
    }

    pub(crate) fn mentions_dimension_from(&self, floor: u64) -> bool {
        self.0.mentions_dimension_from(floor)
    }

    pub(crate) fn split_dimension(&self, id: u64) -> Option<(Self, Option<Self>)> {
        let (local, factor) = self.0.split_dimension(id, 0)?;

        Some((Self(local), factor.map(Self)))
    }

    pub(crate) fn names(&self) -> Vec<String> {
        let mut names = std::collections::BTreeSet::new();
        let mut pending = vec![&self.0];

        while let Some(value) = pending.pop() {
            if let Expression::Name(name) = value {
                names.insert(name.to_string());
            }

            pending.extend(value.children());
        }

        names.into_iter().collect()
    }

    pub(crate) fn compare_legacy(&self, limit: &Self) -> CostComparison {
        let mut pending = vec![&self.0, &limit.0];

        while let Some(expression) = pending.pop() {
            if matches!(
                expression,
                Expression::Name(_) | Expression::Dimension { .. }
            ) {
                return self.compare(limit);
            }

            pending.extend(expression.children());
        }

        let roots = [Self::dimension(u64::MAX, Domain::Size)];

        match (self.bind(&|_| None, &roots), limit.bind(&|_| None, &roots)) {
            (Ok(cost), Ok(limit)) => cost.compare(&limit),
            _ => CostComparison::Inconclusive,
        }
    }
}

impl Default for Expression {
    fn default() -> Self {
        Self::ONE
    }
}

impl Expression {
    fn children(&self) -> impl Iterator<Item = &Self> {
        let (values, left, right): (&[Self], Option<&Self>, Option<&Self>) = match self {
            Self::Sum(values) | Self::Product(values) | Self::Maximum(values) => {
                (values, None, None)
            }
            Self::Log(value) | Self::Factorial(value) => (&[], Some(value), None),
            Self::Power(left, right) | Self::Ratio(left, right) => (&[], Some(left), Some(right)),
            _ => (&[], None, None),
        };

        values.iter().chain(left).chain(right)
    }

    pub const ONE: Self = Self::Constant(1);
    pub const N: Self = Self::LegacyN;
    pub const LOG: Self = Self::LegacyLog;
    pub const N_LOG_N: Self = Self::LegacyNLog;

    pub fn dimension(id: u64, domain: Domain) -> Self {
        Self::Dimension { id, domain }
    }
    pub fn is_one(&self) -> bool {
        matches!(self, Self::Constant(1))
    }
    pub fn multiply(&self, other: &Self) -> Result<Self, CostError> {
        Self::product(vec![self.clone(), other.clone()])
    }
    pub fn sum(values: Vec<Self>) -> Result<Self, CostError> {
        Self::combine(values, 0)
    }
    pub fn product(values: Vec<Self>) -> Result<Self, CostError> {
        Self::combine(values, 1)
    }
    pub fn maximum(values: Vec<Self>) -> Result<Self, CostError> {
        Self::combine(values, 2)
    }

    fn combine(values: Vec<Self>, kind: u8) -> Result<Self, CostError> {
        if values.is_empty() {
            return Err(CostError::Domain);
        }

        let mut output = Vec::new();
        let mut constant = if kind == 1 { 1u64 } else { 0 };
        let mut stack = values;

        while let Some(value) = stack.pop() {
            value.check_budget()?;

            if output.len() + stack.len() > MAX_NODES {
                return Err(CostError::Resource);
            }

            match (&value, kind) {
                (Self::Sum(children), 0)
                | (Self::Product(children), 1)
                | (Self::Maximum(children), 2) => stack.extend(children.iter().cloned()),
                (Self::Constant(number), _) => {
                    constant = match kind {
                        0 => constant.checked_add(*number).ok_or(CostError::Overflow)?,
                        1 => constant.checked_mul(*number).ok_or(CostError::Overflow)?,
                        _ => constant.max(*number),
                    };
                }
                _ => output.push(value),
            }
        }

        if kind == 1 && constant == 0 && output.iter().all(Self::valid) {
            return Ok(Self::Constant(0));
        }

        if constant != if kind == 1 { 1 } else { 0 } || output.is_empty() {
            output.push(Self::Constant(constant));
        }

        output.sort_by_key(Self::structural_key);

        if kind == 1 {
            let mut grouped = Vec::new();
            let mut cursor = 0;

            while cursor < output.len() {
                let mut end = cursor + 1;

                while end < output.len() && output[end] == output[cursor] {
                    end += 1;
                }

                let value = output[cursor].clone();

                grouped.push(if end - cursor == 1 {
                    value
                } else {
                    Self::power(value, Self::Constant((end - cursor) as u64))?
                });

                cursor = end;
            }

            output = grouped;

            output.sort_by_key(Self::structural_key);
        }

        if kind == 2 {
            output.dedup();

            output = undominated_of(output);
        }

        let result = if kind == 1
            && output.len() == 2
            && output.contains(&Self::LegacyN)
            && output.contains(&Self::LegacyLog)
        {
            Self::LegacyNLog
        } else if output.len() == 1 {
            output.remove(0)
        } else {
            match kind {
                0 => Self::Sum(output.into()),
                1 => Self::Product(output.into()),
                _ => Self::Maximum(output.into()),
            }
        };

        result.check_budget()?;

        Ok(result)
    }

    pub fn power(base: Self, exponent: Self) -> Result<Self, CostError> {
        base.check_budget()?;
        exponent.check_budget()?;

        if exponent == Self::Constant(0) && base.positive() {
            return Ok(Self::ONE);
        }

        if exponent.is_one() {
            return Ok(base);
        }

        if let (Self::Constant(base), Self::Constant(exponent)) = (&base, &exponent) {
            if *base == 0 && *exponent == 0 {
                return Err(CostError::Domain);
            }

            let exponent: u32 = (*exponent).try_into().map_err(|_| CostError::Overflow)?;

            return base
                .checked_pow(exponent)
                .map(Self::Constant)
                .ok_or(CostError::Overflow);
        }

        let result = Self::Power(Arc::new(base), Arc::new(exponent));

        result.check_budget()?;

        Ok(result)
    }

    pub fn ratio(numerator: Self, denominator: Self) -> Result<Self, CostError> {
        numerator.check_budget()?;
        denominator.check_budget()?;

        if !denominator.positive() {
            return Err(CostError::Domain);
        }

        if numerator == denominator {
            return Ok(Self::ONE);
        }

        if denominator.is_one() {
            return Ok(numerator);
        }

        let result = Self::Ratio(Arc::new(numerator), Arc::new(denominator));

        result.check_budget()?;

        Ok(result)
    }

    pub fn logarithm(argument: Self) -> Result<Self, CostError> {
        argument.check_budget()?;

        if !argument.positive() {
            return Err(CostError::Domain);
        }

        let result = Self::Log(Arc::new(argument));

        result.check_budget()?;

        Ok(result)
    }

    pub fn factorial(argument: Self) -> Result<Self, CostError> {
        argument.check_budget()?;

        if !argument.integer() {
            return Err(CostError::Domain);
        }

        if let Self::Constant(value) = argument {
            let mut result = 1u64;

            for factor in 2..=value {
                result = result.checked_mul(factor).ok_or(CostError::Overflow)?;
            }

            return Ok(Self::Constant(result));
        }

        let result = Self::Factorial(Arc::new(argument));

        result.check_budget()?;

        Ok(result)
    }

    fn mentions_dimension_where(&self, accept: &impl Fn(u64) -> bool) -> bool {
        let mut pending = vec![self];
        let mut visited = 0usize;

        while let Some(value) = pending.pop() {
            visited += 1;

            if visited > MAX_NODES {
                return true;
            }

            if matches!(value, Self::Dimension { id, .. } if accept(*id)) {
                return true;
            }

            pending.extend(value.children());
        }

        false
    }

    fn mentions_dimension(&self, id: u64) -> bool {
        self.mentions_dimension_where(&|found| found == id)
    }

    fn mentions_dimension_from(&self, floor: u64) -> bool {
        self.mentions_dimension_where(&|found| found >= floor)
    }

    fn split_dimension(&self, id: u64, depth: usize) -> Option<(Self, Option<Self>)> {
        if depth > MAX_DEPTH {
            return None;
        }

        if !self.mentions_dimension(id) {
            return Some((self.clone(), None));
        }

        match self {
            Self::Dimension { .. } => Some((Self::ONE, Some(Self::ONE))),
            Self::Sum(children) | Self::Maximum(children) => {
                let additive = matches!(self, Self::Sum(_));
                let mut locals = Vec::new();
                let mut factors = Vec::new();

                for child in children.iter() {
                    let (local, factor) = child.split_dimension(id, depth + 1)?;

                    locals.push(local);

                    if let Some(factor) = factor {
                        factors.push(factor);
                    }
                }

                let combine = |values| match additive {
                    true => Self::sum(values),
                    false => Self::maximum(values),
                };
                let local = combine(locals).ok()?;
                let factor = match factors.is_empty() {
                    true => None,
                    false => Some(combine(factors).ok()?),
                };

                Some((local, factor))
            }
            Self::Product(children) => {
                let mut constant = Vec::new();
                let mut carrying = None;

                for child in children.iter() {
                    if !child.mentions_dimension(id) {
                        constant.push(child.clone());

                        continue;
                    }

                    if carrying.is_some() {
                        return None;
                    }

                    carrying = Some(child.split_dimension(id, depth + 1)?);
                }

                let (local, factor) = carrying?;
                let factor = factor?;
                let mut local_values = constant.clone();
                let mut factor_values = constant;

                local_values.push(local);
                factor_values.push(factor);

                Some((
                    Self::product(local_values).ok()?,
                    Some(Self::product(factor_values).ok()?),
                ))
            }
            _ => None,
        }
    }

    fn integer(&self) -> bool {
        match self {
            Self::Constant(_)
            | Self::Dimension {
                domain: Domain::Size,
                ..
            } => true,
            Self::Sum(values) | Self::Product(values) | Self::Maximum(values) => {
                values.iter().all(Self::integer)
            }
            Self::Power(base, exponent) => base.integer() && exponent.integer(),
            Self::Factorial(value) => value.integer(),
            _ => false,
        }
    }
    fn positive(&self) -> bool {
        match self {
            Self::Constant(value) => *value > 0,
            Self::Dimension { .. } => true,
            Self::Sum(values) | Self::Maximum(values) => {
                values.iter().all(Self::nonnegative) && values.iter().any(Self::positive)
            }
            Self::Product(values) => values.iter().all(Self::positive),
            Self::Log(value) => value.positive(),
            Self::Power(base, exponent) => base.positive() && exponent.nonnegative(),
            Self::Ratio(a, b) => a.positive() && b.positive(),
            Self::Factorial(value) => value.integer(),
            _ => false,
        }
    }
    fn nonnegative(&self) -> bool {
        matches!(self, Self::Constant(0)) || self.positive()
    }
    fn valid(&self) -> bool {
        match self {
            Self::Name(_) | Self::LegacyN | Self::LegacyLog | Self::LegacyNLog => false,
            Self::Sum(values) | Self::Product(values) | Self::Maximum(values) => {
                !values.is_empty() && values.iter().all(Self::valid)
            }
            Self::Log(value) => value.valid() && value.positive(),
            Self::Power(a, b) => a.valid() && b.valid() && a.positive() && b.nonnegative(),
            Self::Ratio(a, b) => a.valid() && b.valid() && a.nonnegative() && b.positive(),
            Self::Factorial(value) => value.valid() && value.integer(),
            _ => true,
        }
    }

    fn check_budget(&self) -> Result<(), CostError> {
        let mut stack = vec![(self, 0)];
        let mut count = 0;
        let mut text_bytes = 3usize;

        while let Some((value, depth)) = stack.pop() {
            count += 1;

            if depth > MAX_DEPTH || count > MAX_NODES {
                return Err(CostError::Resource);
            }

            let overhead = match value {
                Self::Constant(number) => number.to_string().len(),
                Self::LegacyN => 1,
                Self::LegacyLog => 5,
                Self::LegacyNLog => 7,
                Self::Name(name) => name.len(),
                Self::Dimension { id, .. } => 5 + id.to_string().len(),
                Self::Sum(values) | Self::Product(values) => 2 + 3 * values.len().saturating_sub(1),
                Self::Maximum(values) => 5 + 2 * values.len().saturating_sub(1),
                Self::Log(_) => 5,
                Self::Factorial(_) => 3,
                Self::Power(_, _) => 5,
                Self::Ratio(_, _) => 7,
            };
            text_bytes = text_bytes
                .checked_add(overhead)
                .ok_or(CostError::Resource)?;

            if text_bytes > MAX_TEXT {
                return Err(CostError::Resource);
            }

            match value {
                Self::Sum(children) | Self::Product(children) | Self::Maximum(children) => {
                    stack.extend(children.iter().map(|child| (child, depth + 1)))
                }
                Self::Log(child) | Self::Factorial(child) => stack.push((child, depth + 1)),
                Self::Power(a, b) | Self::Ratio(a, b) => {
                    stack.push((a, depth + 1));
                    stack.push((b, depth + 1));
                }
                _ => {}
            }
        }

        Ok(())
    }

    pub fn bind(
        &self,
        resolve: &impl Fn(&str) -> Option<Self>,
        roots: &[Self],
    ) -> Result<Self, CostError> {
        self.check_budget()?;

        for root in roots {
            root.check_budget()?;
        }

        if roots.iter().any(|root| !root.valid() || !root.integer()) {
            return Err(CostError::InvalidRoot);
        }

        let mut envelope = roots.to_vec();

        if !roots.iter().any(at_least_one) {
            envelope.push(Self::ONE);
        }

        let envelope = Self::maximum(envelope)?;

        self.bind_inner(resolve, &envelope)
    }
    fn bind_inner(
        &self,
        resolve: &impl Fn(&str) -> Option<Self>,
        envelope: &Self,
    ) -> Result<Self, CostError> {
        let child = |cost: &Self| cost.bind_inner(resolve, envelope);
        let result = match self {
            Self::Name(name) => {
                resolve(name).ok_or_else(|| CostError::UnknownName(name.to_string()))?
            }
            Self::LegacyN => envelope.clone(),
            Self::LegacyLog => Self::logarithm(envelope.clone())?,
            Self::LegacyNLog => envelope.multiply(&Self::logarithm(envelope.clone())?)?,
            Self::Sum(values) => Self::sum(values.iter().map(child).collect::<Result<_, _>>()?)?,
            Self::Product(values) => {
                Self::product(values.iter().map(child).collect::<Result<_, _>>()?)?
            }
            Self::Maximum(values) => {
                Self::maximum(values.iter().map(child).collect::<Result<_, _>>()?)?
            }
            Self::Log(value) => Self::logarithm(child(value)?)?,
            Self::Factorial(value) => Self::factorial(child(value)?)?,
            Self::Power(a, b) => Self::power(child(a)?, child(b)?)?,
            Self::Ratio(a, b) => Self::ratio(child(a)?, child(b)?)?,
            _ => self.clone(),
        };

        result.check_budget()?;

        if !result.valid() {
            return Err(CostError::Domain);
        }

        Ok(result)
    }

    pub fn structural_key(&self) -> String {
        if self.check_budget().is_err() {
            "ResourceExceeded".into()
        } else {
            format!("{self:?}")
        }
    }
    pub fn text(&self) -> String {
        self.text_with(&|id| format!("size_{id}"))
    }
    pub fn text_with(&self, name: &impl Fn(u64) -> String) -> String {
        if self.check_budget().is_err() {
            "O(unknown)".into()
        } else {
            format!("O({})", self.inner_text(name))
        }
    }
    fn inner_text(&self, name: &impl Fn(u64) -> String) -> String {
        let text = |value: &Self| value.inner_text(name);

        match self {
            Self::Constant(number) => number.to_string(),
            Self::LegacyN => "N".into(),
            Self::LegacyLog => "log N".into(),
            Self::LegacyNLog => "N log N".into(),
            Self::Name(name) => name.to_string(),
            Self::Dimension { id, .. } => name(*id),
            Self::Sum(values) => format!(
                "({})",
                values.iter().map(text).collect::<Vec<_>>().join(" + ")
            ),
            Self::Product(values) => format!(
                "({})",
                values.iter().map(text).collect::<Vec<_>>().join(" * ")
            ),
            Self::Maximum(values) => format!(
                "max({})",
                values.iter().map(text).collect::<Vec<_>>().join(", ")
            ),
            Self::Log(value) => format!("log({})", text(value)),
            Self::Factorial(value) => format!("({})!", text(value)),
            Self::Power(a, b) => match (a.as_ref(), b.as_ref()) {
                (Self::LegacyN | Self::Dimension { .. } | Self::Name(_), Self::Constant(power)) => {
                    format!("{}^{power}", text(a))
                }
                _ => format!("({})^({})", text(a), text(b)),
            },
            Self::Ratio(a, b) => format!("({}) / ({})", text(a), text(b)),
        }
    }

    fn write_inner(
        &self,
        out: &mut dyn std::fmt::Write,
        name: &impl Fn(u64, &mut dyn std::fmt::Write) -> std::fmt::Result,
    ) -> std::fmt::Result {
        match self {
            Self::Constant(number) => write!(out, "{number}"),
            Self::LegacyN => out.write_str("N"),
            Self::LegacyLog => out.write_str("log N"),
            Self::LegacyNLog => out.write_str("N log N"),
            Self::Name(text) => out.write_str(text),
            Self::Dimension { id, .. } => name(*id, out),
            Self::Sum(values) | Self::Product(values) | Self::Maximum(values) => {
                let (prefix, separator) = match self {
                    Self::Sum(_) => ("(", " + "),
                    Self::Product(_) => ("(", " * "),
                    _ => ("max(", ", "),
                };

                out.write_str(prefix)?;

                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        out.write_str(separator)?;
                    }

                    value.write_inner(out, name)?;
                }

                out.write_char(')')
            }
            Self::Log(value) | Self::Factorial(value) => {
                out.write_str(if matches!(self, Self::Log(_)) {
                    "log("
                } else {
                    "("
                })?;
                value.write_inner(out, name)?;

                out.write_str(if matches!(self, Self::Log(_)) {
                    ")"
                } else {
                    ")!"
                })
            }
            Self::Power(a, b) => {
                if matches!(
                    (a.as_ref(), b.as_ref()),
                    (
                        Self::LegacyN | Self::Dimension { .. } | Self::Name(_),
                        Self::Constant(_)
                    )
                ) {
                    a.write_inner(out, name)?;
                    out.write_char('^')?;

                    b.write_inner(out, name)
                } else {
                    out.write_char('(')?;
                    a.write_inner(out, name)?;
                    out.write_str(")^(")?;
                    b.write_inner(out, name)?;

                    out.write_char(')')
                }
            }
            Self::Ratio(a, b) => {
                out.write_char('(')?;
                a.write_inner(out, name)?;
                out.write_str(") / (")?;
                b.write_inner(out, name)?;

                out.write_char(')')
            }
        }
    }
    pub fn compare(&self, limit: &Self) -> CostComparison {
        self.compare_with_budget(limit, COMPARISON_CREDITS).0
    }

    fn compare_with_budget(&self, limit: &Self, credits: usize) -> (CostComparison, usize) {
        let mut budget = credits;

        if !reserve_proof(self, limit, &mut budget) {
            return (CostComparison::Inconclusive, credits - budget);
        }

        if self.check_budget().is_err()
            || limit.check_budget().is_err()
            || !self.valid()
            || !limit.valid()
        {
            return (CostComparison::Inconclusive, credits - budget);
        }

        if within(self, limit, &mut budget) {
            return (CostComparison::Within, credits - budget);
        }

        if budget == 0 {
            return (CostComparison::Inconclusive, credits - budget);
        }

        let result =
            if within(limit, self, &mut budget) && strictly_larger(self, limit, &mut budget) {
                CostComparison::Exceeds
            } else {
                CostComparison::Inconclusive
            };

        (result, credits - budget)
    }

    pub fn parse(text: &str) -> Result<Self, CostError> {
        if text.len() > MAX_TEXT {
            return Err(CostError::Resource);
        }

        let mut parser = Parser {
            source: text,
            text: text.as_bytes(),
            offset: 0,
            nodes: 0,
        };

        parser.space();
        parser.expect(b'O')?;
        parser.expect(b'(')?;

        let result = parser.expression(0)?;

        parser.expect(b')')?;
        parser.space();

        if parser.offset != parser.text.len() {
            return Err(CostError::Syntax(parser.offset));
        }

        result.check_budget()?;

        Ok(result)
    }
}

type Monomial = BTreeMap<u64, (i128, i128)>;
fn reserve_walk(value: &Expression, budget: &mut usize, factor: usize) -> bool {
    let mut stack = vec![value];

    while let Some(value) = stack.pop() {
        let Some(remaining) = budget.checked_sub(factor) else {
            *budget = 0;

            return false;
        };
        *budget = remaining;

        stack.extend(value.children());
    }

    true
}
fn reserve_proof(a: &Expression, b: &Expression, budget: &mut usize) -> bool {
    reserve_walk(a, budget, PROOF_CREDITS_PER_NODE)
        && reserve_walk(b, budget, PROOF_CREDITS_PER_NODE)
}
fn monomial(value: &Expression) -> Option<Monomial> {
    match value {
        Expression::Constant(number) if *number > 0 => Some(BTreeMap::new()),
        Expression::Dimension {
            id,
            domain: Domain::Size,
        } => Some(BTreeMap::from([(*id, (1, 0))])),
        Expression::Log(value) => match value.as_ref() {
            Expression::Dimension {
                id,
                domain: Domain::Size,
            } => Some(BTreeMap::from([(*id, (0, 1))])),
            _ => None,
        },
        Expression::Product(values) => {
            let mut output = BTreeMap::new();

            for child in values.iter() {
                add_powers(&mut output, monomial(child)?, 1)?;
            }

            Some(output)
        }
        Expression::Ratio(a, b) => {
            let mut output = monomial(a)?;

            add_powers(&mut output, monomial(b)?, -1)?;

            Some(output)
        }
        Expression::Power(base, exponent) => {
            let Expression::Constant(exponent) = exponent.as_ref() else {
                return None;
            };
            let mut output = BTreeMap::new();

            add_powers(&mut output, monomial(base)?, (*exponent).into())?;

            Some(output)
        }
        _ => None,
    }
}
fn add_powers(output: &mut Monomial, values: Monomial, factor: i128) -> Option<()> {
    for (id, (power, log)) in values {
        let entry = output.entry(id).or_insert((0i128, 0i128));
        entry.0 = entry.0.checked_add(power.checked_mul(factor)?)?;
        entry.1 = entry.1.checked_add(log.checked_mul(factor)?)?;
    }

    Some(())
}
fn monomial_within(a: &Monomial, b: &Monomial) -> bool {
    a.keys()
        .chain(b.keys())
        .all(|id| a.get(id).copied().unwrap_or_default() <= b.get(id).copied().unwrap_or_default())
}
fn dominance_of(value: &Expression) -> Option<Monomial> {
    if matches!(value, Expression::Constant(_)) {
        return None;
    }

    let mut powers = monomial(value)?;

    powers.retain(|_, growth| *growth != (0, 0));

    Some(powers)
}
fn undominated_of(values: Vec<Expression>) -> Vec<Expression> {
    if values.len() > MAX_REDUCED_TERMS {
        return values;
    }

    let powers: Vec<Option<Monomial>> = values.iter().map(dominance_of).collect();

    values
        .into_iter()
        .zip(powers.iter())
        .filter(|(_, dominated)| {
            dominated.as_ref().is_none_or(|dominated| {
                !powers.iter().flatten().any(|dominating| {
                    dominating != dominated && monomial_within(dominated, dominating)
                })
            })
        })
        .map(|(value, _)| value)
        .collect()
}
fn scaled_dimension(value: &Expression) -> Option<(u64, u128)> {
    match value {
        Expression::Dimension {
            id,
            domain: Domain::Size,
        } => Some((*id, 1)),
        Expression::Product(values) => {
            let mut dimension = None;
            let mut coefficient = 1u128;

            for value in values.iter() {
                match value {
                    Expression::Constant(number) => {
                        coefficient = coefficient.checked_mul((*number).into())?
                    }
                    Expression::Dimension {
                        id,
                        domain: Domain::Size,
                    } if dimension.is_none() => dimension = Some(*id),
                    _ => return None,
                }
            }

            Some((dimension?, coefficient))
        }
        _ => None,
    }
}
fn at_least_one(value: &Expression) -> bool {
    match value {
        Expression::Constant(number) => *number >= 1,
        Expression::Dimension {
            domain: Domain::Size,
            ..
        }
        | Expression::Log(_)
        | Expression::Factorial(_) => true,
        Expression::Sum(values) | Expression::Maximum(values) => values.iter().any(at_least_one),
        Expression::Product(values) => values.iter().all(at_least_one),
        Expression::Power(base, _) => at_least_one(base),
        _ => false,
    }
}
fn log_product(value: &Expression) -> Option<Expression> {
    let Expression::Log(argument) = value else {
        return None;
    };
    let Expression::Product(values) = argument.as_ref() else {
        return None;
    };

    if !values.iter().all(at_least_one) {
        return None;
    }

    Expression::sum(
        values
            .iter()
            .map(|value| Expression::Log(Arc::new(value.clone())))
            .collect(),
    )
    .ok()
}
fn envelope_growth(value: &Expression, base: &Expression) -> Option<(i128, i128)> {
    if value == base {
        return Some((1, 0));
    }

    match value {
        Expression::Constant(value) if *value > 0 => Some((0, 0)),
        Expression::Log(value) if value.as_ref() == base => Some((0, 1)),
        Expression::Product(values) => values.iter().try_fold((0i128, 0i128), |(a, b), child| {
            let (c, d) = envelope_growth(child, base)?;

            Some((a.checked_add(c)?, b.checked_add(d)?))
        }),
        Expression::Power(value, exponent) => {
            let Expression::Constant(exponent) = exponent.as_ref() else {
                return None;
            };
            let (a, b) = envelope_growth(value, base)?;

            Some((
                a.checked_mul(i128::from(*exponent))?,
                b.checked_mul(i128::from(*exponent))?,
            ))
        }
        Expression::Ratio(left, right) => {
            let (a, b) = envelope_growth(left, base)?;
            let (c, d) = envelope_growth(right, base)?;

            Some((a.checked_sub(c)?, b.checked_sub(d)?))
        }
        _ => None,
    }
}

fn shared_envelope_growth(a: &Expression, b: &Expression) -> Option<((i128, i128), (i128, i128))> {
    let mut pending = vec![a, b];
    let base = loop {
        match pending.pop()? {
            value @ Expression::Maximum(children)
                if children.iter().all(|child| {
                    matches!(
                        child,
                        Expression::Dimension {
                            domain: Domain::Size,
                            ..
                        } | Expression::Constant(1)
                    )
                }) && children.iter().any(|child| {
                    matches!(
                        child,
                        Expression::Dimension {
                            domain: Domain::Size,
                            ..
                        }
                    )
                }) =>
            {
                break value
            }
            Expression::Product(children) => pending.extend(children.iter()),
            Expression::Log(child) | Expression::Power(child, _) => pending.push(child),
            Expression::Ratio(left, right) => pending.extend([left.as_ref(), right.as_ref()]),
            _ => {}
        }
    };

    Some((envelope_growth(a, base)?, envelope_growth(b, base)?))
}

fn within(a: &Expression, b: &Expression, budget: &mut usize) -> bool {
    if !reserve_proof(a, b, budget) {
        return false;
    }

    if a == b || matches!(a, Expression::Constant(0)) {
        return true;
    }

    if let Some((left, right)) = shared_envelope_growth(a, b) {
        if left <= right {
            return true;
        }
    }

    if let (Some(a), Some(b)) = (monomial(a), monomial(b)) {
        if monomial_within(&a, &b) {
            return true;
        }
    }

    if let Some(expanded) = log_product(a) {
        if within(&expanded, b, budget) {
            return true;
        }
    }

    if let Some(expanded) = log_product(b) {
        if within(a, &expanded, budget) {
            return true;
        }
    }

    if exponential_order(a, b).is_some_and(|ordering| ordering.is_le()) {
        return true;
    }

    if dominates_its_monomials(b, a) {
        return true;
    }

    if let Expression::Product(values) = b {
        if values.iter().all(at_least_one) && values.iter().any(|value| within(a, value, budget)) {
            return true;
        }
    }

    match (a, b) {
        (Expression::Sum(values) | Expression::Maximum(values), _)
            if values.iter().all(|value| within(value, b, budget)) =>
        {
            return true
        }
        (_, Expression::Sum(values) | Expression::Maximum(values))
            if values.iter().any(|value| within(a, value, budget)) =>
        {
            return true
        }
        (Expression::Product(values), Expression::Power(base, power))
            if **power == Expression::Constant(values.len() as u64)
                && values.iter().all(|value| within(value, base, budget)) =>
        {
            return true
        }
        (Expression::Power(x, e), Expression::Power(y, f)) => {
            if let (Expression::Constant(left), Expression::Constant(right)) =
                (e.as_ref(), f.as_ref())
            {
                if left <= right && at_least_one(y) && within(x, y, budget) {
                    return true;
                }
            }

            if e != f {
                return false;
            }

            if let Expression::Constant(_) = e.as_ref() {
                if within(x, y, budget) {
                    return true;
                }
            }

            if let (Expression::Constant(x), Expression::Constant(y)) = (x.as_ref(), y.as_ref()) {
                return *x > 1 && x <= y;
            }
        }
        (Expression::Power(base, exponent), Expression::Factorial(argument))
            if exponent == argument
                && matches!(base.as_ref(),Expression::Constant(value) if *value > 1) =>
        {
            return true
        }
        (Expression::Factorial(argument), Expression::Power(base, exponent))
            if argument == base && base == exponent =>
        {
            return true
        }
        _ => {}
    }

    if let Expression::Power(base, exponent) = b {
        if let Expression::Maximum(values) = base.as_ref() {
            for value in values.iter() {
                let Ok(branch) = Expression::power(value.clone(), exponent.as_ref().clone()) else {
                    continue;
                };

                if within(a, &branch, budget) {
                    return true;
                }
            }
        }
    }

    false
}
fn strictly_larger(a: &Expression, b: &Expression, budget: &mut usize) -> bool {
    if !reserve_proof(a, b, budget) {
        return false;
    }

    if let Some((left, right)) = shared_envelope_growth(a, b) {
        if left > right {
            return true;
        }
    }

    if dominates_its_monomials(a, b) {
        return true;
    }

    if let Expression::Maximum(values) = a {
        if values.iter().any(|value| strictly_larger(value, b, budget)) {
            return true;
        }
    }

    if let Expression::Product(values) = a {
        if values.iter().all(at_least_one)
            && values.iter().any(|value| strictly_larger(value, b, budget))
        {
            return true;
        }
    }

    if let (Some(a), Some(b)) = (monomial(a), monomial(b)) {
        return a != b && monomial_within(&b, &a);
    }

    if let (Some(a), Some(b)) = (witness_growth(a, None), witness_growth(b, None)) {
        if a > b {
            return true;
        }
    }

    for id in dimension_ids(a).into_iter().chain(dimension_ids(b)) {
        if !reserve_proof(a, b, budget) {
            return false;
        }

        if let (Some(a), Some(b)) = (witness_growth(a, Some(id)), witness_growth(b, Some(id))) {
            if a > b {
                return true;
            }
        }
    }

    if exponential_order(a, b).is_some_and(|ordering| ordering.is_gt()) {
        return true;
    }

    match (a, b) {
        (Expression::Power(base, exponent), Expression::Power(other, same))
            if exponent == same
                && matches!(
                    exponent.as_ref(),
                    Expression::Dimension {
                        domain: Domain::Size,
                        ..
                    }
                ) =>
        {
            matches!((base.as_ref(),other.as_ref()),(Expression::Constant(a),Expression::Constant(b)) if a>b && *b>1)
        }
        (Expression::Factorial(argument), Expression::Power(base, exponent))
            if argument == exponent
                && matches!(
                    argument.as_ref(),
                    Expression::Dimension {
                        domain: Domain::Size,
                        ..
                    }
                ) =>
        {
            matches!(base.as_ref(),Expression::Constant(value) if *value>1)
        }
        (Expression::Power(base, exponent), Expression::Factorial(argument)) => {
            base == exponent
                && base == argument
                && matches!(
                    base.as_ref(),
                    Expression::Dimension {
                        domain: Domain::Size,
                        ..
                    }
                )
        }
        _ => false,
    }
}
fn dominates_its_monomials(value: &Expression, other: &Expression) -> bool {
    let argument = match value {
        Expression::Power(base, exponent) if matches!(base.as_ref(), Expression::Constant(number) if *number > 1) => {
            exponent.as_ref()
        }
        Expression::Factorial(argument) => argument.as_ref(),
        _ => return false,
    };
    let Expression::Dimension {
        id,
        domain: Domain::Size,
    } = argument
    else {
        return false;
    };

    monomial(other).is_some_and(|powers| powers.keys().all(|key| key == id))
}

fn exponential_order(a: &Expression, b: &Expression) -> Option<std::cmp::Ordering> {
    let (Expression::Power(base, exponent), Expression::Power(other, next)) = (a, b) else {
        return None;
    };

    if base != other || !matches!(base.as_ref(), Expression::Constant(number) if *number > 1) {
        return None;
    }

    let ((x, a), (y, b)) = (scaled_dimension(exponent)?, scaled_dimension(next)?);

    (x == y).then(|| a.cmp(&b))
}
fn dimension_ids(value: &Expression) -> Vec<u64> {
    let mut stack = vec![value];
    let mut ids = Vec::new();

    while let Some(value) = stack.pop() {
        if let Expression::Dimension {
            id,
            domain: Domain::Size,
        } = value
        {
            ids.push(*id);
        }

        stack.extend(value.children());
    }

    ids.sort_unstable();
    ids.dedup();

    ids
}
fn witness_growth(value: &Expression, selected: Option<u64>) -> Option<(i128, i128)> {
    if let Some(powers) = monomial(value) {
        return powers
            .iter()
            .filter(|(id, _)| selected.is_none_or(|selected| selected == **id))
            .try_fold((0i128, 0i128), |sum, (_, next)| {
                Some((sum.0.checked_add(next.0)?, sum.1.checked_add(next.1)?))
            });
    }

    match value {
        Expression::Sum(values) | Expression::Maximum(values) => values
            .iter()
            .map(|value| witness_growth(value, selected))
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .max(),
        _ => None,
    }
}

struct Parser<'a> {
    source: &'a str,
    text: &'a [u8],
    offset: usize,
    nodes: usize,
}
impl Parser<'_> {
    fn character(&self, offset: usize) -> Option<char> {
        self.source.get(offset..)?.chars().next()
    }

    fn space(&mut self) {
        while let Some(character) = self
            .character(self.offset)
            .filter(|character| character.is_whitespace())
        {
            self.offset += character.len_utf8();
        }
    }
    fn take(&mut self, byte: u8) -> bool {
        self.space();

        if self.text.get(self.offset) == Some(&byte) {
            self.offset += 1;

            true
        } else {
            false
        }
    }
    fn expect(&mut self, byte: u8) -> Result<(), CostError> {
        if self.take(byte) {
            Ok(())
        } else {
            Err(CostError::Syntax(self.offset))
        }
    }
    fn expression(&mut self, depth: usize) -> Result<Expression, CostError> {
        if depth > MAX_PARSE_DEPTH {
            return Err(CostError::Resource);
        }

        let mut output = vec![self.product(depth + 1)?];

        while self.take(b'+') {
            output.push(self.product(depth + 1)?);
        }

        Expression::sum(output)
    }
    fn product(&mut self, depth: usize) -> Result<Expression, CostError> {
        let mut output = self.power(depth + 1)?;

        loop {
            if self.take(b'*') {
                output = output.multiply(&self.power(depth + 1)?)?;
            } else if self.take(b'/') {
                let denominator = self.power(depth + 1)?;

                if denominator == Expression::Constant(0) {
                    return Err(CostError::Domain);
                }

                output = Expression::Ratio(Arc::new(output), Arc::new(denominator));

                output.check_budget()?;
            } else {
                self.space();

                let keyword = self.text.get(self.offset..self.offset + 3) == Some(b"log")
                    && self.character(self.offset + 3).is_none_or(|character| {
                        !oxc_syntax::identifier::is_identifier_part(character) && character != '.'
                    });
                let compact = self.text.get(self.offset..self.offset + 4) == Some(b"logN")
                    && self.character(self.offset + 4).is_none_or(|character| {
                        !oxc_syntax::identifier::is_identifier_part(character) && character != '.'
                    });

                if keyword || compact {
                    output = output.multiply(&self.power(depth + 1)?)?;
                } else {
                    break;
                }
            }
        }

        Ok(output)
    }
    fn power(&mut self, depth: usize) -> Result<Expression, CostError> {
        if depth > MAX_PARSE_DEPTH {
            return Err(CostError::Resource);
        }

        let mut output = self.atom(depth + 1)?;

        while self.take(b'!') {
            output = Expression::Factorial(Arc::new(output));

            output.check_budget()?;
        }

        if self.take(b'^') {
            output = Expression::power(output, self.power(depth + 1)?)?;
        }

        Ok(output)
    }
    fn atom(&mut self, depth: usize) -> Result<Expression, CostError> {
        self.nodes += 1;

        if depth > MAX_PARSE_DEPTH || self.nodes > MAX_PARSE_NODES {
            return Err(CostError::Resource);
        }

        if self.take(b'(') {
            let output = self.expression(depth + 1)?;

            self.expect(b')')?;

            return Ok(output);
        }

        self.space();

        let start = self.offset;

        if self.text.get(start).is_some_and(u8::is_ascii_digit) {
            while self.text.get(self.offset).is_some_and(u8::is_ascii_digit) {
                self.offset += 1;
            }

            let text = std::str::from_utf8(&self.text[start..self.offset])
                .map_err(|_| CostError::Syntax(start))?;

            return text
                .parse::<u64>()
                .map(Expression::Constant)
                .map_err(|_| CostError::Overflow);
        }

        loop {
            let Some(first) = self
                .character(self.offset)
                .filter(|character| oxc_syntax::identifier::is_identifier_start(*character))
            else {
                return Err(CostError::Syntax(self.offset));
            };
            self.offset += first.len_utf8();

            while let Some(character) = self
                .character(self.offset)
                .filter(|character| oxc_syntax::identifier::is_identifier_part(*character))
            {
                self.offset += character.len_utf8();
            }

            if self.text.get(self.offset) != Some(&b'.') {
                break;
            }

            self.offset += 1;
        }

        let name = std::str::from_utf8(&self.text[start..self.offset])
            .map_err(|_| CostError::Syntax(start))?;

        if name == "max" {
            self.expect(b'(')?;

            let mut values = vec![self.expression(depth + 1)?];

            while self.take(b',') {
                values.push(self.expression(depth + 1)?);
            }

            self.expect(b')')?;

            return Expression::maximum(values);
        }

        if name == "log" {
            let exponent = if self.take(b'^') {
                Some(self.atom(depth + 1)?)
            } else {
                None
            };
            let value = self.atom(depth + 1)?;

            if value == Expression::Constant(0) {
                return Err(CostError::Domain);
            }

            let logarithm = if value == Expression::LegacyN {
                Expression::LegacyLog
            } else {
                Expression::Log(Arc::new(value))
            };

            return match exponent {
                Some(exponent) => Expression::power(logarithm, exponent),
                None => Ok(logarithm),
            };
        }

        match name {
            "N" => Ok(Expression::N),
            "logN" => Ok(Expression::LOG),
            "NlogN" => Ok(Expression::N_LOG_N),
            _ => Ok(Expression::Name(name.into())),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Preference {
    #[default]
    Absent,
    Cold,
    Unmarked,
    Hot,
}

/// Spec §1 State of a node's reading: Known when no contribution is unknown, Unknown when unknown contributions are
/// its only work, Partial otherwise.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    Known,
    Partial,
    Unknown,
}

/// The state of a reading whose unknown contributions are `unknowns` and whose preference is Absent when `absent`. A
/// contribution under an unknown multiplicity adds nothing to the cost (`Part::unmultiplied`), so the cost joins the
/// proven contributions only: the bound when nothing is unknown, the floor otherwise. A reading that executes no work
/// of its own stays Absent however many unknowns it carries, so an Absent reading with unknowns has no proven
/// contribution and is Unknown.
pub fn state_of(unknowns: Option<UnknownId>, absent: bool) -> State {
    match (unknowns, absent) {
        (None, _) => State::Known,
        (Some(_), true) => State::Unknown,
        (Some(_), false) => State::Partial,
    }
}

#[derive(Clone, Debug, Default)]
pub struct Part {
    pub origin: Option<SourceSpan>,
    pub cost_error: Option<CostError>,
    pub cost: Cost,
    pub trace: Option<TraceId>,
    pub preference: Preference,
    pub unknowns: Option<UnknownId>,
    pub retained: Option<UnknownId>,
    /// The derivation of `cost`: `None` for a unit cost no rule needs to derive, or for a cost some rule application
    /// behind it left underived.
    pub derivation: Option<DerivationId>,
}

/// Parts compare without their derivations: a derivation records how olint proved a part's cost and never changes
/// what the analysis does with the part.
impl PartialEq for Part {
    fn eq(&self, other: &Self) -> bool {
        self.origin == other.origin
            && self.cost_error == other.cost_error
            && self.cost == other.cost
            && self.trace == other.trace
            && self.preference == other.preference
            && self.unknowns == other.unknowns
            && self.retained == other.retained
    }
}

impl Eq for Part {}

/// The derivation joining parts by `rule` into a part costing `cost`, from each part's derivation and whether its cost
/// is a unit. A unit part without derivation needs none and is left out. Any other part without derivation leaves the
/// join underived. A join resting on one derivation of the joined cost is that derivation.
fn joined(
    arena: &mut DerivationArena,
    rule: &'static str,
    sides: &[(Option<DerivationId>, bool)],
    cost: &Cost,
) -> Option<DerivationId> {
    let mut premises: Vec<DerivationId> = Vec::with_capacity(sides.len());

    for (derivation, unit) in sides {
        match derivation {
            Some(derivation) if !premises.contains(derivation) => premises.push(*derivation),
            Some(_) => {}
            None if *unit => {}
            None => return None,
        }
    }

    match premises.as_slice() {
        [] => None,
        [only] if arena.get(*only).is_some_and(|held| held.cost == *cost) => Some(*only),
        _ => arena.derive(rule, None, &premises, Vec::new(), cost.clone()),
    }
}

fn side_of(part: &Part) -> (Option<DerivationId>, bool) {
    (part.derivation, part.cost.is_one())
}

impl Part {
    pub fn called(mut self, origin: SourceSpan, unknowns: &mut Unknowns) -> Self {
        self.origin = Some(origin);
        self.unknowns = unknowns.called(self.unknowns, origin);
        self.retained = unknowns.called(self.retained, origin);

        self
    }

    pub fn retaining(mut self, retained: Option<UnknownId>, unknowns: &mut Unknowns) -> Self {
        self.unknowns = unknowns.join(self.unknowns, retained);
        self.retained = unknowns.join(self.retained, retained);

        self
    }

    pub fn scaled(mut self, factor: Option<Cost>, unknowns: &mut Unknowns) -> Self {
        self.unknowns = unknowns.scale(self.unknowns, factor.clone());
        self.retained = unknowns.scale(self.retained, factor);

        self
    }

    /// Spec §1 Contribution and Floor: work under an unknown multiplicity is an unknown contribution, so it adds no
    /// cost to its node's floor and its unknowns stay, scaled by the unknown factor.
    pub fn unmultiplied(self, unknowns: &mut Unknowns) -> Self {
        Part {
            cost: Cost::ONE,
            trace: None,
            derivation: None,
            ..self.scaled(None, unknowns)
        }
    }

    pub fn state(&self) -> State {
        state_of(self.unknowns, self.is_absent())
    }

    pub fn explanation_failed(mut self, origin: SourceSpan, unknowns: &mut Unknowns) -> Self {
        self.cost_error = Some(CostError::Resource);
        let failure = unknowns.origin(origin, UnknownReason::ResourceExhaustion);
        self.unknowns = unknowns.join(self.unknowns, Some(failure));

        self
    }
    pub fn explain(
        mut self,
        label: impl std::fmt::Display,
        site: Site,
        origin: SourceSpan,
        inner: bool,
        traces: &mut TraceArena,
        unknowns: &mut Unknowns,
    ) -> Self {
        let (child, continuation) = if inner {
            (self.trace, None)
        } else {
            (None, self.trace)
        };
        let cost = if inner { self.cost.clone() } else { Cost::ONE };

        match traces.factor_format(label, site, origin, cost, child, continuation) {
            Ok(trace) => self.trace = Some(trace),
            Err(_) => {
                self.cost_error = Some(CostError::Resource);
                let failure = unknowns.origin(origin, UnknownReason::ResourceExhaustion);
                self.unknowns = unknowns.join(self.unknowns, Some(failure));
            }
        }

        self.origin = Some(origin);

        self
    }

    pub fn is_complete(&self) -> bool {
        self.unknowns.is_none() && self.cost_error.is_none()
    }
    pub fn none() -> Part {
        Part::default()
    }

    pub fn unmarked(cost: Cost, trace: Option<TraceId>) -> Part {
        Part {
            origin: None,
            cost_error: None,
            cost,
            trace,
            preference: Preference::Unmarked,
            unknowns: None,
            retained: None,
            derivation: None,
        }
    }

    /// This part with its cost derived by `derivation`.
    pub fn derived(self, derivation: Option<DerivationId>) -> Part {
        Part { derivation, ..self }
    }

    pub fn is_absent(&self) -> bool {
        self.preference == Preference::Absent
    }

    pub fn executed(self) -> Part {
        match self.is_absent() {
            true => self.preferred(Preference::Unmarked),
            false => self,
        }
    }

    pub fn holds_no_work(&self) -> bool {
        self.cost.is_one() && self.unknowns == self.retained
    }

    pub fn holds_only_provenance(&self) -> bool {
        self.retained.is_some() && self.holds_no_work()
    }

    fn rank(&self) -> u8 {
        if self.is_absent() {
            return 0;
        }

        match self.preference {
            Preference::Cold => 1,
            Preference::Absent | Preference::Unmarked => 2,
            Preference::Hot => 3,
        }
    }

    /// The larger of two parts. Its derivation keeps both sides as premises, whichever side the join selects: by
    /// `preference-rank` when their preferences differ, `max-dominance` when one cost covers the other, and
    /// `max-normalise` when the join keeps the maximum of both costs.
    pub fn max(self, other: Part, unknowns: &mut Unknowns, traces: &mut TraceArena) -> Part {
        let sides = [side_of(&self), side_of(&other)];
        let (selected, rule) = self.select(other, unknowns, traces);
        let derivation = match selected.cost_error {
            Some(_) => None,
            None => joined(&mut traces.derivations, rule, &sides, &selected.cost),
        };

        selected.derived(derivation)
    }

    fn select(
        self,
        other: Part,
        unknowns: &mut Unknowns,
        traces: &mut TraceArena,
    ) -> (Part, &'static str) {
        let (mine, theirs) = (self.rank(), other.rank());
        let selected_error = if mine == theirs {
            self.cost_error.clone().or(other.cost_error.clone())
        } else if theirs > mine {
            other.cost_error.clone()
        } else {
            self.cost_error.clone()
        };
        let selected_origin = if theirs > mine {
            other.origin
        } else {
            self.origin.or(other.origin)
        };
        let retained = unknowns.join(self.retained, other.retained);
        let selected_unknowns = if mine == theirs {
            unknowns.join(self.unknowns, other.unknowns)
        } else if theirs > mine {
            other.unknowns
        } else {
            self.unknowns
        };
        let selected_unknowns = unknowns.join(selected_unknowns, retained);

        let comparison = other.cost.compare_legacy(&self.cost);
        let both =
            theirs == mine && comparison == CostComparison::Inconclusive && self.cost != other.cost;
        let rule = match (mine == theirs, both) {
            (false, _) => "preference-rank",
            (true, true) => "max-normalise",
            (true, false) => "max-dominance",
        };
        let mut selected =
            if theirs > mine || (theirs == mine && comparison == CostComparison::Exceeds) {
                other
            } else if both {
                let mut combined = self;

                match Cost::maximum(vec![combined.cost.clone(), other.cost.clone()]) {
                    Ok(cost) => combined.cost = cost,
                    Err(error) => {
                        combined.cost_error = Some(error);
                    }
                }

                match traces.group(combined.trace, other.trace) {
                    Ok(trace) => combined.trace = trace,
                    Err(_) => combined.cost_error = Some(CostError::Resource),
                }

                combined
            } else {
                self
            };
        selected.unknowns = selected_unknowns;
        selected.retained = retained;
        selected.cost_error = selected.cost_error.or(selected_error);
        selected.origin = selected.origin.or(selected_origin);

        if selected.cost_error.is_some() {
            if let Some(origin) = selected.origin {
                let failure = unknowns.origin(origin, UnknownReason::ResourceExhaustion);
                selected.unknowns = unknowns.join(selected.unknowns, Some(failure));
            }
        }

        (selected, rule)
    }

    pub fn preferred(self, preference: Preference) -> Part {
        Part { preference, ..self }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ExecutionPhase {
    #[default]
    Immediate,
    Scheduled,
    Lazy,
}

fn channel_order_of(phase: ExecutionPhase, completion: Completion) -> (u8, u8, usize) {
    let phase = match phase {
        ExecutionPhase::Immediate => 0,
        ExecutionPhase::Scheduled => 1,
        ExecutionPhase::Lazy => 2,
    };
    let (kind, target) = match completion {
        Completion::Normal => (0, 0),
        Completion::Return => (1, 0),
        Completion::Throw => (2, 0),
        Completion::Break(target) => (3, target.index()),
        Completion::Continue(target) => (4, target.index()),
    };

    (phase, kind, target)
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reading {
    pub completions: Vec<(ExecutionPhase, Completion, Part)>,
}

impl From<Part> for Reading {
    fn from(part: Part) -> Self {
        Reading::of_completion(ExecutionPhase::Immediate, Completion::Normal, part)
    }
}

impl Reading {
    pub(crate) fn holds_no_work(&self) -> bool {
        self.completions
            .iter()
            .all(|channel| channel.2.holds_no_work())
    }

    pub(crate) fn called(self, origin: SourceSpan, unknowns: &mut Unknowns) -> Reading {
        self.map_parts(|part| part.called(origin, unknowns))
    }

    pub(crate) fn executed(self) -> Reading {
        if self.completions.is_empty() {
            return Reading::of_part(Part::none().executed());
        }

        self.map_parts(Part::executed)
    }

    pub(crate) fn map_parts(self, mut map: impl FnMut(Part) -> Part) -> Reading {
        let mut reading = Reading::empty();

        for (phase, completion, part) in self.completions {
            reading.set(phase, completion, map(part));
        }

        reading
    }

    pub(crate) fn normalized(self, unknowns: &mut Unknowns, traces: &mut TraceArena) -> Reading {
        let mut reading = Reading::empty();

        for (phase, _, part) in self.completions {
            reading.join(phase, Completion::Normal, part, unknowns, traces);
        }

        reading
    }

    pub(crate) fn retaining(
        self,
        unknown: Option<crate::unknowns::UnknownId>,
        unknowns: &mut Unknowns,
    ) -> Reading {
        if self.completions.is_empty() {
            return Reading::of_part(Part::none().retaining(unknown, unknowns));
        }

        self.map_parts(|part| part.retaining(unknown, unknowns))
    }

    pub fn empty() -> Reading {
        Reading::default()
    }

    pub fn of_part(part: impl Into<Reading>) -> Reading {
        part.into()
    }

    pub fn of_completion(phase: ExecutionPhase, completion: Completion, part: Part) -> Reading {
        let mut reading = Reading::empty();

        reading.set(phase, completion, part);

        reading
    }

    pub fn set(&mut self, phase: ExecutionPhase, completion: Completion, part: Part) {
        let order = channel_order_of(phase, completion);
        let position = self
            .completions
            .iter()
            .position(|channel| channel_order_of(channel.0, channel.1) >= order);

        match position {
            Some(position)
                if channel_order_of(self.completions[position].0, self.completions[position].1)
                    == order =>
            {
                match part == Part::none() {
                    true => {
                        self.completions.remove(position);
                    }
                    false => self.completions[position].2 = part,
                }
            }
            _ if part == Part::none() => {}
            Some(position) => self.completions.insert(position, (phase, completion, part)),
            None => self.completions.push((phase, completion, part)),
        }
    }

    pub fn part_of(&self, phase: ExecutionPhase, completion: Completion) -> Part {
        let order = channel_order_of(phase, completion);

        self.completions
            .iter()
            .find(|channel| channel_order_of(channel.0, channel.1) == order)
            .map(|channel| channel.2.clone())
            .unwrap_or_default()
    }

    pub fn main(&self) -> Part {
        self.part_of(ExecutionPhase::Immediate, Completion::Normal)
    }

    pub fn with_main(mut self, part: Part) -> Reading {
        self.set(ExecutionPhase::Immediate, Completion::Normal, part);

        self
    }

    pub fn escapes(&self) -> impl Iterator<Item = &(ExecutionPhase, Completion, Part)> {
        self.completions
            .iter()
            .filter(|channel| channel.1 != Completion::Normal)
    }

    fn beside_main(&self) -> impl Iterator<Item = &(ExecutionPhase, Completion, Part)> {
        let main = channel_order_of(ExecutionPhase::Immediate, Completion::Normal);

        self.completions
            .iter()
            .filter(move |channel| channel_order_of(channel.0, channel.1) != main)
    }

    pub fn join(
        &mut self,
        phase: ExecutionPhase,
        completion: Completion,
        part: Part,
        unknowns: &mut Unknowns,
        traces: &mut TraceArena,
    ) {
        let held = self.part_of(phase, completion);

        self.set(phase, completion, held.max(part, unknowns, traces));
    }

    pub fn merge(
        mut self,
        other: impl Into<Reading>,
        unknowns: &mut Unknowns,
        traces: &mut TraceArena,
    ) -> Reading {
        for (phase, completion, part) in other.into().completions {
            self.join(phase, completion, part, unknowns, traces);
        }

        self
    }

    pub fn preferred(self, preference: Preference) -> Reading {
        let main = self.main().preferred(preference);
        let held = channel_order_of(ExecutionPhase::Immediate, Completion::Normal);
        let mut reading = Reading {
            completions: self
                .completions
                .into_iter()
                .filter(|channel| channel_order_of(channel.0, channel.1) != held)
                .map(|(phase, completion, part)| {
                    let part = match part.is_absent() {
                        true => part,
                        false => part.preferred(preference),
                    };

                    (phase, completion, part)
                })
                .collect(),
        };

        reading.set(ExecutionPhase::Immediate, Completion::Normal, main);

        reading
    }

    fn retains_exit_work(&self) -> bool {
        self.escapes().any(|channel| !channel.2.is_absent())
    }

    pub fn sibling(self) -> Reading {
        if self
            .completions
            .iter()
            .any(|channel| !channel.2.is_absent() || channel.2.holds_only_provenance())
            || self.retains_exit_work()
        {
            return self;
        }

        let main = self.main().preferred(Preference::Unmarked);

        self.with_main(main)
    }

    /// The maximum over every channel outside the lazy phase, derived by `channel-total` from every channel's part.
    pub fn total(&self, unknowns: &mut Unknowns, traces: &mut TraceArena) -> Part {
        let main = self.main();
        let channels = self
            .beside_main()
            .filter(|channel| channel.0 != ExecutionPhase::Lazy)
            .map(|channel| &channel.2);

        channel_total(main, channels, unknowns, traces)
    }

    /// The maximum over the lazy phase's channels, derived by `channel-total`.
    pub fn latent(&self, unknowns: &mut Unknowns, traces: &mut TraceArena) -> Part {
        let channels = self
            .completions
            .iter()
            .filter(|channel| channel.0 == ExecutionPhase::Lazy)
            .map(|channel| &channel.2);

        channel_total(Part::none(), channels, unknowns, traces)
    }

    pub fn in_phase(
        self,
        phase: ExecutionPhase,
        unknowns: &mut Unknowns,
        traces: &mut TraceArena,
    ) -> Reading {
        let mut reading = Reading::empty();

        for (original, completion, part) in self.completions {
            let phase = if original == ExecutionPhase::Lazy && phase == ExecutionPhase::Scheduled {
                ExecutionPhase::Lazy
            } else {
                phase
            };

            reading.join(phase, completion, part, unknowns, traces);
        }

        reading
    }
}

fn channel_total<'r>(
    first: Part,
    channels: impl Iterator<Item = &'r Part>,
    unknowns: &mut Unknowns,
    traces: &mut TraceArena,
) -> Part {
    let mut sides = vec![side_of(&first)];
    let mut total = first;

    for part in channels {
        sides.push(side_of(part));

        total = total.select(part.clone(), unknowns, traces).0;
    }

    let derivation = match total.cost_error {
        Some(_) => None,
        None => joined(
            &mut traces.derivations,
            "channel-total",
            &sides,
            &total.cost,
        ),
    };

    total.derived(derivation)
}

/// `inner` repeated `factor` times, derived by `nest-product` from `witness`, the derivation of the bound `factor`,
/// and `inner`'s derivation.
pub fn nest(
    label: String,
    site: Site,
    origin: SourceSpan,
    (factor, witness): (Cost, Option<DerivationId>),
    inner: Part,
    unknowns: &mut Unknowns,
    traces: &mut TraceArena,
) -> Part {
    let trace = traces.factor(label, site, origin, factor.clone(), None, inner.trace);
    let trace_error = trace.is_err();

    let retained = unknowns.scale(inner.retained, Some(factor.clone()));
    let mut selected_unknowns = unknowns.scale(inner.unknowns, Some(factor.clone()));

    if trace_error {
        let failure = unknowns.origin(origin, UnknownReason::ResourceExhaustion);
        selected_unknowns = unknowns.join(selected_unknowns, Some(failure));
    }

    // A product past the cost representation is an unknown contribution, so it adds nothing to the floor (§1 Floor).
    let (cost, trace, derived) = match factor.multiply(&inner.cost) {
        Ok(cost) => (cost, trace.ok(), true),
        Err(_) => {
            let failure = unknowns.origin(origin, UnknownReason::ResourceExhaustion);
            selected_unknowns = unknowns.join(selected_unknowns, Some(failure));

            (Cost::ONE, None, false)
        }
    };
    let premises = match (inner.derivation, witness) {
        (Some(premise), Some(witness)) => Some(vec![witness, premise]),
        (None, Some(witness)) if inner.cost.is_one() => Some(vec![witness]),
        _ => None,
    };
    let derivation = premises
        .filter(|_| derived && !trace_error && inner.cost_error.is_none())
        .and_then(|premises| {
            traces.derivations.derive(
                "nest-product",
                Some(origin),
                &premises,
                Vec::new(),
                cost.clone(),
            )
        });

    Part {
        origin: Some(origin),
        cost_error: inner
            .cost_error
            .or(trace_error.then_some(CostError::Resource)),
        unknowns: selected_unknowns,
        retained,
        cost,
        trace,
        preference: inner.preference,
        derivation,
    }
}

#[cfg(test)]
#[path = "cost.test.rs"]
mod tests;

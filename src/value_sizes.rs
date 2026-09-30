use std::collections::HashMap;

use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
    MemberExpression, ObjectPropertyKind, PropertyKind,
};
use oxc_ast::AstKind;
use oxc_semantic::{AstNodes, NodeId, SymbolId};
use oxc_span::GetSpan;
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};

use crate::analysis::{work::Event, Analysis};
use crate::constants::constant_initializer_of;
use crate::cost::Cost;
use crate::declarations::{Declaration, FunctionNode};
use crate::declared_types::Kind;
use crate::project::FileId;
use crate::syntax::{call_of, member_expression_of, unwrap};
use crate::tables::{DERIVED_METHODS, OBJECT_KEYED, TYPED_ARRAYS};

use super::{SizeId, SizeQuantity};

const MAXIMUM_SIZE_DEPTH: usize = 64;
const MAXIMUM_ALIAS_DEPTH: usize = 8;
const READING_METHODS: [&str; 19] = [
    "at",
    "concat",
    "entries",
    "flat",
    "get",
    "has",
    "includes",
    "indexOf",
    "join",
    "keys",
    "lastIndexOf",
    "slice",
    "toLocaleString",
    "toReversed",
    "toSorted",
    "toSpliced",
    "toString",
    "values",
    "with",
];
const ELEMENT_CALLBACK_METHODS: [&str; 10] = [
    "every",
    "filter",
    "find",
    "findIndex",
    "findLast",
    "findLastIndex",
    "flatMap",
    "forEach",
    "map",
    "some",
];
const ACCUMULATOR_CALLBACK_METHODS: [&str; 2] = ["reduce", "reduceRight"];
const SHRINKING_METHODS: [&str; 2] = ["pop", "shift"];
const RECEIVER_RETURNING_METHODS: [&str; 4] = ["sort", "reverse", "fill", "copyWithin"];
const OBJECT_READERS: [&str; 9] = [
    "keys",
    "values",
    "entries",
    "getOwnPropertyNames",
    "isFrozen",
    "isSealed",
    "isExtensible",
    "hasOwn",
    "freeze",
];
const ITERATING_CONSTRUCTORS: [&str; 4] = ["Set", "Map", "WeakSet", "WeakMap"];
const COERCED_MEMBERS: [&str; 5] = [
    "toString",
    "valueOf",
    "join",
    "toLocaleString",
    "@@toPrimitive",
];
const ITERATED_MEMBERS: [&str; 5] = ["values", "next", "return", "@@iterator", "@@asyncIterator"];
const AWAITED_MEMBERS: [&str; 1] = ["then"];
const GROWING_METHODS: [&str; 2] = ["push", "unshift"];
const RESIZING_METHODS: [&str; 5] = ["push", "unshift", "splice", "add", "set"];
/// The resizing methods that add one entry per argument, so a call with no spread argument adds a
/// constant number of entries.
const COUNTED_RESIZING_METHODS: [&str; 4] = ["push", "unshift", "add", "set"];
const DELETING_METHODS: [&str; 2] = ["delete", "clear"];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Cardinality {
    Constant,
    Symbolic(SizeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Shape {
    Primitive,
    Fixed,
    Array,
    Object,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Measure {
    constant: bool,
    shape: Shape,
}

#[derive(Clone, Copy)]
struct Holder {
    function: Option<NodeId>,
    shape: Shape,
    exact: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HolderSummary {
    stable: bool,
    returned: bool,
    local: bool,
    function: Option<NodeId>,
}

pub(crate) enum Growth<'a> {
    Stable,
    Unstable,
    Sites {
        calls: Vec<&'a CallExpression<'a>>,
        open: bool,
    },
}

#[derive(Clone)]
enum GrowthSummary {
    Stable,
    Unstable,
    Sites { calls: Vec<NodeId>, open: bool },
}

/// How a function resizes one of its bindings in place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Resizing {
    /// No site resizes the binding.
    Unchanged,
    /// Every resizing site runs at most once per call and adds a constant number of entries.
    Bounded,
    /// A site resizes the binding by an amount or a number of times the size cannot track.
    Untracked,
}

#[derive(Default)]
pub(crate) struct SizeMemory {
    declarations: HashMap<(FileId, NodeId), Option<Measure>>,
    holders: HashMap<(FileId, SymbolId, Shape, bool), HolderSummary>,
    growths: HashMap<(FileId, SymbolId, Shape), GrowthSummary>,
    evaluating: HashMap<FileId, bool>,
    resized: HashMap<(FileId, SymbolId), Resizing>,
    pub(crate) inherited: HashMap<Kind, bool>,
}

impl HolderSummary {
    const UNSTABLE: HolderSummary = HolderSummary {
        stable: false,
        returned: false,
        local: false,
        function: None,
    };
}

impl Shape {
    fn join(self, other: Shape) -> Shape {
        match (self, other) {
            (left, right) if left == right => left,
            (Shape::Primitive | Shape::Fixed, other) | (other, Shape::Primitive | Shape::Fixed) => {
                other
            }
            _ => Shape::Unknown,
        }
    }

    fn is_linear(self) -> bool {
        matches!(self, Shape::Primitive | Shape::Fixed | Shape::Array)
    }

    fn needs_history(self) -> bool {
        !matches!(self, Shape::Primitive | Shape::Fixed)
    }

    fn inherited_kind(self) -> Kind {
        match self {
            Shape::Primitive => Kind::String,
            Shape::Array => Kind::Array,
            Shape::Object => Kind::Other,
            Shape::Fixed | Shape::Unknown => Kind::Unknown,
        }
    }
}

impl Measure {
    const VARIABLE: Measure = Measure {
        constant: false,
        shape: Shape::Unknown,
    };

    fn of(constant: bool, shape: Shape) -> Measure {
        Measure { constant, shape }
    }

    fn counts(self) -> bool {
        self.constant && self.shape.is_linear()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SizeUse {
    Length,
    Keys,
    Enumerated,
}

fn symbol_of_declaration(declaration: &Declaration<'_>) -> Option<(FileId, SymbolId, NodeId)> {
    match declaration {
        Declaration::Variable {
            file, declarator, ..
        } => match &declarator.id {
            BindingPattern::BindingIdentifier(identifier) => {
                Some((*file, identifier.symbol_id.get()?, declarator.node_id()))
            }
            _ => None,
        },
        Declaration::Enum { file, declaration } => Some((
            *file,
            declaration.id.symbol_id.get()?,
            declaration.node_id(),
        )),
        _ => None,
    }
}

fn value_references_of(scoping: &oxc_semantic::Scoping, symbol: SymbolId) -> Vec<(NodeId, bool)> {
    scoping
        .get_resolved_references(symbol)
        .filter(|reference| !reference.flags().is_type() && !reference.flags().is_value_as_type())
        .filter(|reference| reference.is_read() || !reference.is_write())
        .map(|reference| (reference.node_id(), reference.is_write()))
        .collect()
}

fn is_unbound_named(
    scoping: &oxc_semantic::Scoping,
    expression: &Expression<'_>,
    names: &[&str],
) -> bool {
    matches!(
        unwrap(expression),
        Expression::Identifier(reference)
            if names.contains(&reference.name.as_str())
                && reference
                    .reference_id
                    .get()
                    .is_some_and(|id| scoping.get_reference(id).symbol_id().is_none())
    )
}

fn is_reading_context(kind: &AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::TSTypeQuery(_)
            | AstKind::TSQualifiedName(_)
            | AstKind::SwitchCase(_)
            | AstKind::SwitchStatement(_)
            | AstKind::IfStatement(_)
            | AstKind::ForStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
    )
}

pub(crate) fn has_direct_eval(semantic: &oxc_semantic::Semantic<'_>) -> bool {
    !direct_evals_of(semantic).is_empty()
}

/// The `eval` references of a file that are direct eval calls.
pub(crate) fn direct_evals_of(semantic: &oxc_semantic::Semantic<'_>) -> Vec<NodeId> {
    let nodes = semantic.nodes();
    let scoping = semantic.scoping();

    scoping
        .root_unresolved_references()
        .get("eval")
        .map(|references| {
            references
                .iter()
                .map(|reference| scoping.get_reference(*reference).node_id())
                .filter(|node| is_direct_call(nodes, *node))
                .collect()
        })
        .unwrap_or_default()
}

pub(crate) fn is_direct_call(nodes: &AstNodes<'_>, node: NodeId) -> bool {
    let callee = outermost_of(nodes, node);

    matches!(
        nodes.parent_kind(callee),
        AstKind::CallExpression(call) if call.callee.span() == nodes.kind(callee).span()
    )
}

pub(crate) fn outermost_of(nodes: &AstNodes<'_>, node: NodeId) -> NodeId {
    let mut current = node;

    while matches!(
        nodes.parent_kind(current),
        AstKind::ParenthesizedExpression(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSTypeAssertion(_)
            | AstKind::TSInstantiationExpression(_)
    ) {
        current = nodes.parent_id(current);
    }

    current
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn cardinality_of(&mut self, file: FileId, e: &'a Expression<'a>) -> Cardinality {
        let size_use = self.size_use_of(file, e);
        let measure = self.measure_of(file, e, 0);
        let constant = match size_use {
            SizeUse::Length => measure.counts(),
            SizeUse::Keys => measure.constant,
            SizeUse::Enumerated => measure.constant && self.is_inheritance_closed(measure.shape),
        };

        if constant {
            return Cardinality::Constant;
        }

        let quantity = match (size_use, measure.shape) {
            (SizeUse::Length, Shape::Object) | (SizeUse::Keys | SizeUse::Enumerated, _) => {
                SizeQuantity::Keys
            }
            (SizeUse::Length, _) => SizeQuantity::Length,
        };
        let value = self.storage_value_of(file, e);
        let origin = self
            .values
            .origin_of_value(value)
            .unwrap_or_else(|| self.source_span(file, e.span()));

        Cardinality::Symbolic(SizeId { origin, quantity })
    }

    pub fn size_of_value(&mut self, file: FileId, e: &'a Expression<'a>) -> Option<Cost> {
        (self.cardinality_of(file, e) == Cardinality::Constant).then_some(Cost::ONE)
    }

    fn size_use_of(&self, file: FileId, e: &'a Expression<'a>) -> SizeUse {
        let project = self.project;
        let source = project.file(file);
        let nodes = source.semantic.nodes();
        let span = e.span();

        match nodes.parent_kind(e.node_id()) {
            AstKind::ForInStatement(statement) if statement.right.span() == span => {
                SizeUse::Enumerated
            }
            AstKind::SpreadElement(spread)
                if matches!(
                    nodes.parent_kind(spread.node_id()),
                    AstKind::ObjectExpression(_)
                ) =>
            {
                SizeUse::Keys
            }
            AstKind::CallExpression(call)
                if call
                    .arguments
                    .iter()
                    .any(|argument| argument.span() == span) =>
            {
                match member_expression_of(unwrap(&call.callee)) {
                    Some(MemberExpression::StaticMemberExpression(callee))
                        if OBJECT_KEYED.contains(&callee.property.name.as_str())
                            && is_unbound_named(
                                source.semantic.scoping(),
                                &callee.object,
                                &["Object"],
                            ) =>
                    {
                        SizeUse::Keys
                    }
                    _ => SizeUse::Length,
                }
            }
            _ => SizeUse::Length,
        }
    }

    pub fn is_closed(&mut self, file: FileId, e: &'a Expression<'a>) -> bool {
        let measure = self.measure_of(file, e, 0);

        measure.constant && self.is_inheritance_closed(measure.shape)
    }

    pub(crate) fn declaration_is_constant_sized(&mut self, declaration: Declaration<'a>) -> bool {
        self.declaration_measure_of(declaration, 0)
            .is_some_and(Measure::counts)
    }

    pub(crate) fn declaration_has_constant_keys(&mut self, declaration: Declaration<'a>) -> bool {
        self.declaration_measure_of(declaration, 0)
            .is_some_and(|measure| measure.constant)
    }

    pub(crate) fn declaration_has_exact_size(&mut self, declaration: Declaration<'a>) -> bool {
        let Some(measure) = self.declaration_measure_of(declaration, 0) else {
            return false;
        };
        let Some((file, symbol, _)) = symbol_of_declaration(&declaration) else {
            return false;
        };

        measure.counts()
            && (!measure.shape.needs_history()
                || self.is_stable_symbol(file, symbol, measure.shape, true))
    }

    fn is_inheritance_closed(&mut self, shape: Shape) -> bool {
        !self.may_extend_inherited_keys(shape.inherited_kind())
    }

    fn measure_of(&mut self, file: FileId, e: &'a Expression<'a>, depth: usize) -> Measure {
        if depth > MAXIMUM_SIZE_DEPTH {
            return Measure::VARIABLE;
        }

        let e = unwrap(e);

        match e {
            Expression::ArrayExpression(array) => {
                let mut constant = true;

                for element in &array.elements {
                    if let ArrayExpressionElement::SpreadElement(spread) = element {
                        constant &= self.measure_of(file, &spread.argument, depth + 1).counts();
                    }
                }

                return Measure::of(constant, Shape::Array);
            }
            Expression::ObjectExpression(object) => {
                let mut constant = true;

                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            constant &= self.measure_of(file, &spread.argument, depth + 1).constant;
                        }
                        ObjectPropertyKind::ObjectProperty(property) => {
                            constant &= property.kind == PropertyKind::Init
                                && !property.method
                                && (property.computed
                                    || property.shorthand
                                    || !property.key.is_specific_static_name("__proto__"))
                                && self.is_inert_property(file, &property.value);
                        }
                    }
                }

                return Measure::of(constant, Shape::Object);
            }
            Expression::StringLiteral(_) => return Measure::of(true, Shape::Primitive),
            Expression::TemplateLiteral(template) => {
                return Measure::of(template.expressions.is_empty(), Shape::Primitive)
            }
            Expression::ConditionalExpression(conditional) => {
                let consequent = self.measure_of(file, &conditional.consequent, depth + 1);
                let alternate = self.measure_of(file, &conditional.alternate, depth + 1);

                return Measure::of(
                    consequent.constant && alternate.constant,
                    consequent.shape.join(alternate.shape),
                );
            }
            Expression::BinaryExpression(binary) if binary.operator == BinaryOperator::Addition => {
                let left = self.measure_of(file, &binary.left, depth + 1);
                let right = self.measure_of(file, &binary.right, depth + 1);
                let left = left.counts() && left.shape == Shape::Primitive;
                let right = right.counts() && right.shape == Shape::Primitive;
                let constant = (left || right)
                    && (left || self.is_numeric_constant(file, &binary.left))
                    && (right || self.is_numeric_constant(file, &binary.right));

                return Measure::of(constant, Shape::Primitive);
            }
            Expression::BinaryExpression(_) | Expression::UnaryExpression(_) => {
                return Measure::of(false, Shape::Primitive)
            }
            Expression::NewExpression(new) => return self.construction_measure_of(file, new),
            _ => {}
        }

        if let Some(call) = call_of(e) {
            return self.call_measure_of(file, call, depth);
        }

        let declaration = match e {
            Expression::Identifier(reference) => {
                self.declarations
                    .of_reference(self.project, file, reference)
            }
            _ => {
                member_expression_of(e).and_then(|member| self.declaration_of_access(file, member))
            }
        };

        match declaration {
            Some(Declaration::EnumMember {
                file: target,
                member,
            }) => match &member.initializer {
                Some(initializer) => {
                    let measure = self.measure_of(target, initializer, depth + 1);

                    Measure::of(measure.constant, Shape::Primitive)
                }
                None => Measure::of(false, Shape::Primitive),
            },
            Some(declaration) => self
                .declaration_measure_of(declaration, depth + 1)
                .unwrap_or(Measure::VARIABLE),
            None => Measure::VARIABLE,
        }
    }

    fn construction_measure_of(
        &mut self,
        file: FileId,
        new: &'a oxc_ast::ast::NewExpression<'a>,
    ) -> Measure {
        let scoping = self.project.file(file).semantic.scoping();
        let typed = is_unbound_named(scoping, &new.callee, TYPED_ARRAYS);
        let array = is_unbound_named(scoping, &new.callee, &["Array"]);

        if !(typed || array) || self.intrinsic_replaced_of(file, &new.callee) {
            return Measure::VARIABLE;
        }

        let sized = new.arguments.len() == 1
            && new.arguments[0]
                .as_expression()
                .is_some_and(|argument| self.is_numeric_constant(file, argument));

        match typed {
            true => Measure::of(sized, Shape::Fixed),
            false => Measure::of(sized, Shape::Array),
        }
    }

    fn call_measure_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        depth: usize,
    ) -> Measure {
        let Some(MemberExpression::StaticMemberExpression(callee)) =
            member_expression_of(unwrap(&call.callee))
        else {
            return Measure::VARIABLE;
        };
        let method = callee.property.name.as_str();
        let scoping = self.project.file(file).semantic.scoping();

        if is_unbound_named(scoping, &callee.object, &["Object"]) && OBJECT_KEYED.contains(&method)
        {
            if !self.is_intrinsic_member(file, call) {
                return Measure::VARIABLE;
            }

            let mut measures = Vec::new();

            for argument in &call.arguments {
                match argument {
                    Argument::SpreadElement(_) => return Measure::VARIABLE,
                    other => match other.as_expression() {
                        Some(expression) => {
                            measures.push(self.measure_of(file, expression, depth + 1))
                        }
                        None => return Measure::VARIABLE,
                    },
                }
            }

            let Some(first) = measures.first().copied() else {
                return Measure::VARIABLE;
            };

            return match method {
                "assign" => Measure::of(
                    measures.iter().all(|measure| measure.constant),
                    Shape::Unknown,
                ),
                "freeze" => first,
                _ => Measure::of(first.constant, Shape::Array),
            };
        }

        if !DERIVED_METHODS.contains(&method) {
            return Measure::VARIABLE;
        }

        let receiver = self.measure_of(file, &callee.object, depth + 1);

        if !receiver.counts() || !self.is_intrinsic_member(file, call) {
            return Measure::VARIABLE;
        }

        let shape = match RECEIVER_RETURNING_METHODS.contains(&method) {
            true => receiver.shape,
            false => Shape::Array,
        };
        let constant = match method {
            "flatMap" => match call.arguments.first().and_then(Argument::as_expression) {
                Some(Expression::FunctionExpression(function)) => {
                    self.returns_constant_sized(file, FunctionNode::Function(function))
                }
                Some(Expression::ArrowFunctionExpression(arrow)) => {
                    self.returns_constant_sized(file, FunctionNode::Arrow(arrow))
                }
                _ => false,
            },
            "concat" => call
                .arguments
                .iter()
                .all(|argument| self.is_constant_sized_argument(file, argument)),
            "toSpliced" => call
                .arguments
                .iter()
                .all(|argument| !matches!(argument, Argument::SpreadElement(_))),
            _ => true,
        };

        Measure::of(constant, shape)
    }

    fn declaration_measure_of(
        &mut self,
        declaration: Declaration<'a>,
        depth: usize,
    ) -> Option<Measure> {
        let (file, symbol, node) = symbol_of_declaration(&declaration)?;

        if let Some(known) = self.values.sizes.declarations.get(&(file, node)) {
            return *known;
        }

        self.values.sizes.declarations.insert((file, node), None);

        let measure = match declaration {
            Declaration::Enum { declaration, .. } => {
                Some(Measure::of(!declaration.declare, Shape::Object))
            }
            _ => constant_initializer_of(declaration)
                .map(|(target, initializer)| self.measure_of(target, initializer, depth + 1)),
        };
        let measure = measure.map(|measure| {
            let stable = !measure.constant
                || !measure.shape.needs_history()
                || self.is_stable_symbol(file, symbol, measure.shape, false);

            Measure::of(measure.constant && stable, measure.shape)
        });

        self.values.sizes.declarations.insert((file, node), measure);

        measure
    }

    fn is_inert_property(&mut self, file: FileId, value: &'a Expression<'a>) -> bool {
        matches!(
            unwrap(value),
            Expression::ArrayExpression(_)
                | Expression::ObjectExpression(_)
                | Expression::ArrowFunctionExpression(_)
                | Expression::ClassExpression(_)
        ) || self.is_non_callable_expression(file, value)
    }

    pub(crate) fn is_intrinsic_member(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> bool {
        let Some(member) = member_expression_of(unwrap(&call.callee)) else {
            return false;
        };
        let dispatch = self.member_dispatch_of(file, member);

        dispatch.known.is_empty() && !dispatch.replaced && !self.work_exhausted()
    }

    pub(crate) fn holder_growth_of(
        &mut self,
        declaration: Declaration<'a>,
        primitive: bool,
    ) -> Growth<'a> {
        let Some((file, symbol, _)) = symbol_of_declaration(&declaration) else {
            return Growth::Unstable;
        };
        let shape = match primitive {
            true => Shape::Primitive,
            false => Shape::Array,
        };
        let key = (file, symbol, shape);
        let summary = match self.values.sizes.growths.get(&key) {
            Some(summary) => summary.clone(),
            None => {
                let summary = self.growth_summary_of(file, symbol, shape);

                self.values.sizes.growths.insert(key, summary.clone());

                summary
            }
        };

        match summary {
            GrowthSummary::Stable => Growth::Stable,
            GrowthSummary::Unstable => Growth::Unstable,
            GrowthSummary::Sites { calls, open } => Growth::Sites {
                calls: calls
                    .into_iter()
                    .filter_map(|node| match self.kind_of_node(file, node) {
                        AstKind::CallExpression(call) => Some(call),
                        _ => None,
                    })
                    .collect(),
                open,
            },
        }
    }

    fn growth_summary_of(&mut self, file: FileId, symbol: SymbolId, shape: Shape) -> GrowthSummary {
        if !shape.needs_history() || self.is_stable_symbol(file, symbol, shape, false) {
            return GrowthSummary::Stable;
        }

        let project = self.project;
        let scoping = project.file(file).semantic.scoping();
        let function = self.enclosing_function_of(file, scoping.symbol_declaration(symbol));

        if function.is_none() || self.evaluates_directly(file) {
            return GrowthSummary::Unstable;
        }

        let references = value_references_of(scoping, symbol);
        let holder = Holder {
            function,
            shape,
            exact: false,
        };
        let mut calls = Vec::new();
        let mut open = false;
        let mut summary = HolderSummary {
            stable: true,
            returned: false,
            local: true,
            function,
        };

        for (node, written) in references {
            if !self.charge_work(Event::SizeStep, 1) {
                return GrowthSummary::Sites { calls, open: true };
            }

            let local = self.enclosing_function_of(file, node) == function;

            summary.local &= local;

            if written {
                open = true;

                continue;
            }

            if let Some(call) = self.growing_call_of(file, node) {
                match local {
                    true => calls.push(call.node_id()),
                    false => open = true,
                }

                continue;
            }

            if !self.is_stable_use(file, node, holder, &mut summary, 0) {
                open = true;
            }
        }

        open |= summary.returned && !summary.local;

        match calls.is_empty() {
            true => GrowthSummary::Unstable,
            false => GrowthSummary::Sites { calls, open },
        }
    }

    /// Whether the local holder `symbol` keeps its initializer's size up to the first entry into
    /// `region`: every reference outside `region` is a stable use in the holder's own function, and
    /// `region` lies in that function outside every loop, so it is entered once per call.
    pub(crate) fn is_stable_before(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        region: NodeId,
    ) -> bool {
        let project = self.project;
        let source = project.file(file);
        let scoping = source.semantic.scoping();
        let nodes = source.semantic.nodes();
        let function = self.enclosing_function_of(file, scoping.symbol_declaration(symbol));

        if function.is_none()
            || self.evaluates_directly(file)
            || self.enclosing_function_of(file, region) != function
            || nodes
                .ancestor_ids(region)
                .take_while(|ancestor| Some(*ancestor) != function)
                .any(|ancestor| crate::syntax::is_iteration_kind(&nodes.kind(ancestor)))
        {
            return false;
        }

        let holder = Holder {
            function,
            shape: Shape::Array,
            exact: false,
        };
        let mut summary = HolderSummary {
            stable: true,
            returned: false,
            local: true,
            function,
        };

        for (node, written) in value_references_of(scoping, symbol) {
            if !self.charge_work(Event::SizeStep, 1) {
                return false;
            }

            if nodes.ancestor_ids(node).any(|ancestor| ancestor == region) {
                continue;
            }

            if written
                || self.enclosing_function_of(file, node) != function
                || !self.is_stable_use(file, node, holder, &mut summary, 0)
            {
                return false;
            }
        }

        true
    }

    /// Whether the function that binds `symbol` resizes its value in place by an amount its size
    /// cannot track: a resizing site that can repeat, inside a loop, a nested function or a
    /// recursive call of the binding function, or a site that adds a data-dependent number of
    /// entries or writes a member, which can extend an array's `length` to any value. The one site
    /// that keeps the input dimension is a non-spread `push`, `unshift`, `add` or `set` call that
    /// runs once per call of a non-recursive function, adding a constant.
    pub(crate) fn is_resized_in_place(&mut self, file: FileId, symbol: SymbolId) -> bool {
        let resizing = match self.values.sizes.resized.get(&(file, symbol)) {
            Some(resizing) => *resizing,
            None => {
                let resizing = self.resizing_of(file, symbol, None);

                self.values.sizes.resized.insert((file, symbol), resizing);

                resizing
            }
        };

        self.is_untracked_resizing(file, symbol, resizing)
    }

    /// `is_resized_in_place`, ignoring the resizing sites inside `region` when `region` is entered
    /// once per call, outside every loop of the binding function.
    pub(crate) fn is_resized_outside(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        region: Option<NodeId>,
    ) -> bool {
        let resizing = self.resizing_of(file, symbol, region);

        self.is_untracked_resizing(file, symbol, resizing)
    }

    /// Whether `resizing` leaves the size of `symbol` untracked. A bounded site in a function that
    /// recurs runs once per recursive call, so it adds as many entries as the recursion is deep.
    /// The recursion is read at each query, since a function joins a recurrence only once the
    /// scheduler finds its cycle.
    fn is_untracked_resizing(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        resizing: Resizing,
    ) -> bool {
        match resizing {
            Resizing::Unchanged => false,
            Resizing::Untracked => true,
            Resizing::Bounded => {
                let scoping = self.project.file(file).semantic.scoping();

                self.enclosing_function_of(file, scoping.symbol_declaration(symbol))
                    .is_none_or(|node| {
                        self.may_recur(crate::declarations::FunctionId { file, node })
                    })
            }
        }
    }

    fn resizing_of(&mut self, file: FileId, symbol: SymbolId, region: Option<NodeId>) -> Resizing {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let nodes = semantic.nodes();
        let references = value_references_of(semantic.scoping(), symbol);
        let function =
            self.enclosing_function_of(file, semantic.scoping().symbol_declaration(symbol));

        if !self.charge_work(Event::SizeStep, references.len() as u64) {
            return Resizing::Untracked;
        }

        let mut resizing = Resizing::Unchanged;
        // A region inside a loop is entered again after its own resizing sites ran.
        let region = region.filter(|region| {
            self.enclosing_function_of(file, *region) == function
                && !nodes
                    .ancestor_ids(*region)
                    .take_while(|ancestor| Some(*ancestor) != function)
                    .any(|ancestor| crate::syntax::is_iteration_kind(&nodes.kind(ancestor)))
        });

        for (node, _) in references {
            if resizing == Resizing::Untracked {
                break;
            }

            if region
                .is_some_and(|region| nodes.ancestor_ids(node).any(|ancestor| ancestor == region))
            {
                continue;
            }

            let current = outermost_of(nodes, node);
            let span = nodes.kind(current).span();
            let member = nodes.parent_id(current);
            let (object, name) = match nodes.kind(member) {
                AstKind::StaticMemberExpression(access) => {
                    (access.object.span(), Some(access.property.name.as_str()))
                }
                AstKind::ComputedMemberExpression(access) => (access.object.span(), None),
                _ => continue,
            };

            if object != span {
                continue;
            }

            let accessed = outermost_of(nodes, member);
            let accessed_span = nodes.kind(accessed).span();
            let (resizes, counted) = match nodes.parent_kind(accessed) {
                AstKind::CallExpression(call) if call.callee.span() == accessed_span => {
                    let resizes = name.is_some_and(|name| RESIZING_METHODS.contains(&name))
                        && self.is_intrinsic_member(file, call);
                    let counted = name.is_some_and(|name| COUNTED_RESIZING_METHODS.contains(&name))
                        && !call
                            .arguments
                            .iter()
                            .any(|argument| matches!(argument, Argument::SpreadElement(_)));

                    (resizes, counted)
                }
                AstKind::AssignmentExpression(assignment) => {
                    (assignment.left.span() == accessed_span, false)
                }
                AstKind::UpdateExpression(_) => (true, false),
                AstKind::UnaryExpression(unary) => (unary.operator == UnaryOperator::Delete, false),
                _ => (false, false),
            };

            if !resizes {
                continue;
            }

            // A site that runs at most once per call adds a constant to the size.
            let repeated = self.enclosing_function_of(file, node) != function
                || nodes
                    .ancestor_ids(node)
                    .take_while(|ancestor| Some(*ancestor) != function)
                    .any(|ancestor| crate::syntax::is_iteration_kind(&nodes.kind(ancestor)));

            resizing = if repeated || !counted {
                Resizing::Untracked
            } else {
                Resizing::Bounded
            };
        }

        resizing
    }

    pub(crate) fn has_deleted_entries(
        &mut self,
        file: FileId,
        reference: &'a oxc_ast::ast::IdentifierReference<'a>,
    ) -> bool {
        let project = self.project;
        let semantic = &project.file(file).semantic;
        let Some(symbol) = reference
            .reference_id
            .get()
            .and_then(|id| semantic.scoping().get_reference(id).symbol_id())
        else {
            return false;
        };
        let references = value_references_of(semantic.scoping(), symbol);

        if !self.charge_work(Event::SizeStep, references.len() as u64) {
            return true;
        }

        let nodes = semantic.nodes();

        references.into_iter().any(|(node, _)| {
            let current = outermost_of(nodes, node);
            let member = nodes.parent_id(current);
            let AstKind::StaticMemberExpression(access) = nodes.kind(member) else {
                return false;
            };

            if access.object.span() != nodes.kind(current).span()
                || !DELETING_METHODS.contains(&access.property.name.as_str())
            {
                return false;
            }

            let callee = outermost_of(nodes, member);

            matches!(
                nodes.parent_kind(callee),
                AstKind::CallExpression(call) if call.callee.span() == nodes.kind(callee).span()
            )
        })
    }

    fn growing_call_of(&mut self, file: FileId, node: NodeId) -> Option<&'a CallExpression<'a>> {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let current = outermost_of(nodes, node);
        let span = nodes.kind(current).span();
        let member = nodes.parent_id(current);
        let AstKind::StaticMemberExpression(access) = nodes.kind(member) else {
            return None;
        };

        if access.object.span() != span || !GROWING_METHODS.contains(&access.property.name.as_str())
        {
            return None;
        }

        let callee = outermost_of(nodes, member);
        let AstKind::CallExpression(call) = nodes.parent_kind(callee) else {
            return None;
        };

        if call.callee.span() != nodes.kind(callee).span() || !self.is_intrinsic_member(file, call)
        {
            return None;
        }

        Some(call)
    }

    fn evaluates_directly(&mut self, file: FileId) -> bool {
        if let Some(found) = self.values.sizes.evaluating.get(&file) {
            return *found;
        }

        let found = has_direct_eval(&self.project.file(file).semantic);

        self.values.sizes.evaluating.insert(file, found);

        found
    }

    fn is_stable_symbol(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        shape: Shape,
        exact: bool,
    ) -> bool {
        let summary = self.holder_summary_of(file, symbol, shape, exact, 0);

        summary.stable && (!summary.returned || (summary.local && summary.function.is_some()))
    }

    fn holder_summary_of(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        shape: Shape,
        exact: bool,
        depth: usize,
    ) -> HolderSummary {
        let key = (file, symbol, shape, exact);

        if let Some(summary) = self.values.sizes.holders.get(&key) {
            return *summary;
        }

        self.values
            .sizes
            .holders
            .insert(key, HolderSummary::UNSTABLE);
        self.stats.count("sizes: holder");

        let summary = match depth > MAXIMUM_ALIAS_DEPTH {
            true => HolderSummary::UNSTABLE,
            false => self.holder_summary_within(file, symbol, shape, exact, depth),
        };

        self.values.sizes.holders.insert(key, summary);

        summary
    }

    fn holder_summary_within(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        shape: Shape,
        exact: bool,
        depth: usize,
    ) -> HolderSummary {
        if self.evaluates_directly(file) {
            return HolderSummary::UNSTABLE;
        }

        let project = self.project;
        let source = project.file(file);
        let scoping = source.semantic.scoping();
        let nodes = source.semantic.nodes();
        let declaration = scoping.symbol_declaration(symbol);
        let variable = matches!(
            nodes.kind(declaration),
            AstKind::VariableDeclarator(_) | AstKind::TSEnumDeclaration(_)
        );
        let exported = variable
            && nodes.ancestors(declaration).take(3).any(|ancestor| {
                matches!(
                    ancestor.kind(),
                    AstKind::ExportDeclaration(_)
                        | AstKind::ExportNamedDeclaration(_)
                        | AstKind::ExportDefaultDeclaration(_)
                )
            });
        let ambient = match nodes.parent_kind(declaration) {
            AstKind::VariableDeclaration(statement) => statement.declare,
            _ => {
                matches!(nodes.kind(declaration), AstKind::TSEnumDeclaration(enumeration) if enumeration.declare)
            }
        };
        let global = scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
            && !source.module_record.has_module_syntax;

        if exported || ambient || global {
            return HolderSummary::UNSTABLE;
        }

        let function = self.enclosing_function_of(file, declaration);

        if !variable && function.is_none_or(|function| self.dynamic_scope_of(file, function).1) {
            return HolderSummary::UNSTABLE;
        }

        let references = value_references_of(scoping, symbol);
        let mut summary = HolderSummary {
            stable: true,
            returned: false,
            local: true,
            function,
        };
        let holder = Holder {
            function,
            shape,
            exact,
        };

        for (node, written) in references {
            if !self.charge_work(Event::SizeStep, 1) {
                return HolderSummary::UNSTABLE;
            }

            summary.local &= self.enclosing_function_of(file, node) == function;

            if written || !self.is_stable_use(file, node, holder, &mut summary, depth) {
                return HolderSummary::UNSTABLE;
            }
        }

        summary
    }

    fn is_inert_holder(&mut self, shape: Shape, names: &[&str]) -> bool {
        let kind = match shape {
            Shape::Primitive | Shape::Fixed => return true,
            Shape::Array => Kind::Array,
            Shape::Object => Kind::Other,
            Shape::Unknown => Kind::Unknown,
        };

        !self.builtin_members_replaced(kind, names)
    }

    fn is_stable_alias(
        &mut self,
        file: FileId,
        symbol: SymbolId,
        holder: Holder,
        summary: &mut HolderSummary,
        depth: usize,
    ) -> bool {
        let alias = self.holder_summary_of(file, symbol, holder.shape, holder.exact, depth + 1);

        summary.returned |= alias.returned;
        summary.local &= alias.local && alias.function == holder.function;

        alias.stable
    }

    fn is_stable_use(
        &mut self,
        file: FileId,
        node: NodeId,
        holder: Holder,
        summary: &mut HolderSummary,
        depth: usize,
    ) -> bool {
        let project = self.project;
        let nodes = project.file(file).semantic.nodes();
        let mut current = node;

        loop {
            current = outermost_of(nodes, current);

            let span = nodes.kind(current).span();
            let parent = nodes.parent_id(current);

            if parent == current {
                return false;
            }

            match nodes.kind(parent) {
                AstKind::LogicalExpression(_) | AstKind::ChainExpression(_) => current = parent,
                AstKind::AwaitExpression(_) => {
                    if !self.is_inert_holder(holder.shape, &AWAITED_MEMBERS) {
                        return false;
                    }

                    current = parent;
                }
                AstKind::ConditionalExpression(conditional) => {
                    if conditional.test.span() == span {
                        return true;
                    }

                    current = parent;
                }
                AstKind::SequenceExpression(sequence) => {
                    if sequence.expressions.last().map(GetSpan::span) != Some(span) {
                        return true;
                    }

                    current = parent;
                }
                AstKind::TemplateLiteral(_) => {
                    return !matches!(
                        nodes.parent_kind(parent),
                        AstKind::TaggedTemplateExpression(_)
                    ) && self.is_inert_holder(holder.shape, &COERCED_MEMBERS)
                }
                AstKind::BinaryExpression(binary) => {
                    return match binary.operator {
                        BinaryOperator::StrictEquality | BinaryOperator::StrictInequality => true,
                        BinaryOperator::In if binary.right.span() == span => true,
                        _ => self.is_inert_holder(holder.shape, &COERCED_MEMBERS),
                    }
                }
                AstKind::UnaryExpression(unary) => {
                    return match unary.operator {
                        UnaryOperator::Delete => false,
                        UnaryOperator::Typeof | UnaryOperator::Void | UnaryOperator::LogicalNot => {
                            true
                        }
                        _ => self.is_inert_holder(holder.shape, &COERCED_MEMBERS),
                    }
                }
                AstKind::SpreadElement(_) => {
                    return matches!(nodes.parent_kind(parent), AstKind::ObjectExpression(_))
                        || self.is_inert_holder(holder.shape, &ITERATED_MEMBERS)
                }
                kind if is_reading_context(&kind) => return true,
                AstKind::StaticMemberExpression(member) => {
                    return member.object.span() != span
                        || self.is_stable_member_use(file, parent, holder, summary, depth)
                }
                AstKind::ComputedMemberExpression(member) => {
                    return match member.object.span() == span {
                        true => self.is_stable_member_use(file, parent, holder, summary, depth),
                        false => self.is_inert_holder(holder.shape, &COERCED_MEMBERS),
                    }
                }
                AstKind::PrivateFieldExpression(member) => {
                    return member.object.span() != span
                        || self.is_stable_member_use(file, parent, holder, summary, depth)
                }
                AstKind::CallExpression(call) => {
                    return match call
                        .arguments
                        .iter()
                        .position(|argument| argument.span() == span)
                    {
                        Some(index) => self.is_reading_call(file, call, index, holder),
                        None => false,
                    }
                }
                AstKind::NewExpression(new) => {
                    let scoping = project.file(file).semantic.scoping();

                    return new
                        .arguments
                        .first()
                        .is_some_and(|argument| argument.span() == span)
                        && (is_unbound_named(scoping, &new.callee, &ITERATING_CONSTRUCTORS)
                            || is_unbound_named(scoping, &new.callee, TYPED_ARRAYS))
                        && !self.intrinsic_replaced_of(file, &new.callee)
                        && self.is_inert_holder(holder.shape, &ITERATED_MEMBERS);
                }
                AstKind::VariableDeclarator(declarator) => {
                    if declarator.init.as_ref().map(GetSpan::span) != Some(span) {
                        return false;
                    }

                    return match &declarator.id {
                        BindingPattern::BindingIdentifier(identifier) => {
                            match identifier.symbol_id.get() {
                                Some(symbol) => {
                                    self.is_stable_alias(file, symbol, holder, summary, depth)
                                }
                                None => false,
                            }
                        }
                        BindingPattern::ArrayPattern(_) => {
                            self.is_inert_holder(holder.shape, &ITERATED_MEMBERS)
                        }
                        _ => true,
                    };
                }
                AstKind::AssignmentExpression(assignment) => {
                    if assignment.right.span() != span {
                        return false;
                    }

                    if !assignment.operator.is_assign() && !assignment.operator.is_logical() {
                        return self.is_inert_holder(holder.shape, &COERCED_MEMBERS);
                    }

                    match &assignment.left {
                        AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                            let Some(crate::declarations::Binding::Symbol {
                                file: target,
                                symbol,
                            }) = self.binding_of_identifier(file, reference)
                            else {
                                return false;
                            };

                            if target != file
                                || !self.is_stable_alias(target, symbol, holder, summary, depth)
                            {
                                return false;
                            }
                        }
                        AssignmentTarget::ArrayAssignmentTarget(_) => {
                            if !self.is_inert_holder(holder.shape, &ITERATED_MEMBERS) {
                                return false;
                            }
                        }
                        AssignmentTarget::ObjectAssignmentTarget(_) => {}
                        _ => return false,
                    }

                    current = parent;
                }
                AstKind::ForOfStatement(statement) => {
                    return statement.right.span() == span
                        && self.is_inert_holder(holder.shape, &ITERATED_MEMBERS)
                }
                AstKind::ForInStatement(statement) => return statement.right.span() == span,
                AstKind::ReturnStatement(_) => {
                    summary.returned = true;

                    return true;
                }
                AstKind::ExpressionStatement(_) => {
                    let body = nodes.parent_id(parent);

                    if matches!(
                        nodes.parent_kind(body),
                        AstKind::ArrowFunctionExpression(arrow) if arrow.get_expression().is_some()
                    ) {
                        summary.returned = true;
                    }

                    return true;
                }
                _ => return false,
            }
        }
    }

    fn is_stable_member_use(
        &mut self,
        file: FileId,
        member: NodeId,
        holder: Holder,
        summary: &mut HolderSummary,
        depth: usize,
    ) -> bool {
        let nodes = self.project.file(file).semantic.nodes();
        let current = outermost_of(nodes, member);
        let span = nodes.kind(current).span();

        let stable = match nodes.parent_kind(current) {
            AstKind::CallExpression(call) if call.callee.span() == span => {
                return self.is_stable_receiver_call(file, call, member, holder, summary, depth)
            }
            AstKind::TaggedTemplateExpression(tagged) => tagged.tag.span() != span,
            AstKind::AssignmentExpression(assignment) => assignment.left.span() != span,
            AstKind::UnaryExpression(unary) => unary.operator != UnaryOperator::Delete,
            AstKind::AssignmentTargetWithDefault(target) => target.binding.span() != span,
            AstKind::AssignmentTargetPropertyProperty(property) => property.binding.span() != span,
            AstKind::ForInStatement(statement) => statement.left.span() != span,
            AstKind::ForOfStatement(statement) => statement.left.span() != span,
            AstKind::UpdateExpression(_)
            | AstKind::ArrayAssignmentTarget(_)
            | AstKind::ObjectAssignmentTarget(_)
            | AstKind::AssignmentTargetRest(_) => false,
            _ => true,
        };

        stable && self.is_inert_member_read(file, member, holder)
    }

    fn is_inert_member_read(&mut self, file: FileId, member: NodeId, holder: Holder) -> bool {
        let kind = match holder.shape {
            Shape::Primitive => Kind::String,
            Shape::Fixed | Shape::Array => Kind::Array,
            Shape::Object => Kind::Other,
            Shape::Unknown => Kind::Unknown,
        };
        let indexed = matches!(holder.shape, Shape::Primitive | Shape::Fixed | Shape::Array);
        let name = match self.kind_of_node(file, member) {
            AstKind::StaticMemberExpression(access) => Some(access.property.name.to_string()),
            AstKind::ComputedMemberExpression(access) => {
                self.known_key(file, &access.expression).ok()
            }
            _ => return true,
        };
        let own = name.as_deref().is_none_or(|name| {
            name == "length"
                || name
                    .parse::<u32>()
                    .is_ok_and(|index| index.to_string() == name)
        });

        if indexed && own {
            return true;
        }

        !self.builtin_accessors_defined(kind, name.as_deref())
    }

    fn is_stable_receiver_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: NodeId,
        holder: Holder,
        summary: &mut HolderSummary,
        depth: usize,
    ) -> bool {
        if holder.shape != Shape::Array {
            return false;
        }

        let method = match self.kind_of_node(file, member) {
            AstKind::StaticMemberExpression(access) => access.property.name.to_string(),
            AstKind::ComputedMemberExpression(access) => {
                match self.known_key(file, &access.expression) {
                    Ok(key) => key,
                    Err(_) => return false,
                }
            }
            _ => return false,
        };

        if !self.is_intrinsic_member(file, call) {
            return false;
        }

        let method = method.as_str();

        if SHRINKING_METHODS.contains(&method) {
            return !holder.exact;
        }

        if method == "splice" {
            return !holder.exact
                && call.arguments.len() <= 2
                && call
                    .arguments
                    .iter()
                    .all(|argument| !matches!(argument, Argument::SpreadElement(_)));
        }

        let callback_limit = if ELEMENT_CALLBACK_METHODS.contains(&method) {
            Some(2)
        } else if ACCUMULATOR_CALLBACK_METHODS.contains(&method) {
            Some(3)
        } else {
            None
        };

        if let Some(limit) = callback_limit {
            if !self.is_isolated_callback(file, call.arguments.first(), limit) {
                return false;
            }
        } else if !READING_METHODS.contains(&method)
            && !RECEIVER_RETURNING_METHODS.contains(&method)
        {
            return false;
        }

        if RECEIVER_RETURNING_METHODS.contains(&method) {
            return self.is_stable_use(file, call.node_id(), holder, summary, depth + 1);
        }

        true
    }

    fn is_isolated_callback(
        &mut self,
        file: FileId,
        argument: Option<&'a Argument<'a>>,
        limit: usize,
    ) -> bool {
        let Some(argument) = argument else {
            return true;
        };

        match argument.as_expression().map(unwrap) {
            Some(Expression::ArrowFunctionExpression(arrow)) => {
                arrow.params.rest.is_none() && arrow.params.items.len() <= limit
            }
            Some(Expression::FunctionExpression(function)) => {
                function.params.rest.is_none()
                    && function.params.items.len() <= limit
                    && !self.dynamic_scope_of(file, function.node_id()).1
            }
            _ => false,
        }
    }

    fn is_reading_call(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        index: usize,
        holder: Holder,
    ) -> bool {
        let Some(MemberExpression::StaticMemberExpression(callee)) =
            member_expression_of(unwrap(&call.callee))
        else {
            return false;
        };
        let scoping = self.project.file(file).semantic.scoping();
        let method = callee.property.name.as_str();
        let reads = if is_unbound_named(scoping, &callee.object, &["Object"]) {
            (index == 0 && OBJECT_READERS.contains(&method)) || (index > 0 && method == "assign")
        } else if is_unbound_named(scoping, &callee.object, &["Array"]) {
            index == 0
                && (method == "isArray"
                    || (method == "from" && self.is_inert_holder(holder.shape, &ITERATED_MEMBERS)))
        } else {
            false
        };

        reads && self.is_intrinsic_member(file, call)
    }
}

#[cfg(test)]
#[path = "value_sizes.test.rs"]
mod tests;

use oxc_ast::ast::{
    Argument, CallExpression, Expression, MemberExpression, NewExpression, ObjectPropertyKind,
    RegExpFlags,
};
use oxc_ast::AstKind;
use oxc_span::{GetSpan, Span};

use crate::analysis::Analysis;
use crate::bounds::short;
use crate::cost::{Cost, ExecutionPhase, Part, Reading};
use crate::declarations::{Declaration, TargetSet};
use crate::declared_types::Kind;
use crate::flow::Completion;
use crate::invocations::{coercion_keys, iteration_keys};
use crate::project::FileId;
use crate::syntax::{identifier_of, member_expression_of, unwrap};
use crate::tables::STRING_LINEAR;
use crate::unknowns::UnknownReason;
use crate::values::{protocol_key_of, MemberKey, Size};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Identity {
    Namespace(&'static str),
    Function,
    Constructor,
    Receiver(Kind),
    Callable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Receiver,
    First,
    Keys,
    EveryKeys,
    Arity,
    Graph,
    Each,
    Every,
    Elements,
    Nested,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Work {
    Constant,
    Linear(Operand),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Count {
    Once,
    PerElement,
    PerMatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Read,
    Coerced,
    Pattern(&'static [&'static str]),
    Iterated,
    Inspected,
    Serialized,
    Written,
    Opaque,
    Callback(Count),
    Grouping,
    Executor,
    Callee,
    Forwarded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Output {
    Unrelated,
    Copied,
    Concatenated,
    Flattened,
    Produced,
    Repeated,
    Padded,
    Joined,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeModel {
    pub identity: Identity,
    pub names: &'static [&'static str],
    pub work: Work,
    pub receiver: Role,
    pub arguments: &'static [Role],
    pub rest: Role,
    pub phase: ExecutionPhase,
    pub output: Output,
}

impl Output {
    pub fn materializes(self) -> bool {
        matches!(self, Output::Repeated | Output::Padded)
    }
}

impl Role {
    pub fn invokes(self) -> bool {
        matches!(self, Role::Callback(_) | Role::Grouping | Role::Executor)
    }

    pub fn retains(self) -> bool {
        matches!(self, Role::Written | Role::Opaque | Role::Forwarded)
    }

    pub fn exposes(self) -> bool {
        matches!(self, Role::Iterated | Role::Serialized)
    }
}

const REPLACE_KEYS: &[&str] = &["@@replace"];
const REPLACE_ALL_KEYS: &[&str] = &["@@match", "@@replace"];
const SPLIT_KEYS: &[&str] = &["@@split"];
const MATCH_KEYS: &[&str] = &["@@match"];
const MATCH_ALL_KEYS: &[&str] = &["@@match", "@@matchAll"];
const SEARCH_KEYS: &[&str] = &["@@search"];
const TO_JSON_KEYS: &[&str] = &["toJSON"];

const fn model_of(
    identity: Identity,
    names: &'static [&'static str],
    work: Work,
    arguments: &'static [Role],
    rest: Role,
) -> NativeModel {
    NativeModel {
        identity,
        names,
        work,
        receiver: Role::Read,
        arguments,
        rest,
        phase: ExecutionPhase::Immediate,
        output: Output::Unrelated,
    }
}

const fn producing(model: NativeModel, output: Output) -> NativeModel {
    NativeModel { output, ..model }
}

pub static MODELS: &[NativeModel] = &[
    producing(
        model_of(
            Identity::Namespace("Array"),
            &["from"],
            Work::Linear(Operand::First),
            &[
                Role::Iterated,
                Role::Callback(Count::PerElement),
                Role::Forwarded,
            ],
            Role::Read,
        ),
        Output::Copied,
    ),
    model_of(
        Identity::Namespace("Array"),
        &["of"],
        Work::Linear(Operand::Arity),
        &[],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Object"),
        &["keys", "freeze"],
        Work::Linear(Operand::Keys),
        &[],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Object"),
        &["values", "entries"],
        Work::Linear(Operand::Keys),
        &[Role::Inspected],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Object"),
        &["assign"],
        Work::Linear(Operand::EveryKeys),
        &[Role::Written],
        Role::Inspected,
    ),
    model_of(
        Identity::Namespace("Object"),
        &["fromEntries"],
        Work::Linear(Operand::First),
        &[Role::Opaque],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Object"),
        &["groupBy"],
        Work::Linear(Operand::First),
        &[Role::Iterated, Role::Grouping],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Map"),
        &["groupBy"],
        Work::Linear(Operand::First),
        &[Role::Iterated, Role::Callback(Count::PerElement)],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("JSON"),
        &["parse"],
        Work::Linear(Operand::First),
        &[Role::Coerced, Role::Callback(Count::PerElement)],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("JSON"),
        &["stringify"],
        Work::Linear(Operand::Graph),
        &[
            Role::Serialized,
            Role::Callback(Count::PerElement),
            Role::Coerced,
        ],
        Role::Read,
    ),
    model_of(
        Identity::Namespace("Buffer"),
        &["from"],
        Work::Linear(Operand::First),
        &[Role::Opaque],
        Role::Coerced,
    ),
    producing(
        model_of(
            Identity::Namespace("Buffer"),
            &["concat"],
            Work::Linear(Operand::Elements),
            &[Role::Read],
            Role::Coerced,
        ),
        Output::Joined,
    ),
    model_of(
        Identity::Namespace("Buffer"),
        &["alloc", "allocUnsafe"],
        Work::Linear(Operand::First),
        &[],
        Role::Coerced,
    ),
    model_of(
        Identity::Namespace("Buffer"),
        &["compare"],
        Work::Linear(Operand::First),
        &[],
        Role::Read,
    ),
    model_of(
        Identity::Function,
        &["structuredClone"],
        Work::Linear(Operand::Graph),
        &[Role::Inspected],
        Role::Opaque,
    ),
    model_of(
        Identity::Constructor,
        &["Promise"],
        Work::Constant,
        &[Role::Executor],
        Role::Read,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::Array),
            &["concat"],
            Work::Linear(Operand::Every),
            &[],
            Role::Read,
        ),
        Output::Concatenated,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::Array),
            &["flat"],
            Work::Linear(Operand::Nested),
            &[Role::Coerced],
            Role::Read,
        ),
        Output::Flattened,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::Array),
            &["flatMap"],
            Work::Linear(Operand::Each),
            &[Role::Callback(Count::PerElement), Role::Read],
            Role::Read,
        ),
        Output::Produced,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::String),
            &["concat"],
            Work::Linear(Operand::Every),
            &[],
            Role::Coerced,
        ),
        Output::Concatenated,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::String),
            &["repeat"],
            Work::Linear(Operand::Receiver),
            &[Role::Coerced],
            Role::Read,
        ),
        Output::Repeated,
    ),
    producing(
        model_of(
            Identity::Receiver(Kind::String),
            &["padStart", "padEnd"],
            Work::Linear(Operand::Receiver),
            &[Role::Coerced, Role::Coerced],
            Role::Read,
        ),
        Output::Padded,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["replace"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(REPLACE_KEYS), Role::Callback(Count::PerMatch)],
        Role::Read,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["replaceAll"],
        Work::Linear(Operand::Receiver),
        &[
            Role::Pattern(REPLACE_ALL_KEYS),
            Role::Callback(Count::PerElement),
        ],
        Role::Read,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["split"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(SPLIT_KEYS)],
        Role::Coerced,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["match"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(MATCH_KEYS)],
        Role::Read,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["matchAll"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(MATCH_ALL_KEYS)],
        Role::Read,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["search"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(SEARCH_KEYS)],
        Role::Read,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        &["includes", "startsWith", "endsWith"],
        Work::Linear(Operand::Receiver),
        &[Role::Pattern(MATCH_KEYS)],
        Role::Coerced,
    ),
    model_of(
        Identity::Receiver(Kind::String),
        STRING_LINEAR,
        Work::Linear(Operand::Receiver),
        &[],
        Role::Coerced,
    ),
    NativeModel {
        identity: Identity::Callable,
        names: &["call"],
        work: Work::Constant,
        receiver: Role::Callee,
        arguments: &[],
        rest: Role::Forwarded,
        phase: ExecutionPhase::Immediate,
        output: Output::Unrelated,
    },
];

pub fn native_model_of(identity: Identity, name: &str) -> Option<&'static NativeModel> {
    MODELS
        .iter()
        .find(|model| model.identity == identity && model.names.contains(&name))
}

pub fn namespace_model_of(owner: &str, name: &str) -> Option<&'static NativeModel> {
    MODELS.iter().find(|model| {
        matches!(model.identity, Identity::Namespace(namespace) if namespace == owner)
            && model.names.contains(&name)
    })
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Native {
    Modelled(&'static NativeModel),
    Receiver(Kind),
    Unmodelled,
}

pub(crate) struct NativeSite<'a> {
    pub(crate) file: FileId,
    pub(crate) span: Span,
    pub(crate) call: Option<&'a CallExpression<'a>>,
    pub(crate) receiver: Option<&'a Expression<'a>>,
    pub(crate) name: String,
    pub(crate) arguments: &'a [Argument<'a>],
}

impl<'a> NativeSite<'a> {
    fn spread_of(&self) -> Option<usize> {
        self.arguments
            .iter()
            .position(|argument| matches!(argument, Argument::SpreadElement(_)))
    }

    fn role_of(&self, model: &NativeModel, index: usize) -> Role {
        match self.spread_of() {
            Some(spread) if index >= spread => Role::Opaque,
            _ => model.arguments.get(index).copied().unwrap_or(model.rest),
        }
    }

    fn invokes_argument(&self, model: &NativeModel) -> bool {
        (0..self.arguments.len()).any(|index| self.role_of(model, index).invokes())
    }

    fn contains(&self, model: &NativeModel, index: usize) -> bool {
        let role = self.role_of(model, index);

        !role.retains() && !(role.exposes() && self.invokes_argument(model))
    }

    fn hides_invocation(&self, model: &NativeModel) -> bool {
        let Some(spread) = self.spread_of() else {
            return false;
        };

        model.rest.invokes()
            || model
                .arguments
                .iter()
                .skip(spread)
                .any(|role| role.invokes())
    }

    fn expression_at(&self, index: usize) -> Option<&'a Expression<'a>> {
        self.arguments.get(index).and_then(Argument::as_expression)
    }
}

fn global_flag_of(pattern: &Expression<'_>) -> Option<bool> {
    match unwrap(pattern) {
        Expression::RegExpLiteral(literal) => Some(literal.regex.flags.contains(RegExpFlags::G)),
        _ => None,
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn is_intrinsic_reference(
        &self,
        file: FileId,
        reference: &'a oxc_ast::ast::IdentifierReference<'a>,
    ) -> bool {
        let semantic = &self.project.file(file).semantic;
        let bound = reference
            .reference_id
            .get()
            .and_then(|id| semantic.scoping().get_reference(id).symbol_id());

        if bound.is_none() {
            return true;
        }

        match self
            .declarations
            .of_reference(self.project, file, reference)
        {
            Some(Declaration::Variable {
                file: target,
                declarator,
                ..
            }) => {
                declarator.init.is_none()
                    && matches!(
                        self.project
                            .file(target)
                            .semantic
                            .nodes()
                            .parent_kind(declarator.node_id()),
                        AstKind::VariableDeclaration(declaration) if declaration.declare
                    )
            }
            _ => false,
        }
    }

    pub(crate) fn native_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: Option<&'a MemberExpression<'a>>,
        counted: bool,
    ) -> Native {
        let Some(member) = member else {
            return match identifier_of(unwrap(&call.callee)) {
                Some(reference) if self.is_intrinsic_reference(file, reference) => {
                    native_model_of(Identity::Function, reference.name.as_str())
                        .map_or(Native::Unmodelled, Native::Modelled)
                }
                _ => Native::Unmodelled,
            };
        };
        let method = self.static_member_name_of(file, member).unwrap_or_default();
        let receiver = member.object();

        if let Some(owner) = identifier_of(receiver) {
            if let Some(model) = namespace_model_of(owner.name.as_str(), &method) {
                if self.is_intrinsic_reference(file, owner) {
                    return Native::Modelled(model);
                }
            }
        }

        if let Some(model) = native_model_of(Identity::Callable, &method) {
            if !self
                .callee_targets_of_expression(file, receiver)
                .known
                .is_empty()
            {
                return Native::Modelled(model);
            }
        }

        let kind = match counted {
            true => self.kind_of(file, receiver, &method),
            false => self.receiver_kind_of(file, receiver, &method),
        };

        match native_model_of(Identity::Receiver(kind), &method) {
            Some(model) => Native::Modelled(model),
            None => Native::Receiver(kind),
        }
    }

    pub(crate) fn construction_model_of(
        &self,
        file: FileId,
        new: &'a NewExpression<'a>,
    ) -> Option<&'static NativeModel> {
        let reference = identifier_of(unwrap(&new.callee))?;

        if !self.is_intrinsic_reference(file, reference) {
            return None;
        }

        native_model_of(Identity::Constructor, reference.name.as_str())
    }

    pub(crate) fn call_site_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        member: Option<&'a MemberExpression<'a>>,
    ) -> NativeSite<'a> {
        let name = match member {
            Some(member) => self.static_member_name_of(file, member).unwrap_or_default(),
            None => identifier_of(unwrap(&call.callee))
                .map(|reference| reference.name.to_string())
                .unwrap_or_default(),
        };

        NativeSite {
            file,
            span: call.span,
            call: Some(call),
            receiver: member.map(MemberExpression::object),
            name,
            arguments: &call.arguments,
        }
    }

    pub(crate) fn construction_site_of(
        &self,
        file: FileId,
        new: &'a NewExpression<'a>,
    ) -> NativeSite<'a> {
        NativeSite {
            file,
            span: new.span,
            call: None,
            receiver: None,
            name: identifier_of(unwrap(&new.callee))
                .map(|reference| reference.name.to_string())
                .unwrap_or_default(),
            arguments: &new.arguments,
        }
    }

    fn callee_targets_of_expression(
        &mut self,
        file: FileId,
        receiver: &'a Expression<'a>,
    ) -> TargetSet {
        self.resolved_expression_callee_of(file, receiver, receiver.node_id())
            .targets
    }

    pub(crate) fn native_reading_of(
        &mut self,
        site: &NativeSite<'a>,
        model: &'static NativeModel,
        reading: Reading,
        counted: bool,
    ) -> Reading {
        let file = site.file;
        let origin = self.source_span(file, site.span);
        let charge = self.native_charge_of(site, model);
        let bounded = charge.length.is_one();
        let mut inner = Part::none();
        let mut beside = match model.receiver {
            Role::Callee => self.forwarded_part_of(site),
            _ => Part::none(),
        };

        for (index, argument) in site.arguments.iter().enumerate() {
            let role = site.role_of(model, index);
            let (part, count) = self.argument_part_of(site, argument, role);

            match count {
                Count::Once => beside = beside.max(part, &mut self.unknowns, &mut self.traces),
                _ => inner = inner.max(part, &mut self.unknowns, &mut self.traces),
            }
        }

        if model.output == Output::Produced {
            let result = self.result_size_of(file, site.arguments.first(), &charge.element, 0);
            let copied = Part::unmarked(result.length.clone(), None);

            inner = inner.max(copied, &mut self.unknowns, &mut self.traces);

            if !result.length_resolved {
                let unresolved = self.unknown_part(file, site.span, UnknownReason::SizeRelation);

                beside = beside.max(unresolved, &mut self.unknowns, &mut self.traces);
            }
        }

        if !charge.length_resolved {
            let unresolved = self.unknown_part(file, site.span, UnknownReason::SizeRelation);

            beside = beside.max(unresolved, &mut self.unknowns, &mut self.traces);
        }

        if model.output.materializes() && !self.is_counted_argument(site) {
            let materialized = self.unknown_part(file, site.span, UnknownReason::UnsupportedModel);

            beside = beside.max(materialized, &mut self.unknowns, &mut self.traces);
        }

        if site.hides_invocation(model) {
            let hidden = self.unknown_part(file, site.span, UnknownReason::Target);

            beside = beside.max(hidden, &mut self.unknowns, &mut self.traces);
        }

        let label = self.native_label_of(site, model);

        if counted {
            if let Some(statistic) = self.native_statistic_of(site, model, bounded) {
                self.stats.count(&statistic);
            }
        }

        let part = match (bounded, label) {
            (false, Some(label)) => {
                let site_of = self.project.site_of(file, site.span);

                crate::cost::nest(
                    label,
                    site_of,
                    origin,
                    charge.length,
                    inner.executed(),
                    &mut self.unknowns,
                    &mut self.traces,
                )
            }
            _ => inner,
        };
        let part = part.max(beside, &mut self.unknowns, &mut self.traces);

        if part == Part::none() {
            return reading;
        }

        let mut reading = reading;

        reading.join(
            model.phase,
            Completion::Normal,
            part,
            &mut self.unknowns,
            &mut self.traces,
        );

        reading
    }

    fn native_label_of(&self, site: &NativeSite<'a>, model: &NativeModel) -> Option<String> {
        let file = site.file;

        match model.identity {
            Identity::Namespace(owner) => {
                let argument = match site.arguments.first() {
                    Some(argument) => short(self.text_of(file, argument.span())),
                    None => String::new(),
                };

                Some(format!("{owner}.{}({argument})", site.name))
            }
            Identity::Function => Some(format!("{}()", site.name)),
            Identity::Receiver(Kind::Array) => {
                let receiver = site
                    .receiver
                    .map(|receiver| short(self.text_of(file, receiver.span())))
                    .unwrap_or_default();

                Some(format!("{receiver}.{}()", site.name))
            }
            Identity::Receiver(Kind::String) => {
                let receiver = site
                    .receiver
                    .map(|receiver| short(self.text_of(file, receiver.span())))
                    .unwrap_or_default();

                Some(format!("{receiver}.{}() [string]", site.name))
            }
            _ => None,
        }
    }

    fn native_statistic_of(
        &self,
        site: &NativeSite<'a>,
        model: &NativeModel,
        bounded: bool,
    ) -> Option<String> {
        let measure = match bounded {
            true => "bounded",
            false => "N",
        };

        match model.identity {
            Identity::Namespace(owner) => Some(format!("{owner}.{}: {measure}", site.name)),
            Identity::Receiver(Kind::Array) => Some(format!("array method: {measure}")),
            Identity::Receiver(Kind::String) => Some(format!("string method: {measure}")),
            _ => None,
        }
    }

    fn native_charge_of(&mut self, site: &NativeSite<'a>, model: &NativeModel) -> Size {
        let file = site.file;

        match model.work {
            Work::Linear(Operand::Each) => match site.receiver {
                Some(receiver) if !self.is_share_sized(file, receiver) => {
                    self.collection_size_of(file, receiver)
                }
                _ => Size::constant(),
            },
            Work::Linear(Operand::Every | Operand::Elements | Operand::Nested) => self
                .output_size_of(site, model, 0)
                .unwrap_or_else(Size::unresolved),
            Work::Linear(operand @ (Operand::Receiver | Operand::First))
                if !self.is_native_bounded(site, model.work) =>
            {
                let measured = match operand {
                    Operand::Receiver => site.receiver,
                    _ => site.expression_at(0),
                };
                let produced = measured.and_then(|measured| self.produced_size_of(file, measured));

                match produced {
                    Some(size) if size.exceeds || !size.length_resolved => size,
                    _ => Size::sized(Cost::N),
                }
            }
            work => match self.is_native_bounded(site, work) {
                true => Size::constant(),
                false => Size::sized(Cost::N),
            },
        }
    }

    fn is_counted_argument(&mut self, site: &NativeSite<'a>) -> bool {
        match site.arguments.first() {
            Some(argument) => argument
                .as_expression()
                .is_some_and(|expression| self.is_numeric_constant(site.file, expression)),
            None => true,
        }
    }

    fn is_native_bounded(&mut self, site: &NativeSite<'a>, work: Work) -> bool {
        let file = site.file;
        let first = site.arguments.first();

        match work {
            Work::Constant | Work::Linear(Operand::Arity) => true,
            Work::Linear(
                Operand::Graph
                | Operand::Each
                | Operand::Every
                | Operand::Elements
                | Operand::Nested,
            ) => false,
            Work::Linear(Operand::First) => {
                first.is_some_and(|argument| self.is_constant_sized_argument(file, argument))
            }
            Work::Linear(Operand::Keys) => {
                first.is_some_and(|argument| self.is_bounded_keys_argument(file, argument))
            }
            Work::Linear(Operand::EveryKeys) => {
                first.is_some()
                    && site
                        .arguments
                        .iter()
                        .all(|argument| self.is_bounded_keys_argument(file, argument))
            }
            Work::Linear(Operand::Receiver) => {
                site.receiver.is_some_and(|receiver| {
                    self.is_constant_sized(file, receiver) || self.is_share_sized(file, receiver)
                }) || site
                    .call
                    .is_some_and(|call| self.is_share_sized_call(file, call))
            }
        }
    }

    fn is_bounded_keys_argument(&mut self, file: FileId, argument: &'a Argument<'a>) -> bool {
        self.is_constant_sized_argument(file, argument)
            || argument
                .as_expression()
                .is_some_and(|expression| self.is_enum_object(file, expression))
            || self.is_closed_argument(file, argument)
    }

    fn argument_part_of(
        &mut self,
        site: &NativeSite<'a>,
        argument: &'a Argument<'a>,
        role: Role,
    ) -> (Part, Count) {
        let file = site.file;
        let Some(expression) = argument.as_expression() else {
            if let Argument::SpreadElement(spread) = argument {
                self.record_argument_reach(file, &spread.argument);
            }

            return (Part::none(), Count::Once);
        };

        match role {
            Role::Read | Role::Forwarded | Role::Callee => (Part::none(), Count::Once),
            Role::Coerced => (self.operand_coercion_part_of(file, expression), Count::Once),
            Role::Pattern(keys) => (self.searched_part_of(file, expression, keys), Count::Once),
            Role::Iterated => (
                self.delegated_part_of(file, expression.span(), expression, false)
                    .unwrap_or_default(),
                Count::Once,
            ),
            Role::Inspected => (self.inspected_part_of(file, expression), Count::Once),
            Role::Serialized => (self.serialized_part_of(file, expression), Count::Once),
            Role::Written => (self.written_part_of(file, expression), Count::Once),
            Role::Opaque => (self.opaque_part_of(file, expression), Count::Once),
            Role::Callback(count) => {
                if self.is_non_callable_argument(file, expression) {
                    return (self.operand_coercion_part_of(file, expression), Count::Once);
                }

                let facts = self.argument_facts_of(file, argument);
                let part = self.invoke_callback(&facts, file, argument.span(), &[]);
                let count = match count {
                    Count::PerMatch => match site.expression_at(0) {
                        Some(pattern) => match global_flag_of(pattern) {
                            Some(true) => Count::PerElement,
                            Some(false) => Count::Once,
                            None if self.is_primitive_operand(file, pattern) => Count::Once,
                            None => Count::PerElement,
                        },
                        None => Count::Once,
                    },
                    other => other,
                };

                (part, count)
            }
            Role::Grouping => {
                let facts = self.argument_facts_of(file, argument);
                let part = self.invoke_callback(&facts, file, argument.span(), &[]);
                let keyed = self.grouping_key_part_of(file, expression, &facts.value.targets);

                (
                    part.max(keyed, &mut self.unknowns, &mut self.traces),
                    Count::PerElement,
                )
            }
            Role::Executor => (self.executor_part_of(file, argument), Count::Once),
        }
    }

    fn is_non_callable_argument(&mut self, file: FileId, expression: &'a Expression<'a>) -> bool {
        matches!(
            unwrap(expression),
            Expression::ArrayExpression(_) | Expression::ObjectExpression(_)
        ) || self.is_primitive_operand(file, expression)
            || self.is_non_callable_expression(file, expression)
    }

    fn record_argument_reach(&mut self, file: FileId, expression: &'a Expression<'a>) {
        let value = self.storage_value_of(file, expression);

        for values in [
            &mut self.current_effects.unknown_reachable,
            &mut self.current_effects.escapes,
        ] {
            if !values.contains(&value) {
                values.push(value);
            }
        }
    }

    fn opaque_part_of(&mut self, file: FileId, expression: &'a Expression<'a>) -> Part {
        if self.is_primitive_operand(file, expression) {
            return Part::none();
        }

        self.record_argument_reach(file, expression);

        let keys: Vec<MemberKey> = coercion_keys()
            .into_iter()
            .chain(iteration_keys())
            .collect();

        if !self.may_access(None) && !self.may_implement_any(&keys) {
            return Part::none();
        }

        let targets = TargetSet {
            known: Vec::new(),
            open: true,
        };

        self.implicit_part_of((file, expression.span()), &targets, "native", &[expression])
    }

    fn searched_part_of(
        &mut self,
        file: FileId,
        pattern: &'a Expression<'a>,
        names: &[&str],
    ) -> Part {
        if matches!(unwrap(pattern), Expression::RegExpLiteral(_))
            || self.is_primitive_operand(file, pattern)
        {
            return Part::none();
        }

        let keys: Vec<MemberKey> = names
            .iter()
            .map(|name| protocol_key_of(name))
            .chain(coercion_keys())
            .collect();
        let targets = self.protocol_targets_of(file, pattern, &keys);

        self.implicit_part_of((file, pattern.span()), &targets, "pattern", &[pattern])
    }

    fn written_part_of(&mut self, file: FileId, target: &'a Expression<'a>) -> Part {
        let value = self.storage_value_of(file, target);

        if !self.current_effects.member_writes.contains(&value) {
            self.current_effects.member_writes.push(value);
        }

        let targets = TargetSet {
            known: Vec::new(),
            open: self.may_access(None),
        };

        self.implicit_part_of((file, target.span()), &targets, "setter", &[target])
    }

    fn serialized_part_of(&mut self, file: FileId, value: &'a Expression<'a>) -> Part {
        let inspected = self.inspected_part_of(file, value);
        let keys: Vec<MemberKey> = TO_JSON_KEYS
            .iter()
            .map(|name| protocol_key_of(name))
            .collect();

        if self.is_primitive_operand(file, value) || !self.may_implement_any(&keys) {
            return inspected;
        }

        let targets = self.protocol_targets_of(file, value, &keys);
        let root = self.implicit_part_of((file, value.span()), &targets, "toJSON", &[value]);
        let nested = match !targets.open && self.serializes_primitives(file, value, &targets) {
            true => Part::none(),
            false => self.unknown_visits_part_of(file, value),
        };

        inspected
            .max(root, &mut self.unknowns, &mut self.traces)
            .max(nested, &mut self.unknowns, &mut self.traces)
    }

    fn serializes_primitives(
        &mut self,
        file: FileId,
        value: &'a Expression<'a>,
        targets: &TargetSet,
    ) -> bool {
        if !targets.known.is_empty() {
            return targets
                .known
                .iter()
                .all(|target| self.returns_only_primitives(*target));
        }

        let values: Vec<&'a Expression<'a>> = match unwrap(value) {
            Expression::ObjectExpression(object) => {
                let mut values = Vec::new();

                for property in &object.properties {
                    let ObjectPropertyKind::ObjectProperty(property) = property else {
                        return false;
                    };

                    values.push(&property.value);
                }

                values
            }
            Expression::ArrayExpression(array) => {
                let mut values = Vec::new();

                for element in &array.elements {
                    let Some(element) = element.as_expression() else {
                        return false;
                    };

                    values.push(element);
                }

                values
            }
            _ => return self.has_primitive_elements(file, value),
        };

        values
            .into_iter()
            .all(|value| self.is_primitive_operand(file, value))
    }

    fn grouping_key_part_of(
        &mut self,
        file: FileId,
        callback: &'a Expression<'a>,
        targets: &TargetSet,
    ) -> Part {
        if !self.may_implement_any(&coercion_keys()) {
            return Part::none();
        }

        let primitive = !targets.open
            && !targets.known.is_empty()
            && targets
                .known
                .iter()
                .all(|target| self.returns_only_primitives(*target));

        if primitive {
            return Part::none();
        }

        let open = TargetSet {
            known: Vec::new(),
            open: true,
        };

        self.implicit_part_of((file, callback.span()), &open, "coercion", &[])
    }

    fn executor_part_of(&mut self, file: FileId, argument: &'a Argument<'a>) -> Part {
        let Some(expression) = argument.as_expression() else {
            return Part::none();
        };

        if self.is_non_callable_argument(file, expression) {
            return Part::none();
        }

        let facts = self.argument_facts_of(file, argument);

        self.invoke_callback(&facts, file, argument.span(), &[Part::none(), Part::none()])
    }

    fn forwarded_part_of(&mut self, site: &NativeSite<'a>) -> Part {
        let file = site.file;
        let Some(receiver) = site.receiver else {
            return Part::none();
        };
        let forwarded = match site.arguments.first() {
            Some(Argument::SpreadElement(_)) => None,
            Some(_) => Some(&site.arguments[1..]),
            None => Some(site.arguments),
        };
        let Some(forwarded) = forwarded else {
            return self
                .unknown_invocation(file, site.span, site.arguments, UnknownReason::Target)
                .main();
        };
        let targets = self.callee_targets_of_expression(file, receiver);
        let origin = self.source_span(file, site.span);
        let site_of = self.project.site_of(file, site.span);
        let remainder = match targets.open {
            true => {
                self.unknown_invocation(file, site.span, forwarded, UnknownReason::Target)
                    .main()
                    .unknowns
            }
            false => None,
        };
        let mut part = Part::none();

        for known in &targets.known {
            let function = self.function_at(*known);
            let (called, cyclic) = self.call_user(known.file, function, file, forwarded, site.span);
            let called = self.named_call_of((known.file, function), called, (site_of, origin));
            let called = called
                .called(origin, &mut self.unknowns)
                .retaining(remainder, &mut self.unknowns);
            let called = self.called_part_of(known.file, function, called, cyclic);

            part = part.max(called, &mut self.unknowns, &mut self.traces);
        }

        part
    }

    pub(crate) fn callee_member_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<&'a MemberExpression<'a>> {
        member_expression_of(unwrap(&call.callee)).filter(|member| {
            !matches!(member, MemberExpression::ComputedMemberExpression(_))
                || self.static_member_name_of(file, member).is_some()
        })
    }

    fn modelled_call_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> Option<(NativeSite<'a>, &'static NativeModel)> {
        if self.is_call_exhausted(file, call.node_id())
            || self.intrinsic_replaced_of(file, &call.callee)
        {
            return None;
        }

        let member = self.callee_member_of(file, call);
        let Native::Modelled(model) = self.native_of(file, call, member, false) else {
            return None;
        };

        Some((self.call_site_of(file, call, member), model))
    }

    pub(crate) fn records_native_effects(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
    ) -> bool {
        let Some((site, model)) = self.modelled_call_of(file, call) else {
            return false;
        };

        self.native_reading_of(&site, model, Reading::empty(), false);

        true
    }

    pub(crate) fn records_construction_effects(
        &mut self,
        file: FileId,
        new: &'a NewExpression<'a>,
    ) -> bool {
        let Some(model) = self.construction_model_of(file, new) else {
            return false;
        };

        if self.intrinsic_replaced_of(file, &new.callee) {
            return false;
        }

        let site = self.construction_site_of(file, new);

        self.native_reading_of(&site, model, Reading::empty(), false);

        true
    }

    pub(crate) fn call_size_of(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        depth: usize,
    ) -> Option<Size> {
        if self.is_call_exhausted(file, call.node_id())
            || self.intrinsic_replaced_of(file, &call.callee)
        {
            return None;
        }

        let member = self.callee_member_of(file, call);

        if member.is_some() && !self.is_intrinsic_member(file, call) {
            return None;
        }

        match self.native_of(file, call, member, false) {
            Native::Modelled(model) => {
                let site = self.call_site_of(file, call, member);

                self.output_size_of(&site, model, depth)
            }
            Native::Receiver(Kind::Array) => {
                let member = member?;
                let method = self.static_member_name_of(file, member)?;

                self.array_method_size_of(file, call, member.object(), &method, depth)
            }
            _ => None,
        }
    }

    pub(crate) fn output_size_of(
        &mut self,
        site: &NativeSite<'a>,
        model: &NativeModel,
        depth: usize,
    ) -> Option<Size> {
        let file = site.file;
        let next = depth + 1;
        let receiver = match site.receiver {
            Some(receiver) => self.collection_size_at(file, receiver, next),
            None => Size::constant(),
        };

        match model.output {
            Output::Unrelated => None,
            Output::Copied => {
                let source = match site.expression_at(0) {
                    Some(source) => self.collection_size_at(file, source, next),
                    None => Size::unresolved(),
                };

                match site.arguments.get(1) {
                    Some(callback) => {
                        let result =
                            self.result_size_of(file, Some(callback), &source.element, next);

                        Some(source.containing(&result))
                    }
                    None => Some(source),
                }
            }
            Output::Concatenated => {
                let array = model.identity == Identity::Receiver(Kind::Array);
                let mut size = receiver;

                for argument in site.arguments {
                    let operand = match argument {
                        Argument::SpreadElement(spread) => self
                            .collection_size_at(file, &spread.argument, next)
                            .flattened(),
                        _ => match argument.as_expression() {
                            Some(operand) if array && self.is_primitive_operand(file, operand) => {
                                Size::constant()
                            }
                            Some(operand) => self.collection_size_at(file, operand, next),
                            None => Size::unresolved(),
                        },
                    };

                    size = size.combined(&operand);
                }

                Some(size)
            }
            Output::Flattened => {
                let depth = match site.expression_at(0) {
                    Some(depth) => match self.known_value(file, depth).value.as_deref() {
                        Ok(crate::values::Primitive::Number(depth)) => Some(*depth),
                        _ => None,
                    },
                    None => Some(1.0),
                };

                Some(match depth {
                    Some(depth) if depth < 1.0 => receiver,
                    Some(depth) if depth < 2.0 => receiver.flattened(),
                    _ => receiver.flattened().unresolved_length(),
                })
            }
            Output::Produced => {
                let result =
                    self.result_size_of(file, site.arguments.first(), &receiver.element, next);

                Some(receiver.producing(&result))
            }
            Output::Repeated => Some(match self.count_argument_of(site, 0) {
                Some(count) => receiver.repeated(&Size::sized(count)),
                None => receiver.unresolved_length(),
            }),
            Output::Padded => Some(match self.count_argument_of(site, 0) {
                Some(count) => receiver.combined(&Size::sized(count)),
                None => receiver.unresolved_length(),
            }),
            Output::Joined => {
                let list = match site.expression_at(0) {
                    Some(list) => self.collection_size_at(file, list, next).flattened(),
                    None => Size::unresolved(),
                };

                Some(match site.arguments.get(1) {
                    None => list,
                    Some(_) => match self.count_argument_of(site, 1) {
                        Some(total) => list.combined(&Size::sized(total)),
                        None => list.unresolved_length(),
                    },
                })
            }
        }
    }

    fn count_argument_of(&mut self, site: &NativeSite<'a>, index: usize) -> Option<Cost> {
        let Some(argument) = site.arguments.get(index) else {
            return Some(Cost::ONE);
        };
        let argument = argument.as_expression()?;

        self.count_of(site.file, argument)
    }

    pub(crate) fn is_contained_native_argument(
        &mut self,
        file: FileId,
        call: &'a CallExpression<'a>,
        index: usize,
    ) -> bool {
        self.modelled_call_of(file, call)
            .is_some_and(|(site, model)| site.contains(model, index))
    }
}

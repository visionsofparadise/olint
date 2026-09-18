use super::*;
use crate::unknowns::SourceSpan;
use crate::values::Values;
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;

fn flows_of(source: &str) -> Vec<(String, ValueFlow)> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;
    let nodes = semantic.nodes();

    nodes
        .iter()
        .filter_map(|node| match node.kind() {
            AstKind::IdentifierReference(reference) if reference.name == "o" => {
                let flow = value_flow_of(nodes, node.id());
                let described = match flow {
                    ValueFlow::Read => "read".to_string(),
                    ValueFlow::Member => "member".to_string(),
                    ValueFlow::Receiver(site)
                    | ValueFlow::Alias(site)
                    | ValueFlow::Stored(site)
                    | ValueFlow::Escaped(site)
                    | ValueFlow::Argument(site, _) => {
                        nodes.kind(site).span().source_text(source).to_string()
                    }
                };

                Some((described, flow))
            }
            _ => None,
        })
        .collect()
}

fn span(start: u32) -> SourceSpan {
    SourceSpan {
        file: crate::project::FileId(0),
        start,
        end: start + 1,
    }
}

#[test]
fn value_flows_separate_member_use_from_aliases_arguments_and_escapes() {
    let source = "o.x; o.m(); typeof o; const q = o; h.y = o; f(1, (o as any)); new K(o); const c = { k: [o] }; function g() { return o; } throw o;";
    let flows = flows_of(source);
    let kinds: Vec<_> = flows
        .iter()
        .map(|(text, flow)| match flow {
            ValueFlow::Read => "read".to_string(),
            ValueFlow::Member => "member".to_string(),
            ValueFlow::Receiver(_) => format!("receiver {text}"),
            ValueFlow::Alias(_) => format!("alias {text}"),
            ValueFlow::Stored(_) => format!("stored {text}"),
            ValueFlow::Argument(_, index) => format!("argument {index} {text}"),
            ValueFlow::Escaped(_) => format!("escaped {text}"),
        })
        .collect();

    assert_eq!(
        kinds,
        [
            "member",
            "receiver o.m()",
            "read",
            "alias q = o",
            "stored h.y = o",
            "argument 1 f(1, (o as any))",
            "argument 0 new K(o)",
            "alias c = { k: [o] }",
            "escaped return o;",
            "escaped throw o;",
        ]
    );
}

#[test]
fn conditional_tests_and_computed_keys_do_not_carry_the_value() {
    let flows = flows_of("const a = o ? 1 : 2; const b = x[o]; const c = flag ? o : null;");
    let kinds: Vec<_> = flows.iter().map(|(_, flow)| *flow).collect();

    assert!(matches!(
        kinds[..],
        [ValueFlow::Read, ValueFlow::Read, ValueFlow::Alias(_)]
    ));
}

#[test]
fn joins_are_order_and_duplicate_insensitive() {
    let first = Effects {
        member_writes: vec![ValueId(1), ValueId(2)],
        unknown_reachable: vec![ValueId(3)],
        ..Effects::default()
    };
    let second = Effects {
        member_writes: vec![ValueId(2), ValueId(1)],
        escapes: vec![ValueId(4)],
        unknown_global: true,
        ..Effects::default()
    };
    let mut left = first.clone();
    let mut right = second.clone();

    left.join(&second);
    left.join(&second);
    right.join(&first);

    let sorted = |effects: &Effects| {
        let mut writes = effects.member_writes.clone();

        writes.sort();

        (
            writes,
            effects.escapes.clone(),
            effects.unknown_reachable.clone(),
        )
    };

    assert_eq!(sorted(&left), sorted(&right));
    assert!(left.unknown_global && right.unknown_global);
    assert!(Effects::default().is_empty());
    assert!(!Effects::unknown().is_empty());
}

#[test]
fn substitution_replaces_parameter_storage_with_argument_storage() {
    let mut effects = Effects {
        member_writes: vec![ValueId(7), ValueId(9)],
        escapes: vec![ValueId(7)],
        unknown_reachable: vec![ValueId(8), ValueId(7)],
        ..Effects::default()
    };

    effects.substitute(ValueId(7), ValueId(9));

    assert_eq!(effects.member_writes, [ValueId(9)]);
    assert_eq!(effects.escapes, [ValueId(9)]);
    assert_eq!(effects.unknown_reachable, [ValueId(8), ValueId(9)]);
}

#[test]
fn only_distinct_allocations_are_known_not_to_alias() {
    let mut values = Values::default();
    let first = values.allocation(span(1)).value;
    let second = values.allocation(span(2)).value;
    let parameter = values.at(span(3)).value;

    assert!(values.may_alias(first, first));
    assert!(!values.may_alias(first, second));
    assert!(values.may_alias(first, parameter));

    let other = values.at(span(4)).value;

    assert!(values.may_alias(parameter, other));
    assert_eq!(values.at(span(1)).value, first);
    assert!(values.is_allocation(first) && !values.is_allocation(parameter));
}

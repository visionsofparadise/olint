use super::*;
use crate::values::Limits;
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;

#[test]
fn foreign_enum_declaration_or_semantic_is_rejected_before_work() {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, "enum E { A=1 }", SourceType::ts()).parse();
    let foreign = Parser::new(&allocator, "enum E { A=2 }", SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;
    let foreign_semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&foreign.program)
        .semantic;
    let Statement::TSEnumDeclaration(own) = &parsed.program.body[0] else {
        panic!()
    };
    let Statement::TSEnumDeclaration(other) = &foreign.program.body[0] else {
        panic!()
    };

    assert_eq!(own.node_id(), other.node_id());

    let mut adapter = PrimitiveAdapter::new(&semantic, Limits::default());

    assert!(matches!(
        evaluate_enum(&semantic, other, &mut adapter),
        Err(Failure::UncertifiedReference)
    ));
    assert!(matches!(
        evaluate_enum(&foreign_semantic, other, &mut adapter),
        Err(Failure::UncertifiedReference)
    ));
    assert_eq!(adapter.work.node_visits, 0);
    assert_eq!(
        evaluate_enum(&semantic, own, &mut adapter).unwrap()[0].value,
        Ok(ConstantValue::Number(1.0))
    );
}

#[test]
fn computed_names_and_imported_values_require_verified_identity() {
    inspect(
        "import { Count } from './source'; enum E { ['a']=2, B=E['a'], Unknown=Count, Fixed=5 }",
        Limits::default(),
        |mut results| {
            let values = results.remove(0).unwrap();

            assert_eq!(values[0].value, Ok(ConstantValue::Number(2.0)));
            assert_eq!(values[1].value, Ok(ConstantValue::Number(2.0)));
            assert_eq!(values[2].value, Err(Failure::UncertifiedReference));
            assert_eq!(values[3].value, Ok(ConstantValue::Number(5.0)));
        },
    );
}

#[test]
fn many_members_exhaust_visit_budget_without_automatic_evaluation() {
    inspect(
        "enum E { A=1, B, C, D, E, F, G }",
        Limits {
            nodes: 5,
            ..Limits::default()
        },
        |mut results| assert!(matches!(results.remove(0), Err(Failure::NodeLimit))),
    );
}

fn inspect(
    source: &str,
    limits: Limits,
    test: impl FnOnce(Vec<Result<Vec<EnumInitializer>, Failure>>),
) {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::ts()).parse();

    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    let result = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_enum_eval(false)
        .build(&parsed.program);
    let mut adapter = PrimitiveAdapter::new(&result.semantic, limits);
    let values = result
        .semantic
        .nodes()
        .iter()
        .filter_map(|node| {
            if let oxc_ast::AstKind::TSEnumDeclaration(declaration) = node.kind() {
                Some(evaluate_enum(&result.semantic, declaration, &mut adapter))
            } else {
                None
            }
        })
        .collect();

    test(values);
}

#[test]
fn runtime_member_is_unknown_fixed_values_and_dependencies_survive() {
    inspect(
        "enum E { A=2+3, B, C=A+1, D=E.B+1, Runtime=n, Fixed=9, Next }",
        Limits::default(),
        |mut results| {
            let values = results.remove(0).unwrap();

            for (index, number) in [(0, 5.0), (1, 6.0), (2, 6.0), (3, 7.0), (5, 9.0), (6, 10.0)] {
                assert_eq!(values[index].value, Ok(ConstantValue::Number(number)));
            }

            assert!(values[4].value.is_err());
        },
    );
}

#[test]
fn enum_qualification_counterexamples_use_primitive_authority() {
    inspect(
        "enum E { A=1**(0/0), B=+'2', C=~'2', D=-'2', Bad='\\uD800', Fixed=3 }",
        Limits::default(),
        |mut results| {
            let values = results.remove(0).unwrap();

            assert!(matches!(values[0].value,Ok(ConstantValue::Number(value)) if value.is_nan()));
            assert_eq!(values[1].value, Ok(ConstantValue::Number(2.0)));
            assert_eq!(values[2].value, Ok(ConstantValue::Number(-3.0)));
            assert!(values[3].value.is_err());
            assert_eq!(values[4].value, Err(Failure::LoneSurrogate));
            assert_eq!(values[5].value, Ok(ConstantValue::Number(3.0)));
        },
    );
}

#[test]
fn opaque_work_invalidates_dependency_certificate_and_symbols_stay_distinct() {
    inspect(
        "enum E { A=1, B=(mutate(),7), C=E.A, Fixed=3, D=Fixed } function f(){ enum E { A=2 } }",
        Limits::default(),
        |mut results| {
            let first = results.remove(0).unwrap();
            let second = results.remove(0).unwrap();

            assert_eq!(first[1].value, Ok(ConstantValue::Number(7.0)));
            assert!(first[2].value.is_err());
            assert_eq!(first[4].value, Ok(ConstantValue::Number(3.0)));
            assert_ne!(first[0].symbol, second[0].symbol);
        },
    );
}

#[test]
fn derived_enum_payload_is_bounded_before_growth() {
    inspect(
        "enum E { A='abcd', B=A+A, C=B+B, D=C+C }",
        Limits {
            value_bytes: 80,
            ..Limits::default()
        },
        |mut results| {
            let values = results.remove(0).unwrap();

            assert!(values[0].value.is_ok());
            assert!(values
                .iter()
                .any(|value| value.value == Err(Failure::PayloadLimit)));
        },
    );
}

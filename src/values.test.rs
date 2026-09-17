use super::*;
use oxc_allocator::Allocator;
use oxc_ast::ast::*;
use oxc_ecmascript::{ConstantValue, ValueType};
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;

#[test]
fn foreign_expression_with_colliding_ids_is_rejected_before_work() {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, "const a=7; const value=a;", SourceType::ts()).parse();
    let foreign = Parser::new(&allocator, "const b=9; const value=b;", SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;
    let foreign_semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&foreign.program)
        .semantic;
    let Statement::VariableDeclaration(own) = &parsed.program.body[1] else {
        panic!()
    };
    let Statement::VariableDeclaration(other) = &foreign.program.body[1] else {
        panic!()
    };
    let own = own.declarations[0].init.as_ref().unwrap();
    let other = other.declarations[0].init.as_ref().unwrap();

    assert_eq!(own.node_id(), other.node_id());
    assert_eq!(semantic.nodes().len(), foreign_semantic.nodes().len());

    let mut certified = CertifiedValues::new(&semantic);
    let symbol = semantic
        .scoping()
        .symbol_ids()
        .find(|id| semantic.scoping().symbol_name(*id) == "a")
        .unwrap();

    certified.symbols.insert(symbol, ConstantValue::Number(7.0));

    let mut adapter = PrimitiveAdapter::new(&semantic, Limits::default());

    assert_eq!(
        adapter.evaluate(other, &certified).value,
        Err(Failure::UncertifiedReference)
    );
    assert_eq!(adapter.work.node_visits, 0);
    assert_eq!(
        adapter.evaluate(own, &certified).value,
        Ok(ConstantValue::Number(7.0))
    );
}

#[test]
fn certificates_are_source_scoped_and_shadowed_globals_are_unresolved() {
    let allocator = Allocator::default();
    let parsed = Parser::new(
        &allocator,
        "const NaN=3; const Infinity=4; const result=NaN+Infinity;",
        SourceType::ts(),
    )
    .parse();
    let first = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_enum_eval(false)
        .build(&parsed.program)
        .semantic;
    let other_parsed = Parser::new(&allocator, "const other=9;", SourceType::ts()).parse();
    let other = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_enum_eval(false)
        .build(&other_parsed.program)
        .semantic;
    let Statement::VariableDeclaration(declaration) = &parsed.program.body[2] else {
        panic!()
    };
    let expression = declaration.declarations[0].init.as_ref().unwrap();
    let mut adapter = PrimitiveAdapter::new(&first, Limits::default());

    assert_eq!(
        adapter
            .evaluate(expression, &CertifiedValues::new(&first))
            .value,
        Err(Failure::UncertifiedReference)
    );

    let visits = adapter.work.node_visits;

    assert_eq!(
        adapter
            .evaluate(expression, &CertifiedValues::new(&other))
            .value,
        Err(Failure::UncertifiedReference)
    );
    assert_eq!(adapter.work.node_visits, visits);
}

fn inspect(
    source: &str,
    limits: Limits,
    test: impl FnOnce(ValueResult, &mut PrimitiveAdapter<'_, '_>),
) {
    let allocator = Allocator::default();
    let source = format!("const result=({source});");
    let parsed = Parser::new(&allocator, &source, SourceType::ts()).parse();

    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    let result = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);

    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

    let Statement::VariableDeclaration(declaration) = &parsed.program.body[0] else {
        panic!()
    };
    let expression = declaration.declarations[0].init.as_ref().unwrap();
    let mut adapter = PrimitiveAdapter::new(&result.semantic, limits);
    let value = adapter.evaluate(expression, &CertifiedValues::new(&result.semantic));

    assert_eq!(value.evaluation, expression.node_id());
    test(value, &mut adapter);
}

#[test]
fn qualified_arithmetic_and_coercions() {
    for (source, expected) in [
        ("2+3", 5.0),
        ("+'2'", 2.0),
        ("~'2'", -3.0),
        ("'3'*2", 6.0),
        ("true+2", 3.0),
        ("null+2", 2.0),
        ("'😀'.length", 2.0),
    ] {
        inspect(source, Limits::default(), |value, _| {
            assert!(
                matches!(value.value,Ok(ConstantValue::Number(value)) if value==expected),
                "{source}: {value:?}"
            )
        });
    }

    for source in ["1 ** (0/0)", "(-1) ** (1/0)", "0/0"] {
        inspect(source, Limits::default(), |value, _| {
            assert!(
                matches!(value.value,Ok(ConstantValue::Number(value)) if value.is_nan()),
                "{source}: {value:?}"
            )
        });
    }
}

#[test]
fn exact_kinds_and_keys() {
    for (source, key, kind) in [
        ("-0", "0", ValueType::Number),
        ("0/0", "NaN", ValueType::Number),
        ("1/0", "Infinity", ValueType::Number),
        ("1n", "1", ValueType::BigInt),
        ("'x'", "x", ValueType::String),
        ("true", "true", ValueType::Boolean),
        ("null", "null", ValueType::Null),
        ("void expensive()", "undefined", ValueType::Undefined),
    ] {
        inspect(source, Limits::default(), |result, adapter| {
            let value = result.value.unwrap();

            assert_eq!(value.value_type(), kind);
            assert_eq!(adapter.property_key(&value).unwrap(), key);

            if source == "-0" {
                assert!(
                    matches!(value,ConstantValue::Number(value) if value.to_bits()==(-0.0f64).to_bits())
                );
            }
        });
    }

    inspect("1n+2n", Limits::default(), |result, adapter| {
        assert_eq!(adapter.property_key(&result.value.unwrap()).unwrap(), "3")
    });
    inspect("1n===1", Limits::default(), |result, _| {
        assert_eq!(result.value, Ok(ConstantValue::Boolean(false)))
    });
    inspect("1n==1", Limits::default(), |result, _| {
        assert_eq!(result.value, Ok(ConstantValue::Boolean(true)))
    });
}

#[test]
fn unsupported_coercions_and_surrogates_remain_explicit() {
    for source in [
        "1n+2",
        "+1n",
        "1n/0n",
        "1n<<999999999999999999999n",
        "({valueOf(){ expensive(); return 1; }})+1",
        "({toString(){ expensive(); return 'x'; }})+''",
        "2**100",
        "-'2'",
        "NaN",
        "Infinity",
    ] {
        inspect(source, Limits::default(), |value, _| {
            assert!(value.value.is_err(), "{source}: {value:?}")
        });
    }

    inspect("'\\uD800'", Limits::default(), |value, _| {
        assert_eq!(value.value, Err(Failure::LoneSurrogate))
    });
}

#[test]
fn known_result_retains_original_evaluation_identity() {
    inspect("(expensive(),7)", Limits::default(), |value, _| {
        assert_eq!(value.value, Ok(ConstantValue::Number(7.0)))
    });
    inspect("void expensive()", Limits::default(), |value, _| {
        assert_eq!(value.value, Ok(ConstantValue::Undefined))
    });
    inspect("false&&expensive()", Limits::default(), |value, _| {
        assert_eq!(value.value, Ok(ConstantValue::Boolean(false)))
    });
}

#[test]
fn deterministic_limits_precede_operations_and_allocations() {
    inspect(
        "'abcd'+'efgh'",
        Limits {
            value_bytes: 7,
            ..Limits::default()
        },
        |value, adapter| {
            assert_eq!(value.value, Err(Failure::PayloadLimit));
            assert_eq!(adapter.work.primitive_operations, 0);
        },
    );
    inspect(
        "1+2",
        Limits {
            nodes: 2,
            ..Limits::default()
        },
        |value, _| assert_eq!(value.value, Err(Failure::NodeLimit)),
    );
    inspect(
        "((((1))))",
        Limits {
            depth: 3,
            ..Limits::default()
        },
        |value, _| assert_eq!(value.value, Err(Failure::DepthLimit)),
    );
    inspect(
        "'1234'",
        Limits {
            cumulative_bytes: 63,
            ..Limits::default()
        },
        |value, adapter| {
            assert_eq!(value.value, Err(Failure::PayloadLimit));
            assert_eq!(adapter.work.reserved_bytes, 0);
        },
    );
}

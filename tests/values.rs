use olint::analysis::Analysis;
use olint::cost::Cost;
use olint::values::{Failure, Limits, Primitive};

mod support;

use support::{file_of, probe_results_of, probes_of, run_in_project, run_with_source, summary_of};

fn values_of(source: &str) -> Vec<Result<Primitive, Failure>> {
    probe_results_of(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |analysis, file, probe| {
            analysis
                .known_value(file, probe)
                .value
                .map(|value| (*value).clone())
        },
    )
}

#[test]
fn actual_primitives_and_computed_keys_preserve_language_distinctions() {
    let values = values_of("function f(){probe(2+3);probe(1n==1);probe(1n===1);probe(-0);probe(0/0);probe(1/0);probe('😀'.length);probe(1n+2);probe(+1n);probe(-'2');}");

    assert_eq!(values[0], Ok(Primitive::Number(5.0)));
    assert_eq!(values[1], Ok(Primitive::Boolean(true)));
    assert_eq!(values[2], Ok(Primitive::Boolean(false)));
    assert!(
        matches!(values[3], Ok(Primitive::Number(value)) if value.to_bits() == (-0.0f64).to_bits())
    );
    assert!(matches!(values[4], Ok(Primitive::Number(value)) if value.is_nan()));
    assert_eq!(values[5], Ok(Primitive::Number(f64::INFINITY)));
    assert_eq!(values[6], Ok(Primitive::Number(2.0)));
    assert!(values[7..].iter().all(Result::is_err));

    let keys = probe_results_of(&[("tsconfig.json", "{}"), ("index.ts", "function f(){probe(-0);probe(0/0);probe(1/0);probe(1n);probe(true);probe(void expensive());}")], |analysis, file, expression| analysis.known_key(file, expression));

    assert_eq!(
        keys,
        ["0", "NaN", "Infinity", "1", "true", "undefined"].map(|key| Ok(key.to_string()))
    );
}

#[test]
fn enum_initializers_and_computed_member_names_are_evaluated() {
    let values = values_of("enum E { Count=n, Fixed=2+3, Next, Copy=Fixed, Text='x', Again=Text } function f(){probe(E.Count);probe(E.Fixed);probe(E.Next);probe(E.Copy);probe(E['Fi'+'xed']);probe(E.Again);}");

    assert!(values[0].is_err());
    assert_eq!(
        values[1..5],
        [
            Ok(Primitive::Number(5.0)),
            Ok(Primitive::Number(6.0)),
            Ok(Primitive::Number(5.0)),
            Ok(Primitive::Number(5.0))
        ]
    );
    assert_eq!(values[5], Ok(Primitive::String("x".into())));

    let numeric = probe_results_of(&[("tsconfig.json", "{}"), ("index.ts", "enum E { Count=n, Fixed=5 } function f(){probe(E.Count);probe(E.Fixed);probe(1/0);probe(0/0);probe(true);probe(1n);probe(++E.Fixed);probe(E.Fixed=2);}")], |analysis, file, expression| analysis.is_numeric_constant(file, expression));

    assert_eq!(
        numeric,
        [false, true, false, false, false, false, false, false]
    );
}

#[test]
fn qualified_enum_counterexamples_and_mutation_fence_survive_integration() {
    let values = values_of("enum E { Power=1**(0/0), Plus=+'2', Not=~'2', Surrogate='\\uD800' } enum F { A=1, B=(mutate(),7), C=A, D=9 } function f(){probe(E.Power);probe(E.Plus);probe(E.Not);probe(E.Surrogate);probe(F.B);probe(F.C);probe(F.D);}");

    assert!(matches!(values[0], Ok(Primitive::Number(value)) if value.is_nan()));
    assert_eq!(values[1], Ok(Primitive::Number(2.0)));
    assert_eq!(values[2], Ok(Primitive::Number(-3.0)));
    assert!(values[3].is_err());
    assert_eq!(values[4], Ok(Primitive::Number(7.0)));
    assert!(values[5].is_err());
    assert_eq!(values[6], Ok(Primitive::Number(9.0)));
}

#[test]
fn imported_constants_and_enums_keep_source_identity() {
    let values = probe_results_of(&[("tsconfig.json", "{}"), ("a.ts", "export enum E { A=2 } export const N=4;"), ("b.ts", "export enum E { A=n }"), ("index.ts", "import {E as A,N} from './a'; import {E as B} from './b'; function f(){probe(A.A);probe(B.A);probe(N*2);}")], |analysis, file, probe| analysis.known_value(file, probe).value.map(|value| (*value).clone()));

    assert_eq!(values[0], Ok(Primitive::Number(2.0)));
    assert!(values[1].is_err());
    assert_eq!(values[2], Ok(Primitive::Number(8.0)));
}

#[test]
fn value_results_never_erase_cost_or_certify_coercion_hooks() {
    for body in [
        "return new Array((expensive(),7));",
        "enum E { A=(expensive(),7) } return new Array(E.A);",
    ] {
        let source = format!("/** @perf O(N^3) */ function expensive(){{return 7;}} export function root(){{{body}}}");

        run_with_source(&source, |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "root");
            let expected = analysis
                .bind_function_cost(file, function, &Cost::parse("O(N^3)").unwrap())
                .unwrap();

            assert_eq!(summary_of(analysis, file, "root").cost, expected);
        });
    }

    let values = values_of("function f(){probe((expensive(),7));probe(void expensive());probe(({valueOf(){return 1}})+2);probe(({toString(){return 'x'}})+'y');}");

    assert_eq!(values[0], Ok(Primitive::Number(7.0)));
    assert_eq!(values[1], Ok(Primitive::Undefined));
    assert!(values[2..].iter().all(Result::is_err));
}

#[test]
fn source_ownership_is_checked_before_cache_lookup() {
    run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", "const x=1; function f(){probe(x)}"),
            ("other.ts", "const y=2; function g(){probe(y)}"),
        ],
        |project, root| {
            let file = file_of(project, root, "index.ts");
            let other = file_of(project, root, "other.ts");
            let mut analysis = Analysis::new(project, support::SYNTACTIC);
            let own = probes_of(project, file)[0];
            let foreign = probes_of(project, other)[0];

            assert_eq!(
                analysis.known_value(file, own).value.as_deref(),
                Ok(&Primitive::Number(1.0))
            );

            let before = analysis.values.primitive_work(file).node_visits;

            assert_eq!(
                analysis.known_value(file, foreign).value.unwrap_err(),
                Failure::UncertifiedReference
            );
            assert_eq!(analysis.values.primitive_work(file).node_visits, before);
        },
    );
}

#[test]
fn cumulative_budget_and_cached_values_survive_recording_reset() {
    run_with_source(
        "function f(){probe('a'+'b');probe('c'+'d');}",
        |analysis, file| {
            assert!(analysis.values.set_primitive_limits(Limits {
                nodes: 8,
                ..Limits::default()
            }));

            let probes = probes_of(analysis.project, file);
            let first = analysis.known_value(file, probes[0]);

            assert!(first.value.is_ok());

            let before = analysis.values.primitive_work(file).node_visits;

            analysis.reset_between_passes();
            assert_eq!(analysis.known_value(file, probes[0]).value, first.value);
            assert_eq!(analysis.values.primitive_work(file).node_visits, before);
            assert_eq!(
                analysis.known_value(file, probes[1]).value.unwrap_err(),
                Failure::NodeLimit
            );
            assert!(!analysis.values.set_primitive_limits(Limits::default()));
        },
    );
}

#[test]
fn derived_payload_rejection_precedes_primitive_operations() {
    run_with_source(
        "function f(){probe('12345678'+'12345678');}",
        |analysis, file| {
            assert!(analysis.values.set_primitive_limits(Limits {
                value_bytes: 40,
                ..Limits::default()
            }));

            let expression = probes_of(analysis.project, file)[0];

            assert_eq!(
                analysis.known_value(file, expression).value.unwrap_err(),
                Failure::PayloadLimit
            );
            assert_eq!(analysis.values.primitive_work(file).primitive_operations, 0);
        },
    );
}

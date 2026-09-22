use std::collections::BTreeSet;

use olint::analysis::Analysis;
use olint::config::read_config;
use olint::cost::Cost;
use olint::public::public_functions;
use olint::unknowns::UnknownReason;

mod support;

use support::{legacy_result_of, SYNTACTIC};

const HELPERS: &str = "function quadratic(xs: number[]) { let total = 0; for (const x of xs) for (const y of xs) total += x + y; return total; }\nfunction scan(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }\nfunction cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }";

fn selected_of(declarations: &str, body: &str) -> (Cost, bool, BTreeSet<UnknownReason>) {
    legacy_result_of(
        &format!("{HELPERS}\n{declarations}\nexport function selected{body}"),
        "selected",
    )
}

fn assert_selected(cases: &[(&str, &str, &str, bool)]) {
    for (declarations, body, expected, complete) in cases {
        let (cost, found, reasons) = selected_of(declarations, body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}: {reasons:?}");
        assert_eq!(found, *complete, "{body}: {reasons:?}");
    }
}

#[test]
fn replacement_callbacks_run_once_per_match_or_once_per_call() {
    assert_selected(&[
        (
            "",
            r#"(s: string, xs: number[]) { return s.replaceAll("x", () => { quadratic(xs); return "y"; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            "",
            r#"(s: string, xs: number[]) { return s.replace(/x/g, () => { quadratic(xs); return "y"; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            "",
            r#"(s: string, xs: number[], pattern: RegExp) { return s.replace(pattern, () => { quadratic(xs); return "y"; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            "",
            r#"(s: string, xs: number[]) { return s.replace(/x/, () => { quadratic(xs); return "y"; }); }"#,
            "O(N^2)",
            true,
        ),
        (
            "",
            r#"(s: string, xs: number[]) { return s.replace("x", () => { quadratic(xs); return "y"; }); }"#,
            "O(N^2)",
            true,
        ),
        (
            "",
            r#"(s: string) { return s.replace(/x/g, "y"); }"#,
            "O(N)",
            true,
        ),
        (
            "",
            r#"(s: string, t: string) { return s.replace(/x/g, t); }"#,
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn grouping_callbacks_run_once_per_element() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return Object.groupBy(xs, () => quadratic(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return Map.groupBy(xs, () => quadratic(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return Object.groupBy([1, 2], () => quadratic(xs)); }",
            "O(N^2)",
            true,
        ),
    ]);
}

#[test]
fn grouping_keys_coerce_callback_results() {
    let key = r#"class Key { toString() { return "k"; } }"#;

    assert_selected(&[
        (
            key,
            "(xs: number[]) { return Object.groupBy(xs, (x: number) => x); }",
            "O(N)",
            true,
        ),
        (
            key,
            "(xs: number[]) { return Object.groupBy(xs, () => new Key() as any); }",
            "O(N)",
            false,
        ),
        (
            key,
            "(xs: number[]) { return Map.groupBy(xs, () => new Key()); }",
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn json_callbacks_run_for_every_visited_value() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return JSON.stringify(xs, (_, value) => { quadratic(xs); return value; }); }",
            "O(N^3)",
            true,
        ),
        (
            "",
            "(s: string, xs: number[]) { return JSON.parse(s, (_, value) => { quadratic(xs); return value; }); }",
            "O(N^3)",
            true,
        ),
        (
            "",
            r#"(xs: number[]) { return JSON.stringify(xs, ["a"]); }"#,
            "O(N)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return JSON.stringify(xs, null, 2); }",
            "O(N)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return JSON.stringify([xs]); }",
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn to_json_runs_on_the_serialized_value() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return JSON.stringify({ toJSON() { return quadratic(xs); } }); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return JSON.stringify({ toJSON() { return { value: quadratic(xs) }; } }); }",
            "O(N^2)",
            false,
        ),
        (
            "class Box { toJSON() { return 1; } }",
            "(xs: number[]) { return JSON.stringify(xs); }",
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn serialization_reads_properties_through_getters() {
    let getter = "const holder = { get value() { return 1; } };";

    assert_selected(&[
        (
            getter,
            "(xs: number[]) { return JSON.stringify(xs); }",
            "O(N)",
            true,
        ),
        (
            getter,
            "(items: object[]) { return JSON.stringify(items); }",
            "O(N)",
            false,
        ),
        (
            getter,
            "(items: object[]) { return Object.values(items); }",
            "O(N)",
            false,
        ),
    ]);
}

#[test]
fn promise_executor_runs_synchronously_with_native_settlers() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return new Promise<number>((resolve) => resolve(quadratic(xs))); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return new Promise<number>((resolve, reject) => { if (xs.length === 0) reject(xs.length); resolve(quadratic(xs)); }); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return new Promise<number>(() => { for (const x of xs) quadratic(xs); }); }",
            "O(N^3)",
            true,
        ),
    ]);
}

#[test]
fn unknown_callbacks_keep_known_work_and_stay_partial() {
    for (body, expected) in [
        (
            "(s: string, replacer: (match: string) => string) { return s.replace(/a/g, replacer); }",
            "O(N)",
        ),
        (
            "(s: string, reviver: (key: string, value: unknown) => unknown) { return JSON.parse(s, reviver); }",
            "O(N)",
        ),
        (
            "(xs: number[], key: (x: number) => string) { return Map.groupBy(xs, key); }",
            "O(N)",
        ),
        (
            "(executor: (resolve: (value: number) => void) => void) { return new Promise<number>(executor); }",
            "O(1)",
        ),
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}");
        assert!(!complete, "{body}");
        assert!(reasons.contains(&UnknownReason::Target), "{body}: {reasons:?}");
    }
}

#[test]
fn array_from_and_sort_comparator_controls_remain() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return Array.from(xs, () => quadratic(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return xs.sort(() => scan(xs)); }",
            "O(N^2 log N)",
            true,
        ),
    ]);
}

#[test]
fn array_of_is_charged_by_its_arity() {
    assert_selected(&[
        ("", "(xs: number[]) { return Array.of(xs); }", "O(1)", true),
        (
            "",
            "(a: number, b: number) { return Array.of(a, b); }",
            "O(1)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return Array.of(...xs); }",
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn namespace_models_require_intrinsic_identity() {
    let (cost, complete, reasons) = selected_of(
        "",
        "(JSON: { stringify(value: unknown): string }, xs: number[]) { return JSON.stringify(xs); }",
    );

    assert_eq!(cost, Cost::ONE);
    assert!(!complete);
    assert!(
        reasons.contains(&UnknownReason::UnsupportedModel),
        "{reasons:?}"
    );

    assert_selected(&[(
        "declare const Buffer: { concat(list: unknown[]): unknown };",
        "(parts: unknown[]) { return Buffer.concat(parts); }",
        "O(N)",
        true,
    )]);
}

#[test]
fn call_forwards_its_arguments_to_known_functions() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { cube.call(null, xs); }",
            "O(N^3)",
            true,
        ),
        (
            "const table = { run: cube };",
            "(xs: number[]) { table.run.call(table, xs); }",
            "O(N^3)",
            false,
        ),
        (
            "const table = { run: cube };",
            "(xs: number[]) { table.run(xs); }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[], parts: [null, number[]]) { cube.call(...parts); }",
            "O(N)",
            false,
        ),
    ]);
}

#[test]
fn modelled_natives_keep_the_loop_bounds_they_cannot_affect() {
    assert_selected(&[
        (
            "",
            "(xs: number[], o: Record<string, number>) { for (let i = 0; i < xs.length; i++) { Object.keys(o); } }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(s: string, needle: string, n: number) { let total = 0; for (let i = 0; i < n; i++) total += s.indexOf(needle); return total; }",
            "O(N^2)",
            true,
        ),
        (
            "",
            r#"(s: string, n: number) { for (let i = 0; i < n; i++) { s.replace(/a/g, () => { i = 0; return ""; }); } }"#,
            "O(N)",
            false,
        ),
        (
            "",
            "(n: number, source: { limit: number }) { const box = { limit: n }; for (let i = 0; i < box.limit; i++) { Object.assign(box, source); } }",
            "O(N)",
            false,
        ),
    ]);
}

#[test]
fn call_carries_the_forwarded_function_effects() {
    assert_selected(&[
        (
            "function grow(this: { limit: number }, n: number) { this.limit += n; }",
            "(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } grow.call(box, n); } return total; }",
            "O(N^2)",
            true,
        ),
        (
            "function peek(this: { limit: number }, n: number) { return this.limit + n; }",
            "(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } peek.call(box, n); } return total; }",
            "O(N)",
            true,
        ),
        (
            "",
            "(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n; j++) { reset.call(null); while (i < n) { i++; total++; } } return total; }",
            "O(N^2)",
            true,
        ),
    ]);
}

fn surface_is_complete(source: &str) -> bool {
    let mut complete = false;
    let files = [
        ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#),
        ("tsconfig.json", r#"{"files":["index.ts"]}"#),
        ("index.ts", source),
    ];

    support::run_in_project(&files, |project, _| {
        let config = read_config(project, None).unwrap();
        let coverage = public_functions(&mut Analysis::new(project, SYNTACTIC), &config).unwrap();

        complete = coverage.unknowns.is_none();
    });

    complete
}

#[test]
fn surfaced_objects_passed_to_reading_natives_keep_public_coverage() {
    for (call, complete) in [
        ("Object.freeze(api)", true),
        ("JSON.stringify(api)", true),
        ("Object.keys(api)", true),
        ("Object.assign(api, other)", false),
        ("Object.fromEntries(api as any)", false),
        ("JSON.stringify(api, (key, value) => value)", false),
        ("Array.from([1], (x) => x, api)", false),
        ("api.run.call(api)", false),
    ] {
        let source = format!(
            "export const api = {{ run() {{ return 1; }} }};\nconst other = {{ run() {{ return 2; }} }};\nexport function selected() {{ {call}; }}"
        );

        assert_eq!(surface_is_complete(&source), complete, "{call}");
    }
}

use std::collections::BTreeSet;

use olint::analysis::Analysis;
use olint::config::read_config;
use olint::cost::{Cost, CostComparison, ExecutionPhase, Reading};
use olint::public::public_functions;
use olint::unknowns::UnknownReason;

use crate::support;

use support::{classified_result_of, legacy_result_of, SYNTACTIC};

const HELPERS: &str = "function quadratic(xs: number[]) { let total = 0; for (const x of xs) for (const y of xs) total += x + y; return total; }\nfunction scan(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }\nfunction cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }";

fn selected_of(declarations: &str, body: &str) -> (Cost, bool, BTreeSet<UnknownReason>) {
    let (cost, complete, reasons) = legacy_result_of(
        &format!("{HELPERS}\n{declarations}\nexport function selected{body}"),
        "selected",
    );

    (support::projected_class_of(&cost), complete, reasons)
}

fn assert_selected(cases: &[(&str, &str, &str, bool)]) {
    for (declarations, body, expected, complete) in cases {
        let (cost, found, reasons) = selected_of(declarations, body);
        let cost = support::projected_class_of(&cost);

        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse(expected).unwrap(),
            "{body}: {reasons:?}"
        );
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
            false,
        ),
        (
            "",
            r#"(s: string, xs: number[], pattern: RegExp) { return s.replace(pattern, () => { quadratic(xs); return "y"; }); }"#,
            "O(N^3)",
            false,
        ),
        (
            "",
            r#"(s: string, xs: number[]) { return s.replace(/x/, () => { quadratic(xs); return "y"; }); }"#,
            "O(N^2)",
            false,
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
            false,
        ),
        (
            "",
            r#"(s: string, t: string) { return s.replace(/x/g, t); }"#,
            "O(N)",
            false,
        ),
    ]);
}

#[test]
fn replacement_callbacks_compose_with_classified_matching() {
    for (body, expected, complete) in [
        (
            r#"(s: string, xs: number[]) { return s.replace(/^a*a*$/, () => { cube(xs); return ""; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replace(/^a*$/, () => { scan(xs); return ""; }); }"#,
            "O(N)",
            true,
        ),
        (
            r#"(s: string) { return s.replace(/^a*a*$/, () => "b"); }"#,
            "O(N^2)",
            true,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replace(/^a*a*$/g, () => { cube(xs); return ""; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replaceAll(/^a*a*$/g, () => { cube(xs); return ""; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replace(/x*y/g, () => { quadratic(xs); return ""; }); }"#,
            "O(N^3)",
            true,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replace(/^a*a*$/gm, () => { quadratic(xs); return ""; }); }"#,
            "O(N^3)",
            false,
        ),
        (
            r#"(s: string, xs: number[]) { return s.replace(/^(a+)+$/, () => { scan(xs); return ""; }); }"#,
            "O(N)",
            false,
        ),
    ] {
        let (cost, found, reasons) = classified_result_of(
            &format!(
                "{HELPERS}
export function selected{body}"
            ),
            "selected",
        );

        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse(expected).unwrap(),
            "{body}: {reasons:?}"
        );
        assert_eq!(found, complete, "{body}: {reasons:?}");
    }
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
            "O(1)",
        ),
        (
            "(executor: (resolve: (value: number) => void) => void) { return new Promise<number>(executor); }",
            "O(1)",
        ),
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}");
        assert!(!complete, "{body}");

        if body.contains("Map.groupBy") { assert!(reasons.contains(&UnknownReason::Bound), "{reasons:?}"); }

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
        "O(N^2)",
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
            "(xs: number[], o: Record<string, number>) { for (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 1000000000; i++) { Object.keys(o); } }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(s: string, needle: string, n: number) { let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) total += s.indexOf(needle); return total; }",
            "O(N^2)",
            true,
        ),
        (
            "",
            r#"(s: string, n: number) { for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) { s.replace(/a/g, () => { i = 0; return ""; }); } }"#,
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
            "(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000000; j++) { while (i < box.limit) { i++; total++; } grow.call(box, n); } return total; }",
            "O(N)",
            false,
        ),
        (
            "function peek(this: { limit: number }, n: number) { return this.limit + n; }",
            "(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000000; j++) { while (i < box.limit) { i++; total++; } peek.call(box, n); } return total; }",
            "O(N)",
            false,
        ),
        (
            "",
            "(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n && n >= 0 && n <= 1000000000; j++) { reset.call(null); while (i < n && i >= 0 && n >= 0 && n <= 1000000000) { i++; total++; } } return total; }",
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
        ("Object.fromEntries(api as any)", true),
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

fn bound_result_of(body: &str, expected: &str) -> (bool, bool) {
    let source = format!("{HELPERS}\nexport function selected{body}");
    let mut found = None;

    support::run_with_source(&source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");
        let part = support::summary_of(analysis, file, "selected");
        let bound = analysis
            .bind_function_cost(file, function, &Cost::parse(expected).unwrap())
            .unwrap();
        let equal = part.cost.compare(&bound) == CostComparison::Within
            && bound.compare(&part.cost) == CostComparison::Within;

        found = Some((equal, part.is_complete()));
    });

    found.expect("the source declares the selected function")
}

#[test]
fn concatenation_charges_every_operand() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return ([] as number[]).concat(xs); }",
            "O(N)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return [1, 2].concat(xs); }",
            "O(N)",
            true,
        ),
        ("", r#"(s: string) { return "".concat(s); }"#, "O(N)", true),
        (
            "",
            "() { const xs = [1, 2, 3]; return xs.concat([4, 5]); }",
            "O(1)",
            true,
        ),
        ("", "(n: number) { return [1, 2].concat(n); }", "O(1)", true),
    ]);

    assert_eq!(
        bound_result_of(
            "(xs: number[], lists: number[][]) { return xs.concat(...lists); }",
            "O(lists * max(xs, lists))"
        ),
        (true, true)
    );
}

#[test]
fn flattening_charges_the_elements_it_visits() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { return xs.map(() => xs).flat(); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return xs.flatMap(() => xs); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return [1, 2].flatMap(() => xs); }",
            "O(N)",
            true,
        ),
        (
            "",
            "(rows: number[][]) { return rows.flat(); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(rows: number[][]) { return rows.flatMap((row) => row); }",
            "O(N^2)",
            true,
        ),
        ("", "(xs: number[]) { return xs.flat(); }", "O(N)", true),
        (
            "",
            "(xs: number[]) { return xs.flatMap((x) => [x, x]); }",
            "O(N)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return xs.flatMap((x) => x); }",
            "O(N)",
            true,
        ),
        (
            "",
            "(xs: number[]) { return xs.flatMap(() => quadratic(xs)); }",
            "O(N^3)",
            true,
        ),
    ]);
}

#[test]
fn unknown_result_sizes_leave_flattening_partial() {
    for (body, expected) in [
        (
            "(xs: number[], f: (x: number) => number[]) { return xs.flatMap(f); }",
            "O(xs * max(xs, f))",
        ),
        (
            "(rows: number[][], depth: number) { return rows.flat(depth); }",
            "O(rows * max(rows, depth))",
        ),
    ] {
        let (_, _, reasons) = selected_of("", body);

        assert_eq!(bound_result_of(body, expected), (true, false), "{body}");
        assert!(
            reasons.contains(&UnknownReason::SizeRelation),
            "{body}: {reasons:?}"
        );
    }
}

#[test]
fn independent_inner_sizes_stay_explicit() {
    for body in [
        "(xs: number[], ys: number[]) { return xs.flatMap(() => ys); }",
        "(xs: number[], ys: number[]) { return xs.map(() => ys).flat(); }",
    ] {
        assert_eq!(bound_result_of(body, "O(xs * ys)"), (true, true), "{body}");
        assert_eq!(bound_result_of(body, "O(xs^2)"), (false, true), "{body}");
    }

    assert_eq!(
        bound_result_of(
            "(xs: number[], ys: number[]) { return xs.concat(ys); }",
            "O(max(xs, ys))"
        ),
        (true, true)
    );
}

#[test]
fn buffer_concatenation_charges_every_part() {
    let buffer = "declare const Buffer: { concat(list: unknown[], total?: number): unknown };";

    assert_selected(&[
        (
            buffer,
            "(a: Uint8Array, b: Uint8Array) { return Buffer.concat([a, b]); }",
            "O(N)",
            true,
        ),
        (
            buffer,
            "(parts: Uint8Array[]) { return Buffer.concat(parts); }",
            "O(N^2)",
            true,
        ),
        (
            buffer,
            "(a: Uint8Array, total: number) { return Buffer.concat([a], total); }",
            "O(N)",
            true,
        ),
        (
            buffer,
            "() { return Buffer.concat([new Uint8Array(2), new Uint8Array(3)]); }",
            "O(1)",
            true,
        ),
    ]);
}

#[test]
fn repeated_strings_keep_materialization_unknown() {
    for body in [
        r#"(count: number) { return "x".repeat(count); }"#,
        r#"(count: number) { return "x".padStart(count); }"#,
        r#"(count: number) { return "x".padEnd(count, "y"); }"#,
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(cost, Cost::ONE, "{body}");
        assert!(!complete, "{body}");
        assert!(
            reasons.contains(&UnknownReason::UnsupportedModel),
            "{body}: {reasons:?}"
        );
    }

    assert_selected(&[
        ("", "(s: string) { return s.repeat(3); }", "O(N)", true),
        (
            "",
            r#"(s: string) { return s.padStart(8, "0"); }"#,
            "O(N)",
            true,
        ),
    ]);

    assert_eq!(
        bound_result_of(
            r#"(s: string, n: number) { return s.repeat(n).split(""); }"#,
            "O(s * n)"
        ),
        (true, false)
    );
}

fn assert_unknown_visits(cases: &[(&str, &str, &str)]) {
    for (declarations, body, expected) in cases {
        let (cost, complete, reasons) = selected_of(declarations, body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}: {reasons:?}");
        assert!(!complete, "{body}: {reasons:?}");
        assert!(
            reasons.contains(&UnknownReason::Bound),
            "{body}: {reasons:?}"
        );
    }
}

#[test]
fn live_collection_callbacks_run_once_per_budgeted_visit() {
    assert_selected(&[
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { if (values.size < xs.length * xs.length) values.add(values.size); }); return values; }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { if (values.size < xs.length) values.add(values.size); scan(xs); }); return values; }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); const alias = values; values.forEach(() => { if (alias.size < xs.length * xs.length) alias.add(alias.size); }); return values; }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(n: number) { const table = new Map<number, number>(); table.set(0, 0); table.forEach((value, key) => { if (n >= table.size) table.set(key + 1, value); }); return table; }",
            "O(N)",
            true,
        ),
        (
            "",
            "(s: Set<number>) { let total = 0; s.forEach((value) => { if (s.size < 10) s.add(value + 1); total += value; }); return total; }",
            "O(N)",
            true,
        ),
    ]);

    assert_eq!(
        bound_result_of(
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { if (values.size < xs.length * xs.length) values.add(values.size); }); return values; }",
            "O(max(1, xs^2))"
        ),
        (true, true)
    );
}

#[test]
fn unsupported_live_collection_growth_leaves_visits_unknown() {
    assert_unknown_visits(&[
        (
            "function grow(target: Set<number>, limit: number) { if (target.size < limit) target.add(target.size); }",
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { grow(values, xs.length); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach((value, key, set) => { if (set.size < xs.length) set.add(set.size); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); let alias = values; values.forEach(() => { if (alias.size < xs.length) alias.add(alias.size); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach(function (this: Set<number>) { if (this.size < xs.length) this.add(this.size); scan(xs); }, values); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach((value) => { values.add(value + 1); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); let limit = xs.length; values.forEach(() => { if (values.size < limit) { values.add(values.size); limit++; } scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { if (values.size < xs.length) {} else values.add(values.size); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); values.forEach(() => { if (values.size < xs.length) for (let i = 0; i < 2; i++) values.add(values.size + i); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[], other: Set<number>) { const values = new Set([0]); values.forEach(() => { if (other.size < xs.length) values.add(values.size); scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(m: Map<number, number>, xs: number[]) { m.forEach((value, key) => { m.set(key, value + 1); scan(xs); }); return m; }",
            "O(N)",
        ),
        (
            "",
            "(xs: number[]) { const values = new Set([0]); const limits = [0]; values.forEach(() => { if (values.size < limits.length) { values.add(values.size); limits.length = values.size + 1; } scan(xs); }); return values; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, xs: number[]) { s.forEach((value) => { if (s.size < xs.length) s.add(value + 1); s.add(value + 2); scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, xs: number[]) { const limits = [0]; s.forEach((value) => { if (s.size < xs.length) s.add(value + 1); if (s.size < limits.length) { s.add(value + 2); limits.length = s.size + 1; } scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(this: { items: number[] }, s: Set<number>, xs: number[]) { s.forEach((value) => { if (s.size < xs.length) s.add(value + 1); if (s.size < this.items.length) s.add(value + 2); scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, xs: number[], o: { count: number }) { s.forEach((value) => { if (s.size < xs.length) s.add(value + 1); if (s.size < o.count) s.add(value + 2); scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, xs: number[]) { s.forEach((value) => { if (s.size < xs.concat(xs).length) s.add(value + 1); scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, callback: (value: number) => void) { s.forEach(callback); }",
            "O(1)",
        ),
    ]);
}

#[test]
fn reinserted_entries_can_exceed_the_final_size() {
    assert_unknown_visits(&[
        (
            "",
            "(s: Set<number>, xs: number[]) { s.forEach((value) => { if (s.size < xs.length) { s.delete(value); s.add(value); } scan(xs); }); return s; }",
            "O(N)",
        ),
        (
            "",
            "(s: Set<number>, xs: number[]) { let count = 0; s.forEach((value) => { if (count < xs.length) { count++; s.delete(value); s.add(value); } scan(xs); }); return count; }",
            "O(N)",
        ),
    ]);
}

#[test]
fn stable_live_collections_stay_size_bounded() {
    assert_selected(&[
        (
            "",
            "(s: Set<number>, xs: number[]) { s.forEach(() => scan(xs)); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(m: Map<number, number>, xs: number[]) { m.forEach(() => scan(xs)); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(s: Set<number>, xs: number[]) { s.forEach(() => { s.clear(); scan(xs); }); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(s: Set<number>, t: Set<number>, xs: number[]) { s.forEach((value) => { t.delete(value); scan(xs); }); }",
            "O(N^2)",
            true,
        ),
        (
            "",
            "(target: Set<number>, table: Map<number, number>) { target.add(1); table.set(1, 2); target.delete(1); table.clear(); }",
            "O(1)",
            true,
        ),
    ]);
}

#[test]
fn array_for_each_keeps_its_snapshot_length() {
    for body in [
        "(xs: number[]) { xs.forEach((x) => { if (xs.length < 2 * xs.length) xs.push(x); scan(xs); }); }",
        "(xs: number[]) { const values = [0]; values.forEach(() => { if (values.length < xs.length) values.push(values.length); scan(xs); }); }",
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(cost, Cost::parse("O(N^2)").unwrap(), "{body}: {reasons:?}");
        assert!(!complete, "{body}: {reasons:?}");
        assert!(
            !reasons.contains(&UnknownReason::Bound),
            "{body}: {reasons:?}"
        );
    }
}

fn traced_selected_of(declarations: &str, body: &str) -> (Cost, bool, Vec<String>, Reading) {
    let source = format!("{HELPERS}\n{declarations}\nexport function selected{body}");
    let mut found = None;

    support::run_with_source(&source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");
        let reading = analysis.summarize(file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let cost = support::projected_class_of(&part.cost);
        let labels = support::trace_nodes(&analysis.traces, part.trace)
            .into_iter()
            .map(|node| node.label.clone())
            .collect();

        found = Some((cost, part.is_complete(), labels, reading));
    });

    found.expect("the source declares selected")
}

fn scheduled_labels_of(labels: &[String]) -> usize {
    labels
        .iter()
        .filter(|label| label.ends_with("callback [scheduled]"))
        .count()
}

fn assert_phase_costs(source: &str, immediate: &str, scheduled: &str) {
    support::run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");
        let reading = analysis.summarize(file, function);

        for (phase, expected) in [
            (ExecutionPhase::Immediate, immediate),
            (ExecutionPhase::Scheduled, scheduled),
        ] {
            let costs: Vec<_> = reading
                .completions
                .iter()
                .filter(|channel| channel.0 == phase)
                .map(|channel| channel.2.cost.clone())
                .collect();
            let cost = if costs.is_empty() {
                Cost::ONE
            } else {
                Cost::maximum(costs).unwrap()
            };
            let cost = support::legacy_class_of(analysis, file, function, &cost);

            assert_eq!(
                support::projected_class_of(&cost),
                Cost::parse(expected).unwrap(),
                "{phase:?}: {source}: {reading:?}"
            );
        }
    });
}

#[test]
fn scheduled_channels_survive_calls_callbacks_loops_and_returns() {
    let cases = [
        ("scan(xs); return p.then(() => quadratic(xs));", "", "O(N)", "O(N^2)"),
        ("scan(xs); return schedule(xs, p);", "function schedule(xs: number[], p: Promise<number>) { return p.then(() => quadratic(xs)); }", "O(N)", "O(N^2)"),
        ("scan(xs); invoke(() => p.then(() => quadratic(xs)));", "function invoke(work: () => unknown) { return work(); }", "O(N)", "O(N^2)"),
        ("for (const x of xs) p.then(() => quadratic(xs));", "", "O(N)", "O(N^3)"),
        ("for (const x of xs) return p.then(() => quadratic(xs));", "", "O(1)", "O(N^2)"),
        ("xs.forEach(() => p.then(() => quadratic(xs)));", "", "O(N)", "O(N^3)"),
        ("const obj = { get value() { return p.then(() => quadratic(xs)); } }; scan(xs); return obj.value;", "", "O(N)", "O(N^2)"),
        ("class Item { value = p.then(() => quadratic(xs)); } scan(xs); return new Item();", "", "O(N)", "O(N^2)"),
        ("scan(xs); for (const value of produce(xs, p)) {}", "function* produce(xs: number[], p: Promise<number>) { p.then(() => quadratic(xs)); yield 1; }", "O(N)", "O(N^2)"),
        ("scan(xs); return p.then(() => produce(xs));", "function* produce(xs: number[]) { cube(xs); yield 1; }", "O(N)", "O(1)"),
        ("scan(xs); return later(xs);", "async function later(xs: number[]) { await 0; cube(xs); }", "O(N)", "O(N^3)"),
        ("scan(xs); return later(xs);", "async function later(xs: number[]) { for (const x of xs) { await 0; cube(xs); } }", "O(N)", "O(N^4)"),
        ("scan(xs); return later(xs);", "function* produce(xs: number[]) { cube(xs); yield 1; } async function later(xs: number[]) { await 0; return produce(xs); }", "O(N)", "O(1)"),
        ("consume(immediate(xs, p)); consume(scheduled(xs, p));", "function* immediate(xs: number[], p: Promise<number>) { cube(xs); yield 1; } function* scheduled(xs: number[], p: Promise<number>) { p.then(() => cube(xs)); yield 1; } function consume(values: Iterable<number>) { for (const value of values) {} }", "O(N^3)", "O(N^3)"),
        ("consume(scheduled(xs, p)); consume(immediate(xs, p));", "function* immediate(xs: number[], p: Promise<number>) { cube(xs); yield 1; } function* scheduled(xs: number[], p: Promise<number>) { p.then(() => cube(xs)); yield 1; } function consume(values: Iterable<number>) { for (const value of values) {} }", "O(N^3)", "O(N^3)"),
        ("let i = 0; for (const x of xs) { for (const y of xs) { while (i < xs.length && xs.length >= 0 && xs.length <= 1000000000) { i++; p.then(() => quadratic(xs)); } } }", "", "O(N)", "O(N^3)"),
        ("for (const x of xs) { let i = 0; for (const y of xs) { while (i < xs.length && xs.length >= 0 && xs.length <= 1000000000) { i++; p.then(() => quadratic(xs)); } } }", "", "O(N^2)", "O(N^4)"),
        ("for (const x of xs) [...produce(xs, p)];", "function* produce(xs: number[], p: Promise<number>) { return cube(xs); }", "O(N^4)", "O(1)"),
        ("for (const x of xs) [...produce(xs, p)];", "function* produce(xs: number[], p: Promise<number>) { return p.then(() => cube(xs)); }", "O(N)", "O(N^4)"),
    ];

    for (body, helper, immediate, scheduled) in cases {
        let source = format!("{HELPERS}\n{helper}\nexport function selected(xs: number[], p: Promise<number>) {{ {body} }}");

        assert_phase_costs(&source, immediate, scheduled);
    }
}

#[test]
fn cold_scheduled_callbacks_keep_their_selected_work() {
    let source = format!("{HELPERS}\nexport function selected(xs: number[]) {{ /** @perf cold */ async function later() {{ await 0; cube(xs); }} return xs.map(later); }}");

    support::run_with_source(&source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");
        let reading = analysis.summarize(file, function);
        let total = reading.total(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(
            support::legacy_class_of(analysis, file, function, &total.cost),
            Cost::parse("O(N^4)").unwrap(),
            "{reading:?}"
        );
    });
}

#[test]
fn uncertain_await_placement_retains_both_possible_execution_phases() {
    for body in [
        "if (xs.length > 1) await 0; cube(xs);",
        "return (await 0, cube(xs));",
        "for (const x of xs) { cube(xs); await 0; }",
    ] {
        let source =
            format!("{HELPERS}\nexport async function selected(xs: number[]) {{ {body} }}");

        support::run_with_source(&source, |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "selected");
            let reading = analysis.summarize(file, function);

            for phase in [ExecutionPhase::Immediate, ExecutionPhase::Scheduled] {
                let part = reading.part_of(phase, olint::flow::Completion::Normal);

                assert!(!part.cost.is_one(), "{body}: {reading:?}");
                assert!(!part.is_complete(), "{body}: {reading:?}");
            }
        });
    }
}

#[test]
fn promise_continuations_run_once_as_scheduled_work() {
    for (body, expected, scheduled) in [
        (
            "(xs: number[], p: Promise<number>) { return p.then(() => quadratic(xs)); }",
            "O(N^2)",
            1,
        ),
        (
            "(xs: number[], p: Promise<number>) { return p.then(() => scan(xs), () => cube(xs)); }",
            "O(N^3)",
            1,
        ),
        (
            "(xs: number[], p: Promise<number>) { for (const x of xs) p.then(() => quadratic(xs)); }",
            "O(N^3)",
            1,
        ),
        (
            "(xs: number[], p: Promise<number>) { return p.catch(() => scan(xs)).finally(() => quadratic(xs)); }",
            "O(N^2)",
            1,
        ),
        (
            "(xs: number[]) { return new Promise<number>((resolve) => resolve(1)).then(() => quadratic(xs)); }",
            "O(N^2)",
            1,
        ),
    ] {
        let (cost, complete, labels, _) = traced_selected_of("", body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}: {labels:?}");
        assert!(complete, "{body}: {labels:?}");
        assert_eq!(scheduled_labels_of(&labels), scheduled, "{body}: {labels:?}");
    }
}

#[test]
fn an_awaited_continuation_is_attributed_once() {
    let source = format!(
        "{HELPERS}\nexport async function selected(xs: number[], p: Promise<number>) {{ return await p.then(() => quadratic(xs)); }}"
    );

    support::run_with_source(&source, |analysis, file| {
        let part = support::summary_of(analysis, file, "selected");
        let labels: Vec<String> = support::trace_nodes(&analysis.traces, part.trace)
            .into_iter()
            .map(|node| node.label.clone())
            .collect();

        assert_eq!(
            support::projected_class_of(&part.cost),
            Cost::parse("O(N^2)").unwrap()
        );
        assert!(!part.is_complete(), "{labels:?}");
        assert_eq!(scheduled_labels_of(&labels), 1, "{labels:?}");
    });
}

#[test]
fn the_promise_executor_stays_immediate() {
    let (cost, complete, labels, reading) = traced_selected_of(
        "",
        "(xs: number[]) { return new Promise<number>((resolve) => resolve(quadratic(xs))); }",
    );

    assert_eq!(cost, Cost::parse("O(N^2)").unwrap());
    assert!(complete);
    assert_eq!(scheduled_labels_of(&labels), 0, "{labels:?}");
    assert!(reading
        .completions
        .iter()
        .all(|channel| channel.0 == ExecutionPhase::Immediate));
}

#[test]
fn unknown_scheduling_keeps_known_work_and_stays_partial() {
    for (declarations, body) in [
        (
            "",
            "(xs: number[], t: { then(callback: () => void): void }) { t.then(() => quadratic(xs)); }",
        ),
        (
            "",
            "(xs: number[], p: any) { p.then(() => quadratic(xs)); }",
        ),
        (
            "(Promise.prototype as any).then = function () { return 0; };",
            "(xs: number[], p: Promise<number>) { p.then(() => quadratic(xs)); }",
        ),
    ] {
        let (_, complete, reasons) = selected_of(declarations, body);

        assert!(!complete, "{body}: {reasons:?}");
    }
}

#[test]
fn generator_resumption_and_iterated_consumers_charge_lazy_work() {
    let generators = "function* single(xs: number[]) { for (const x of xs) yield x; }\nfunction* square(xs: number[]) { for (const x of xs) for (const y of xs) yield x + y; }";

    assert_selected(&[
        (
            generators,
            "(xs: number[]) { return single(xs).next(); }",
            "O(N)",
            true,
        ),
        (
            generators,
            "(xs: number[]) { return square(xs).return(0); }",
            "O(N^2)",
            true,
        ),
        (
            generators,
            "(xs: number[]) { return Array.from(square(xs), () => quadratic(xs)); }",
            "O(N^4)",
            true,
        ),
        (
            generators,
            "(xs: number[]) { return Array.from(single(xs), () => quadratic(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            generators,
            "(xs: number[]) { return [...square(xs)]; }",
            "O(N^2)",
            true,
        ),
    ]);
}

#[test]
fn promise_resolution_retains_known_thenable_work() {
    assert_selected(&[
        ("", "(xs: number[]) { class Thenable { then(done) { cube(xs); done(1); } } return new Promise(resolve => resolve(new Thenable())); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => { const done = resolve; done({ then(settle) { cube(xs); settle(1); } }); }); }", "O(N^3)", true),
        ("function settle(done, xs) { done({ then(resolve) { cube(xs); resolve(1); } }); }", "(xs: number[]) { return new Promise(resolve => settle(resolve, xs)); }", "O(N^3)", true),
        ("function settle(done, value) { done(value); }", "(xs: number[]) { return new Promise(resolve => settle(resolve, { then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve(1)).then(() => ({ then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise((resolve, reject) => reject(1)).catch(() => ({ then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve(1)).finally(() => ({ then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ get then() { quadratic(xs); return done => { cube(xs); done(1); }; } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ get then() { quadratic(xs); return 1; } })); }", "O(N^2)", true),
        ("", "(xs: number[]) { return new Promise((resolve, reject) => reject({ then(done) { cube(xs); done(1); } })); }", "O(1)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ then: 1 })); }", "O(1)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ then: {} })); }", "O(1)", true),
    ]);
}

#[test]
fn promise_resolution_keeps_unknown_chains_partial() {
    for body in [
        "(xs: number[], value: { then(done): void }) { cube(xs); return new Promise(resolve => resolve(value)); }",
        "(xs: number[], value: { then(done): void }) { return new Promise(resolve => resolve(1)).then(() => { cube(xs); return value; }); }",
        "(xs: number[]) { const value = { then(done) { cube(xs); done(value); } }; return new Promise(resolve => resolve(value)); }",
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(cost, Cost::parse("O(N^3)").unwrap(), "{body}: {reasons:?}");
        assert!(!complete, "{body}: {reasons:?}");
    }
}

#[test]
fn promise_async_returns_assimilate_known_thenables() {
    assert_selected(&[
        ("async function run(xs) { await { then(done) { done({ then(settle) { cube(xs); settle(1); } }); } }; }", "(xs: number[]) { return run(xs); }", "O(N^3)", true),
        ("async function run(xs) { quadratic(xs); return 1; }", "(xs: number[]) { return run(xs); }", "O(N^2)", true),
        ("async function run(xs) { return new Promise(resolve => { quadratic(xs); resolve(1); }); }", "(xs: number[]) { return run(xs); }", "O(N^2)", true),
        ("async function run(xs) { return { then(done) { cube(xs); done(1); } }; }", "(xs: number[]) { return run(xs); }", "O(N^3)", true),
        ("async function run(xs) { await 0; return { then(done) { cube(xs); done(1); } }; }", "(xs: number[]) { return run(xs); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve(1)).then(async () => ({ then(done) { cube(xs); done(1); } })); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Promise(resolve => resolve({ work() { cube(xs); }, then(done) { this.work(); done(1); } })); }", "O(N^3)", false),
        ("function settle(done) { this.work(); done(1); }", "(xs: number[]) { cube(xs); return new Promise(resolve => resolve({ work() { cube(xs); }, then: settle })); }", "O(N^3)", false),
    ]);
}

#[test]
fn promise_getters_and_then_bodies_keep_their_execution_phases() {
    for (body, immediate, scheduled) in [
        ("(xs: number[]) { const p = new Promise(resolve => resolve(1)); Object.defineProperty(p, 'then', { get() { cube(xs); return 1; } }); return new Promise(resolve => resolve(p)); }", "O(N^3)", "O(1)"),
        ("(xs: number[]) { const p = new Promise(resolve => resolve(1)); Object.defineProperty(p, 'then', { get() { quadratic(xs); return done => { cube(xs); done(1); }; } }); return new Promise(resolve => resolve(p)); }", "O(N^2)", "O(N^3)"),
        ("(xs: number[]) { return new Promise(resolve => resolve({ get then() { quadratic(xs); return 1; } })); }", "O(N^2)", "O(1)"),
        ("(xs: number[]) { return new Promise(resolve => resolve({ get then() { quadratic(xs); return done => { cube(xs); done(1); }; } })); }", "O(N^2)", "O(N^3)"),
        ("(xs: number[]) { return new Promise(resolve => resolve(1)).then(() => ({ get then() { quadratic(xs); return done => { cube(xs); done(1); }; } })); }", "O(1)", "O(N^3)"),
        ("(xs: number[]) { async function run() { return { get then() { quadratic(xs); return done => { cube(xs); done(1); }; } }; } return run(); }", "O(N^2)", "O(N^3)"),
        ("(xs: number[]) { async function run() { await 0; return { get then() { quadratic(xs); return done => { cube(xs); done(1); }; } }; } return run(); }", "O(1)", "O(N^3)"),
        ("(xs: number[]) { async function run() { await { get then() { quadratic(xs); return done => { cube(xs); done(1); }; } }; } return run(); }", "O(N^2)", "O(N^3)"),
    ] {
        let source = format!("{HELPERS}\nexport function selected{body}");

        assert_phase_costs(&source, immediate, scheduled);
    }
}

#[test]
fn promise_settlers_refresh_between_analysis_generations() {
    let source = format!("{HELPERS}\nexport function selected(xs: number[]) {{ return new Promise(resolve => resolve({{ then(done) {{ cube(xs); done(1); }} }})); }}");

    support::run_with_source(&source, |analysis, file| {
        for _ in 0..2 {
            let function = support::function_of_name(analysis.project, file, "selected");
            let part = support::summary_of(analysis, file, "selected");

            assert_eq!(
                support::legacy_class_of(analysis, file, function, &part.cost),
                Cost::parse("O(N^3)").unwrap()
            );
            assert!(part.is_complete());
            analysis.reset_between_passes();
        }
    });
}

#[test]
fn promise_async_generator_results_retain_known_work_with_protocol_uncertainty() {
    for completion in ["yield", "return"] {
        let declarations = format!("async function* produce(xs) {{ {completion} {{ then(done) {{ cube(xs); done(1); }} }}; }} async function run(xs) {{ for await (const value of produce(xs)) void value; }}");

        assert_selected(&[
            (
                &declarations,
                "(xs: number[]) { return run(xs); }",
                "O(N^3)",
                false,
            ),
            (
                &declarations,
                "(xs: number[]) { const iterator = produce(xs); }",
                "O(1)",
                true,
            ),
        ]);
    }
}

#[test]
fn custom_iterator_visits_require_source_evidence() {
    for body in [
        "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; for (const value of values) cube(xs); }",
        "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { quadratic(xs); return { done: false, value: 1 }; } }; } }; for (const value of values) cube(xs); }",
        "(xs: number[]) { let i = 0; const values = { [Symbol.iterator]() { return { next() { return { done: i++ >= xs.length, value: i }; } }; } }; for (const value of values) cube(xs); }",
        "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; Array.from(values, () => cube(xs)); }",
    ] {
        let (cost, complete, reasons) = selected_of("", body);

        assert_eq!(support::projected_class_of(&cost), Cost::parse("O(N^3)").unwrap(), "{body}: {reasons:?}");
        assert!(!complete, "{body}");
        assert!(reasons.contains(&UnknownReason::Bound), "{body}: {reasons:?}");
    }
}

#[test]
fn iterator_materialization_keeps_unknown_counts_and_known_protocol_work() {
    for expression in [
        "[...values]",
        "Array.from(values)",
        "new Set(values)",
        "new Uint8Array(values)",
    ] {
        let body = format!("(xs: number[]) {{ const values = {{ [Symbol.iterator]() {{ return {{ next() {{ cube(xs); return {{ done: false, value: 1 }}; }} }}; }} }}; return {expression}; }}");

        assert_unknown_iteration_count(&body);
    }

    for expression in [
        "[...values]",
        "Array.from(values)",
        "new Set(values)",
        "new Uint8Array(values)",
    ] {
        let body = format!("(xs: number[]) {{ const values = {{ [Symbol.iterator]() {{ return {{ next() {{ return {{ done: false, value: 1 }}; }} }}; }} }}; const copied = {expression}; for (const value of copied) cube(xs); }}");

        assert_unknown_iteration_count(&body);
    }
}

#[test]
fn iterator_getters_keep_their_once_and_per_visit_work() {
    assert_selected(&[
        ("", "(xs: number[]) { const values = { get [Symbol.iterator]() { cube(xs); return function () { return { next() { return { done: true }; } }; }; } }; for (const value of values) void value; }", "O(N^3)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { get next() { cube(xs); return function () { return { done: true }; }; } }; } }; for (const value of values) void value; }", "O(N^3)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { get done() { cube(xs); return true; } }; } }; } }; for (const value of values) void value; }", "O(N^3)", false),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, get value() { cube(xs); return 1; } }; } }; } }; for (const value of values) void value; }", "O(N^3)", false),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: true, get value() { cube(xs); return 1; } }; } }; } }; for (const value of values) void value; }", "O(1)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, get return() { cube(xs); return function () { return { done: true }; }; } }; } }; for (const value of values) break; }", "O(N^3)", true),
    ]);
}

#[test]
fn proven_generator_counts_reach_acquisition_and_copies() {
    assert_selected(&[
        ("", "(xs: number[]) { const values = { *[Symbol.iterator]() { for (const a of xs) for (const b of xs) yield a + b; } }; for (const value of values) cube(xs); }", "O(N^5)", true),
        ("", "(xs: number[]) { function* make() { for (const a of xs) for (const b of xs) yield a + b; } const values = { [Symbol.iterator]() { return make(); } }; for (const value of values) cube(xs); }", "O(N^5)", true),
        ("", "(xs: number[]) { const values = { *[Symbol.iterator]() { for (const a of xs) for (const b of xs) yield a + b; } }; const copied = [...values]; for (const value of copied) cube(xs); }", "O(N^5)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { quadratic(xs); return { done: true }; } }; } }; for (const value of values) void value; }", "O(N^2)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; for (const value of values) { cube(xs); break; } }", "O(N^3)", true),
    ]);
}

#[test]
fn asynchronous_result_resolution_cannot_prove_raw_done() {
    for next in [
        "next() { return { done: true, then(resolve) { resolve({ done: false, value: 1 }); } }; }",
        "async next() { return { done: true, then(resolve) { resolve({ done: false, value: 1 }); } }; }",
        "next() { return { done: true, get then() { cube(xs); return (resolve) => resolve({ done: false, value: 1 }); } }; }",
    ] {
        let source = format!("{HELPERS}\nexport async function selected(xs: number[]) {{ const values = {{ [Symbol.asyncIterator]() {{ return {{ {next} }}; }} }}; for await (const value of values) cube(xs); }}");
        let (cost, complete, reasons) = legacy_result_of(&source, "selected");

        assert_eq!(support::projected_class_of(&cost), Cost::parse("O(N^3)").unwrap(), "{next}: {reasons:?}");
        assert!(!complete);
        assert!(reasons.contains(&UnknownReason::Bound), "{next}: {reasons:?}");
    }
}

#[test]
fn collection_constructor_modes_preserve_native_controls() {
    assert_selected(&[
        ("", "() { return new Set(); }", "O(1)", true),
        ("", "() { return new Map(null); }", "O(1)", true),
        ("", "(xs: number[]) { return new Set(xs); }", "O(N)", true),
        ("", "(xs: number[]) { return new Uint8Array(xs); }", "O(N)", true),
        ("", "() { return new Uint8Array(); }", "O(1)", true),
        ("", "() { return new Uint8Array(4); }", "O(1)", true),
        ("", "() { return new Uint8Array('4'); }", "O(1)", true),
        ("", "() { return new Uint8Array({ length: 2, 0: 1, 1: 2 }); }", "O(1)", true),
        ("", "(xs: number[]) { const values = new Set(xs); return new Uint8Array(values); }", "O(N)", true),
        ("", "(xs: number[]) { Set.prototype.add = function(value) { cube(xs); }; return new Set(xs); }", "O(N^4)", false),
        ("", "(xs: number[]) { Object.defineProperty(Set.prototype, 'add', { get() { cube(xs); return function(value) {}; } }); return new Set(xs); }", "O(N^3)", false),
    ]);
}

#[test]
fn delegated_and_destructured_consumption_preserve_count_boundaries() {
    assert_selected(&[
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { cube(xs); return { done: false, value: 1 }; } }; } }; const [first] = values; return first; }", "O(N^3)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { cube(xs); return { done: false, value: 1 }; } }; } }; const [...rest] = values; return rest; }", "O(N^3)", false),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; function* forwarded() { yield* values; } for (const value of forwarded()) cube(xs); }", "O(N^3)", false),
        ("", "(xs: number[], stop: boolean) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; for (const value of values) { cube(xs); if (stop) break; } }", "O(N^3)", false),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; for (const value of values) { cube(xs); continue; } }", "O(N^3)", false),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; } }; } }; for (const value of values) { cube(xs); return 1; } return 0; }", "O(N^3)", true),
    ]);
}

#[test]
fn native_iterables_retain_their_declared_acquisition_contract() {
    assert_selected(&[
        ("", "(xs: number[], text: string) { for (const value of text) cube(xs); }", "O(N^4)", true),
        ("", "(xs: number[], values: Set<number>) { for (const value of values) cube(xs); }", "O(N^4)", true),
        ("", "(xs: number[], values: Map<number, number>) { for (const value of values) cube(xs); }", "O(N^4)", true),
        ("", "(xs: number[], values: Uint8Array) { for (const value of values) cube(xs); }", "O(N^4)", true),
        ("", "(xs: number[]) { for (const value of xs.values()) cube(xs); }", "O(N^4)", false),
        ("", "(xs: number[]) { for (const value of xs.entries()) cube(xs); }", "O(N^4)", false),
        ("", "(xs: number[]) { Array.prototype[Symbol.iterator] = function() { return { next() { return { done: false, value: 1 }; } }; }; for (const value of xs) cube(xs); }", "O(1)", false),
    ]);
}

#[test]
fn collection_adders_and_entry_accessors_retain_source_work() {
    assert_selected(&[
        ("", "(xs: number[]) { Map.prototype.set = function(key, value) { cube(xs); }; return new Map(xs.map(x => [x, x])); }", "O(N^4)", false),
        ("", "(xs: number[]) { const entries = [{ get 0() { cube(xs); return 1; }, 1: 2 }]; return new Map(entries); }", "O(N^3)", true),
        ("", "(xs: number[]) { const entries = { [Symbol.iterator]() { return { next() { return { done: false, value: { get 0() { cube(xs); return 1; }, 1: 2 } }; } }; } }; return new Map(entries); }", "O(N^3)", false),
        ("", "(xs: number[]) { const entries = new Set([1]); Set.prototype.add = function(value) { entries.add(value + 1); cube(xs); }; return new Set(entries); }", "O(N^3)", false),
    ]);
}

#[test]
fn constructor_adders_receive_elements_and_entry_fields() {
    assert_selected(&[
        ("", "(xs: number[]) { Set.prototype.add = function(value: number[]) { for (const a of value) for (const b of value) void b; }; return new Set([xs]); }", "O(N^2)", true),
        ("", "(xs: number[]) { Set.prototype.add = function(value: number[]) { cube(value); }; return new Set([xs.flatMap(() => xs)]); }", "O(N^6)", true),
        ("", "(xs: number[], ys: number[]) { Map.prototype.set = function(key: number[], value: number[]) { for (const a of key) for (const b of value) void b; }; return new Map([[xs, ys]]); }", "O(N^2)", true),
    ]);
}

#[test]
fn typed_iterable_conversion_retains_known_element_work() {
    assert_selected(&[
        ("", "(xs: number[]) { return new Uint8Array([{ valueOf() { cube(xs); return 1; } }]); }", "O(N^3)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { return { done: false, value: { valueOf() { cube(xs); return 1; } } }; } }; } }; return new Uint8Array(values); }", "O(N^3)", false),
    ]);
}

#[test]
fn arraylike_typed_construction_and_entry_consumption_retain_getters() {
    assert_selected(&[
        ("", "(xs: number[]) { return new Uint8Array({ length: 1, get 0() { cube(xs); return 1; } }); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Uint8Array({ get length() { cube(xs); return 1; }, 0: 1 }); }", "O(N^3)", true),
        ("", "(xs: number[]) { return Object.fromEntries([[1, 2], [3, 4]]); }", "O(1)", true),
        ("", "(xs: number[]) { const values = { [Symbol.iterator]() { return { next() { cube(xs); return { done: false, value: [1, 2] }; } }; } }; return Object.fromEntries(values); }", "O(N^3)", false),
        ("", "(xs: number[]) { return Object.fromEntries([{ get 0() { cube(xs); return 1; }, 1: 2 }]); }", "O(N^3)", true),
    ]);
}

#[test]
fn returned_iterable_factories_preserve_acquisition_captures() {
    assert_selected(&[
        ("function make(values: number[]) { return { *[Symbol.iterator]() { for (const a of values) for (const b of values) yield a; } }; }", "(xs: number[], ys: number[]) { for (const value of make(ys)) cube(xs); }", "O(N^5)", true),
        ("function make(values: number[]) { return { *[Symbol.iterator]() { for (const a of values) for (const b of values) yield a; } }; }", "(xs: number[]) { for (const value of make([1])) cube(xs); }", "O(N^3)", true),
    ]);
}

#[test]
fn entry_key_conversion_is_specific_to_object_construction() {
    assert_selected(&[
        ("", "(xs: number[]) { return Object.fromEntries([[{toString(){cube(xs);return 'x';}},1]]); }", "O(N^3)", true),
        ("", "(xs: number[]) { return new Map([[{toString(){cube(xs);return 'x';}},1]]); }", "O(1)", true),
    ]);
}

#[test]
fn constructor_adder_sizes_keep_independent_dimensions() {
    let body = "(xs: number[], ys: number[]) { Map.prototype.set = function(key: number[], value: number[]) { for (const a of key) for (const b of value) void b; }; return new Map([[xs,ys]]); }";

    assert_eq!(bound_result_of(body, "O(xs * ys)"), (true, true));
    assert_eq!(bound_result_of(body, "O(xs^2)"), (false, true));
}

#[test]
fn supplied_iterable_identity_survives_exports_without_certifying_other_actuals() {
    let source = format!("{HELPERS} export function consume(value, xs:number[]){{for(const item of value)cube(xs);}} export function forward(value,xs:number[]){{const same=value;consume(same,xs);}} export function array(xs:number[]){{forward(xs,xs);}} export function custom(xs:number[]){{forward({{[Symbol.iterator](){{return {{next(){{return {{done:false,value:1}};}}}};}}}},xs);}}");

    for order in [["array", "custom"], ["custom", "array"]] {
        support::run_with_source(&source, |analysis, file| {
            for _ in 0..2 {
                for name in order {
                    let part = support::summary_of(analysis, file, name);
                    let expected = if name == "array" { "O(N^4)" } else { "O(N^3)" };

                    assert_eq!(
                        support::projected_class_of(&part.cost),
                        Cost::parse(expected).unwrap(),
                        "{order:?}: {name}"
                    );
                    assert_eq!(part.is_complete(), name == "array", "{order:?}: {name}");
                }

                analysis.reset_between_passes();
            }
        });
    }
}

#[test]
fn contextual_produced_iterables_keep_their_unproved_count_in_both_orders() {
    let source = format!("{HELPERS} export function consume(value,xs:number[]){{for(const item of value)cube(xs);}} export function forward(value,xs:number[]){{const produced=value.slice();consume(produced,xs);}} export function array(xs:number[]){{forward(xs,xs);}} export function custom(xs:number[]){{forward({{slice(){{return {{[Symbol.iterator](){{return {{next(){{return {{done:false,value:1}};}}}};}}}};}}}},xs);}}");

    for order in [["array", "custom"], ["custom", "array"]] {
        support::run_with_source(&source, |analysis, file| {
            for name in order {
                let part = support::summary_of(analysis, file, name);

                assert_eq!(
                    support::projected_class_of(&part.cost),
                    Cost::parse("O(N^3)").unwrap(),
                    "{order:?}: {name}"
                );
                assert!(!part.is_complete(), "{order:?}: {name}");
            }
        });
    }
}

#[test]
fn array_from_arraylike_mode_retains_length_index_and_mapping_work() {
    assert_selected(&[
        ("", "(xs:number[]){return Array.from({get length(){cube(xs);return 2;}, get 0(){cube(xs);return 1;}});}", "O(N^3)", true),
        ("", "(xs:number[],n:number){return Array.from({get length(){cube(xs);return n;}, get 0(){cube(xs);return 1;}});}", "O(N^4)", true),
        ("", "(xs:number[],n:number){return Array.from({length:n},()=>cube(xs));}", "O(N^4)", true),
        ("declare function lengthOf():number;", "(xs:number[]){return Array.from({get length(){cube(xs);return lengthOf();},get 0(){cube(xs);return 1;}});}", "O(N^3)", false),
    ]);
}

#[test]
fn declared_array_elements_require_numeric_property_keys() {
    assert_selected(&[
        ("", "(xs:number[],rows:number[][]){const index=0;for(const value of rows[index])cube(xs);}", "O(N^4)", true),
        ("", "(xs:number[]){const rows:number[][]=[];(rows as any).custom={[Symbol.iterator](){return {next(){return {done:false,value:1};}};}};for(const value of rows['custom'])cube(xs);}", "O(N^3)", false),
    ]);
}

fn assert_unknown_iteration_count(body: &str) {
    let (cost, complete, reasons) = selected_of("", body);

    assert_eq!(
        support::projected_class_of(&cost),
        Cost::parse("O(N^3)").unwrap(),
        "{body}: {reasons:?}"
    );
    assert!(!complete);
    assert!(
        reasons.contains(&UnknownReason::Bound),
        "{body}: {reasons:?}"
    );
}

#[test]
fn supplied_nested_array_wrappers_preserve_outer_iteration_bounds() {
    for mark in ["", "cold", "O(N)", "ignore"] {
        let directive = if mark.is_empty() {
            String::new()
        } else {
            format!("/** @perf {mark} */\n")
        };
        let source = format!("{directive}function work(values:number[][]){{for(const row of values)for(const value of row)void value;}} export function selected(xs:number[][]){{for(const row of xs)work([row]);for(const a of xs)for(const b of xs)for(const c of xs)void c;}}");

        support::run_with_source(&source, |analysis, file| {
            let part = support::summary_of(analysis, file, "selected");
            let reasons = support::unknown_reasons(analysis, part.unknowns);

            assert_eq!(
                part.is_complete(),
                mark.is_empty() || mark == "cold",
                "{mark}: {reasons:?}"
            );
            assert_eq!(
                reasons.contains(&UnknownReason::Bound),
                mark == "O(N)" || mark == "ignore"
            );
            assert_eq!(
                support::projected_class_of(&part.cost),
                Cost::parse("O(N^3)").unwrap()
            );
        });
    }
}

#[test]
fn native_assign_retains_known_property_work() {
    assert_native_property_work(&[
        (
            r#"(xs: number[]) {const target={slow(value:number[]){cube(value)},set x(value:number[]){this.slow(value)}};return Object.assign(target,{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={slow(value:number[]){cube(value)},set x(value:number[]){this.slow(value)}};target.x=xs;return target;}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {class Base{slow(value:number[]){cube(value)}set x(value:number[]){this.slow(value)}}class Child extends Base{}return Object.assign(new Child(),{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {class Base{slow(value:number[]){cube(value)}set x(value:number[]){this.slow(value)}}class Child extends Base{}const target=new Child();target.x=xs;return target;}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {class Base{slow(value:number[]){quadratic(value)}set x(value:number[]){this.slow(value)}}class Child extends Base{slow(value:number[]){cube(value)}}return Object.assign(new Child(),{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {class Base{slow(value:number[]){quadratic(value)}set x(value:number[]){this.slow(value)}}class Child extends Base{slow(value:number[]){cube(value)}}const target=new Child();target.x=xs;return target;}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set __proto__(value:number[]){cube(value)}};return Object.assign(target,{get __proto__(){return xs}});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set __proto__(value:unknown){cube(xs)}};return Object.assign(target,{__proto__(){return 0}});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const __proto__=xs;const target={set __proto__(value:number[]){cube(value)}};return Object.assign(target,{__proto__});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set __proto__(value:unknown){cube(xs)}};return Object.assign(target,{__proto__:null});}"#,
            "O(N)",
        ),
        (
            r#"(xs: number[]) {const target={set x(value:number){cube(xs)}}; return Object.assign(target,{x:1});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set x(value:number[]){cube(value)}}; return Object.assign(target,{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set x(value:number[]){cube(value)}}; return Object.assign(target,{x:xs.flatMap(()=>xs)});}"#,
            "O(N^6)",
        ),
        (
            r#"(xs: number[]) {class Base{set x(value:number[]){cube(value)}} class Child extends Base{}; return Object.assign(new Child(),{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {class Target{static set x(value:number[]){cube(value)}} return Object.assign(Target,{x:xs});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const target={set x(value:number[]){cube(value)}}; return Object.assign(target,{get x(){return xs}});}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {return Object.assign({x:0},{x:1});}"#,
            "O(1)",
        ),
    ]);
}

#[test]
fn assignment_setter_supplied_owner_reaches_pending_effects() {
    for (supplied, affected) in [("values", true), ("other", false)] {
        let source = format!("{HELPERS} export async function selected(xs:number[]){{const values=new Set([0]);const other=new Set([0]);const target={{set x(v:Set<number>){{Promise.resolve().then(()=>{{v.delete(0);v.add(0)}})}}}};Object.assign(target,{{x:{supplied}}});for(const value of values){{await 0;cube(xs)}}}}");
        let (cost, _, reasons) = legacy_result_of(&source, "selected");

        assert_eq!(
            reasons.contains(&UnknownReason::Bound),
            affected,
            "{supplied}: {reasons:?}"
        );
        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse("O(N^3)").unwrap()
        );
    }
}

#[test]
fn native_property_parameter_sources_keep_both_call_orders() {
    for calls in ["copy(first);copy(second)", "copy(second);copy(first)"] {
        let source = format!("{HELPERS} function copy(target:object){{return Object.assign(target,{{x:1}})}} export function selected(xs:number[]){{const first={{set x(value:number){{cube(xs)}}}};const second={{set x(value:number){{quadratic(xs)}}}};{calls};}}");
        let (cost, _, reasons) = legacy_result_of(&source, "selected");

        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse("O(N^3)").unwrap(),
            "{calls}: {reasons:?}"
        );
    }
}

#[test]
fn native_concat_retains_known_property_work() {
    assert_native_property_work(&[
        (
            r#"(xs: number[]) {const items=[0];Object.defineProperty(items,"constructor",{get(){cube(xs);return Array}});return items.concat([]);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={length:{valueOf(){cube(xs);return 1}},[Symbol.isConcatSpreadable]:true,0:1};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={get length(){return {valueOf(){cube(xs);return 1}}},[Symbol.isConcatSpreadable]:true,0:1};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={length:1,[Symbol.isConcatSpreadable]:true,get 0(){cube(xs);return 0}};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={length:1,get [Symbol.isConcatSpreadable](){cube(xs);return true},0:1};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={get length(){cube(xs);return 1},[Symbol.isConcatSpreadable]:true,0:1};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const item={length:1,[Symbol.isConcatSpreadable]:false,get 0(){cube(xs);return 0}};return [].concat(item as any);}"#,
            "O(N)",
        ),
        (r#"(xs: number[]) {return [1].concat([2]);}"#, "O(1)"),
        (
            r#"(xs: number[]) {const prototype={get 0(){cube(xs);return 0}};const item={__proto__:prototype,length:1,[Symbol.isConcatSpreadable]:true};return [].concat(item as any);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const items=[0];Object.defineProperty(items,"constructor",{value:{get [Symbol.species](){cube(xs);return Array}}});return items.concat([]);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const items=[0];Object.defineProperty(items,"constructor",{value:{[Symbol.species]:class Result{constructor(){cube(xs)}}}});return items.concat([]);}"#,
            "O(N^3)",
        ),
        (
            r#"(xs: number[]) {const items=[0];Object.defineProperty(items,"0",{get(){cube(xs);return 0}});return items.concat([]);}"#,
            "O(N^3)",
        ),
    ]);
}

#[test]
fn concat_length_coercion_preserves_pending_owner_effects() {
    for (written, affected) in [("values", true), ("other", false)] {
        let source = format!("{HELPERS} export async function selected(xs:number[]){{const values=new Set([0]);const other=new Set([0]);const item={{[Symbol.isConcatSpreadable]:true,length:{{valueOf(){{Promise.resolve().then(()=>{{{written}.delete(0);{written}.add(0)}});return 1}}}},0:0}};[].concat(item as any);for(const value of values){{await 0;cube(xs)}}}}");
        let (cost, _, reasons) = legacy_result_of(&source, "selected");

        assert_eq!(
            reasons.contains(&UnknownReason::Bound),
            affected,
            "{written}: {reasons:?}"
        );
        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse("O(N^3)").unwrap()
        );
    }
}

#[test]
fn concat_unknown_spreadability_retains_possible_length_coercion() {
    for fields in [
        "const item={ [key]:true,length:{valueOf(){cube(xs);return 1}},0:0};",
        "const item:any={length:{valueOf(){cube(xs);return 1}},0:0};item[key]=true;",
        "const item={ [Symbol.isConcatSpreadable]:false,[key]:true,length:{valueOf(){cube(xs);return 1}},0:0};",
        "const item:any={ [Symbol.isConcatSpreadable]:false,length:{valueOf(){cube(xs);return 1}},0:0};item[key]=true;",
        "const item:any=[0];item[Symbol.isConcatSpreadable]=false;Object.defineProperty(item,'0',{get(){cube(xs);return 0}});item[key]=true;",
    ] {
        let source = format!("{HELPERS} export function selected(xs:number[],key:symbol){{{fields}return [].concat(item as any)}}");
        let (cost, _, reasons) = legacy_result_of(&source, "selected");

        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse("O(N^3)").unwrap(),
            "{fields}: {reasons:?}"
        );
    }
}

fn assert_native_property_work(cases: &[(&str, &str)]) {
    for (body, expected) in cases {
        let (cost, _, reasons) = selected_of("", body);

        assert_eq!(
            support::projected_class_of(&cost),
            Cost::parse(expected).unwrap(),
            "{body}: {reasons:?}"
        );
    }
}

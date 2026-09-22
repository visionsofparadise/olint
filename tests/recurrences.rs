use olint::analysis::Analysis;
use olint::cost::{Cost, CostComparison, Part};
use olint::project::FileId;
use olint::unknowns::UnknownReason;

mod support;

use support::{function_of_name, legacy_class_of, run_with_source, summary_of, unknown_reasons};

fn text_of(analysis: &Analysis<'_, '_>, cost: &Cost) -> String {
    cost.text_with(&|id| analysis.values.label(id))
}

fn class_of(analysis: &mut Analysis<'_, '_>, file: FileId, name: &str) -> Cost {
    let function = function_of_name(analysis.project, file, name);
    let part = summary_of(analysis, file, name);

    legacy_class_of(analysis, file, function, &part.cost)
}

fn assert_class(source: &str, name: &str, expected: &str, complete: bool) {
    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, name);
        let class = class_of(analysis, file, name);

        assert_eq!(
            class,
            Cost::parse(expected).unwrap(),
            "{name}: {}",
            text_of(analysis, &part.cost)
        );
        assert_eq!(part.is_complete(), complete, "{name}");
    });
}

fn assert_above(source: &str, name: &str, floor: &str, ceiling: &str) {
    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, name);
        let function = function_of_name(analysis.project, file, name);
        let floor = analysis
            .bind_function_cost(file, function, &Cost::parse(floor).unwrap())
            .unwrap();
        let ceiling = analysis
            .bind_function_cost(file, function, &Cost::parse(ceiling).unwrap())
            .unwrap();

        assert_eq!(
            part.cost.compare(&ceiling),
            CostComparison::Within,
            "{name}: {}",
            text_of(analysis, &part.cost)
        );
        assert_ne!(
            part.cost.compare(&floor),
            CostComparison::Within,
            "{name}: {}",
            text_of(analysis, &part.cost)
        );
    });
}

fn assert_exceeds_quartic(source: &str, name: &str, expected: &str) {
    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, name);
        let function = function_of_name(analysis.project, file, name);
        let quartic = analysis
            .bind_function_cost(file, function, &Cost::parse("O(N^4)").unwrap())
            .unwrap();

        assert_eq!(text_of(analysis, &part.cost), expected);
        assert_eq!(part.cost.compare(&quartic), CostComparison::Exceeds);
    });
}

fn assert_recurrence_unresolved(source: &str, name: &str) {
    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, name);

        assert!(!part.is_complete(), "{name}");
        assert!(
            unknown_reasons(analysis, part.unknowns).contains(&UnknownReason::Recurrence),
            "{name}: {:?}",
            unknown_reasons(analysis, part.unknowns)
        );
    });
}

const SCAN_PER_DEPTH: &str = "export function f(n: number, values: number[]): number {\n\tif (n <= 0) return 0;\n\tlet total = 0;\n\tfor (const x of values) total += x;\n\treturn total + f(n - 1, values);\n}\n";

#[test]
fn c7_scan_per_depth_charges_the_scan_at_every_level() {
    assert_above(SCAN_PER_DEPTH, "f", "O(N)", "O(N^2)");

    run_with_source(SCAN_PER_DEPTH, |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert!(part.is_complete());
        assert_eq!(
            text_of(analysis, &part.cost),
            "O(max(n, values, (n * max(1, n, values))))"
        );
    });
}

#[test]
fn a_mutual_cycle_agrees_with_its_direct_equivalent() {
    let source = "export function f(n: number, values: number[]): number {\n\tif (n <= 0) return 0;\n\tlet total = 0;\n\tfor (const x of values) total += x;\n\treturn total + g(n - 1, values);\n}\nexport function g(n: number, values: number[]): number {\n\treturn f(n, values);\n}\n";

    assert_above(source, "f", "O(N)", "O(N^2)");
    assert_above(source, "g", "O(N)", "O(N^2)");

    run_with_source(source, |analysis, file| {
        let direct = summary_of(analysis, file, "f");
        let forwarded = summary_of(analysis, file, "g");

        assert_eq!(
            text_of(analysis, &forwarded.cost),
            text_of(analysis, &direct.cost)
        );
    });

    run_with_source(SCAN_PER_DEPTH, |analysis, file| {
        let alone = summary_of(analysis, file, "f");

        run_with_source(source, |cycle, file| {
            let member = summary_of(cycle, file, "f");

            assert_eq!(
                text_of(cycle, &member.cost),
                text_of(analysis, &alone.cost),
                "a forwarding member cannot change the scan per depth"
            );
        });
    });
}

#[test]
fn binary_decrement_reports_exponential_growth() {
    let source = "export function f(n: number): number {\n\tif (n <= 0) return 1;\n\treturn f(n - 1) + f(n - 1) + 1;\n}\n";

    assert_exceeds_quartic(source, "f", "O((2)^(n))");

    run_with_source(source, |analysis, file| {
        assert!(summary_of(analysis, file, "f").is_complete());
    });
}

#[test]
fn a_halved_argument_is_logarithmic_under_its_numeric_guard() {
    let shifted = "export function f(n: number): number {\n\tif (n <= 1) return 0;\n\treturn 1 + f(n >> 1);\n}\n";
    let floored = "export function f(n: number): number {\n\tif (n <= 1) return 0;\n\treturn 1 + f(Math.floor(n / 2));\n}\n";

    for source in [shifted, floored] {
        run_with_source(source, |analysis, file| {
            let part = summary_of(analysis, file, "f");

            assert_eq!(text_of(analysis, &part.cost), "O(log(n))", "{source}");
        });
    }

    assert_class(shifted, "f", "O(log N)", true);
}

#[test]
fn an_exact_halving_without_a_positive_floor_stays_unresolved() {
    let guarded = "export function f(n: number): number {\n\tif (n <= 1) return 0;\n\treturn 1 + f(n / 2);\n}\n";
    let unguarded = "export function f(n: number): number {\n\tif (n <= 0) return 0;\n\treturn 1 + f(n / 2);\n}\n";

    assert_class(guarded, "f", "O(log N)", true);
    assert_recurrence_unresolved(unguarded, "f");
}

#[test]
fn an_equality_base_case_cannot_prove_a_decrement_terminates() {
    let skipping = "export function f(n: number): number {\n\tif (n === 0) return 0;\n\treturn 1 + f(n - 2);\n}\n";
    let ordered = "export function f(n: number): number {\n\tif (n <= 0) return 0;\n\treturn 1 + f(n - 2);\n}\n";

    assert_recurrence_unresolved(skipping, "f");
    assert_class(ordered, "f", "O(N)", true);
}

#[test]
fn a_measure_sized_multiplicity_keeps_its_factorial_expression() {
    let source = "export function f(n: number): number {\n\tif (n <= 0) return 1;\n\tlet total = 0;\n\tfor (let i = 0; i < n; i++) total += f(n - 1);\n\treturn total;\n}\n";

    assert_exceeds_quartic(source, "f", "O(((n)! * max(1, n)))");
}

#[test]
fn mixed_inputs_keep_every_independent_dimension() {
    let source = "export function f(n: number, values: number[], ys: number[]): number {\n\tif (n <= 0) return 0;\n\tlet total = 0;\n\tfor (const y of ys) total += y;\n\tfor (const x of values) total += x;\n\treturn total + f(n - 1, values, ys);\n}\n";

    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert_eq!(
            text_of(analysis, &part.cost),
            "O(max(n, values, ys, (n * max(1, n, values, ys))))"
        );
        assert!(part.is_complete());
    });
}

#[test]
fn an_argument_with_no_proven_relation_stays_unresolved() {
    let source = "export function f(n: number, values: number[]): number {\n\tif (n <= 0) return 0;\n\tlet total = 0;\n\tfor (const x of values) total += x;\n\treturn total + f(values.length, values);\n}\n";

    assert_recurrence_unresolved(source, "f");
}

#[test]
fn a_recursive_call_under_an_unresolved_bound_stays_unresolved() {
    let source = "export function f(n: number, rows: number[][]): number {\n\tif (n <= 0) return 0;\n\tlet total = 0;\n\tfor (const row of rows) total += f(n - 1, row.map((v) => [v]));\n\treturn total;\n}\n";

    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert!(!part.is_complete());
    });
}

#[test]
fn a_pass_through_callback_keeps_the_solved_depth() {
    let source = "export function f(n: number, xs: number[], callback: () => void): void {\n\tif (n <= 0) {\n\t\tcallback();\n\t\treturn;\n\t}\n\tfor (const x of xs) callback();\n\tf(n - 1, xs, callback);\n}\nexport function run(xs: number[], n: number): void {\n\tlet total = 0;\n\tf(n, xs, () => {\n\t\ttotal += 1;\n\t});\n}\n";

    assert_above(source, "run", "O(N)", "O(N^2)");
}

#[test]
fn c1_specialized_callback_recursion_terminates_without_a_fabricated_envelope() {
    let source = "export function f(n: number, xs: number[], callback: () => void): void {\n\tif (n <= 0) {\n\t\tcallback();\n\t\treturn;\n\t}\n\tf(n - 1, xs, () => {\n\t\tfor (const x of xs) callback();\n\t});\n}\n";

    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, "f");
        let function = function_of_name(analysis.project, file, "f");
        let envelope = analysis
            .bind_function_cost(file, function, &Cost::parse("O(N)").unwrap())
            .unwrap();

        support::assert_scheduler_terminal(analysis.scheduler_stats());

        assert!(!part.is_complete());
        assert_eq!(envelope.compare(&part.cost), CostComparison::Exceeds);
    });
}

#[test]
fn a_growing_recursive_callback_stays_incomplete() {
    let source = "export function f(n: number, xs: number[], callback: () => void): void {\n\tif (n <= 0) {\n\t\tcallback();\n\t\treturn;\n\t}\n\tf(n - 1, xs, () => {\n\t\tcallback();\n\t\tcallback();\n\t});\n}\n";

    run_with_source(source, |analysis, file| {
        let part: Part = summary_of(analysis, file, "f");

        support::assert_scheduler_terminal(analysis.scheduler_stats());

        assert!(!part.is_complete());
    });
}

#[test]
fn a_directive_cost_still_overrides_a_solvable_recurrence() {
    let source = "/** @perf O(1) */\nexport function f(n: number): number {\n\tif (n <= 0) return 0;\n\treturn 1 + f(n - 1);\n}\n";

    assert_class(source, "f", "O(1)", true);
}

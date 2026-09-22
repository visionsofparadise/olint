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

type RecurrenceRow<'r> = (&'r str, &'r str, &'r str);

fn recurrence_results_of(rows: &[RecurrenceRow<'_>]) -> Vec<(String, String, bool, bool)> {
    rows.iter()
        .map(|(label, name, source)| {
            let mut found = None;

            run_with_source(source, |analysis, file| {
                let part = summary_of(analysis, file, name);
                let reasons = unknown_reasons(analysis, part.unknowns);

                found = Some((
                    label.to_string(),
                    text_of(analysis, &part.cost),
                    part.is_complete(),
                    reasons.contains(&UnknownReason::Recurrence),
                ));
            });

            found.expect("the source declares the named function")
        })
        .collect()
}

#[test]
fn an_argument_that_can_grow_across_depth_keeps_its_recursion_unresolved() {
    let rows = [
        (
            "an array doubled by spread",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; const doubled = [...xs, ...xs]; let t = 0; for (const x of doubled) t += x; return t + f(n - 1, doubled); }",
        ),
        (
            "an array doubled by concat",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; const doubled = xs.concat(xs); let t = 0; for (const x of doubled) t += x; return t + f(n - 1, doubled); }",
        ),
        (
            "a string doubled by concatenation",
            "f",
            "export function f(n: number, s: string): number { if (n <= 0) return 0; const bigger = s + s; let t = 0; for (const c of bigger) t += c.length; return t + f(n - 1, bigger); }",
        ),
        (
            "a record rebuilt around a doubled field",
            "f",
            "export function f(n: number, box: { items: number[] }): number { if (n <= 0) return 0; let t = 0; for (const x of box.items) t += x; return t + f(n - 1, { items: box.items.concat(box.items) }); }",
        ),
        (
            "a second array doubled beside an unchanged one",
            "f",
            "export function f(n: number, xs: number[], ys: number[]): number { if (n <= 0) return 0; let t = 0; for (const y of ys) t += y; return t + f(n - 1, xs, ys.concat(ys)); }",
        ),
        (
            "an array of rows doubled by concat",
            "f",
            "export function f(n: number, rows: number[][]): number { if (n <= 0) return 0; let t = 0; for (const r of rows) t += r.length; return t + f(n - 1, rows.concat(rows)); }",
        ),
        (
            "a second number doubled",
            "f",
            "export function f(n: number, m: number): number { if (n <= 0) return 0; let t = 0; for (let i = 0; i < m; i++) t += i; return t + f(n - 1, m * 2); }",
        ),
        (
            "a second number incremented",
            "f",
            "export function f(n: number, m: number): number { if (n <= 0) return 0; let t = 0; for (let i = 0; i < m; i++) t += i; return t + f(n - 1, m + 1); }",
        ),
        (
            "a second number decremented below every bound",
            "f",
            "export function f(n: number, m: number): number { if (n <= 0) return 0; let t = 0; for (let i = 0; i < m; i++) t += i; return t + f(n - 1, m - 1); }",
        ),
        (
            "an accumulator extended by one element",
            "f",
            "export function f(n: number, acc: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of acc) t += x; return t + f(n - 1, [...acc, n]); }",
        ),
        (
            "a doubled array under a halving measure",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 1) return 0; let t = 0; for (const x of xs) t += x; return t + f(n >> 1, xs.concat(xs)); }",
        ),
        (
            "a doubled array under two recursive calls",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, xs.concat(xs)) + f(n - 1, xs.concat(xs)); }",
        ),
        (
            "a doubled array under measure-many calls",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 1; let total = 0; for (let i = 0; i < n; i++) total += f(n - 1, xs.concat(xs)); for (const x of xs) total += x; return total; }",
        ),
        (
            "a doubled array through a mutual cycle",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + g(n - 1, xs.concat(xs)); }\nexport function g(n: number, xs: number[]): number { return f(n, xs); }",
        ),
        (
            "a rest parameter spread twice",
            "f",
            "export function f(n: number, ...xs: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, ...xs, ...xs); }",
        ),
    ];
    let expected: Vec<(String, bool, bool)> = rows
        .iter()
        .map(|(label, _, _)| (label.to_string(), false, true))
        .collect();
    let found: Vec<(String, bool, bool)> = recurrence_results_of(&rows)
        .into_iter()
        .map(|(label, _, complete, recurrence)| (label, complete, recurrence))
        .collect();

    assert_eq!(found, expected);
}

#[test]
fn an_argument_that_cannot_grow_keeps_the_solved_depth() {
    let rows = [
        (
            "an array passed through",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, xs); }",
            "O(max(n, xs, (n * max(1, n, xs))))",
        ),
        (
            "two arrays swapped between parameters",
            "f",
            "export function f(n: number, xs: number[], ys: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, ys, xs); }",
            "O(max(n, xs, ys, (n * max(1, n, xs, ys))))",
        ),
        (
            "a constant number",
            "f",
            "export function f(n: number, xs: number[], k: number): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; for (let i = 0; i < k; i++) t += i; return t + f(n - 1, xs, 3); }",
            "O(max(n, xs, k, (n * max(1, n, xs, k))))",
        ),
        (
            "a constant string",
            "f",
            "export function f(n: number, s: string): number { if (n <= 0) return 0; let t = 0; for (const c of s) t += c.length; return t + f(n - 1, \"ab\"); }",
            "O(max(n, s, (n * max(1, n, s))))",
        ),
        (
            "an omitted optional argument",
            "f",
            "export function f(n: number, xs: number[], k?: number): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, xs); }",
            "O(max(n, xs, k, (n * max(1, n, xs, k))))",
        ),
        (
            "a constant alias of a parameter",
            "f",
            "export function f(n: number, xs: number[]): number { if (n <= 0) return 0; const same = xs; let t = 0; for (const x of same) t += x; return t + f(n - 1, same); }",
            "O(max(n, xs, (n * max(1, n, xs))))",
        ),
        (
            "a rest parameter spread through",
            "f",
            "export function f(n: number, ...xs: number[]): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += x; return t + f(n - 1, ...xs); }",
            "O(max(n, (n * max(1, n))))",
        ),
        (
            "a module function passed as its callback",
            "run",
            "function inc(x: number): number { return x + 1; }\nfunction f(n: number, xs: number[], g: (x: number) => number): number { if (n <= 0) return 0; let t = 0; for (const x of xs) t += g(x); return t + f(n - 1, xs, inc); }\nexport function run(n: number, xs: number[]): number { return f(n, xs, inc); }",
            "O(max(n, xs, (n * max(1, n, xs))))",
        ),
        (
            "a second number decremented under its guard",
            "f",
            "export function f(n: number, m: number): number { if (n <= 0) return 0; if (m <= 0) return 0; let t = 0; for (let i = 0; i < m; i++) t += i; return t + f(n - 1, m - 1); }",
            "O(max(n, m, (n * max(1, n, m))))",
        ),
        (
            "a second number halved",
            "f",
            "export function f(n: number, m: number): number { if (n <= 0) return 0; let t = 0; for (let i = 0; i < m; i++) t += i; return t + f(n - 1, m >> 1); }",
            "O(max(n, m, (n * max(1, n, m))))",
        ),
    ];
    let sources: Vec<RecurrenceRow<'_>> = rows
        .iter()
        .map(|(label, name, source, _)| (*label, *name, *source))
        .collect();
    let expected: Vec<(String, String, bool)> = rows
        .iter()
        .map(|(label, _, _, cost)| (label.to_string(), cost.to_string(), true))
        .collect();
    let found: Vec<(String, String, bool)> = recurrence_results_of(&sources)
        .into_iter()
        .map(|(label, cost, complete, _)| (label, cost, complete))
        .collect();

    assert_eq!(found, expected);
}

const CYCLE_WITH_HIDDEN_WORK: &str = "export function cycleStart(n: number, xs: number[]): number {\n\tif (n <= 0) return 0;\n\tlet t = 0;\n\tfor (const x of xs) for (const y of xs) t += x + y;\n\treturn t + new CycleHolder().step(n - 1, xs);\n}\nexport class CycleHolder {\n\tstep(n: number, xs: number[]): number {\n\t\tif (n <= 0) return 0;\n\t\treturn cycleContinue(n - 1, xs) + xs.length;\n\t}\n}\nexport function cycleContinue(n: number, xs: number[]): number {\n\tif (n <= 0) return 0;\n\treturn cycleStart(n - 1, xs);\n}\n";

const CLEAN_CYCLE: &str = "export function cycleStart(n: number, xs: number[]): number {\n\tif (n <= 0) return 0;\n\tlet t = 0;\n\tfor (const x of xs) for (const y of xs) t += x + y;\n\treturn t + step(n - 1, xs);\n}\nexport function step(n: number, xs: number[]): number {\n\tif (n <= 0) return 0;\n\treturn cycleContinue(n - 1, xs) + xs.length;\n}\nexport function cycleContinue(n: number, xs: number[]): number {\n\tif (n <= 0) return 0;\n\treturn cycleStart(n - 1, xs);\n}\n";

fn member_of<'a>(
    project: &olint::project::Project<'a>,
    file: FileId,
    name: &str,
) -> olint::declarations::FunctionNode<'a> {
    support::first_node_of(project, file, |kind| match kind {
        oxc_ast::AstKind::Function(function)
            if function.id.as_ref().is_some_and(|id| id.name == name) =>
        {
            Some(olint::declarations::FunctionNode::Function(function))
        }
        oxc_ast::AstKind::MethodDefinition(method)
            if method.key.static_name().as_deref() == Some(name) =>
        {
            Some(olint::declarations::FunctionNode::Function(&method.value))
        }
        _ => None,
    })
}

fn orders_of<'m>(members: &[&'m str]) -> Vec<Vec<&'m str>> {
    if members.len() <= 1 {
        return vec![members.to_vec()];
    }

    let mut orders = Vec::new();

    for (index, first) in members.iter().enumerate() {
        let mut rest = members.to_vec();

        rest.remove(index);

        for mut order in orders_of(&rest) {
            order.insert(0, first);
            orders.push(order);
        }
    }

    orders
}

fn component_results_of(source: &str, members: &[&str]) -> Vec<(String, String, bool, bool)> {
    let mut found = Vec::new();

    for order in orders_of(members) {
        let label = order.join(" then ");

        run_with_source(source, |analysis, file| {
            for name in &order {
                let function = member_of(analysis.project, file, name);
                let part = analysis
                    .summarize(file, function)
                    .total(&mut analysis.unknowns, &mut analysis.traces);
                let reasons = unknown_reasons(analysis, part.unknowns);

                found.push((
                    label.clone(),
                    name.to_string(),
                    part.is_complete(),
                    reasons.contains(&UnknownReason::Target),
                ));
            }
        });
    }

    found
}

#[test]
fn every_member_of_a_solved_component_is_partial_when_any_member_is() {
    let members = ["cycleStart", "step", "cycleContinue"];
    let found = component_results_of(CYCLE_WITH_HIDDEN_WORK, &members);
    let expected: Vec<(String, String, bool, bool)> = found
        .iter()
        .map(|(order, name, _, _)| (order.clone(), name.clone(), false, true))
        .collect();

    assert_eq!(found.len(), 18);
    assert_eq!(found, expected);
}

#[test]
fn every_member_of_a_clean_solved_component_stays_complete() {
    let members = ["cycleStart", "step", "cycleContinue"];
    let found = component_results_of(CLEAN_CYCLE, &members);
    let expected: Vec<(String, String, bool, bool)> = found
        .iter()
        .map(|(order, name, _, _)| (order.clone(), name.clone(), true, false))
        .collect();

    assert_eq!(found.len(), 18);
    assert_eq!(found, expected);
}

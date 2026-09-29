use olint::analysis::Analysis;
use olint::budgets::{Budget, Direction, Potential, Spend, StepMagnitude};
use olint::declarations::Binding;
use olint::project::{FileId, Project};
use olint::syntax::is_iteration_kind;
use oxc_ast::AstKind;

use crate::support;

use support::{
    file_of, first_node_of, function_of_name, probes_of, run_in_project, run_with_source, SYNTACTIC,
};

fn single_budget_of(analysis: &mut Analysis<'_, '_>, file: FileId) -> Budget {
    let function = function_of_name(analysis.project, file, "f");
    let context = analysis.collect_budgets(file, function);
    let budgets: Vec<&Budget> = context.budgets.values().collect();

    assert_eq!(budgets.len(), 1);

    budgets[0].clone()
}

fn spend_of_single_loop(analysis: &mut Analysis<'_, '_>, file: FileId) -> Option<Spend> {
    let project = analysis.project;
    let function = function_of_name(project, file, "f");
    let context = analysis.collect_budgets(file, function);
    let loop_kind = first_node_of(project, file, |kind| {
        matches!(kind, AstKind::WhileStatement(_)).then_some(kind)
    });

    analysis.budget_context = Some(context);

    analysis.spent_budget(file, loop_kind)
}

fn budgets_are_empty_in(source: &str, label: &str) {
    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, "f");

        assert!(
            analysis.collect_budgets(file, function).budgets.is_empty(),
            "{label}"
        );
    });
}

#[test]
fn a_counter_raised_toward_an_invariant_bound_is_a_budget() {
    run_with_source(
        "export function f(n: number) {\n\tlet i = 0;\n\twhile (i < n) {\n\t\ti += 1;\n\t}\n}",
        |analysis, file| {
            let budget = single_budget_of(analysis, file);

            assert_eq!(budget.direction, Direction::Up);
            assert_eq!(budget.text, "i < n");
            assert_eq!(budget.scope, None);
            assert_eq!(budget.potential, Potential::Enveloped);
        },
    );
}

#[test]
fn a_counter_moved_both_ways_is_no_budget() {
    run_with_source(
        "export function f(n: number) {\n\tlet i = 0;\n\twhile (i < n) {\n\t\ti += 1;\n\t\tif (i > 3) i--;\n\t}\n}",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "f");

            assert!(analysis.collect_budgets(file, function).budgets.is_empty());
        },
    );
}

#[test]
fn a_for_counter_scopes_its_budget_to_the_for() {
    run_with_source(
        "export function f(n: number) {\n\tfor (let i = 0; i < n; i++) {}\n}",
        |analysis, file| {
            let for_node = first_node_of(analysis.project, file, |kind| match kind {
                AstKind::ForStatement(statement) => Some(statement.node_id()),
                _ => None,
            });

            assert_eq!(single_budget_of(analysis, file).scope, Some(for_node));
        },
    );
}

#[test]
fn a_stable_step_spends_a_share_and_sizes_its_slices() {
    run_with_source(
        "export function f(n: number, g: number, buf: Uint8Array) {\n\tconst p = 4;\n\tlet i = 0;\n\twhile (i < n) {\n\t\tprobe(buf.subarray(0, g));\n\t\tprobe(p + g);\n\t\tprobe(buf.subarray(0, n));\n\t\ti += g;\n\t}\n}",
        |analysis, file| {
            let project = analysis.project;
            let spend = spend_of_single_loop(analysis, file).expect("the step spends the budget");

            assert_eq!(spend.text, "i < n, by g");

            let share = spend.share.expect("a const step is a share");

            assert!(matches!(share, Binding::Symbol { .. }));

            analysis.share_bindings.push(share);

            let sized: Vec<bool> = probes_of(project, file)
                .into_iter()
                .map(|probe| analysis.is_share_sized(file, probe))
                .collect();

            assert_eq!(sized, vec![true, true, false]);
        },
    );
}

#[test]
fn a_bound_written_through_its_namespace_is_not_invariant() {
    let files = [
        ("tsconfig.json", "{}"),
        ("lib.ts", "export let limit = 10;"),
        (
            "index.ts",
            "import * as lib from \"./lib\";
import { limit } from \"./lib\";
export function f(xs: number[]) {
	let i = 0;
	while (i < limit) {
		i++;
	}
	lib.limit += xs.length;
}
export namespace Space {
	export let size = 10;
	export function g(xs: number[]) {
		let j = 0;
		while (j < size) {
			j++;
		}
		Space.size += xs.length;
	}
}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(project, SYNTACTIC);

        for name in ["f", "g"] {
            let function = function_of_name(project, file, name);

            assert!(
                analysis.collect_budgets(file, function).budgets.is_empty(),
                "{name} writes its bound"
            );
        }
    });
}

#[test]
fn every_operand_and_call_argument_contributes_to_bound_invariance() {
    for bound in ["n - k", "Math.min(n, k)"] {
        let source = format!(
            "export function f(n: number, k: number) {{ let i = 0; while (i < {bound}) {{ i++; k--; }} }}"
        );

        run_with_source(&source, |analysis, file| {
            let function = function_of_name(analysis.project, file, "f");

            assert!(
                analysis.collect_budgets(file, function).budgets.is_empty(),
                "{bound}"
            );
        });
    }
}

#[test]
fn destructuring_writes_every_target_and_preserves_default_reads() {
    for assignment in [
        "[other, n] = pair",
        "[, n] = pair",
        "({ n } = object)",
        "[...n] = pair",
    ] {
        let source = format!(
            "export function f(n: any, pair: any, object: any) {{ let i = 0, other; while (i < n) {{ i++; }} {assignment}; }}"
        );

        run_with_source(&source, |analysis, file| {
            let function = function_of_name(analysis.project, file, "f");

            assert!(
                analysis.collect_budgets(file, function).budgets.is_empty(),
                "{assignment}"
            );
        });
    }

    run_with_source(
        "export function f(n: number, object: any) { let i = 0, other; while (i < n) { i++; } ({ other = n } = object); }",
        |analysis, file| {
            assert_eq!(single_budget_of(analysis, file).text, "i < n");
        },
    );
}

#[test]
fn a_constant_endpoint_quantifies_the_initial_potential() {
    run_with_source(
        "export function f() { let i = 2; while (i < 10) { i += 1; } }",
        |analysis, file| {
            assert_eq!(
                single_budget_of(analysis, file).potential,
                Potential::Constant(8.0)
            );
        },
    );
}

#[test]
fn a_counter_without_a_proven_initial_value_is_no_budget() {
    for (source, label) in [
        (
            "export function f(i: number, n: number) { while (i < n) { i++; } }",
            "parameter counter",
        ),
        (
            "export function f(n: number, start: number) { let i = start; while (i < n) { i++; } }",
            "opaque initializer",
        ),
        (
            "export function f(n: number) { let i; i = 0; while (i < n) { i++; } }",
            "absent initializer",
        ),
    ] {
        budgets_are_empty_in(source, label);
    }
}

#[test]
fn a_counter_reset_by_an_iteration_head_is_no_budget() {
    for head in ["for (i of xs)", "for (i in xs)", "for ([i] of pairs)"] {
        let source = format!(
            "export function f(n: number, xs: number[], pairs: number[][]) {{ let i = 0; while (i < n) {{ i++; }} {head} {{ }} }}"
        );

        budgets_are_empty_in(&source, head);
    }
}

#[test]
fn a_write_that_makes_no_proven_advance_is_no_budget() {
    for step in ["i += 0", "i -= 0", "i += -1", "i += 1 - 1"] {
        let source =
            format!("export function f(n: number) {{ let i = 0; while (i < n) {{ {step}; }} }}");

        budgets_are_empty_in(&source, step);
    }

    run_with_source(
        "export function f(n: number) { let i = 0; while (i < n) { i -= 1 - 2; } }",
        |analysis, file| {
            assert_eq!(single_budget_of(analysis, file).direction, Direction::Up);
        },
    );
}

#[test]
fn a_constant_step_cancels_the_budget_it_spends() {
    for step in ["i++", "i += 2", "i += 1 / 4"] {
        let source = format!(
            "export function f(n: number) {{ let i = 0; while (i < n) {{ {step}; }} return i; }}"
        );

        run_with_source(&source, |analysis, file| {
            let spend = spend_of_single_loop(analysis, file).expect("the step spends the budget");

            assert_eq!(spend.magnitude, StepMagnitude::Constant, "{step}");
            assert!(spend.cancels(), "{step}");
            assert_eq!(spend.share, None, "{step}");
        });
    }
}

#[test]
fn a_step_of_unproven_magnitude_never_cancels_the_budget() {
    let stable = "export function f(n: number, g: number) { let i = 0; while (i < n) { i += g; } return i; }";
    let written = "export function f(n: number, m: number) { let i = 0, k = 1; while (i < n) { i += k; } k = m; return i + k; }";

    run_with_source(stable, |analysis, file| {
        let spend = spend_of_single_loop(analysis, file).expect("a stable step shares its budget");

        assert_eq!(spend.magnitude, StepMagnitude::Stable);
        assert!(!spend.cancels());
        assert!(spend.share.is_some());
    });

    run_with_source(written, |analysis, file| {
        assert!(
            spend_of_single_loop(analysis, file).is_none(),
            "a written step proves no progress"
        );
    });
}

type SpendShape = Option<(StepMagnitude, bool)>;

type SpendRow<'r> = (&'r str, String, StepMagnitude, bool);

fn budget_source(body: &str) -> String {
    let body = body.replace("i < n", "i < n && i >= 0");

    format!(
        "export function f(n: number, g: number) {{ if (n >= 0 && n <= 1000000000) {{ let i = 0, total = 0; {body} return total; }} return 0; }}"
    )
}

fn nested_budget_source(outer: &str) -> String {
    budget_source(&format!(
        "for (let j = 0; j < n; j++) {{ {outer} while (i < n) {{ i++; total++; }} }}"
    ))
}

fn trailing_budget_source(outer: &str) -> String {
    budget_source(&format!(
        "for (let j = 0; j < n; j++) {{ while (i < n) {{ i++; total++; }} {outer} }}"
    ))
}

fn shapes_of(
    rows: &[(&str, &str)],
    spend: &dyn Fn(&mut Analysis<'_, '_>, FileId) -> Option<Spend>,
) -> Vec<(String, SpendShape)> {
    let mut found = Vec::new();

    for (label, source) in rows {
        let mut shape = None;

        run_with_source(source, |analysis, file| {
            shape = spend(analysis, file).map(|spend| (spend.magnitude, spend.share.is_some()));
        });

        found.push(((*label).to_string(), shape));
    }

    found
}

fn labelled_sources_of<'r, T>(
    rows: &'r [T],
    of: impl Fn(&'r T) -> (&'r str, &'r str),
) -> Vec<(&'r str, &'r str)> {
    rows.iter().map(of).collect()
}

fn spend_shapes_of(rows: &[SpendRow<'_>]) -> Vec<(String, SpendShape)> {
    let sources = labelled_sources_of(rows, |(label, source, _, _)| (*label, source.as_str()));

    shapes_of(&sources, &spend_of_single_loop)
}

fn expected_shapes_of(rows: &[SpendRow<'_>]) -> Vec<(String, SpendShape)> {
    rows.iter()
        .map(|(label, _, magnitude, share)| ((*label).to_string(), Some((*magnitude, *share))))
        .collect()
}

#[test]
fn a_budget_cancels_only_where_every_write_to_its_counter_is_a_proven_constant() {
    let rows: [SpendRow<'_>; 9] = [
        (
            "a constant step before an identifier step",
            budget_source("while (i < n) { i++; i += g; total++; }"),
            StepMagnitude::Stable,
            false,
        ),
        (
            "an identifier step before a constant step",
            budget_source("while (i < n) { i += g; i++; total++; }"),
            StepMagnitude::Stable,
            true,
        ),
        (
            "a constant step refilled before the loop",
            nested_budget_source("i += g;"),
            StepMagnitude::Stable,
            false,
        ),
        (
            "a constant step refilled after the loop",
            trailing_budget_source("i += g;"),
            StepMagnitude::Stable,
            false,
        ),
        (
            "two proven constant steps",
            budget_source("while (i < n) { i++; i += 1; total++; }"),
            StepMagnitude::Constant,
            false,
        ),
        (
            "a proven fractional pair",
            budget_source("while (i < n) { i++; i += 1 / 4; total++; }"),
            StepMagnitude::Constant,
            false,
        ),
        (
            "a proven constant refill",
            nested_budget_source("i += 2;"),
            StepMagnitude::Constant,
            false,
        ),
        (
            "a lone constant step",
            budget_source("while (i < n) { i++; total++; }"),
            StepMagnitude::Constant,
            false,
        ),
        (
            "a lone identifier step",
            budget_source("while (i < n) { i += g; total++; }"),
            StepMagnitude::Stable,
            true,
        ),
    ];

    assert_eq!(spend_shapes_of(&rows), expected_shapes_of(&rows));
}

#[test]
fn a_refilled_budget_keeps_the_loop_factor_it_cannot_cancel() {
    for (outer, expected) in [("i += g;", "O(N^2)"), ("i += 2;", "O(N)")] {
        let source = nested_budget_source(outer);
        let (cost, complete, _) = support::legacy_result_of(&source, "f");
        let cost = support::projected_class_of(&cost);
        let expected = olint::cost::Cost::parse(expected).expect("a legacy cost parses");

        assert_eq!((cost, complete), (expected, true), "{outer}");
    }
}

type GuardRow<'r> = (&'r str, String, SpendShape);

fn guarded_source(body: &str) -> String {
    let body = body.replace("i < n", "i < n && i >= 0");

    format!(
        "export function f(n: number, g: number, xs: number[], flag: boolean) {{ if (n >= 0 && n <= 1000000000) {{ let i = 0, total = 0; {body} return total; }} return 0; }}"
    )
}

fn last_loop_of<'a>(project: &Project<'a>, file: FileId) -> AstKind<'a> {
    project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .filter(|node| is_iteration_kind(&node.kind()))
        .map(|node| node.kind())
        .last()
        .expect("the source declares a loop")
}

fn spend_of_last_loop(analysis: &mut Analysis<'_, '_>, file: FileId) -> Option<Spend> {
    let project = analysis.project;
    let function = function_of_name(project, file, "f");
    let context = analysis.collect_budgets(file, function);
    let loop_kind = last_loop_of(project, file);

    analysis.budget_context = Some(context);

    analysis.spent_budget(file, loop_kind)
}

fn guard_shapes_of(rows: &[GuardRow<'_>]) -> Vec<(String, SpendShape)> {
    let sources = labelled_sources_of(rows, |(label, source, _)| (*label, source.as_str()));

    shapes_of(&sources, &spend_of_last_loop)
}

fn expected_guard_shapes_of(rows: &[GuardRow<'_>]) -> Vec<(String, SpendShape)> {
    rows.iter()
        .map(|(label, _, shape)| ((*label).to_string(), *shape))
        .collect()
}

#[test]
fn a_budget_cancels_only_a_loop_its_own_condition_guards() {
    let cancels = Some((StepMagnitude::Constant, false));
    let rows: [GuardRow<'_>; 8] = [
        (
            "a sibling for-of the condition never reaches",
            guarded_source(
                "while (i < n) { i++; } for (let j = 0; j < n; j++) { for (const y of xs) { i++; total += y; } }",
            ),
            None,
        ),
        (
            "a for-of nested in the loop the condition guards",
            guarded_source("while (i < n) { for (const y of xs) { i++; total += y; } }"),
            None,
        ),
        (
            "a while continued by a flag",
            guarded_source(
                "while (i < n) { i++; } for (let j = 0; j < n; j++) { while (flag) { i++; total++; } }",
            ),
            None,
        ),
        (
            "a for with no test",
            guarded_source(
                "while (i < n) { i++; } for (let j = 0; j < n; j++) { for (;;) { i++; total++; } }",
            ),
            None,
        ),
        (
            "a for whose update spends a counter its test ignores",
            guarded_source("while (i < n) { i++; } for (let j = 0; j < n; i++) { total++; }"),
            None,
        ),
        (
            "the two-pointer inner while",
            guarded_source("for (let j = 0; j < n; j++) { while (i < n) { i++; total++; } }"),
            cancels,
        ),
        (
            "a second while carrying the same guard",
            guarded_source(
                "for (let j = 0; j < n; j++) { while (i < n) { i++; total++; } while (i < n) { i++; total++; } }",
            ),
            cancels,
        ),
        (
            "a guarded while spending a share",
            guarded_source("for (let j = 0; j < n; j++) { while (i < n) { i += g; total++; } }"),
            Some((StepMagnitude::Stable, true)),
        ),
    ];

    assert_eq!(guard_shapes_of(&rows), expected_guard_shapes_of(&rows));
}

type CostRow<'r> = (&'r str, &'r str, &'r str, bool);

fn assert_guarded_costs(rows: &[CostRow<'_>]) {
    let found: Vec<(&str, String, bool)> = rows
        .iter()
        .map(|(label, body, _, _)| {
            let (cost, complete, _) = support::legacy_result_of(&guarded_source(body), "f");
            let cost = support::projected_class_of(&cost);

            (*label, cost.text(), complete)
        })
        .collect();
    let expected: Vec<(&str, String, bool)> = rows
        .iter()
        .map(|(label, _, expected, complete)| {
            let cost = olint::cost::Cost::parse(expected).expect("a legacy cost parses");

            (*label, cost.text(), *complete)
        })
        .collect();

    assert_eq!(found, expected);
}

#[test]
fn a_budget_cancels_only_where_its_charge_covers_the_potential_across_every_visit() {
    let rows = [
        (
            "a do-while under two enclosing loops",
            "for (let j = 0; j < n; j++) { for (const y of xs) { do { i++; total += y; } while (i < n); } }",
            "O(N^3)",
            true,
        ),
        (
            "a halving do-while under one enclosing loop",
            "let size = n; for (let j = 0; j < n; j++) { do { i++; total++; size = size / 2; } while (size > 1 && i < n); }",
            "O(N log N)",
            true,
        ),
        (
            "a halving while under one enclosing loop",
            "let size = n; for (let j = 0; j < n; j++) { while (size > 1 && i < n) { i++; total++; size = size / 2; } }",
            "O(N log N)",
            true,
        ),
        (
            "a do-while under one enclosing loop",
            "for (let j = 0; j < n; j++) { do { i++; total++; } while (i < n); }",
            "O(N)",
            true,
        ),
        (
            "a while under two enclosing loops",
            "for (let j = 0; j < n; j++) { for (const y of xs) { while (i < n) { i++; total += y; } } }",
            "O(N^2)",
            true,
        ),
        (
            "a do-while no loop encloses",
            "do { i++; total++; } while (i < n);",
            "O(N)",
            true,
        ),
        (
            "the two-pointer inner while",
            "for (let j = 0; j < n; j++) { while (i < n) { i++; total++; } }",
            "O(N)",
            true,
        ),
        (
            "a counter scoped to the enclosing loop",
            "for (let j = 0; j < n; j++) { let k = 0; while (k < n) { k++; total++; } }",
            "O(N^2)",
            true,
        ),
    ];

    assert_guarded_costs(&rows);
}

#[test]
fn an_unguarded_loop_keeps_the_factor_no_budget_cancels() {
    let rows = [
        (
            "a sibling for-of the condition never reaches",
            "while (i < n) { i++; } for (let j = 0; j < n; j++) { for (const y of xs) { i++; total += y; } }",
            "O(N^2)",
            true,
        ),
        (
            "a for-of nested in the loop the condition guards",
            "while (i < n) { for (const y of xs) { i++; total += y; } }",
            "O(N)",
            false,
        ),
        (
            "a while continued by a flag",
            "while (i < n) { i++; } for (let j = 0; j < n; j++) { while (flag) { i++; total++; } }",
            "O(N)",
            false,
        ),
        (
            "the two-pointer inner while",
            "for (let j = 0; j < n; j++) { while (i < n) { i++; total++; } }",
            "O(N)",
            true,
        ),
        (
            "a second while carrying the same guard",
            "for (let j = 0; j < n; j++) { while (i < n) { i++; total++; } while (i < n) { i++; total++; } }",
            "O(N)",
            true,
        ),
    ];

    assert_guarded_costs(&rows);
}

type VisitRow<'r> = (&'r str, &'r str, &'r str, &'r str, bool);

fn assert_live_visits(rows: &[VisitRow<'_>]) {
    let found: Vec<(&str, String, bool, bool)> = rows
        .iter()
        .map(|(label, parameters, body, _, _)| {
            let (cost, complete, reasons) = support::legacy_result_of(
                &format!(
                    "export function f({parameters}) {{ let total = 0; {body} return total; }}"
                ),
                "f",
            );

            (
                *label,
                support::projected_class_of(&cost).text(),
                complete,
                reasons.contains(&olint::unknowns::UnknownReason::Bound),
            )
        })
        .collect();
    let expected: Vec<(&str, String, bool, bool)> = rows
        .iter()
        .map(|(label, _, _, expected, complete)| {
            let cost = olint::cost::Cost::parse(expected).expect("a legacy cost parses");

            (
                *label,
                support::projected_class_of(&cost).text(),
                *complete,
                !*complete,
            )
        })
        .collect();

    assert_eq!(found, expected);
}

#[test]
fn a_size_guarded_addition_budgets_live_collection_visits() {
    let rows = [
        (
            "a singleton set grown to xs squared",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < xs.length * xs.length) values.add(value + 1); }",
            "O(N^3)",
            true,
        ),
        (
            "a singleton map grown to xs squared",
            "xs: number[]",
            "const table = new Map([[0, 0]]); for (const [key] of table) { if (table.size < xs.length * xs.length) table.set(key + 1, 0); }",
            "O(N^3)",
            true,
        ),
        (
            "a budgeted traversal multiplying its body",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < xs.length * xs.length) values.add(value + 1); for (const x of xs) total += x + value; }",
            "O(N^3)",
            true,
        ),
        (
            "a guard admitting two additions",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (xs.length > values.size) { values.add(value + 1); values.add(value + 2); } }",
            "O(N^2)",
            true,
        ),
        (
            "a constant guard keeping the initial size",
            "s: Set<number>",
            "for (const value of s) { if (s.size < 10) s.add(value + 1); total += value; }",
            "O(N * max(1, N))",
            true,
        ),
    ];

    assert_live_visits(&rows);
}

#[test]
fn deletions_leave_live_collection_visits_unknown_beside_stable_traversals() {
    let rows = [
        (
            "deleting each visited entry leaves the entry list untracked",
            "s: Set<number>",
            "for (const value of s) { s.delete(value); total += value; }",
            "O(N)",
            false,
        ),
        (
            "a stable traversal adding to another fresh collection",
            "xs: number[]",
            "const values = new Set(xs); const seen = new Set<number>(); values.forEach(() => {}); for (const value of values) { seen.add(value); total += value; }",
            "O(N^2)",
            true,
        ),
        (
            "a stable traversal",
            "s: Set<number>",
            "for (const value of s) { total += value; }",
            "O(N)",
            true,
        ),
    ];

    assert_live_visits(&rows);
}

#[test]
fn growth_no_size_guard_bounds_leaves_live_visits_unknown() {
    let rows = [
        (
            "a deletion beside a size-guarded addition",
            "xs: number[], s: Set<number>",
            "for (const value of s) { if (s.size < xs.length) { s.delete(value); s.add(value); } }",
            "O(N)",
            false,
        ),
        (
            "an unguarded addition",
            "",
            "const values = new Set([0]); for (const value of values) { values.add(value + 1); }",
            "O(N)",
            false,
        ),
        (
            "an addition in the alternate branch",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < xs.length) {} else values.add(value + 1); }",
            "O(N)",
            false,
        ),
        (
            "a loop between the guard and the addition",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < xs.length) for (let i = 0; i < 2; i++) values.add(value + i); }",
            "O(N)",
            false,
        ),
        (
            "an endpoint the traversal raises",
            "xs: number[]",
            "const values = new Set([0]); let limit = xs.length; for (const value of values) { if (values.size < limit) { values.add(value + 1); limit++; } }",
            "O(N)",
            false,
        ),
        (
            "an endpoint reading the grown collection",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < values.size + xs.length) values.add(value + 1); }",
            "O(N)",
            false,
        ),
        (
            "a deletion through a possible alias beside a guarded addition",
            "xs: number[], s: Set<number>, t: Set<number>",
            "for (const value of s) { if (s.size < xs.length) s.add(value + 1); t.delete(value); }",
            "O(N)",
            false,
        ),
        (
            "an endpoint the traversal lengthens",
            "",
            "const values = new Set([0]); const limits = [0]; for (const value of values) { if (values.size < limits.length) { values.add(value + 1); limits.length = values.size + 1; } }",
            "O(N)",
            false,
        ),
        (
            "a guarded addition beside an unguarded one",
            "xs: number[], s: Set<number>",
            "for (const value of s) { if (s.size < xs.length) s.add(value + 1); s.add(value + 2); }",
            "O(N)",
            false,
        ),
        (
            "a guarded addition beside one whose endpoint the traversal lengthens",
            "xs: number[], s: Set<number>",
            "const limits = [0]; for (const value of s) { if (s.size < xs.length) s.add(value + 1); if (s.size < limits.length) { s.add(value + 2); limits.length = s.size + 1; } }",
            "O(N)",
            false,
        ),
        (
            "a guarded addition beside one whose endpoint reads this",
            "this: { items: number[] }, xs: number[], s: Set<number>",
            "for (const value of s) { if (s.size < xs.length) s.add(value + 1); if (s.size < this.items.length) s.add(value + 2); }",
            "O(N)",
            false,
        ),
        (
            "a guarded addition beside one whose endpoint has no size",
            "xs: number[], s: Set<number>, o: { count: number }",
            "for (const value of s) { if (s.size < xs.length) s.add(value + 1); if (s.size < o.count) s.add(value + 2); }",
            "O(N)",
            false,
        ),
        (
            "an endpoint evaluated through a call",
            "xs: number[]",
            "const values = new Set([0]); for (const value of values) { if (values.size < xs.concat(xs).length) values.add(value + 1); }",
            "O(N)",
            false,
        ),
        (
            "a guard bounding the size from below",
            "",
            "const values = new Set([0]); for (const value of values) { if (values.size > 0) values.add(value + 1); }",
            "O(N)",
            false,
        ),
        (
            "a guard on another collection",
            "xs: number[], t: Set<number>",
            "const values = new Set([0]); for (const value of values) { if (t.size < xs.length) values.add(value + 1); }",
            "O(N)",
            false,
        ),
    ];

    assert_live_visits(&rows);
}

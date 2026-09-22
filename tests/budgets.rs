use olint::analysis::Analysis;
use olint::budgets::{Budget, Direction, Potential, Spend, StepMagnitude};
use olint::declarations::Binding;
use olint::project::FileId;
use oxc_ast::AstKind;

mod support;

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

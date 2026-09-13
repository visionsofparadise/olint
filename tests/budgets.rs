use olint::analysis::Analysis;
use olint::budgets::{Budget, Direction};
use olint::declarations::Binding;
use olint::project::FileId;
use oxc_ast::AstKind;

mod support;

use support::{first_node_of, function_named, probes_of, with_source};

fn single_budget_of(analysis: &mut Analysis<'_, '_>, file: FileId) -> Budget {
    let function = function_named(analysis.project, file, "f");
    let context = analysis.collect_budgets(file, function);
    let budgets: Vec<&Budget> = context.budgets.values().collect();

    assert_eq!(budgets.len(), 1);

    budgets[0].clone()
}

#[test]
fn a_counter_raised_toward_an_invariant_bound_is_a_budget() {
    with_source(
        "export function f(n: number) {\n\tlet i = 0;\n\twhile (i < n) {\n\t\ti += 1;\n\t}\n}",
        |analysis, file| {
            let budget = single_budget_of(analysis, file);

            assert_eq!(budget.direction, Direction::Up);
            assert_eq!(budget.text, "i < n");
            assert_eq!(budget.scope, None);
        },
    );
}

#[test]
fn a_counter_moved_both_ways_is_no_budget() {
    with_source(
        "export function f(n: number) {\n\tlet i = 0;\n\twhile (i < n) {\n\t\ti += 1;\n\t\tif (i > 3) i--;\n\t}\n}",
        |analysis, file| {
            let function = function_named(analysis.project, file, "f");

            assert!(analysis.collect_budgets(file, function).budgets.is_empty());
        },
    );
}

#[test]
fn a_for_counter_scopes_its_budget_to_the_for() {
    with_source(
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
    with_source(
        "export function f(n: number, g: number, buf: Uint8Array) {\n\tconst p = 4;\n\tlet i = 0;\n\twhile (i < n) {\n\t\tprobe(buf.subarray(0, g));\n\t\tprobe(p + g);\n\t\tprobe(buf.subarray(0, n));\n\t\ti += g;\n\t}\n}",
        |analysis, file| {
            let project = analysis.project;
            let function = function_named(project, file, "f");
            let context = analysis.collect_budgets(file, function);
            let loop_kind = first_node_of(project, file, |kind| {
                matches!(kind, AstKind::WhileStatement(_)).then_some(kind)
            });

            analysis.budget_context = Some(context);

            let spend = analysis
                .spent_budget(file, loop_kind)
                .expect("the step spends the budget");

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

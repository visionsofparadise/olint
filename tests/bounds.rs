use std::path::Path;

use olint::analysis::Analysis;
use olint::declarations::FunctionNode;
use olint::project::Project;
use olint::syntax::is_iteration_kind;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;

mod support;

use olint::unknowns::UnknownReason;
use support::{run_with_source, SYNTACTIC};

fn loop_reasons_of(
    analysis: &mut Analysis<'_, '_>,
    file: olint::project::FileId,
) -> Vec<(String, String)> {
    let project = analysis.project;
    let nodes = project.file(file).semantic.nodes();
    let loops: Vec<_> = nodes
        .iter()
        .map(|node| node.kind())
        .filter(is_iteration_kind)
        .collect();
    let mut reasons = Vec::new();

    for kind in loops {
        let function = nodes
            .ancestors(kind.node_id())
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(FunctionNode::Function(function)),
                AstKind::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
                _ => None,
            })
            .expect("every fixture loop sits in a function");
        let reason = analysis.bound_of(file, kind).label().to_string();

        reasons.push((analysis.name_of(file, function), reason));
    }

    reasons
}

#[test]
fn every_bound_reason_fires_on_the_model_fixture() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/model");
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &root.join("tsconfig.json")).expect("fixture loads");
    let mut analysis = Analysis::new(&project, SYNTACTIC);
    let mut reasons = Vec::new();

    for name in ["src/bounds.ts", "src/branches.ts"] {
        let file = project
            .file_by_path(&root.join(name))
            .expect("fixture file loads");

        reasons.extend(loop_reasons_of(&mut analysis, file));
    }

    for (function, reason) in [
        ("constantBoundLoop", "constant bound"),
        ("constantOffsetFromStart", "constant offset from start"),
        ("geometricStepLoop", "geometric step"),
        ("whileHalvingShift", "halving"),
        ("whileHalvingMidpoint", "halving"),
        ("forOfTuple", "N"),
        ("forInClosed", "N"),
        ("forInRecord", "N"),
        ("singleIterationLoop", "single iteration"),
        ("boundedLoopStatement", "@perf bounded"),
    ] {
        assert!(
            reasons
                .iter()
                .any(|(found, why)| found == function && why == reason),
            "{function} reads {reason}: {reasons:?}"
        );
    }
}

#[test]
fn fresh_collections_keep_constant_and_closed_bounds() {
    run_with_source(
        "export function f() {
	const values = [1, 2];
	const table = { a: 1 };
	for (const value of values) void value;
	for (const key in table) void key;
}",
        |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![
                    ("f".to_string(), "constant collection".to_string()),
                    ("f".to_string(), "closed object type".to_string()),
                ]
            );
        },
    );
}

#[test]
fn a_while_counter_stepped_linearly_is_linear() {
    run_with_source(
        "export function f(n: number) {\n\twhile (n > 1) {\n\t\tn = n - 1;\n\t}\n}",
        |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![("f".to_string(), "N".to_string())]
            );
        },
    );
}

#[test]
fn unary_reads_preserve_bounds_while_updates_invalidate_them() {
    for (expression, expected) in [
        ("+n", "halving"),
        ("-n", "halving"),
        ("!n", "halving"),
        ("~n", "halving"),
        ("++n", "N"),
        ("--n", "N"),
        ("n++", "N"),
        ("n--", "N"),
    ] {
        let source = format!(
            "export function f(n: number) {{ while (n > 1) {{ consume({expression}); n >>= 1; }} }}"
        );

        run_with_source(&source, |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![("f".to_string(), expected.to_string())],
                "{expression}"
            );
        });
    }
}

fn first_reason_of(source: &str) -> String {
    let mut found = String::new();

    run_with_source(source, |analysis, file| {
        found = loop_reasons_of(analysis, file)
            .first()
            .map(|(_, reason)| reason.clone())
            .expect("the source declares a loop");
    });

    found
}

fn bound_is_unknown(source: &str, name: &str) -> bool {
    let mut found = false;

    run_with_source(source, |analysis, file| {
        let part = support::summary_of(analysis, file, name);

        found = support::unknown_reasons(analysis, part.unknowns).contains(&UnknownReason::Bound);
    });

    found
}

#[test]
fn a_constant_endpoint_proves_nothing_without_initial_distance_and_progress() {
    for (body, expected) in [
        ("let sum = 0; for (let i = n; i > 0; i--) sum++;", "N"),
        (
            "let sum = 0; for (let i = 0; i < 1; i += 1 / n) sum++;",
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 1; i += 0.25) sum++;",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i++) sum++;",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10 && n > 0; i++) sum++;",
            "constant bound",
        ),
        (
            "let sum = 0; let i = 0; while (i < 4) { i += 2; sum++; }",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i += 0) sum++;",
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i--) sum++;",
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i++) { if (n > 0) i++; sum++; }",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i++) { if (n > 0) i--; sum++; }",
            "N",
        ),
        (
            "let limit = 10; for (let i = 0; i < limit; i++) limit = n;",
            "N",
        ),
        (
            "let sum = 0; let i = 0; while (i < 10) { step: { if (n > 0) break step; i++; } sum++; }",
            "N",
        ),
        (
            "let sum = 0; let i = 0; while (i < 10) { step: { i++; if (n > 0) break step; } sum++; }",
            "constant bound",
        ),
        (
            "let sum = 0; let i = 0; while (i < 10) { step: { if (n > 0) break step; } i++; sum++; }",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; n > 0 ? i++ : 0) sum++;",
            "N",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; n > 0 && i++) sum++;",
            "N",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; n > 0 || i++) sum++;",
            "N",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; (() => i++)()) sum++;",
            "N",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; (i++)) sum++;",
            "constant bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; i++, sum--) sum++;",
            "constant bound",
        ),
    ] {
        let source = format!("export function f(n: number) {{ {body} }}");

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn a_stable_base_and_a_constant_offset_keep_a_fixed_window() {
    for (initial, test, update, expected) in [
        (
            "start",
            "i < start + 5",
            "i++",
            "constant offset from start",
        ),
        (
            "xs.length",
            "i < xs.length + 5",
            "i++",
            "constant offset from start",
        ),
        (
            "start",
            "i > start - 5",
            "i--",
            "constant offset from start",
        ),
        ("start", "i < xs.length + 5", "i++", "N"),
        ("start", "i < start + n", "i++", "N"),
        ("start", "i > start + 5", "i--", "N"),
    ] {
        let source = format!(
            "export function f(xs: number[], start: number, n: number) {{ let sum = 0; for (let i = {initial}; {test}; {update}) sum += xs[i] ?? 0; return sum; }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{test}");
    }
}

#[test]
fn geometric_progress_needs_a_positive_start_and_no_competing_write() {
    for (body, expected) in [
        (
            "for (let i = 1; i < xs.length; i *= 2) sum += i;",
            "geometric step",
        ),
        (
            "for (let i = 1; i < xs.length; i <<= 1) sum += i;",
            "geometric step",
        ),
        ("for (let i = 0; i < xs.length; i *= 2) sum += i;", "N"),
        (
            "for (let i = 1; i < xs.length; i *= 2) { i = Math.floor(i / 2) + 1; sum++; }",
            "N",
        ),
        ("for (let i = 1; i < xs.length; i *= 1.5) sum += i;", "N"),
        (
            "for (let i = 1; i < xs.length; sum > 0 ? (i *= 2) : 0) sum += i;",
            "N",
        ),
        (
            "for (let i = 1; i < xs.length; sum > 0 && (i *= 2)) sum += i;",
            "N",
        ),
        (
            "for (let i = 1; i < xs.length; (i *= 2)) sum += i;",
            "geometric step",
        ),
        (
            "for (let i = 1; i < xs.length; i *= 2, sum--) sum += i;",
            "geometric step",
        ),
    ] {
        let source =
            format!("export function f(xs: number[]) {{ let sum = 0; {body} return sum; }}");

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn contraction_must_hold_on_every_repeating_path() {
    for (body, expected) in [
        (
            "let i = xs.length; while (i > 1) { i = i >> 1; sum++; }",
            "halving",
        ),
        ("let i = xs.length; while (i > 1) { i /= 2; sum++; }", "halving"),
        (
            "let i = xs.length; while (i > 1) { if (sum > 2) i /= 2; sum++; }",
            "N",
        ),
        ("let i = xs.length; while (i > 1) { i = i - 1; sum++; }", "N"),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid; sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = Math.floor((lo + hi) / 2); lo = mid + 1; sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = lo + ((hi - lo) >> 1); hi = mid; sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (hi - hi) / 2 + lo + 1; lo = mid; sum++; }",
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; sum++; }",
            "N",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; lo = mid; sum++; }",
            "iteration bound",
        ),
        (
            "let i = xs.length; while (i > 1) { step: { if (sum > 2) break step; i /= 2; } sum++; }",
            "N",
        ),
        (
            "let i = xs.length; while (i > 1) { step: { i /= 2; if (sum > 2) break step; } sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { step: { if (sum > 2) break step; const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid; } sum++; }",
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { step: { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid; if (sum > 2) break step; } sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo <= hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid; sum++; }",
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (hi >= lo) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid; sum++; }",
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo <= hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid - 1; sum++; }",
            "halving",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo <= hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid; else hi = mid - 1; sum++; }",
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo <= hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid - xs.length; sum++; }",
            "N",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid - xs.length; sum++; }",
            "N",
        ),
        ("let i = xs.length; while (i >= 0) { i /= 2; sum++; }", "N"),
        ("let i = xs.length; while (i > 0) { i /= 2; sum++; }", "halving"),
        ("let i = xs.length; while (i >= 1) { i /= 2; sum++; }", "halving"),
    ] {
        let source =
            format!("export function f(xs: number[]) {{ let sum = 0; {body} return sum; }}");

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn a_counter_reset_to_an_unbounded_value_leaves_the_bound_unresolved() {
    for body in [
        "for (let k = 0; k < n; k++) { k = xs[0]; }",
        "for (let i = 0; i < n; i++) { for (i of xs) void i; }",
        "for (let i = 0; i < n; i++) { for (i of [0]) void i; }",
        "for (let i = 0; i < n; i++) { let j = 0; j = i; i = xs[j]; }",
        "for (let i = 0; i < n; i = xs.length) { void i; }",
        "for (let i = 0; i < n; i++) { const reset = () => { i = 0; }; reset(); }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ {body} return n; }}");

        assert_eq!(first_reason_of(&source), "iteration bound", "{body}");
    }
}

#[test]
fn an_additive_step_of_unknown_magnitude_leaves_the_bound_unresolved() {
    for (body, expected) in [
        (
            "const gap = 1 / (n * n); for (let i = 0; i < n; i += gap) sum++;",
            "iteration bound",
        ),
        (
            "for (let i = 0; i < n; i += step) sum++;",
            "iteration bound",
        ),
        (
            "const gap = 1 / n; for (let i = 0; i < 10; i += gap) sum++;",
            "iteration bound",
        ),
        (
            "for (let i = 0; i < 10; i++) { if (n > 0) i += step; sum++; }",
            "iteration bound",
        ),
        ("for (let i = 0; i < 10; i++) sum++;", "constant bound"),
        ("for (let i = 0; i < 10; i += 3) sum++;", "constant bound"),
        (
            "const gap = 1 / 4; for (let i = 0; i < 10; i += gap) sum++;",
            "constant bound",
        ),
        ("for (let i = 0; i < n; i++) sum++;", "N"),
    ] {
        let source = format!(
            "export function f(n: number, step: number) {{ let sum = 0; {body} return sum; }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn a_body_that_can_repeat_loses_the_single_iteration_proof() {
    for (body, expected) in [
        ("for (const x of xs) { return x; }", "single iteration"),
        ("for (const x of xs) { if (n > 0) continue; break; }", "N"),
        (
            "for (const x of xs) { if (n > 0) { sum += x; continue; } return sum; }",
            "N",
        ),
        (
            "outer: for (const x of xs) { for (const y of xs) { void y; continue outer; } }",
            "N",
        ),
    ] {
        let source = format!(
            "export function f(xs: number[], n: number) {{ let sum = 0; {body} return sum; }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn a_readonly_field_a_constructor_can_reassign_is_not_a_constant_endpoint() {
    for (declared, expected) in [
        ("", "constant bound"),
        ("constructor(n: number) { this.limit = n; }", "N"),
    ] {
        let source = format!(
            "export class K {{ readonly limit: number = 4; {declared} run(): number {{ let total = 0; for (let i = 0; i < this.limit; i++) total++; return total; }} }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{declared}");
    }
}

#[test]
fn a_fresh_local_allocation_cannot_be_reached_through_a_parameter() {
    for (source, unknown) in [
        (
            "export function f(xs: number[]) { const copy = [1, 2, 3]; let total = 0; for (const value of copy) { xs[0] = value; total += value; } return total; }",
            false,
        ),
        (
            "export function f(xs: number[]) { const copy = [1, 2, 3]; let total = 0; for (const value of copy) { copy[0] = value; total += value; } return total; }",
            true,
        ),
        (
            "export function f(xs: number[], keep: (values: number[]) => void) { const copy = [1, 2, 3]; let total = 0; keep(copy); for (const value of copy) { xs[0] = value; total += value; } return total; }",
            true,
        ),
    ] {
        assert_eq!(bound_is_unknown(source, "f"), unknown, "{source}");
    }
}

fn legacy_cost_of(source: &str, name: &str) -> (olint::cost::Cost, bool) {
    let (cost, complete, _) = support::legacy_result_of(source, name);

    (cost, complete)
}

fn cost(text: &str) -> olint::cost::Cost {
    olint::cost::Cost::parse(text).expect("a legacy cost parses")
}

fn nested_budget_source(step: &str) -> String {
    format!(
        "export function f(n: number) {{ const step = {step}; let i = 0, total = 0; for (let j = 0; j < n; j++) {{ while (i < n) {{ i += step; total++; }} }} return total; }}"
    )
}

#[test]
fn a_budget_spent_in_steps_of_unproven_magnitude_keeps_its_nested_work() {
    assert_eq!(
        legacy_cost_of(&nested_budget_source("1 / n"), "f"),
        (cost("O(N)"), false)
    );
    assert_eq!(
        legacy_cost_of(&nested_budget_source("1"), "f"),
        (cost("O(N)"), true)
    );
    assert_eq!(
        legacy_cost_of(&nested_budget_source("1 / 4"), "f"),
        (cost("O(N)"), true)
    );
}

#[test]
fn a_unit_step_two_pointer_budget_still_collapses() {
    let source = "export function f(xs: number[]) { let i = 0, total = 0; for (let j = 0; j < xs.length; j++) { while (i < xs.length) { i++; total++; } } return total; }";

    assert_eq!(legacy_cost_of(source, "f"), (cost("O(N)"), true));
}

#[test]
fn a_replenished_budget_separates_from_an_unrelated_counter() {
    let unrelated = "export function f(n: number, m: number) { let i = 0, k = 0, total = 0; const bump = () => { k = 0; }; for (let j = 0; j < n; j++) { bump(); while (i < n) { i++; total++; } } while (k < m) { k++; total++; } return total; }";
    let escaped = "export function f(n: number, use: (fn: () => void) => void) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n; j++) { use(reset); while (i < n) { i++; total++; } } return total; }";

    assert_eq!(legacy_cost_of(unrelated, "f"), (cost("O(N)"), true));
    assert_eq!(legacy_cost_of(escaped, "f"), (cost("O(N^2)"), false));
}

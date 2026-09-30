use std::path::Path;

use olint::analysis::Analysis;
use olint::declarations::FunctionNode;
use olint::project::Project;
use olint::syntax::is_iteration_kind;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;

use crate::support;

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

        analysis.enter_function_inputs(file, function);

        let reason = analysis.bound_of(file, kind).label().to_string();

        reasons.push((analysis.name_of(file, function), reason));
    }

    reasons
}

#[test]
fn the_model_fixture_distinguishes_proven_and_unresolved_bounds() {
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
        ("constantOffsetFromStart", "iteration bound"),
        ("geometricStepLoop", "iteration bound"),
        ("whileHalvingShift", "iteration bound"),
        ("whileHalvingMidpoint", "iteration bound"),
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
        "export function f(n: number) {\n\twhile (n > 1 && n <= 1000000000) {\n\t\tn = n - 1;\n\t}\n}",
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
        ("++n", "iteration bound"),
        ("--n", "iteration bound"),
        ("n++", "iteration bound"),
        ("n--", "iteration bound"),
    ] {
        let source = format!(
            "export function f(n: number) {{ while (n > 1 && n <= 1000000000) {{ consume({expression}); n >>= 1; }} }}"
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
        ("let sum = 0; for (let i = n; i > 0 && n >= 0 && n <= 1000000000; i--) sum++;", "N"),
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
            "iteration bound",
        ),
        (
            "let limit = 10; for (let i = 0; i < limit; i++) limit = n;",
            "iteration bound",
        ),
        (
            "let sum = 0; let i = 0; while (i < 10) { step: { if (n > 0) break step; i++; } sum++; }",
            "iteration bound",
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
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; n > 0 && i++) sum++;",
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; n > 0 || i++) sum++;",
            "iteration bound",
        ),
        (
            "let sum = 0; for (let i = 0; i < 10; (() => i++)()) sum++;",
            "iteration bound",
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
        (
            "start",
            "i > start + 5",
            "i--",
            "constant offset from start",
        ),
    ] {
        let initial = initial.replace("xs.length", "size");
        let test = test.replace("xs.length", "size");
        let source = format!(
            "export function f(xs: number[], start: number, n: number) {{ const size = xs.length; if (start >= 0 && start <= 1000000000 && n >= 0 && n <= 1000000000 && size >= 0 && size <= 1000000000) {{ let sum = 0; for (let i = {initial}; {test}; {update}) sum += xs[i] ?? 0; return sum; }} return 0; }}"
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
            "iteration bound",
        ),
        (
            "for (let i = 0; i < xs.length; i *= 2) sum += i;",
            "iteration bound",
        ),
        (
            "for (let i = 1; i < xs.length; i *= 2) { i = Math.floor(i / 2) + 1; sum++; }",
            "iteration bound",
        ),
        (
            "for (let i = 1; i < xs.length; i *= 1.5) sum += i;",
            "geometric step",
        ),
        (
            "for (let i = 1; i < xs.length; sum > 0 ? (i *= 2) : 0) sum += i;",
            "iteration bound",
        ),
        (
            "for (let i = 1; i < xs.length; sum > 0 && (i *= 2)) sum += i;",
            "iteration bound",
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
            format!("export function f(xs: number[]) {{ if (xs.length >= 0 && xs.length <= 1000000000) {{ let sum = 0; {body} return sum; }} return 0; }}");

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
            "iteration bound",
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
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; lo = mid; sum++; }",
            "iteration bound",
        ),
        (
            "let i = xs.length; while (i > 1) { step: { if (sum > 2) break step; i /= 2; } sum++; }",
            "iteration bound",
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
            "iteration bound",
        ),
        (
            "let lo = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (xs[mid] < 0) lo = mid + 1; else hi = mid - xs.length; sum++; }",
            "iteration bound",
        ),
        ("let i = xs.length; while (i >= 0) { i /= 2; sum++; }", "iteration bound"),
        ("let i = xs.length; while (i > 0) { i /= 2; sum++; }", "halving"),
        ("let i = xs.length; while (i >= 1) { i /= 2; sum++; }", "halving"),
    ] {
        let body = body.replace("xs.length", "size");
        let source =
            format!("export function f(xs: number[]) {{ const size = xs.length; if (size >= 0 && size <= 1000000000) {{ let sum = 0; {body} return sum; }} return 0; }}");

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
            "export function f(n: number, step: number) {{ if (n >= 0 && n <= 1000000000) {{ let sum = 0; {body} return sum; }} return 0; }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{body}");
    }
}

#[test]
fn a_counter_whose_unconditional_writes_cancel_leaves_the_bound_unresolved() {
    for (body, expected) in [
        (
            "for (let i = 0; i < 10; i++) { i--; sum++; }",
            "iteration bound",
        ),
        (
            "let i = 0; while (i < 10) { i = i + 1; i = i - 1; sum++; }",
            "iteration bound",
        ),
        (
            "for (let i = 0; i < n; i++) { i -= 2; sum++; }",
            "iteration bound",
        ),
        (
            "let i = 0; while (i < 10) { i -= 1; for (const x of xs) { i += 1; sum++; } }",
            "iteration bound",
        ),
        (
            "for (let i = 0; i < 10; i++) { i += 2; i--; sum++; }",
            "constant bound",
        ),
        ("for (let i = 0; i < 10; i++) sum++;", "constant bound"),
    ] {
        let source = format!(
            "export function f(n: number, xs: number[]) {{ let sum = 0; {body} return sum; }}"
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
        (
            "constructor(n: number) { this.limit = n; }",
            "iteration bound",
        ),
    ] {
        let source = format!(
            "export class K {{ readonly limit: number = 4; {declared} run(): number {{ let total = 0; for (let i = 0; i < this.limit; i++) total++; return total; }} }}"
        );

        assert_eq!(first_reason_of(&source), expected, "{declared}");
    }
}

// G22: a declared class type is structural (§2.5), so `f({ n: m })` and a subclass that
// redeclares `n` both stand behind a receiver typed `A`; the field folds only through a receiver
// that holds exactly an `A`, or when the field is private. `this` in an exported class still
// folds, the part of G22 left open while tests/integration/constants.rs pins it.
#[test]
fn a_readonly_field_folds_only_through_an_exact_receiver() {
    for (source, expected) in [
        (
            "class A { readonly n: number = 1; } export function f(a: A) { for (let i = 0; i < a.n; i++) {} }",
            "iteration bound",
        ),
        (
            "class A { readonly n: number = 1; run() { for (let i = 0; i < this.n; i++) {} } } class B extends A { readonly n: number; constructor(n: number) { super(); this.n = n; } } export function f(n: number) { new B(n).run(); }",
            "iteration bound",
        ),
        (
            "class A { readonly n: number = 1; run() { for (let i = 0; i < this.n; i++) {} } } export const make = () => A;",
            "iteration bound",
        ),
        (
            "class A { readonly n: number = 1; run() { for (let i = 0; i < this.n; i++) {} } } export function f() { new A().run(); }",
            "constant bound",
        ),
        (
            "class A { readonly n: number = 1; } export function f(a: unknown) { for (let i = 0; i < (a as A).n; i++) {} }",
            "iteration bound",
        ),
        (
            "class A { readonly n: number = 1; } export function f() { const a = new A(); for (let i = 0; i < a.n; i++) {} }",
            "constant bound",
        ),
        (
            "class A { readonly n: number = 1; } export function f() { for (let i = 0; i < new A().n; i++) {} }",
            "constant bound",
        ),
        (
            "export class A { static readonly N: number = 3; } export function f() { for (let i = 0; i < A.N; i++) {} }",
            "constant bound",
        ),
        (
            "export class A { private readonly n: number = 1; run(a: A) { for (let i = 0; i < a.n; i++) {} } }",
            "constant bound",
        ),
    ] {
        assert_eq!(first_reason_of(source), expected, "{source}");
    }
}

/// ECMA-262 §10.2.2: `new` yields an object a constructor returns in place of the instance, and
/// `super()` binds a base constructor's returned object as `this`, so a class whose constructor or
/// base constructor returns a value no longer holds its own fields.
#[test]
fn a_returning_constructor_leaves_its_instances_inexact() {
    let returning =
        "class A { readonly n: number = 1; constructor(k: number) { return { n: k }; } }";
    let base = "class Base { constructor(k: number) { return { n: k }; } }";

    for (source, expected) in [
        (
            format!("{returning} export function f(k: number) {{ const a = new A(k); for (let i = 0; i < a.n; i++) {{}} }}"),
            "iteration bound",
        ),
        (
            format!("{returning} export function f(k: number) {{ for (let i = 0; i < new A(k).n; i++) {{}} }}"),
            "iteration bound",
        ),
        (
            format!("{base} class B extends Base {{ readonly n: number = 1; }} export function f(k: number) {{ for (let i = 0; i < new B(k).n; i++) {{}} }}"),
            "iteration bound",
        ),
        (
            format!("{base} class B extends Base {{ readonly n: number = 1; constructor(k: number) {{ super(k); for (let i = 0; i < this.n; i++) {{}} }} }} export function f(k: number) {{ new B(k); }}"),
            "iteration bound",
        ),
        (
            "class A { readonly n: number = 1; constructor(k: number) { if (k) return; const g = () => { return k; }; g(); } } export function f(k: number) { for (let i = 0; i < new A(k).n; i++) {} }".to_string(),
            "constant bound",
        ),
    ] {
        assert_eq!(first_reason_of(&source), expected, "{source}");
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
        "export function f(n: number) {{ if (n >= 0 && n <= 1000000000) {{ const step = {step}; let i = 0, total = 0; for (let j = 0; j < n; j++) {{ while (i < n) {{ i += step; total++; }} }} return total; }} return 0; }}"
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
    let source = "export function f(xs: number[]) { if (xs.length >= 0 && xs.length <= 1000000000) { let i = 0, total = 0; for (let j = 0; j < xs.length; j++) { while (i < xs.length) { i++; total++; } } return total; } return 0; }";

    assert_eq!(legacy_cost_of(source, "f"), (cost("O(N)"), true));
}

#[test]
fn a_replenished_budget_separates_from_an_unrelated_counter() {
    let unrelated = "export function f(n: number, m: number) { if (n >= 0 && n <= 1000000000 && m >= 0 && m <= 1000000000) { let i = 0, k = 0, total = 0; const bump = () => { k = 0; }; for (let j = 0; j < n; j++) { bump(); while (i < n) { i++; total++; } } while (k >= 0 && k < m) { k++; total++; } return total; } return 0; }";
    let escaped = "export function f(n: number, use: (fn: () => void) => void) { if (n >= 0 && n <= 1000000000) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n; j++) { use(reset); while (i < n) { i++; total++; } } return total; } return 0; }";

    assert_eq!(legacy_cost_of(unrelated, "f"), (cost("O(N)"), true));
    assert_named_cost(escaped, "O(n)", false);
}

fn shared_window_source(inner: &str) -> String {
    let inner = inner.replace(
        "k < offset + step",
        "k < offset + step && offset >= 0 && offset <= 1000000000",
    );

    format!(
        "export function f(n: number, step: number, q: number, xs: Uint8Array) {{ if (n >= 0 && n <= 1000000000 && step >= 0 && step <= 1000000000) {{ let offset = 0, total = 0; const fine = 1 / n; while (offset < n) {{ {inner} offset += step; }} return total; }} return 0; }}"
    )
}

fn halving_share_source(inner: &str) -> String {
    let inner = inner.replace(
        "k < offset + step",
        "k < offset + step && offset >= 0 && offset <= 1000000000",
    );

    format!(
        "export function f(n: number, step: number) {{ if (n >= 0 && n <= 1000000000 && step >= 0 && step <= 1000000000) {{ let offset = 0, total = 0, size = n; while (size > 1 && offset < n) {{ {inner} offset += step; size = size / 2; }} return total; }} return 0; }}"
    )
}

fn shared_inner_reason_of(source: &str) -> String {
    let mut found = String::new();

    run_with_source(source, |analysis, file| {
        let project = analysis.project;
        let function = support::function_of_name(project, file, "f");
        let context = analysis.collect_budgets(file, function);
        let outer = support::first_node_of(project, file, |kind| {
            matches!(kind, AstKind::WhileStatement(_)).then_some(kind)
        });

        analysis.budget_context = Some(context);

        let spend = analysis
            .spent_budget(file, outer)
            .expect("the outer loop spends its budget");
        let share = spend.share.expect("a stable identifier step is a share");

        analysis.share_bindings.push(share);

        let inner = support::first_node_of(project, file, |kind| {
            matches!(kind, AstKind::ForStatement(_) | AstKind::ForOfStatement(_)).then_some(kind)
        });

        found = analysis.bound_of(file, inner).label().to_string();
    });

    found
}

const SHARE_CONSUMER_ROWS: [(&str, &str); 11] = [
    ("a unit update", "share of budget"),
    ("a unit addition", "share of budget"),
    ("a step of two", "share of budget"),
    (
        "a bare share endpoint under a unit update",
        "share of budget",
    ),
    ("a for-of over a shared slice", "share of budget"),
    ("a step of one over the envelope", "iteration bound"),
    ("a step of an unproven identifier", "iteration bound"),
    ("a proven quarter step", "N"),
    ("a bare share endpoint under a quarter step", "N"),
    ("a unit step the body can skip", "iteration bound"),
    (
        "a unit update a conditional write undoes",
        "iteration bound",
    ),
];

const SHARE_CONSUMER_BODIES: [&str; 11] = [
    "for (let k = offset; k < offset + step; k++) total++;",
    "for (let k = offset; k < offset + step; k += 1) total++;",
    "for (let k = offset; k < offset + step; k += 2) total++;",
    "for (let k = 0; k < step; k++) total++;",
    "for (const y of xs.subarray(0, step)) total += y;",
    "for (let k = offset; k < offset + step; k += fine) total++;",
    "for (let k = offset; k < offset + step; k += q) total++;",
    "for (let k = offset; k < offset + step; k += 1 / 4) total++;",
    "for (let k = 0; k < step; k += 1 / 4) total++;",
    "for (let k = offset; k < offset + step; ) { if (total > 0) k++; total++; }",
    "for (let k = offset; k < offset + step; k++) { if (total > 0) k--; total++; }",
];

#[test]
fn a_share_collapses_only_where_the_consuming_loop_advances_a_whole_unit() {
    let found: Vec<(&str, String)> = SHARE_CONSUMER_ROWS
        .iter()
        .zip(SHARE_CONSUMER_BODIES.iter())
        .map(|((label, _), body)| (*label, shared_inner_reason_of(&shared_window_source(body))))
        .collect();
    let expected: Vec<(&str, String)> = SHARE_CONSUMER_ROWS
        .iter()
        .map(|(label, reason)| (*label, (*reason).to_string()))
        .collect();

    assert_eq!(found, expected);
}

type LegacyRow<'r> = (&'r str, String, &'r str, bool);

fn assert_named_cost(source: &str, expected: &str, complete: bool) {
    run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "f");
        let part = support::summary_of(analysis, file, "f");
        let bound = analysis
            .bind_function_cost(file, function, &cost(expected))
            .unwrap();
        let bound = olint::cost::Cost::maximum(vec![olint::cost::Cost::ONE, bound]).unwrap();

        assert_eq!(part.unknowns.is_none(), complete, "{source}");

        let actual =
            olint::cost::Cost::maximum(vec![olint::cost::Cost::ONE, part.cost.clone()]).unwrap();

        assert_eq!(
            actual.compare(&bound),
            olint::cost::CostComparison::Within,
            "{source}: {:?} versus {:?}",
            actual,
            bound
        );
        assert_eq!(
            bound.compare(&actual),
            olint::cost::CostComparison::Within,
            "{source}: {:?} versus {:?}",
            actual,
            bound
        );
    });
}

fn assert_legacy_rows(rows: &[LegacyRow<'_>]) {
    for (_, source, text, complete) in rows {
        assert_named_cost(source, text, *complete);
    }
}

fn halving_window_source(inner: &str) -> String {
    let inner = inner.replace(
        "k < offset + step",
        "k < offset + step && offset >= 0 && offset <= 1000000000",
    );

    format!(
        "export function f(n: number, step: number, xs: Uint8Array) {{ if (n >= 0 && n <= 1000000000 && step >= 0 && step <= 1000000000) {{ let offset = 0, total = 0, size = n; while (size > 1 && offset < n) {{ {inner} offset += step; size = size / 2; }} return total; }} return 0; }}"
    )
}

fn reset_halving_window_source(inner: &str) -> String {
    let inner = inner.replace(
        "k < offset + step",
        "k < offset + step && offset >= 0 && offset <= 1000000000",
    );

    format!(
        "export function f(n: number, step: number, xs: Uint8Array, ys: number[]) {{ if (n >= 0 && n <= 1000000000 && step >= 0 && step <= 1000000000) {{ let total = 0; for (const y of ys) {{ let offset = 0, size = n; while (size > 1 && offset < n) {{ {inner} offset += step; size = size / 2; }} }} return total; }} return 0; }}"
    )
}

fn reset_window_source(inner: &str) -> String {
    let inner = inner.replace(
        "k < offset + step",
        "k < offset + step && offset >= 0 && offset <= 1000000000",
    );

    format!(
        "export function f(n: number, step: number, xs: Uint8Array, ys: number[]) {{ if (n >= 0 && n <= 1000000000 && step >= 0 && step <= 1000000000) {{ let total = 0; for (const y of ys) {{ let offset = 0; while (offset < n) {{ {inner} offset += step; }} }} return total; }} return 0; }}"
    )
}

#[test]
fn a_share_collapses_only_where_the_enclosing_multiplicity_covers_the_potential() {
    let rows = [
        (
            "a bare share endpoint under a halving budget loop",
            halving_window_source("for (let k = 0; k < step; k += 1) total++;"),
            "O(step * log(n))",
            true,
        ),
        (
            "a shared slice under a halving budget loop",
            halving_window_source("for (const v of xs.subarray(0, step)) total += v;"),
            "O(log(n))",
            false,
        ),
        (
            "a counter the enclosing loop resets",
            reset_halving_window_source("for (let k = offset; k < offset + step; k += 1) total++;"),
            "O(step * ys * log(n))",
            true,
        ),
        (
            "an offset share endpoint under an unresolved budget loop",
            shared_window_source("for (let k = offset; k < offset + step; k += 1) total++;"),
            "O(1)",
            false,
        ),
        (
            "a counter the enclosing unresolved loop resets",
            reset_window_source("for (let k = offset; k < offset + step; k += 1) total++;"),
            "O(ys)",
            false,
        ),
    ];

    assert_legacy_rows(&rows);
}

#[test]
fn a_subunit_share_consumer_keeps_the_factor_its_enclosing_loop_multiplies() {
    let rows = [
        (
            "a quarter step under an unresolved budget loop",
            shared_window_source("for (let k = offset; k < offset + step; k += 1 / 4) total++;"),
            "O(1)",
            false,
        ),
        (
            "a unit step under an unresolved budget loop",
            shared_window_source("for (let k = offset; k < offset + step; k++) total++;"),
            "O(1)",
            false,
        ),
        (
            "a quarter step under a halving budget loop",
            halving_share_source("for (let k = offset; k < offset + step; k += 1 / 4) total++;"),
            "O(step * log(n))",
            true,
        ),
        (
            "a unit step under a halving budget loop",
            halving_share_source("for (let k = offset; k < offset + step; k++) total++;"),
            "O(step * log(n))",
            true,
        ),
    ];

    assert_legacy_rows(&rows);
}

#[test]
fn additive_distance_requires_finite_progress_and_retains_symbolic_sizes() {
    for source in [
        "export function f(xs:number[]){let total=0; for(let i=0;i<xs.length && xs.length>=0 && xs.length<=4294967295;i++)total++; return total}",
        "export function f(xs:number[]){const size=xs.length;let total=0; for(let i=size;i>0 && size>=0 && size<=4294967295;i--)total++; return total}",
        "export function f(xs:number[]){const copy=[...xs];let total=0; for(let i=0;i<copy.length;i++)total++; return total}",
        "export function f(xs:number[]){const k=xs.length;let total=0;for(let i=0;i<k&&k>=0&&k<=1000000000;i++)total++;return total}",
        "export function f(n:number){let total=0; for(let i=0;i<n && n>=0 && n<=1000000000;i++)total++; return total}",
        "export function f(n:number){let total=0; while(n>0 && n<=1000000000){n--;total++} return total}",
        "export function f(n:number){let total=0; for(let i=0;i<n && n>=0 && n<=1000000000;i+=0.25)total++; return total}",
    ] {
        assert_eq!(legacy_cost_of(source, "f"), (cost("O(N)"), true), "{source}");
        assert!(!bound_is_unknown(source, "f"), "{source}");
    }
}

#[test]
fn unbounded_number_inputs_and_stalled_updates_supply_no_iteration_proof() {
    for body in [
        "for(let i=0;i<n;i++)void i;",
        "while(n>0)n--;",
        "for(let i=0;i<Infinity;i++)void i;",
        "for(let i=9007199254740992;i<9007199254740994;i++)void i;",
        "for(let i=1;i<xs.length;i<<=1)void i;",
        "for(let i=0;i<n && n>=0 && n<=1000000000;i+=step)void i;",
        "for(let i=0;i<10;flag?i++:0)void i;",
        "while(true)void 0;",
        "for(;;)void 0;",
    ] {
        let source =
            format!("export function f(n:number,step:number,flag:boolean,xs:number[]){{{body}}}");

        assert!(bound_is_unknown(&source, "f"), "{source}");
    }
}

#[test]
fn unresolved_repetition_retains_proven_local_collection_work() {
    let source = "export function f(n:number,xs:number[]){for(let i=0;i<n;i++){for(const x of xs)for(const y of xs)void y;}}";

    let (known, complete) = legacy_cost_of(source, "f");

    assert_eq!(
        (support::projected_class_of(&known), complete),
        (cost("O(1)"), false)
    );
    assert!(bound_is_unknown(source, "f"));
}

#[test]
fn finite_exact_net_progress_and_geometric_ratios_keep_their_proofs() {
    for (body, expected) in [
        ("for(let i=0;i<10;i++){i+=2;i--;total++;}", "constant bound"),
        (
            "for(let i=start;i>start+5 && start>=0 && start<=1000000000;i--)total++;",
            "constant offset from start",
        ),
        (
            "for(let i=1;i<n && n>=0 && n<=1000000000;i*=1.5)total++;",
            "geometric step",
        ),
    ] {
        let source =
            format!("export function f(start:number,n:number){{let total=0;{body}return total;}}");

        assert_eq!(first_reason_of(&source), expected, "{source}");
        assert!(!bound_is_unknown(&source, "f"), "{source}");
    }
}

#[test]
fn repetition_requires_a_proven_bound_before_it_supplies_generator_yields() {
    for repetition in ["while (true)", "for (;;)", "while (condition)"] {
        let source = format!(
            "export function f(condition: boolean, xs: number[]) {{ {repetition} {{ for (const x of xs) void x; }} }}"
        );

        assert!(bound_is_unknown(&source, "f"), "{source}");

        for consumption in [
            "for (const value of values) { for (const x of xs) void x; }",
            "values.next();",
        ] {
            let source = format!(
                "function* generate(condition: boolean) {{ {repetition} yield 1; }} export function f(condition: boolean, xs: number[]) {{ const values = generate(condition); {consumption} }}"
            );

            assert!(bound_is_unknown(&source, "f"), "{source}");
        }
    }

    for repetition in ["while (false)", "for (; false;)", "do"] {
        let suffix = if repetition == "do" {
            "while (false);"
        } else {
            ""
        };
        let source = format!("export function f() {{ {repetition} {{ void 0; }} {suffix} }}");

        assert!(!bound_is_unknown(&source, "f"), "{source}");
        assert_eq!(legacy_cost_of(&source, "f").0, cost("O(1)"), "{source}");
    }

    assert!(!bound_is_unknown(
        "export function f() { for (;;) { break; } }",
        "f"
    ));
}

#[test]
fn midpoint_proofs_require_a_finite_nonwrapping_interval() {
    for endpoint in ["Infinity", "n", "4294967295"] {
        let source = format!("export function f(n:number){{let lo=0,hi={endpoint};while(lo<hi){{const mid=(lo+hi)>>1;if(n>mid)lo=mid+1;else hi=mid;}}}}");

        assert!(bound_is_unknown(&source, "f"), "{source}");
    }

    let source = "export function f(n:number){if(n>=0&&n<=1000000000){let lo=0,hi=n;while(lo<hi){const mid=(lo+hi)>>1;if(n>mid)lo=mid+1;else hi=mid;}}}";

    assert_eq!(legacy_cost_of(source, "f"), (cost("O(log N)"), true));
}

#[test]
fn guarded_independent_endpoints_remain_distinct() {
    let source = "export function f(n:number,m:number){if(n>=0&&n<=1000000000&&m>=0&&m<=1000000000){let i=0;for(let j=0;j<n;j++){while(i<m)i++;}}}";

    assert_named_cost(source, "O(n + m)", true);
}

#[test]
fn a_cancelled_loop_completes_normally_under_the_loops_that_enclose_it() {
    let source = "export function f(n: number, xs: number[], ys: number[]): number { if (n >= 0 && n <= 1000000000) { let i = 0, total = 0; for (const x of xs) { for (const y of ys) { while (i < n && i >= 0) { i++; total += y; } } } return total; } return 0; }";

    assert_named_cost(source, "O(n + xs * ys)", true);
}

#[test]
fn a_cancelled_loop_evaluates_its_test_on_every_visit() {
    let source = "function sum(xs: readonly number[]): number { let s = 0; for (const x of xs) s += x; return s; } export function f(n: number, m: number, xs: number[]): number { if (n >= 0 && n <= 1000000000 && m >= 0 && m <= 1000000000) { let i = 0, c = 0; for (let j = 0; j < n; j++) { while (sum(xs) > j && i < m && i >= 0) { i++; c++; } } return c; } return 0; }";

    assert_named_cost(source, "O(n * xs + m * xs)", true);
}

#[test]
fn a_share_charges_the_final_step_past_the_budget() {
    let source = "export function f(n: number, m: number): number { if (n >= 0 && n <= 1000000000 && m >= 1 && m <= 1000000000) { let i = 0, steps = 0, t = 0; while (i < n && i >= 0 && steps < n && steps >= 0) { const k = m; for (let j = 0; j < k; j++) t++; i += k; steps++; } return t; } return 0; }";

    assert_named_cost(source, "O(n + m)", true);
}

#[test]
fn guarded_local_assignments_preserve_the_source_quantity() {
    let source = "export function f(xs:number[],run?: (n:number)=>void){let n=1;run?.(n=xs.length);for(let i=0;i<n&&n>=0&&n<=1000000000;i++)for(const x of xs)void x;}";
    let (cost, complete, reasons) = support::legacy_result_of(source, "f");

    assert_eq!(
        support::projected_class_of(&cost),
        olint::cost::Cost::parse("O(N^2)").unwrap()
    );
    assert!(!complete);
    assert!(!reasons.contains(&UnknownReason::Bound));
    assert!(reasons.contains(&UnknownReason::Target));
}

#[test]
fn cyclic_guard_constraints_are_metered_and_keep_finite_witnesses() {
    use olint::analysis::work::Event;

    let mut previous = 0;

    for count in [16, 32, 64] {
        let guards = "n <= m && m <= n && ".repeat(count);
        let source = format!("export function f(n:number,m:number){{for(let i=0;i<n&&n>=0&&m>=0&&{guards}n<=1000000000;i++)void i;}}");

        run_with_source(&source, |analysis, file| {
            let part = support::summary_of(analysis, file, "f");

            assert!(part.is_complete());

            let work = analysis
                .scheduler_stats()
                .work
                .consumed(Event::BudgetPrepassNode);

            if previous > 0 {
                assert!(work <= 3 * previous, "{previous} then {work}");
            }

            previous = work;
        });
    }

    assert!(bound_is_unknown(
        "export function f(n:number,m:number){for(let i=0;i<n&&n>=0&&m>=0&&n<=m&&m<=n;i++)void i;}",
        "f"
    ));
}

#[test]
fn guarded_numeric_bounds_satisfy_their_exact_named_limits() {
    assert_named_cost(
        "export function f(n:number){for(let i=0;i<n&&n>=0&&n<=1000000000;i++)void i;}",
        "O(n)",
        true,
    );
    assert_named_cost("export function f(n:number){let i=0;const reset=()=>{i=0};for(let j=0;j<n&&n>=0&&n<=1000000000;j++){reset();while(i<n&&i>=0&&n>=0&&n<=1000000000)i++;}}", "O(n^2)", true);
}

#[test]
fn guarded_captured_parameters_keep_their_dimension_when_reported_alone() {
    let source = "export function outer(n:number){function inner(){for(let i=0;i<n&&n>=0&&n<=1000000000;i++)void i;}inner();}";

    run_with_source(source, |analysis, file| {
        for name in ["inner", "outer"] {
            let function = support::function_of_name(analysis.project, file, name);
            let part = support::summary_of(analysis, file, name);
            let expected = analysis
                .bind_function_cost(file, function, &cost("O(n)"))
                .unwrap();

            assert!(part.is_complete());
            assert_eq!(
                part.cost.compare(&expected),
                olint::cost::CostComparison::Within
            );
            assert_eq!(
                expected.compare(&part.cost),
                olint::cost::CostComparison::Within
            );
            assert!(!part.cost.is_one());
        }
    });
}

#[test]
fn guarded_reassigned_parameters_retain_the_assigned_source_dimension() {
    run_with_source("export function f(n:number,xs:number[]){n=xs.length;for(let i=0;i<n&&n>=0&&n<=1000000000;i++)for(const x of xs)void x;}", |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "f");
        let part = support::summary_of(analysis, file, "f");
        let old_input = analysis.bind_function_cost(file, function, &cost("O(n)")).unwrap();

        assert!(part.is_complete());
        assert_ne!(part.cost.compare(&old_input), olint::cost::CostComparison::Within);
        assert_eq!(support::projected_class_of(&part.cost), cost("O(N^2)"));
    });
}

#[test]
fn current_guards_do_not_certify_a_captured_mutable_reading() {
    for source in [
        "export function f(n:number){const k=n;n=1;for(let i=0;i<k&&n>=0&&n<=1000000000;i++)void i;}",
        "export function f(n:number){let i=n;n=1;while(i>0&&n>=0&&n<=1000000000)i--;}",
        "export function f(box:{limit:number}){const k=box.limit;box.limit=1;for(let i=0;i<k&&box.limit>=0&&box.limit<=1000000000;i++)void i;}",
        "export function f(xs:number[]){const k=xs.length;xs.length=1;for(let i=0;i<k&&xs.length>=0&&xs.length<=1000000000;i++)void i;}",
    ] {
        assert!(bound_is_unknown(source, "f"), "{source}");
    }

    let source =
        "export function f(n:number){const k=n;for(let i=0;i<k&&n>=0&&n<=1000000000;i++)void i;}";

    assert_eq!(legacy_cost_of(source, "f"), (cost("O(N)"), true));
}

#[test]
fn quantity_memo_preserves_historical_guard_provenance() {
    for endpoint in ["n+k", "k+n"] {
        let source = format!("export function f(n:number){{const k=n;n=1;for(let i=0;i<{endpoint}&&n>=0&&n<=1000000000;i++)void i;}}");

        assert!(bound_is_unknown(&source, "f"), "{source}");
    }
}

#[test]
fn replaced_rounding_intrinsics_cannot_prove_bisection_progress() {
    for operation in ["floor", "trunc"] {
        let source = format!("Math.{operation}=()=>2;export function f(){{let lo=0,hi=2;while(lo<hi){{hi=Math.{operation}((lo+hi)/2);}}}}");

        assert!(bound_is_unknown(&source, "f"), "{source}");
    }
}

#[test]
fn reassigned_budget_endpoints_keep_the_current_quantity_at_calls() {
    let source = "function cube(xs:number[]){for(const x of xs)for(const y of xs)for(const z of xs)void z;}function helper(n:number,xs:number[]){n=xs.length;let i=0;while(i<n&&n>=0&&n<=1000000000){i++;cube(xs);}}export function f(xs:number[]){helper(0,xs);}";
    let (known, complete, reasons) = support::legacy_result_of(source, "f");

    assert_eq!(support::projected_class_of(&known), cost("O(N^4)"));
    assert!(complete, "{reasons:?}");
}

#[test]
fn getter_readings_need_a_guarded_snapshot_for_a_finite_bound() {
    let source = "export function f(){const xs={get length(){return Math.random()<0.5?Infinity:1;}} as unknown as number[];for(let i=0;i<xs.length&&xs.length>=0&&xs.length<=1000000000;i++){}}";

    assert!(bound_is_unknown(source, "f"));

    // The snapshot's length is no input dimension (`input-size-envelope`), so its loop stays
    // unresolved.
    let snapshot = "export function f(){const xs={get length(){return Math.random()<0.5?Infinity:1;}} as unknown as number[];const size=xs.length;for(let i=0;i<size&&size>=0&&size<=1000000000;i++){}}";

    assert!(bound_is_unknown(snapshot, "f"));
}

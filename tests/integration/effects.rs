use olint::cost::Cost;
use olint::unknowns::UnknownReason;

use crate::support;

const DECLARED: &str =
    "declare function opaque(value: unknown): void;\ndeclare function poke(): void;\n";

fn result_of(source: &str, name: &str) -> (Cost, bool) {
    let (cost, complete, _) = reasoned_result_of(source, name);

    (cost, complete)
}

fn reasoned_result_of(source: &str, name: &str) -> (Cost, bool, bool) {
    let (cost, complete, reasons) = support::legacy_result_of(&format!("{DECLARED}{source}"), name);

    (cost, complete, reasons.contains(&UnknownReason::Bound))
}

fn cost(text: &str) -> Cost {
    Cost::parse(text).unwrap()
}

#[test]
fn direct_and_aliased_member_writes_invalidate_budget_facts() {
    for body in [
        "for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } box.limit += n; }",
        "const alias = box; const grow = () => { alias.limit += n; }; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } grow(); }",
        "const grow = () => { box.limit += n; }; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } grow(); }",
    ] {
        let source = format!("export function f(n: number) {{ const box = {{ limit: n }}; let i = 0, total = 0; {body} return total; }}");

        assert_eq!(result_of(&source, "f"), (cost("O(N^2)"), true), "{body}");
    }
}

#[test]
fn closure_resets_invalidate_budget_facts() {
    let source = "export function f(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n; j++) { reset(); while (i < n) { i++; total++; } } return total; }";

    assert_eq!(result_of(source, "f"), (cost("O(N^2)"), true));
}

#[test]
fn callback_writes_invalidate_budget_facts() {
    for call in ["[1].forEach(() => { i = 0; });", "each(() => { i = 0; });"] {
        let source = format!("function each(callback: () => void) {{ callback(); }} export function f(n: number) {{ let i = 0, total = 0; for (let j = 0; j < n; j++) {{ {call} while (i < n) {{ i++; total++; }} }} return total; }}");

        assert_eq!(result_of(&source, "f"), (cost("O(N^2)"), true), "{call}");
    }
}

#[test]
fn escaped_values_invalidate_facts_that_unknown_calls_can_reach() {
    let loop_text = "let i = 0, total = 0; for (let j = 0; j < n; j++) { poke(); while (i < box.limit) { i++; total++; } } return total;";
    let escaped = format!(
        "export function f(n: number) {{ const box = {{ limit: n }}; opaque(box); {loop_text} }}"
    );
    let isolated =
        format!("export function f(n: number) {{ const box = {{ limit: n }}; {loop_text} }}");
    let parameter =
        format!("export function f(n: number, box: {{ limit: number }}) {{ {loop_text} }}");

    assert_eq!(result_of(&escaped, "f"), (cost("O(N^2)"), false));
    assert_eq!(result_of(&isolated, "f"), (cost("O(N)"), false));
    assert_eq!(result_of(&parameter, "f"), (cost("O(N^2)"), false));

    let reset = "export function f(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; opaque(reset); for (let j = 0; j < n; j++) { poke(); while (i < n) { i++; total++; } } return total; }";

    assert_eq!(result_of(reset, "f"), (cost("O(N^2)"), false));
}

#[test]
fn unknown_calls_leave_unrelated_isolated_locals_intact() {
    for body in [
        "for (let i = 0; i < n; i++) { opaque(xs); total++; }",
        "for (let i = 0; i < n; i++) { xs.push(i); total++; }",
        "const box = { v: 1 }; let i = 0; for (let j = 0; j < n; j++) { opaque(box); while (i < n) { i++; total++; } }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ let total = 0; {body} return total; }}");

        assert_eq!(result_of(&source, "f"), (cost("O(N)"), false), "{body}");
    }

    let unrelated = "export function f(n: number) { let i = 0, other = 0, total = 0; const bump = () => { other++; }; for (let j = 0; j < n; j++) { bump(); while (i < n) { i++; total++; } } return total + other; }";

    assert_eq!(result_of(unrelated, "f"), (cost("O(N)"), true));
}

#[test]
fn unknown_calls_invalidate_reachable_loop_storage() {
    for body in [
        "for (let i = 0; i < xs.length; i++) { opaque(xs); }",
        "for (let i = 0; i < xs.length; i++) { poke(); }",
        "for (const x of xs) { opaque(x); }",
        "let i = 0; const reset = () => { i = 0; }; while (i < n) { i++; poke(); }",
        "for (let i = 0; i < n; i++) { poke(); }
function nested() { n = 0; }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ {body} }}");
        let (_, _, bound) = reasoned_result_of(&source, "f");

        assert!(bound, "{body}");
    }

    for body in [
        "for (let i = 0; i < n; i++) { opaque(xs); }",
        "for (let i = 0; i < n; i++) { poke(); }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ {body} }}");
        let (_, _, bound) = reasoned_result_of(&source, "f");

        assert!(!bound, "{body}");
    }
}

#[test]
fn cheap_cold_and_skipped_contributions_keep_their_effects() {
    for (call, expected) in [
        ("// @perf cold\nreset();", "O(N^2)"),
        ("// @perf ignore\nreset();", "O(N^2)"),
        ("if (n > 3) reset(); else heavy(n);", "O(N^2)"),
        (
            "// @perf hot
heavy(n);
reset();",
            "O(N^2)",
        ),
    ] {
        let source = format!("function heavy(n: number) {{ let s = 0; for (let k = 0; k < n; k++) s += k; return s; }} export function f(n: number) {{ let i = 0, total = 0; const reset = () => {{ i = 0; }}; for (let j = 0; j < n; j++) {{\n{call}\nwhile (i < n) {{ i++; total++; }} }} return total; }}");

        assert_eq!(result_of(&source, "f").0, cost(expected), "{call}");
    }
}

#[test]
fn storage_read_through_header_calls_is_invalidated_by_writes() {
    for source in [
        "export function f(n: number) { const box = { limit: n }; let i = 0, total = 0; const size = () => box.limit; const grow = () => { box.limit += n; }; for (let j = 0; j < n; j++) { while (i < size()) { i++; total++; } grow(); } return total; }",
        "function limitOf(b: { limit: number }) { return b.limit; } export function f(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < limitOf(box)) { i++; total++; } box.limit += n; } return total; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(N^2)"), true), "{source}");
    }
}

#[test]
fn constructions_are_distinct_only_when_constructors_return_their_instance() {
    let shared = "const shared = { limit: 0 }; class C { constructor() { return shared; } } export function f(n: number) { const a: any = new C(); const b: any = new C(); a.limit = n; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < a.limit) { i++; total++; } b.limit += n; } return total; }";
    let fresh = "class C { limit = 0; } export function f(n: number) { const a = new C(); const b = new C(); a.limit = n; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < a.limit) { i++; total++; } b.limit += n; } return total; }";

    let wrapped = "export function f(n: number) { const box = { limit: n }; const view: any = new Object(box); let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } view.limit += n; } return total; }";

    assert_eq!(result_of(shared, "f"), (cost("O(N^2)"), true));
    assert_eq!(result_of(fresh, "f").0, cost("O(N)"));
    assert_eq!(result_of(wrapped, "f").0, cost("O(N^2)"));
}

#[test]
fn destructured_counter_writes_invalidate_loop_bounds() {
    for body in [
        "for (let k = 0; k < n; k++) { [k] = [xs[0]]; t++; }",
        "for (let k = 0; k < n; k++) { ({ k } = o); t++; }",
        "let k = 0; while (k < n) { k++; [k] = [xs[0]]; t++; }",
        "let i = 0, j = 0; for (const x of xs) { while (j < n) { j++; } [i, j] = [x, i]; }",
    ] {
        let source = format!("export function f(n: number, xs: number[], o: {{ k: number }}) {{ let t = 0; {body} return t; }}");
        let (_, _, bound) = reasoned_result_of(&source, "f");

        assert!(bound, "{body}");
    }
}

#[test]
fn default_values_in_destructuring_alias_their_source() {
    let aliased = "export function f(n: number) { const box = { limit: n }; let a: any; [a = box] = []; let i = 0, total = 0; for (let j = 0; j < n; j++) { opaque(a); while (i < box.limit) { i++; total++; } } return total; }";
    let shorthand = "export function f(n: number) { const box = { limit: n }; let a: any; ({ a = box } = {} as any); let i = 0, total = 0; for (let j = 0; j < n; j++) { opaque(a); while (i < box.limit) { i++; total++; } } return total; }";

    assert_eq!(result_of(aliased, "f"), (cost("O(N^2)"), false));
    assert_eq!(result_of(shorthand, "f"), (cost("O(N^2)"), false));
}

#[test]
fn direct_eval_reaches_every_binding() {
    let source = "export function f(n: number, code: string) { let i = 0, total = 0; for (let j = 0; j < n; j++) { eval(code); while (i < n) { i++; total++; } } return total; }";
    let (_, _, bound) = reasoned_result_of(source, "f");

    assert!(bound);

    let earlier = "export function f(n: number, code: string) { let i = 0, total = 0; eval(code); for (let j = 0; j < n; j++) { poke(); while (i < n) { i++; total++; } } return total; }";

    let control = earlier.replace("eval(code);", "");

    assert!(reasoned_result_of(earlier, "f").2);
    assert!(!reasoned_result_of(&control, "f").2);
}

#[test]
fn wrapped_direct_eval_callees_share_the_enclosing_scope() {
    for call in [
        "(eval)(code)",
        "(eval as (source: string) => unknown)(code)",
        "eval!(code)",
    ] {
        let source = format!("export function f(n: number, code: string) {{ let i = 0, total = 0; {call}; for (let j = 0; j < n; j++) {{ poke(); while (i < n) {{ i++; total++; }} }} return total; }}");

        assert!(reasoned_result_of(&source, "f").2, "{call}");
    }
}

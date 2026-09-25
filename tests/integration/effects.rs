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
    let mut found = None;

    support::run_with_source(&format!("{DECLARED}{source}"), |analysis, file| {
        let part = support::summary_of(analysis, file, name);
        let reasons = support::unknown_reasons(analysis, part.unknowns);

        found = Some((
            support::projected_class_of(&part.cost),
            part.is_complete(),
            reasons.contains(&UnknownReason::Bound),
        ));
    });

    found.unwrap()
}

fn cost(text: &str) -> Cost {
    Cost::parse(text).unwrap()
}

#[test]
fn direct_and_aliased_member_writes_invalidate_budget_facts() {
    for body in [
        "for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < box.limit) { i++; total++; } box.limit += n; }",
        "const alias = box; const grow = () => { alias.limit += n; }; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < box.limit) { i++; total++; } grow(); }",
        "const grow = () => { box.limit += n; }; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < box.limit) { i++; total++; } grow(); }",
    ] {
        let source = format!("export function f(n: number) {{ const box = {{ limit: n }}; let i = 0, total = 0; {body} return total; }}");

        assert_eq!(reasoned_result_of(&source, "f"), (cost("O(N)"), false, true), "{body}");
    }
}

#[test]
fn closure_resets_invalidate_budget_facts() {
    let source = "export function f(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { reset(); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } } return total; }";

    assert_eq!(result_of(source, "f"), (cost("O(N^2)"), true));
}

#[test]
fn callback_writes_invalidate_budget_facts() {
    for call in ["[1].forEach(() => { i = 0; });", "each(() => { i = 0; });"] {
        let source = format!("function each(callback: () => void) {{ callback(); }} export function f(n: number) {{ let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) {{ {call} while (i >= 0 && i < n && n >= 0 && n <= 1000000) {{ i++; total++; }} }} return total; }}");

        assert_eq!(result_of(&source, "f"), (cost("O(N^2)"), true), "{call}");
    }
}

#[test]
fn escaped_values_invalidate_facts_that_unknown_calls_can_reach() {
    let loop_text = "let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { poke(); while (i < box.limit) { i++; total++; } } return total;";
    let escaped = format!(
        "export function f(n: number) {{ const box = {{ limit: n }}; opaque(box); {loop_text} }}"
    );
    let isolated =
        format!("export function f(n: number) {{ const box = {{ limit: n }}; {loop_text} }}");
    let parameter =
        format!("export function f(n: number, box: {{ limit: number }}) {{ {loop_text} }}");

    assert_eq!(
        reasoned_result_of(&escaped, "f"),
        (cost("O(N)"), false, true)
    );
    assert_eq!(result_of(&isolated, "f"), (cost("O(N)"), false));
    assert_eq!(
        reasoned_result_of(&parameter, "f"),
        (cost("O(N)"), false, true)
    );

    let reset = "export function f(n: number) { let i = 0, total = 0; const reset = () => { i = 0; }; opaque(reset); for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { poke(); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } } return total; }";

    assert_eq!(result_of(reset, "f"), (cost("O(N^2)"), false));
}

#[test]
fn unknown_calls_leave_unrelated_isolated_locals_intact() {
    for body in [
        "for (let i = 0; i < n && n >= 0 && n <= 1000000; i++) { opaque(xs); total++; }",
        "for (let i = 0; i < n && n >= 0 && n <= 1000000; i++) { xs.push(i); total++; }",
        "const box = { v: 1 }; let i = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { opaque(box); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ let total = 0; {body} return total; }}");

        assert_eq!(result_of(&source, "f"), (cost("O(N)"), false), "{body}");
    }

    let unrelated = "export function f(n: number) { let i = 0, other = 0, total = 0; const bump = () => { other++; }; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { bump(); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } } return total + other; }";

    assert_eq!(result_of(unrelated, "f"), (cost("O(N)"), true));
}

#[test]
fn unknown_calls_invalidate_reachable_loop_storage() {
    for body in [
        "for (let i = 0; i < xs.length; i++) { opaque(xs); }",
        "for (let i = 0; i < xs.length; i++) { poke(); }",
        "for (const x of xs) { opaque(x); }",
        "let i = 0; const reset = () => { i = 0; }; while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; poke(); }",
        "for (let i = 0; i < n && n >= 0 && n <= 1000000; i++) { poke(); }
function nested() { n = 0; }",
    ] {
        let source = format!("export function f(n: number, xs: number[]) {{ {body} }}");
        let (_, _, bound) = reasoned_result_of(&source, "f");

        assert!(bound, "{body}");
    }

    for body in [
        "for (let i = 0; i < n && n >= 0 && n <= 1000000; i++) { opaque(xs); }",
        "for (let i = 0; i < n && n >= 0 && n <= 1000000; i++) { poke(); }",
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
        let source = format!("function heavy(n: number) {{ let s = 0; for (let k = 0; k < n && n >= 0 && n <= 1000000; k++) s += k; return s; }} export function f(n: number) {{ let i = 0, total = 0; const reset = () => {{ i = 0; }}; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) {{\n{call}\nwhile (i >= 0 && i < n && n >= 0 && n <= 1000000) {{ i++; total++; }} }} return total; }}");

        assert_eq!(result_of(&source, "f").0, cost(expected), "{call}");
    }
}

#[test]
fn storage_read_through_header_calls_is_invalidated_by_writes() {
    for source in [
        "export function f(n: number) { const box = { limit: n }; let i = 0, total = 0; const size = () => box.limit; const grow = () => { box.limit += n; }; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < size()) { i++; total++; } grow(); } return total; }",
        "function limitOf(b: { limit: number }) { return b.limit; } export function f(n: number) { const box = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < limitOf(box)) { i++; total++; } box.limit += n; } return total; }",
    ] {
        assert_eq!(reasoned_result_of(source, "f"), (cost("O(N)"), false, true), "{source}");
    }
}

#[test]
fn constructions_are_distinct_only_when_constructors_return_their_instance() {
    let shared = "const shared = { limit: 0 }; class C { constructor() { return shared; } } export function f(n: number) { const a: any = new C(); const b: any = new C(); a.limit = n; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < a.limit) { i++; total++; } b.limit += n; } return total; }";
    let fresh = "class C { limit = 0; } export function f(n: number) { const a = new C(); const b = new C(); a.limit = n; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < a.limit) { i++; total++; } b.limit += n; } return total; }";

    let wrapped = "export function f(n: number) { const box = { limit: n }; const view: any = new Object(box); let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { while (i < box.limit) { i++; total++; } view.limit += n; } return total; }";

    assert_eq!(reasoned_result_of(shared, "f"), (cost("O(N)"), false, true));
    assert_eq!(result_of(fresh, "f").0, cost("O(N)"));
    assert_eq!(
        reasoned_result_of(wrapped, "f"),
        (cost("O(N)"), false, true)
    );
}

#[test]
fn destructured_counter_writes_invalidate_loop_bounds() {
    for body in [
        "for (let k = 0; k < n && n >= 0 && n <= 1000000; k++) { [k] = [xs[0]]; t++; }",
        "for (let k = 0; k < n && n >= 0 && n <= 1000000; k++) { ({ k } = o); t++; }",
        "let k = 0; while (k >= 0 && k < n && n >= 0 && n <= 1000000) { k++; [k] = [xs[0]]; t++; }",
        "let i = 0, j = 0; for (const x of xs) { while (j >= 0 && j < n && n >= 0 && n <= 1000000) { j++; } [i, j] = [x, i]; }",
    ] {
        let source = format!("export function f(n: number, xs: number[], o: {{ k: number }}) {{ let t = 0; {body} return t; }}");
        let (_, _, bound) = reasoned_result_of(&source, "f");

        assert!(bound, "{body}");
    }
}

#[test]
fn default_values_in_destructuring_alias_their_source() {
    let aliased = "export function f(n: number) { const box = { limit: n }; let a: any; [a = box] = []; let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { opaque(a); while (i < box.limit) { i++; total++; } } return total; }";
    let shorthand = "export function f(n: number) { const box = { limit: n }; let a: any; ({ a = box } = {} as any); let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { opaque(a); while (i < box.limit) { i++; total++; } } return total; }";

    assert_eq!(
        reasoned_result_of(aliased, "f"),
        (cost("O(N)"), false, true)
    );
    assert_eq!(
        reasoned_result_of(shorthand, "f"),
        (cost("O(N)"), false, true)
    );
}

#[test]
fn direct_eval_reaches_every_binding() {
    let source = "export function f(n: number, code: string) { let i = 0, total = 0; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { eval(code); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } } return total; }";
    let (_, _, bound) = reasoned_result_of(source, "f");

    assert!(bound);

    let earlier = "export function f(n: number, code: string) { let i = 0, total = 0; eval(code); for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) { poke(); while (i >= 0 && i < n && n >= 0 && n <= 1000000) { i++; total++; } } return total; }";

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
        let source = format!("export function f(n: number, code: string) {{ let i = 0, total = 0; {call}; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) {{ poke(); while (i >= 0 && i < n && n >= 0 && n <= 1000000) {{ i++; total++; }} }} return total; }}");

        assert!(reasoned_result_of(&source, "f").2, "{call}");
    }
}

#[test]
fn member_effects_distinguish_the_proven_endpoint_owner() {
    let source = "export function selected(n:number,xs:number[]){const box=[...xs];for(let j=0;j<n&&n>=0&&n<=1000000;j++){let i=0;while(i<box.length)i++;}}";

    assert_eq!(
        reasoned_result_of(source, "selected"),
        (cost("O(N^2)"), true, false)
    );

    for writer in [
        "TARGET.length++;",
        "const alias = TARGET; alias.length++;",
        "const grow = () => { TARGET.length++; }; grow();",
        "grow(TARGET);",
    ] {
        for target in ["box", "other"] {
            let write = writer.replace("TARGET", target);
            let source = format!("function grow(values: number[]) {{ values.length++; }} export function selected(n: number, xs: number[]) {{ const box = [...xs], other = [...xs]; for (let j = 0; j < n && n >= 0 && n <= 1000000; j++) {{ let i = 0; while (i < box.length) {{ i++; {write} }} }} }}");
            let (raw, complete, reasons) = support::legacy_result_of(&source, "selected");
            let known = support::projected_class_of(&raw);
            let unresolved_bound = reasons.contains(&UnknownReason::Bound);

            if target == "box" {
                assert!(!complete && unresolved_bound, "{source}: {known:?}");
            } else {
                assert!(!unresolved_bound, "{source}: {known:?} {reasons:?}");
                assert!(
                    reasons
                        .iter()
                        .all(|reason| *reason == UnknownReason::Target),
                    "{source}: {reasons:?}"
                );
                assert_eq!(known, cost("O(N^2)"), "{source}");
            }
        }
    }
}

#[test]
fn growing_collection_proofs_stop_at_recursive_bound_queries() {
    let source = "export function selected(xs:number[]){const box=[...xs];for(const x of xs){let i=0;while(i<box.length){i++;box.push(1);}}}";
    let (known, complete, bound) = reasoned_result_of(source, "selected");

    assert_eq!(known, cost("O(N)"));
    assert!(!complete && bound);
}

#[test]
fn published_constructor_effects_distinguish_returned_and_fresh_owners() {
    for returned in [false, true] {
        let body = if returned { "return shared;" } else { "" };
        let source = format!("export function selected() {{ const shared = {{ limit: 0 }}; class Box {{ limit = 0; constructor() {{ {body} }} }} const box = new Box(), other = new Box(); function first() {{ box.limit++; }} function second() {{ other.limit++; }} first(); second(); }}");

        support::run_with_source(&source, |analysis, file| {
            support::summary_of(analysis, file, "selected");

            let writes_of = |name| {
                let function = support::function_of_name(analysis.project, file, name);
                let mut writes: Vec<_> = analysis
                    .summary_records_for(olint::declarations::FunctionId {
                        file,
                        node: function.node_id(),
                    })
                    .into_iter()
                    .flat_map(|record| record.effects.member_writes.iter().copied())
                    .collect();

                writes.sort_by_key(|value| value.0);
                writes.dedup();
                assert_eq!(writes.len(), 1, "{source}: {name}: {writes:?}");

                writes[0]
            };

            assert_eq!(
                analysis
                    .values
                    .may_alias(writes_of("first"), writes_of("second")),
                returned,
                "{source}"
            );
        });
    }
}

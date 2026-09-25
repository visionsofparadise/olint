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

#[test]
fn suspended_live_iteration_accounts_for_outstanding_collection_writes() {
    let cube = "function cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }";
    let producer = "async function grow(n: number) { if (n >= 0 && n <= 1000000) { let next = 1; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { await 0; values.add(next++); } } }";

    for (setup, body, unresolved) in [
        (format!("{producer} grow(xs.length);"), "for (const x of values) { await 0; cube(xs); }", true),
        (format!("{producer} grow(xs.length);"), "for (const x of values) { cube(xs); }", false),
        (String::new(), "for (const x of values) { await 0; cube(xs); }", false),
        ("values.add(1);".to_string(), "for (const x of values) { await 0; cube(xs); }", false),
        ("const other = new Set<number>(); async function grow() { await 0; other.add(1); } grow();".to_string(), "for (const x of values) { await 0; cube(xs); }", false),
        ("p.then(() => values.add(1));".to_string(), "for (const x of values) { await 0; cube(xs); }", true),
        ("p.then(() => { values.delete(0); values.add(0); });".to_string(), "for (const x of values) { await 0; cube(xs); }", true),
        ("function launch() { p.then(() => values.add(1)); } launch();".to_string(), "for (const x of values) { await 0; cube(xs); }", true),
        (format!("{producer} grow(xs.length); async function tick() {{ await 0; }}"), "for (const x of values) { tick(); cube(xs); }", false),
        (format!("{producer} grow(xs.length); async function tick() {{ await 0; }}"), "for (const x of values) { await tick(); cube(xs); }", true),
    ] {
        let source = format!("{cube} export async function selected(xs: number[], p: Promise<number>) {{ const values = new Set([0]); {setup} {body} }}");
        let map = source.replace("new Set([0])", "new Map([[0,0]])")
            .replace("values.add(next++)", "values.set(next,next++)")
            .replace("values.add(1)", "values.set(1,1)")
            .replace("values.add(0)", "values.set(0,0)");

        for source in [source, map] {
            let (cost, _, reasons) = support::legacy_result_of(&source, "selected");

            assert_eq!(reasons.contains(&olint::unknowns::UnknownReason::Bound), unresolved, "{source}: {reasons:?}");
            assert_eq!(support::projected_class_of(&cost), cost_of_pending(unresolved), "{source}: {cost:?}");
        }
    }
}

#[test]
fn suspended_numeric_loops_reject_pending_counter_and_endpoint_writes() {
    let cube =
        "function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}";

    for (setup, condition, body, unresolved) in [
        (
            "async function grow(){await 0;i=0;}grow();",
            "i<3",
            "await 0;cube(xs);",
            true,
        ),
        (
            "async function grow(){await 0;i=0;}grow();",
            "i<3",
            "cube(xs);",
            true,
        ),
        ("", "i<3", "await 0;cube(xs);", false),
        (
            "async function grow(){await 0;other=0;}grow();",
            "i<3",
            "await 0;cube(xs);",
            false,
        ),
        ("p.then(()=>{i=0;});", "i<3", "await 0;cube(xs);", true),
        (
            "function launch(){p.then(()=>{i=0;});}launch();",
            "i<3",
            "await 0;cube(xs);",
            true,
        ),
        (
            "async function grow(){await 0;n++;}grow();",
            "i<n&&n>=0&&n<=1000000",
            "await 0;cube(xs);",
            true,
        ),
    ] {
        let source = format!("{cube} export async function selected(xs:number[],p:Promise<number>){{let i=0,n=3,other=0;{setup}for(;{condition};i++){{{body}}}}}");

        assert_pending_cost(&source, unresolved, cost("O(N^3)"));
    }
}

#[test]
fn pending_writes_follow_supplied_generator_storage() {
    let cube =
        "function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}";

    for (generator, iteration) in [
        ("function* generate(values:Set<number>){yield* values;}", "for(const value of iterator){await 0;cube(xs);}"),
        ("async function* generate(values:Set<number>){for(const value of values){await 0;yield value;}}", "for await(const value of iterator){cube(xs);}"),
    ] {
        for (producer, unresolved) in [("grow(values);", true), ("grow(other);", false), ("", false)] {
            for (consumer, call) in [
                (String::new(), iteration.to_string()),
                (format!("async function consume(iterator:AsyncIterable<number>&Iterable<number>,xs:number[]){{{iteration}}}"), "await consume(iterator,xs);".to_string()),
            ] {
                let source = format!("{cube}{generator}async function grow(values:Set<number>){{await 0;values.delete(0);values.add(0);}}{consumer}export async function selected(xs:number[]){{const values=new Set([0]),other=new Set([0]);const iterator=generate(values);{producer}{call}}}");

                assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
            }
        }
    }
}

#[test]
fn pending_writes_follow_captured_and_alternative_generator_storage() {
    let helpers = "function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}async function grow(values:Set<number>){await 0;values.delete(0);values.add(0);}async function consume(iterator:Iterable<number>,xs:number[]){for(const value of iterator){await 0;cube(xs);}}";

    for factory in ["function* generate(){yield* values;}const iterator=generate();", "function* left(){yield* values;}function* right(){yield* values;}const iterator=flag?left():right();", "function* generate(){yield* values;}function wrap(){return generate();}const iterator=wrap();"] {
        for (producer, unresolved) in [("grow(values);", true), ("grow(other);", false), ("", false)] {
            let source=format!("{helpers}export async function selected(xs:number[],flag:boolean){{const values=new Set([0]),other=new Set([0]);{factory}{producer}await consume(iterator,xs);}}");

            assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
        }
    }
}

#[test]
fn pending_callee_contexts_remain_distinct_in_both_orders() {
    let helpers="function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}async function grow(values:Set<number>){await 0;values.delete(0);values.add(0);}async function consume(values:Set<number>,xs:number[]){for(const value of values){await 0;cube(xs);}}async function pending(values:Set<number>,xs:number[]){grow(values);await consume(values,xs);}async function stable(values:Set<number>,xs:number[]){await consume(values,xs);}";

    for calls in [
        "await pending(values,xs);await stable(other,xs);",
        "await stable(other,xs);await pending(values,xs);",
    ] {
        let source=format!("{helpers}export async function selected(xs:number[]){{const values=new Set([0]),other=new Set([0]);{calls}}}");
        let (known, _, reasons) = support::legacy_result_of(&source, "selected");

        assert!(
            reasons.contains(&UnknownReason::Bound),
            "{source}: {reasons:?}"
        );
        assert_eq!(
            support::projected_class_of(&known),
            cost("O(N^4)"),
            "{source}: {known:?}"
        );
    }
}

#[test]
fn pending_owner_identity_survives_multiple_forwarding_calls() {
    let helpers="function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}async function grow(values:Set<number>){await 0;values.delete(0);values.add(0);}async function consume(values:Set<number>,xs:number[]){for(const value of values){await 0;cube(xs);}}";

    for (written, unresolved) in [("values", true), ("other", false)] {
        let source=format!("{helpers}async function wrapper(values:Set<number>,other:Set<number>,xs:number[]){{grow({written});await consume(values,xs);}}async function forward(values:Set<number>,other:Set<number>,xs:number[]){{await wrapper(values,other,xs);}}export async function selected(xs:number[]){{const values=new Set([0]),other=new Set([0]);await forward(values,other,xs);}}");

        assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
    }
}

#[test]
fn implicit_native_and_consumed_generator_work_can_schedule_writers() {
    let helpers =
        "function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}";

    for (producer, unresolved) in [
        ("Array.from({[Symbol.iterator](){p.then(()=>{values.delete(0);values.add(0);});return [0][Symbol.iterator]();}});",true),
        ("Object.values({get value(){p.then(()=>{values.delete(0);values.add(0);});return 0;}});",true),
        ("function* start(){p.then(()=>{values.delete(0);values.add(0);});yield 0;}for(const ignored of start()){}",true),
        ("function* start(){p.then(()=>{values.delete(0);values.add(0);});yield 0;}start();",false),
    ] {
        for (written, shared) in [("values", true), ("other", false)] {
        let producer=producer.replace("values.", &format!("{written}."));
        let unresolved=unresolved && shared;
        let source=format!("{helpers}export async function selected(xs:number[],p:Promise<number>){{const values=new Set([0]),other=new Set([0]);{producer}for(const value of values){{await 0;cube(xs);}}}}");

        assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
        }
    }
}

#[test]
fn async_generator_yield_exposes_pending_collection_writes() {
    for (written, unresolved) in [("values", true), ("other", false)] {
        let source=format!("export async function* selected(p:Promise<number>){{const values=new Set([0]),other=new Set([0]);p.then(()=>{{{written}.delete(0);{written}.add(0);}});for(const value of values)yield value;}}");

        support::run_with_source(&source, |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "selected");
            let reading = analysis.summarize(file, function);
            let bound = reading.completions.iter().any(|channel| {
                support::unknown_reasons(analysis, channel.2.unknowns)
                    .contains(&UnknownReason::Bound)
            });

            assert_eq!(bound, unresolved, "{source}");
        });
    }
}

#[test]
fn generator_storage_dependencies_are_metered_and_canonicalized_once() {
    let mut counts = Vec::new();

    for count in [16, 32, 64] {
        let loops = (0..count)
            .map(|index| {
                format!("const values{index}=[...xs];for(const value of values{index})yield value;")
            })
            .collect::<String>();
        let source = format!("export function* selected(xs:number[]){{{loops}}}");

        counts.push(pending_steps_of(&source));
    }

    assert_pending_growth(&counts);

    let source="function* values(xs:number[]){for(const value of xs)yield value;}export async function selected(xs:number[]){const iterator=values(xs);for(const value of iterator){await 0;void value;}}";

    support::run_with_source(source, |analysis, file| {
        analysis
            .set_scheduler_limits(olint::summaries::SchedulerLimits {
                work: olint::analysis::work::Limits::uniform(100_000)
                    .with(olint::analysis::work::Event::EffectPrepassNode, 4),
                ..olint::summaries::SchedulerLimits::default()
            })
            .unwrap();

        let part = support::summary_of(analysis, file, "selected");

        assert!(support::unknown_reasons(analysis, part.unknowns)
            .contains(&UnknownReason::ResourceExhaustion));
    });
}

#[test]
fn pending_caller_chains_reuse_scheduling_classification() {
    let mut counts = Vec::new();

    for count in [8, 16, 32] {
        let chain = (0..count)
            .map(|index| {
                format!(
                    "function f{index}(values:Set<number>,xs:number[]){{return f{}(values,xs);}}",
                    index + 1
                )
            })
            .collect::<String>();
        let source=format!("{chain}async function f{count}(values:Set<number>,xs:number[]){{for(const value of values){{await 0;for(const x of xs)void x;}}}}async function grow(values:Set<number>){{await 0;values.delete(0);values.add(0);}}export async function selected(xs:number[]){{const values=new Set([0]);grow(values);await f0(values,xs);}}");

        support::run_with_source(&source, |analysis, file| {
            let part = support::summary_of(analysis, file, "selected");

            assert!(
                support::unknown_reasons(analysis, part.unknowns).contains(&UnknownReason::Bound)
            );
            counts.push(
                analysis
                    .scheduler_stats()
                    .work
                    .consumed(olint::analysis::work::Event::EffectPrepassNode),
            );
        });
    }

    assert_pending_growth(&counts);
}

#[test]
fn scheduling_cycles_keep_late_producers_and_ignore_pure_backedges() {
    for scheduler in ["", "p.then(()=>{values.delete(0);values.add(0);});"] {
        for reverse in [false, true] {
            let a = format!("function a(n:number){{if(n>0)b(n-1);{scheduler}}}");
            let b = "function b(n:number){if(n>0)a(n-1);}";
            let functions = if reverse {
                format!("{b}{a}")
            } else {
                format!("{a}{b}")
            };
            let source=format!("function cube(xs:number[]){{for(const a of xs)for(const b of xs)for(const c of xs)void c;}}export async function selected(xs:number[],p:Promise<number>){{const values=new Set([0]);{functions}a(3);b(3);for(const value of values){{await 0;cube(xs);}}}}");

            assert_pending_cost(
                &source,
                !scheduler.is_empty(),
                cost_of_pending(!scheduler.is_empty()),
            );
        }
    }
}

#[test]
fn decorated_constructors_keep_pending_interference_explicit() {
    for constructor in ["", "constructor(){}"] {
        for (class_decorator, method_decorator) in [("", ""), ("@decorate", ""), ("", "@decorate")]
        {
            let derived_constructor = if constructor.is_empty() {
                ""
            } else {
                "constructor(){super();}"
            };
            let base = format!(
                "{class_decorator} class Base{{{constructor}{method_decorator} method(){{}}}}"
            );

            for (shape, class) in [
                format!("{class_decorator} class Holder{{{constructor}{method_decorator} method(){{}}}}"),
                format!("{base} class Holder extends Base{{{derived_constructor}}}"),
                format!("{base} const Parent=Base;class Middle extends Parent{{}}class Holder extends Middle{{{derived_constructor}}}"),
            ].into_iter().enumerate() {
              let decorated = !class_decorator.is_empty() || !method_decorator.is_empty();

              if shape == 2 && !decorated {
                  continue;
              }

              for inside in [false, true] {
                let (outer, inner) = if inside {
                    ("", class.as_str())
                } else {
                    (class.as_str(), "")
                };
                let source=format!("declare function decorate(value:any,context:any):any;function cube(xs:number[]){{for(const a of xs)for(const b of xs)for(const c of xs)void c;}}{outer}export async function selected(xs:number[]){{const values=new Set([0]);{inner}new Holder();for(const value of values){{await 0;cube(xs);}}}}");
                let unresolved = decorated || (shape == 1 && constructor.is_empty());

                assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
              }
            }
        }
    }
}

#[test]
fn pending_effects_follow_callback_specializations_in_both_orders() {
    for calls in [
        "await consume(()=>{},xs);await consume(()=>{i=0;},xs);",
        "await consume(()=>{i=0;},xs);await consume(()=>{},xs);",
    ] {
        let source = format!("export async function selected(xs:number[],p:Promise<number>){{let i=0;async function consume(reset:()=>void,values:number[]){{p.then(reset);for(;i<3;i++){{await 0;for(const x of values)void x;}}}}{calls}}}");
        let (_, _, reasons) = support::legacy_result_of(&source, "selected");

        assert!(
            reasons.contains(&olint::unknowns::UnknownReason::Bound),
            "{source}: {reasons:?}"
        );
    }
}

#[test]
fn suspended_async_generators_reject_pending_counter_resets() {
    let source = "export async function* selected(xs:number[],p:Promise<number>){let i=0;p.then(()=>{i=0;});for(;i<3;i++){await 0;for(const x of xs)void x;yield i;}}";

    support::run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");
        let reading = analysis.summarize(file, function);

        assert!(reading
            .completions
            .iter()
            .any(
                |channel| support::unknown_reasons(analysis, channel.2.unknowns)
                    .contains(&olint::unknowns::UnknownReason::Bound)
            ));
    });
}

#[test]
fn pending_effect_scan_exhaustion_stays_explicit() {
    let source = "export async function selected(p:Promise<number>){const values=new Set([0]);p.then(()=>values.add(1));for(const value of values){await 0;void value;}}";

    support::run_with_source(source, |analysis, file| {
        let event = olint::analysis::work::Event::EffectPrepassNode;

        analysis
            .set_scheduler_limits(olint::summaries::SchedulerLimits {
                work: olint::analysis::work::Limits::uniform(100_000).with(event, 0),
                ..olint::summaries::SchedulerLimits::default()
            })
            .unwrap();

        let part = support::summary_of(analysis, file, "selected");

        assert!(!part.is_complete());
        assert!(support::unknown_reasons(analysis, part.unknowns)
            .contains(&olint::unknowns::UnknownReason::ResourceExhaustion));
        assert!(analysis.scheduler_stats().work.exhausted(event));
    });
}

#[test]
fn pending_counter_writes_fail_strict_unknown_policy() {
    let project = support::project_of(&[
        ("tsconfig.json", "{}"),
        ("olint.config.json", r#"{"entrypoints":["index.ts"],"max":"O(N^8)","unknown":"error"}"#),
        ("index.ts", "export async function selected(p:Promise<number>){let i=0;p.then(()=>{i=0;});for(;i<3;i++){await 0;}}"),
    ]);
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_olint"))
        .current_dir(project.path())
        .args(["--types=syntactic", "--tsconfig=tsconfig.json"])
        .output()
        .unwrap();

    assert_eq!(
        output.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("iteration bound"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn suspended_loops_share_their_pending_effect_scan() {
    let mut counts = Vec::new();

    for count in [16, 32, 64] {
        let loops = "for (const value of values) { await 0; void value; }\n".repeat(count);
        let source = format!("export async function selected(p: Promise<number>) {{ const values = new Set([0]); p.then(() => values.add(1)); {loops} }}");

        counts.push(pending_steps_of(&source));
    }

    assert_pending_growth(&counts);
}

#[test]
fn suspended_callees_receive_pending_caller_effects() {
    let helpers = "function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;} async function consume(values:Set<number>,xs:number[]){for(const value of values){await 0;cube(xs);}} async function grow(values:Set<number>){await 0;values.delete(0);values.add(0);}";

    for (setup, unresolved) in [
        ("grow(values);", true),
        ("grow(other);", false),
        ("", false),
    ] {
        let source=format!("{helpers} export async function selected(xs:number[]){{const values=new Set([0]),other=new Set([0]);{setup}await consume(values,xs);}}");

        assert_pending_cost(&source, unresolved, cost_of_pending(unresolved));
    }
}

#[test]
fn generator_counter_resumption_has_no_unproved_yield_count() {
    let source="function cube(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c;}export function selected(xs:number[]){let i=0;function* generate(){for(i=0;i<3;i++)yield i;}const iterator=generate();for(const value of iterator){i=0;cube(xs);}}";
    let (known, complete, reasons) = support::legacy_result_of(source, "selected");

    assert!(!complete);
    assert!(reasons.contains(&UnknownReason::Bound), "{reasons:?}");
    assert_eq!(
        support::projected_class_of(&known),
        Cost::parse("O(N^3)").unwrap()
    );
}

fn cost_of_pending(unresolved: bool) -> Cost {
    cost(if unresolved { "O(N^3)" } else { "O(N^4)" })
}

fn assert_pending_cost(source: &str, unresolved: bool, expected: Cost) {
    let (known, _, reasons) = support::legacy_result_of(source, "selected");

    assert_eq!(
        reasons.contains(&UnknownReason::Bound),
        unresolved,
        "{source}: {reasons:?}"
    );
    assert_eq!(
        support::projected_class_of(&known),
        expected,
        "{source}: {known:?}"
    );
}

fn pending_steps_of(source: &str) -> u64 {
    let mut steps = 0;

    support::run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "selected");

        analysis.summarize(file, function);

        steps = analysis
            .scheduler_stats()
            .work
            .consumed(olint::analysis::work::Event::EffectPrepassNode);
    });

    steps
}

fn assert_pending_growth(counts: &[u64]) {
    for pair in counts.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{counts:?}");
    }
}

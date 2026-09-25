use std::collections::BTreeSet;

use olint::analysis::TypeMode;
use olint::cost::Cost;
use olint::unknowns::UnknownReason;

use crate::support;

use support::{assert_selected, index_of, selected_result_in};

const QUADRATIC: &str = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }";

fn assert_reasons(cases: &[(String, &str, UnknownReason)]) {
    for types in [TypeMode::Syntactic, TypeMode::Tsc] {
        for (source, expected, reason) in cases {
            let (cost, reasons): (Cost, BTreeSet<UnknownReason>) =
                selected_result_in(&[("index.ts", source.as_str())], types);

            assert_eq!(cost, Cost::parse(expected).unwrap(), "{types:?} {source}");
            assert!(reasons.contains(reason), "{types:?} {source}: {reasons:?}");
        }
    }
}

#[test]
fn accessors_invoke_their_known_getters_and_setters() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ get value() {{ return quadratic(xs); }} }}; return box.value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ set value(n: number) {{ quadratic(xs); }} }}; box.value = 1; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ get value() {{ return quadratic(xs); }} }} return new Box().value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ set value(n: number) {{ quadratic(xs); }} }} const box = new Box(); box.value = 2; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ get value() {{ return quadratic(xs); }}, set value(n: number) {{ quadratic(xs); }} }}; box.value += 1; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ get value() {{ return quadratic(xs); }} }}; let total = 0; for (const x of xs) total += box.value; return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ get value() {{ return quadratic(xs); }} }}; delete (box as any).value; return 1; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ value: 1 }}; return box.value + xs.length; }}")), "O(1)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn described_properties_compose_their_getters_and_values() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', {{ get() {{ return quadratic(xs); }} }}); return o.v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ v: number }}; Reflect.defineProperty(o, 'v', {{ get: () => quadratic(xs) }}); return o.v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ v: number }}; Object.defineProperties(o, {{ v: {{ get() {{ return quadratic(xs); }} }} }}); return o.v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ run(): number }}; Object.defineProperty(o, 'run', {{ value: () => quadratic(xs) }}); return o.run(); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ run(): number }}; Object.defineProperties(o, {{ run: {{ value: () => quadratic(xs) }} }}); return o.run(); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', {{ set(n: number) {{ quadratic(xs); }} }}); o.v = 1; }}")), "O(N^2)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn coercions_and_tags_invoke_their_known_implementations() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ valueOf() {{ return quadratic(xs); }} }}; return +box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ toString() {{ quadratic(xs); return ''; }} }}; return `${{box}}`; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ [Symbol.toPrimitive]() {{ return quadratic(xs); }} }}; return (box as any) + 1; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ valueOf() {{ return quadratic(xs); }} }}; let total = 0; for (const x of xs) total += +box; return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function tag(parts: TemplateStringsArray) {{ return quadratic(xs); }} return tag`hello`; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const tags = {{ tag(parts: TemplateStringsArray) {{ return quadratic(xs); }} }}; return tags.tag`hello`; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function tag(parts: TemplateStringsArray, value: number) {{ return value; }} return tag`${{quadratic(xs)}}`; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nclass Named {{ toString() {{ return 'named'; }} }}\nexport function selected(xs: number[], n: number) {{ let total = 0; for (const x of xs) total += x + n; return `${{total}}` + new Named(); }}")), "O(N)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn iterator_protocols_charge_acquisition_each_visit_and_applicable_close() {
    let next = "{ [Symbol.iterator]() { let count = 0; return { next() { quadratic(xs); return { done: count++ >= xs.length, value: count }; } }; } }";
    let closing = "{ [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { quadratic(xs); return { done: true, value: 0 }; } }; } }";
    let cubic = "{ [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { for (const x of xs) quadratic(xs); return { done: true, value: 0 }; } }; } }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {next}; for (const value of iterable) {{}} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {next}; return [...iterable]; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Walk {{ [Symbol.iterator]() {{ return this; }} next() {{ quadratic(xs); return {{ done: true, value: 0 }}; }} }} for (const v of new Walk()) {{}} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {{ *[Symbol.iterator]() {{ yield quadratic(xs); }} }}; for (const v of iterable) {{}} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const value of iterable) {{ if (value) break; }} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const x of xs) {{ for (const value of iterable) {{ break; }} }} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; for (const value of iterable) {{ blk: {{ break blk; }} }} }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; for (const value of iterable) {{ switch (value) {{ case 1: break; }} }} }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; outer: for (const value of iterable) {{ continue outer; }} }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; outer: for (const value of iterable) {{ for (const x of xs) {{ break outer; }} }} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; const [a, b] = iterable; return a + b; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const value of iterable) {{ void value; }} }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ let total = 0; for (const x of xs) for (const y of xs) total += x + y; return total; }}")), "O(N^2)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn unknown_implementations_keep_proven_multiplicity_and_surrounding_work() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(tag: (parts: TemplateStringsArray) => number, xs: number[], n: number) {{ let total = 0; for (let i = 0; i < n; i++) total += tag`x` + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(descriptor: PropertyDescriptor, xs: number[], n: number) {{ const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', descriptor); let total = 0; for (let i = 0; i < n; i++) total += o.v + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(f: () => number, xs: number[], n: number) {{ const box = {{ valueOf() {{ return 1; }} }}; box.valueOf = f; let total = 0; for (let i = 0; i < n; i++) total += +box + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(step: () => IteratorResult<number>, xs: number[]) {{ const iterator = {{ next(): IteratorResult<number> {{ return {{ done: true, value: 0 }}; }} }}; iterator.next = step; const iterable = {{ [Symbol.iterator]() {{ return iterator; }} }}; let total = 0; for (const v of iterable) total += quadratic(xs); return total; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport class Keys {{ [Symbol.iterator]() {{ return [1].values(); }} }}\nexport function selected(items: Iterable<number>, xs: number[]) {{ let total = 0; for (const v of items) total += quadratic(xs); return total; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport class Keys {{ [Symbol.iterator]() {{ return [1].values(); }} }}\nexport function selected(xs: number[]) {{ let total = 0; for (const x of xs) total += quadratic(xs); return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nclass Holder {{ get value() {{ return 1; }} }}\nexport function selected(o: {{ value: number }}, xs: number[], n: number) {{ let total = 0; for (let i = 0; i < n; i++) total += o.value + quadratic(xs); return total + new Holder().value; }}")), "O(N^3)", true),
    ];

    assert_selected(&cases);
}

#[test]
fn implicit_calls_compose_their_writes_into_effects() {
    let cases = [
        ("export function selected(xs: number[]) { const box = { get grow() { xs.push(1); return 0; } }; let total = 0; for (let i = 0; i < xs.length; i++) total += box.grow; return total; }".to_string(), "O(1)", UnknownReason::Bound),
        ("export function selected(xs: number[]) { const box = { set grow(v: number) { xs.push(v); } }; for (let i = 0; i < xs.length; i++) box.grow = i; }".to_string(), "O(1)", UnknownReason::Bound),
        ("export function selected(xs: number[]) { const box = { toString() { xs.push(1); return ''; } }; let text = ''; for (let i = 0; i < xs.length; i++) text += `${box}`; return text; }".to_string(), "O(1)", UnknownReason::Bound),
        ("export function selected(xs: number[]) { const iterable = { [Symbol.iterator]() { let count = 0; return { next() { xs.push(1); return { done: count++ > 3, value: 0 }; } }; } }; let total = 0; for (let i = 0; i < xs.length; i++) for (const v of iterable) total += v; return total; }".to_string(), "O(1)", UnknownReason::Bound),
    ];

    assert_reasons(&cases);

    let controls = [
        (index_of("export function selected(xs: number[]) { const box = { get grow() { return 0; } }; let total = 0; for (let i = 0; i < xs.length; i++) total += box.grow; return total; }".to_string()), "O(N)", false),
        (index_of("export function selected(xs: number[]) { const box = { toString() { return ''; } }; let text = ''; for (let i = 0; i < xs.length; i++) text += `${box}`; return text; }".to_string()), "O(N)", false),
    ];

    assert_selected(&controls);
}

#[test]
fn builtin_accessors_and_replaced_iterators_keep_fresh_arrays_variable() {
    let cases = [
        (index_of("Object.defineProperty(Array.prototype, 'grow', { get(this: number[]) { this.push(1); return 0; } });\nexport function selected(n: number) { const xs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n; i++) { total += (xs as unknown as { grow: number }).grow; for (const x of xs) total += x; } return total; }".to_string()), "O(N^2)", false),
        (index_of("export function selected(n: number) { const ys: number[] = [1, 2, 3]; const it: any = [][Symbol.iterator](); it.__proto__.next = function () { return { done: true, value: 0 }; }; let total = 0; for (let i = 0; i < n; i++) { for (const y of ys) total += y; } return total; }".to_string()), "O(N)", true),
        (index_of("export function selected(n: number) { const zs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n; i++) { total += (zs as unknown as { grow: number }).grow; for (const z of zs) total += z; } return total; }".to_string()), "O(N)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn construction_contexts_resolve_this_and_super_members() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return quadratic(xs); }} v = this.m(); }} for (const x of xs) new Box(); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return quadratic(xs); }} constructor() {{ this.m(); }} }} for (const x of xs) new Box(); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static s() {{ return quadratic(xs); }} static v = this.s(); }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static s() {{ return quadratic(xs); }} static {{ this.s(); }} }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{ m() {{ return quadratic(xs); }} }} class B extends A {{ v = super.m(); }} for (const x of xs) new B(); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{ static m() {{ return quadratic(xs); }} }} class B extends A {{ static v = super.m(); }} return B; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return 1; }} v = this.m(); }} class Heavy extends Box {{ m() {{ return quadratic(xs); }} }} return new Heavy(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport class Box {{ constructor(xs: number[]) {{ this.m(xs); }} m(xs: number[]) {{ return quadratic(xs); }} }}\nexport function selected(xs: number[]) {{ return new Box(xs); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return quadratic(xs); }} n() {{ return this.m(); }} }} return new Box().n(); }}")), "O(N^2)", true),
    ];

    assert_selected(&cases);
}

#[test]
fn functions_passed_as_values_receive_their_forwarded_arguments() {
    let slow = "function slow(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; return true; }";
    let cases = [
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ t.includes = v; }}\nfunction apply(f: (t: any, v: unknown) => void, xs: number[]) {{ f(Array.prototype, () => slow(xs)); }}\nexport function selected(xs: number[]) {{ set(new Set<number>(), null); apply(set, xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ t.includes = v; }}\nfunction apply(f: (t: any, v: unknown) => void, xs: number[]) {{ const g = f; g(Array.prototype, () => slow(xs)); }}\nexport function selected(xs: number[]) {{ apply(set, xs); const zs = [1]; return zs.includes(0); }}")), "O(N)", true),
    ];

    assert_selected(&cases);
}

#[test]
fn reference_valued_implementations_enter_the_protocol_index() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const heavy = () => quadratic(xs); const box = {{ xs, valueOf: heavy }}; return +(box as any); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const heavy = () => {{ quadratic(xs); return ''; }}; class Box {{ toString = heavy; }} return `${{new Box()}}`; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function* walk() {{ for (const x of xs) yield quadratic(xs); }} const it = {{ [Symbol.iterator]: walk }}; for (const v of it) void v; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const getV = () => quadratic(xs); const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', {{ get: getV }}); return o.v; }}")), "O(N^2)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn declared_primitive_types_skip_coercion_while_values_keep_getters() {
    let heavy = "const heavy = { valueOf() { return quadratic(xs); }, toString() { quadratic(xs); return ''; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nfunction inner(n: number) {{ return n + 1; }}\nexport function selected(xs: number[]) {{ {heavy} return inner(heavy as any); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nconst probe = {{ valueOf() {{ return 1; }} }};\nexport function selected(n: number) {{ return n + 1; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {heavy} let v: number = heavy as any; return v + 1; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\ndeclare const ambient: number;\nconst probe = {{ valueOf() {{ return 1; }} }};\nexport function selected() {{ return ambient + 1; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nfunction text(s: string) {{ return `${{s}}`; }}\nexport function selected(xs: number[]) {{ {heavy} return text(heavy as any); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {heavy} const o: {{ n: number }} = {{ n: heavy as any }}; return o.n * 2; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {heavy} return (heavy as any) + 1; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nconst probe = {{ valueOf() {{ return 1; }} }};\nexport function selected(o: any) {{ return o + 1; }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\nfunction lengthOf(a: number[]) {{ return a.length; }}\nexport function selected(xs: number[]) {{ class Long {{ get length() {{ return quadratic(xs); }} }} return lengthOf(new Long() as any); }}")), "O(1)", true),
    ];

    assert_selected(&cases);
}

#[test]
fn computed_definition_keys_convert_their_values() {
    let key = "const key = { toString() { quadratic(xs); return 'k'; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} return {{ [key as any]: 1 }}; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} class Box {{ [key as any] = 1; }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} class Box {{ [key as any]() {{ return 1; }} }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} const {{ [key as any]: value }} = {{ k: 1 }} as any; return value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} const name = 'k'; return {{ [name]: 1, [0]: 2 }}; }}")), "O(1)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn compound_update_key_and_membership_operands_coerce() {
    let box_of = "{ valueOf() { return quadratic(xs); } }";
    let key = "const key = { toString() { quadratic(xs); return 'k'; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ let box: any = {box_of}; box += 1; return box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ let box: any = {box_of}; box++; return box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{ v: {box_of} as any }}; o.v += 1; return o.v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} const o: any = {{}}; return o[key as any]; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {key} return (key as any) in {{}}; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const o = {{ length: {box_of} }}; return +o.length; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const unused = {box_of}; const ys = [1, 2]; const o: any = {{}}; const named = o['k']; const indexed = o[0]; return ys.length * 2; }}")), "O(1)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn destructuring_patterns_read_getters_and_iterate_sources() {
    let getter = "const box = { get value() { return quadratic(xs); } };";
    let it = "const it = { [Symbol.iterator]() { return { next() { quadratic(xs); return { done: false, value: 1 }; } }; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {getter} const {{ value }} = box; return value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {getter} let value = 0; ({{ value }} = box); return value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {it} function take([a]: any) {{ return a; }} return take(it); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {getter} function take({{ value }}: any) {{ return value; }} return take(box); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {it} const {{ p: [a] }} = {{ p: it }}; return a; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {it} let t = 0; for (const [a] of [it, it]) t += a; return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {getter} let t = 0; for (const {{ value }} of [box, box]) t += value; return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {it} try {{ throw it; }} catch ([a]) {{ return a; }} }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const {{ a, b }} = {{ a: 1, b: xs }}; return a + b.length; }}")), "O(1)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn delegated_yields_and_head_targets_run_the_protocol_per_visit() {
    let it = "const it = { [Symbol.iterator]() { let count = 0; return { next() { quadratic(xs); return { done: count++ >= xs.length, value: 1 }; } }; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nfunction* walk(xs: number[]) {{ {it} yield* it; }}\nexport function selected(xs: number[]) {{ for (const v of walk(xs)) void v; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ set p(v: number) {{ quadratic(xs); }} }}; for (box.p of xs) {{}} }}")), "O(N^3)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn iterators_close_on_every_abrupt_path_out_of_the_body() {
    let closing = "const it = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { quadratic(xs); return { done: true, value: 0 }; } }; } };";
    let thrower = "function thrower(x: number): void { if (x > 1) throw 0; }";
    let cases = [
        (index_of(format!("{QUADRATIC}\n{thrower}\nexport function selected(xs: number[]) {{ {closing} for (const v of it) {{ thrower(v); }} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nfunction* walk(xs: number[]) {{ {closing} for (const v of it) {{ yield v; }} }}\nexport function selected(xs: number[]) {{ for (const v of walk(xs)) void v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {closing} for (const v of it) {{ await v; }} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} for (const v of it) {{ switch (v) {{ case 1: break; }} }} }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} let t = 0; for (const v of it) {{ t += v; }} return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} const box = {{ get bad(): number {{ throw 0; }} }}; let t = 0; for (const v of it) {{ t = box.bad; }} return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} const o: {{ p?: {{ q: number }} }} = {{}}; let t = 0; for (const v of it) {{ t = o.p!.q; }} return t; }}")), "O(N^2)", false),
    ];

    assert_selected(&cases);
}

#[test]
fn deferred_code_in_classes_keeps_ordinary_receiver_resolution() {
    let cases = [
        (index_of("export class K { static h(xs: number[]) { for (const x of xs) void x; } static s = (xs: number[]) => { this.h(xs); }; }\nexport function selected(xs: number[]) { K.s(xs); }".to_string()), "O(N)", true),
        (index_of("export class I { m(xs: number[]) { for (const x of xs) void x; } f = (xs: number[]) => this.m(xs); }\nexport function selected(xs: number[]) { new I().f(xs); }".to_string()), "O(N)", true),
        (index_of("export class K { static h(xs: number[]) { for (const x of xs) void x; return 1; } static v = this.h([]); }\nexport function selected(xs: number[]) { K.h(xs); }".to_string()), "O(N)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return 1; }} v = () => this.m(); }} const b = new Box(); (b as any).m = () => quadratic(xs); return b.v(); }}")), "O(1)", true),
    ];

    assert_selected(&cases);
}

#[test]
fn unresolved_iteration_protocols_leave_multiplicity_unproven() {
    let set = "export function set(t: any, k: string, v: any) { t[k] = v; }";
    let indexed =
        "/** @perf O(xs^2) */\nfunction quadratic(xs: number[]): number { return xs.length; }";
    let cases = [
        (format!("{set}\nexport function selected(xs: number[]) {{ let t = 0; for (const a of xs) for (const b of xs) t += a * b; return t; }}"), "O(1)", UnknownReason::Bound),
        (format!("{set}\n{indexed}\nexport function selected(xs: number[]) {{ let t = 0; for (const a of xs) t += quadratic(xs); return t; }}"), "O(N^2)", UnknownReason::Bound),
    ];

    assert_reasons(&cases);

    let controls = [(
        index_of("export function selected(xs: number[]) { let t = 0; for (const a of xs) for (const b of xs) t += a * b; return t; }".to_string()),
        "O(N^2)",
        false,
    )];

    assert_selected(&controls);
}

#[test]
fn instance_checks_invoke_their_known_has_instance_implementations() {
    let marker = "class Marker { static [Symbol.hasInstance](value: unknown) { return quadratic(xs) > 0; } }";
    let literal =
        "const marker = { [Symbol.hasInstance](value: unknown) { return quadratic(xs) > 0; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], value: unknown) {{ {marker} return value instanceof Marker; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], value: unknown) {{ {literal} return value instanceof (marker as any); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], value: unknown) {{ class Marker {{}} Object.defineProperty(Marker, Symbol.hasInstance, {{ value: () => quadratic(xs) > 0 }}); return value instanceof Marker; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {marker} let total = 0; for (const x of xs) if (x instanceof Marker) total += x; return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\n{marker}\nexport function selected(value: unknown, constructor: Function) {{ return value instanceof constructor; }}")), "O(1)", true),
    ];

    assert_selected(&cases);

    let controls = [
        (index_of(format!("{QUADRATIC}\n{marker}\nexport function selected(value: unknown) {{ class Plain {{ v = 1; }} return value instanceof Plain; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{marker}\nexport function selected(xs: number[], value: unknown) {{ class Plain {{ v = 1; }} let total = 0; for (const x of xs) if (value instanceof Plain) total += x; return total; }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown) {{ class Plain {{ v = 1; }} return value instanceof Plain; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown, constructor: Function) {{ return value instanceof constructor; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown) {{ return value instanceof Error; }}")), "O(1)", false),
    ];

    assert_selected(&controls);
}

#[test]
fn awaits_invoke_their_known_then_implementations() {
    let thenable =
        "const thenable = { then(resolve: (value: number) => void) { quadratic(xs); } };";
    let class_thenable =
        "class Thenable { then(resolve: (value: number) => void) { quadratic(xs); } }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {thenable} return await (thenable as unknown as Promise<number>); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {class_thenable} return await (new Thenable() as unknown as Promise<number>); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ const box = {{ get then() {{ quadratic(xs); return undefined; }} }}; return await (box as any); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {thenable} let total = 0; for (const x of xs) total += await (thenable as unknown as Promise<number>); return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(value: any) {{ return await value; }}")), "O(1)", true),
    ];

    assert_selected(&cases);

    let controls = [
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nasync function producer() {{ return 1; }}\nexport async function selected() {{ return await producer(); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(source: Promise<number>) {{ return await source; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected() {{ return await Promise.resolve(1); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nasync function producer() {{ return 1; }}\nexport async function selected(xs: number[]) {{ let total = 0; for (const x of xs) total += await producer(); return total; }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(value: number) {{ return await value; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(rows: AsyncIterable<number>) {{ let total = 0; for await (const row of rows) total += row; return total; }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(value: any) {{ return await value; }}")), "O(1)", false),
    ];

    assert_selected(&controls);
}

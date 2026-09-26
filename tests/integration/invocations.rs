use std::collections::BTreeSet;

use olint::analysis::TypeMode;
use olint::cost::Cost;
use olint::unknowns::UnknownReason;

use crate::support;

use support::{assert_projected_selected, index_of, selected_result_in};

const QUADRATIC: &str = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }";

fn assert_reasons(cases: &[(String, &str, UnknownReason)]) {
    for types in [TypeMode::Syntactic, TypeMode::Tsc] {
        for (source, expected, reason) in cases {
            let (cost, reasons): (Cost, BTreeSet<UnknownReason>) =
                selected_result_in(&[("index.ts", source.as_str())], types);

            assert_eq!(
                support::projected_class_of(&cost),
                Cost::parse(expected).unwrap(),
                "{types:?} {source}"
            );
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

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
}

#[test]
fn iterator_protocols_charge_acquisition_each_visit_and_applicable_close() {
    let next = "{ [Symbol.iterator]() { let count = 0; return { next() { quadratic(xs); return { done: count++ >= xs.length, value: count }; } }; } }";
    let closing = "{ [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { quadratic(xs); return { done: true, value: 0 }; } }; } }";
    let cubic = "{ [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { for (const x of xs) quadratic(xs); return { done: true, value: 0 }; } }; } }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {next}; for (const value of iterable) {{}} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {next}; return [...iterable]; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Walk {{ [Symbol.iterator]() {{ return this; }} next() {{ quadratic(xs); return {{ done: true, value: 0 }}; }} }} for (const v of new Walk()) {{}} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {{ *[Symbol.iterator]() {{ yield quadratic(xs); }} }}; for (const v of iterable) {{}} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const value of iterable) {{ if (value) break; }} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const x of xs) {{ for (const value of iterable) {{ break; }} }} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; for (const value of iterable) {{ blk: {{ break blk; }} }} }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; for (const value of iterable) {{ switch (value) {{ case 1: break; }} }} }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; outer: for (const value of iterable) {{ continue outer; }} }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {cubic}; outer: for (const value of iterable) {{ for (const x of xs) {{ break outer; }} }} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; const [a, b] = iterable; return a + b; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const iterable = {closing}; for (const value of iterable) {{ void value; }} }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ let total = 0; for (const x of xs) for (const y of xs) total += x + y; return total; }}")), "O(N^2)", false),
    ];

    assert_projected_selected(&cases);
    assert_iteration_bounds(
        &cases,
        &[
            (0, true),
            (1, true),
            (2, false),
            (3, false),
            (6, true),
            (7, true),
            (8, true),
            (11, true),
        ],
    );
}

#[test]
fn unknown_implementations_keep_proven_multiplicity_and_surrounding_work() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(tag: (parts: TemplateStringsArray) => number, xs: number[], n: number) {{ let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) total += tag`x` + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(descriptor: PropertyDescriptor, xs: number[], n: number) {{ const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', descriptor); let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) total += o.v + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(f: () => number, xs: number[], n: number) {{ const box = {{ valueOf() {{ return 1; }} }}; box.valueOf = f; let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) total += +box + quadratic(xs); return total; }}")), "O(N^3)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(step: () => IteratorResult<number>, xs: number[]) {{ const iterator = {{ next(): IteratorResult<number> {{ return {{ done: true, value: 0 }}; }} }}; iterator.next = step; const iterable = {{ [Symbol.iterator]() {{ return iterator; }} }}; let total = 0; for (const v of iterable) total += quadratic(xs); return total; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport class Keys {{ [Symbol.iterator]() {{ return [1].values(); }} }}\nexport function selected(items: Iterable<number>, xs: number[]) {{ let total = 0; for (const v of items) total += quadratic(xs); return total; }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport class Keys {{ [Symbol.iterator]() {{ return [1].values(); }} }}\nexport function selected(xs: number[]) {{ let total = 0; for (const x of xs) total += quadratic(xs); return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nclass Holder {{ get value() {{ return 1; }} }}\nexport function selected(o: {{ value: number }}, xs: number[], n: number) {{ let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) total += o.value + quadratic(xs); return total + new Holder().value; }}")), "O(N^3)", true),
    ];

    assert_projected_selected(&cases);
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
        (index_of("export function selected(xs: number[]) { const box = { get grow() { return 0; } }; let total = 0; for (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 1000000000; i++) total += box.grow; return total; }".to_string()), "O(N)", false),
        (index_of("export function selected(xs: number[]) { const box = { toString() { return ''; } }; let text = ''; for (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 1000000000; i++) text += `${box}`; return text; }".to_string()), "O(N)", false),
    ];

    assert_projected_selected(&controls);
}

#[test]
fn builtin_accessors_and_replaced_iterators_keep_fresh_arrays_variable() {
    let cases = [
        (index_of("Object.defineProperty(Array.prototype, 'grow', { get(this: number[]) { this.push(1); return 0; } });\nexport function selected(n: number) { const xs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) { total += (xs as unknown as { grow: number }).grow; for (const x of xs) total += x; } return total; }".to_string()), "O(N^2)", false),
        (index_of("export function selected(n: number) { const ys: number[] = [1, 2, 3]; const it: any = [][Symbol.iterator](); it.__proto__.next = function () { return { done: true, value: 0 }; }; let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) { for (const y of ys) total += y; } return total; }".to_string()), "O(N)", true),
        (index_of("export function selected(n: number) { const zs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n && n >= 0 && n <= 1000000000; i++) { total += (zs as unknown as { grow: number }).grow; for (const z of zs) total += z; } return total; }".to_string()), "O(N)", false),
    ];

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
}

#[test]
fn functions_passed_as_values_receive_their_forwarded_arguments() {
    let slow = "function slow(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; return true; }";
    let cases = [
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ t.includes = v; }}\nfunction apply(f: (t: any, v: unknown) => void, xs: number[]) {{ f(Array.prototype, () => slow(xs)); }}\nexport function selected(xs: number[]) {{ set(new Set<number>(), null); apply(set, xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ t.includes = v; }}\nfunction apply(f: (t: any, v: unknown) => void, xs: number[]) {{ const g = f; g(Array.prototype, () => slow(xs)); }}\nexport function selected(xs: number[]) {{ apply(set, xs); const zs = [1]; return zs.includes(0); }}")), "O(N)", true),
    ];

    assert_projected_selected(&cases);
}

#[test]
fn reference_valued_implementations_enter_the_protocol_index() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const heavy = () => quadratic(xs); const box = {{ xs, valueOf: heavy }}; return +(box as any); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const heavy = () => {{ quadratic(xs); return ''; }}; class Box {{ toString = heavy; }} return `${{new Box()}}`; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function* walk() {{ for (const x of xs) yield quadratic(xs); }} const it = {{ [Symbol.iterator]: walk }}; for (const v of it) void v; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const getV = () => quadratic(xs); const o = {{}} as {{ v: number }}; Object.defineProperty(o, 'v', {{ get: getV }}); return o.v; }}")), "O(N^2)", false),
    ];

    assert_projected_selected(&cases);
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
        (index_of(format!("{QUADRATIC}\nfunction lengthOf(a: number[]) {{ return a.length; }}\nexport function selected(xs: number[]) {{ class Long {{ get length() {{ return quadratic(xs); }} }} return lengthOf(new Long() as any); }}")), "O(N^2)", false),
    ];

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
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

    assert_projected_selected(&cases);
}

#[test]
fn delegated_yields_and_head_targets_run_the_protocol_per_visit() {
    let it = "const it = { [Symbol.iterator]() { let count = 0; return { next() { quadratic(xs); return { done: count++ >= xs.length, value: 1 }; } }; } };";
    let cases = [
        (index_of(format!("{QUADRATIC}\nfunction* walk(xs: number[]) {{ {it} yield* it; }}\nexport function selected(xs: number[]) {{ for (const v of walk(xs)) void v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const box = {{ set p(v: number) {{ quadratic(xs); }} }}; for (box.p of xs) {{}} }}")), "O(N^3)", false),
    ];

    assert_projected_selected(&cases);
    assert_iteration_bounds(&cases, &[(0, true), (1, false)]);
}

#[test]
fn iterators_close_on_every_abrupt_path_out_of_the_body() {
    let closing = "const it = { [Symbol.iterator]() { return { next() { return { done: false, value: 1 }; }, return() { quadratic(xs); return { done: true, value: 0 }; } }; } };";
    let thrower = "function thrower(x: number): void { if (x > 1) throw 0; }";
    let cases = [
        (index_of(format!("{QUADRATIC}\n{thrower}\nexport function selected(xs: number[]) {{ {closing} for (const v of it) {{ thrower(v); }} }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nfunction* walk(xs: number[]) {{ {closing} for (const v of it) {{ yield v; }} }}\nexport function selected(xs: number[]) {{ for (const v of walk(xs)) void v; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {closing} for (const v of it) {{ await v; }} }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} for (const v of it) {{ switch (v) {{ case 1: break; }} }} }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} let t = 0; for (const v of it) {{ t += v; }} return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} const box = {{ get bad(): number {{ throw 0; }} }}; let t = 0; for (const v of it) {{ t = box.bad; }} return t; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ {closing} const o: {{ p?: {{ q: number }} }} = {{}}; let t = 0; for (const v of it) {{ t = o.p!.q; }} return t; }}")), "O(N^2)", false),
    ];

    assert_projected_selected(&cases);
    assert_iteration_bounds(&cases, &[(3, true)]);
}

#[test]
fn deferred_code_in_classes_keeps_ordinary_receiver_resolution() {
    let cases = [
        (index_of("export class K { static h(xs: number[]) { for (const x of xs) void x; } static s = (xs: number[]) => { this.h(xs); }; }\nexport function selected(xs: number[]) { K.s(xs); }".to_string()), "O(N)", true),
        (index_of("export class I { m(xs: number[]) { for (const x of xs) void x; } f = (xs: number[]) => this.m(xs); }\nexport function selected(xs: number[]) { new I().f(xs); }".to_string()), "O(N)", true),
        (index_of("export class K { static h(xs: number[]) { for (const x of xs) void x; return 1; } static v = this.h([]); }\nexport function selected(xs: number[]) { K.h(xs); }".to_string()), "O(N)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return 1; }} v = () => this.m(); }} const b = new Box(); (b as any).m = () => quadratic(xs); return b.v(); }}")), "O(1)", true),
    ];

    assert_projected_selected(&cases);
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

    assert_projected_selected(&controls);
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

    assert_projected_selected(&cases);

    let controls = [
        (index_of(format!("{QUADRATIC}\n{marker}\nexport function selected(value: unknown) {{ class Plain {{ v = 1; }} return value instanceof Plain; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{marker}\nexport function selected(xs: number[], value: unknown) {{ class Plain {{ v = 1; }} let total = 0; for (const x of xs) if (value instanceof Plain) total += x; return total; }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown) {{ class Plain {{ v = 1; }} return value instanceof Plain; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown, constructor: Function) {{ return value instanceof constructor; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(value: unknown) {{ return value instanceof Error; }}")), "O(1)", false),
    ];

    assert_projected_selected(&controls);
}

#[test]
fn awaits_invoke_their_known_then_implementations() {
    let thenable =
        "const thenable = { then(resolve: (value: number) => void) { quadratic(xs); } };";
    let class_thenable =
        "class Thenable { then(resolve: (value: number) => void) { quadratic(xs); } }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {thenable} return await (thenable as unknown as Promise<number>); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {class_thenable} return await (new Thenable() as unknown as Promise<number>); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ const box = {{ get then() {{ quadratic(xs); return undefined; }} }}; return await (box as any); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport async function selected(xs: number[]) {{ {thenable} let total = 0; for (const x of xs) total += await (thenable as unknown as Promise<number>); return total; }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(value: any) {{ return await value; }}")), "O(1)", true),
    ];

    assert_projected_selected(&cases);

    let controls = [
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nasync function producer() {{ return 1; }}\nexport async function selected() {{ return await producer(); }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(source: Promise<number>) {{ return await source; }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected() {{ return await Promise.resolve(1); }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nasync function producer() {{ return 1; }}\nexport async function selected(xs: number[]) {{ let total = 0; for (const x of xs) total += await producer(); return total; }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(value: number) {{ return await value; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{class_thenable}\nexport async function selected(rows: AsyncIterable<number>) {{ let total = 0; for await (const row of rows) total += row; return total; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport async function selected(value: any) {{ return await value; }}")), "O(1)", true),
    ];

    assert_projected_selected(&controls);
}

const JSX_WORK: &str = "export function quadratic(xs: number[]) { let t = 0; for (const a of xs) for (const b of xs) t += a * b; return t; }\nexport function Cube(props: { xs: number[] }) { let t = 0; for (const a of props.xs) for (const b of props.xs) for (const c of props.xs) t += a * b * c; return t; }\n";
const STORING_FACTORY: &str = "export function h(type: any, props: any, ...children: any[]) { return { type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
const CALLING_FACTORY: &str = "export function h(type: any, props: any, ...children: any[]) { return typeof type === \"function\" ? type(props) : { type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
const STORING_RUNTIME: &str =
    "export function jsx(type, props, key) { return { type, props, key }; }\n";
const CALLING_RUNTIME: &str = "export function jsx(type, props, key) { return typeof type === \"function\" ? type(props) : { type, props, key }; }\n";
const RUNTIME_FRAGMENT: &str = "export function Fragment(props) { return props; }\n";
const LIBRARY_PACKAGE: &str = r#"{ "name": "lib", "type": "module", "exports": { ".": "./index.js", "./jsx-runtime": "./jsx-runtime.js", "./jsx-dev-runtime": "./jsx-dev-runtime.js" } }"#;
const CLASSIC_OPTIONS: &str =
    r#", "jsx": "react", "jsxFactory": "h", "jsxFragmentFactory": "Fragment""#;
const AUTOMATIC_OPTIONS: &str = r#", "jsx": "react-jsx", "jsxImportSource": "lib""#;
const CLASSIC_IMPORTS: &str =
    "import { h, Fragment } from \"./h\";\nimport { quadratic, Cube } from \"./work\";\n";
const AUTOMATIC_IMPORTS: &str = "import { quadratic, Cube } from \"./work\";\n";

fn jsx_options_of(options: &str) -> String {
    format!(
        r#"{{ "compilerOptions": {{ "strict": true, "noEmit": true, "module": "esnext", "moduleResolution": "bundler", "target": "es2022", "types": []{options} }}, "include": ["src"] }}"#
    )
}

fn jsx_project_of(
    options: &str,
    index: &str,
    extra: &[(&'static str, &str)],
) -> Vec<(&'static str, String)> {
    let mut files = vec![
        ("tsconfig.json", jsx_options_of(options)),
        ("src/index.tsx", index.to_string()),
        ("src/work.ts", JSX_WORK.to_string()),
    ];

    for (name, source) in extra {
        files.retain(|(existing, _)| existing != name);
        files.push((name, source.to_string()));
    }

    files
}

fn jsx_library_of(jsx: &str, jsxs: &str, fragment: &str) -> String {
    format!("{jsx}{jsxs}{fragment}")
}

#[test]
fn classic_jsx_factories_resolve_through_their_scope() {
    let classic = |body: &str, factory: &str, expected: &'static str, partial: bool| {
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{body}\n"),
                &[("src/h.ts", factory)],
            ),
            expected,
            partial,
        )
    };
    let fragment_factory = CALLING_FACTORY.replace(
        "export function Fragment(props: any) { return props; }",
        "import { quadratic } from \"./work\";\nexport function Fragment(props: any) { return quadratic(props.xs); }",
    );
    let cases = [
        classic("export function selected() { return <div />; }", STORING_FACTORY, "O(1)", false),
        classic("export function selected(xs: number[]) { return <Cube xs={xs} />; }", CALLING_FACTORY, "O(N^3)", false),
        classic("export function selected(xs: number[]) { return <Cube xs={xs} />; }", STORING_FACTORY, "O(1)", false),
        classic("export function selected() { return <div />; }", CALLING_FACTORY, "O(1)", true),
        classic("export function selected(xs: number[]) { return <>{1}</>; }", &fragment_factory, "O(N^2)", false),
        classic("export function selected(xs: number[]) { return xs.map(() => <Cube xs={xs} />); }", CALLING_FACTORY, "O(N^4)", false),
        (jsx_project_of(r#", "jsx": "react""#, &format!("/** @jsx h */\n{CLASSIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(N^3)", false),
        (jsx_project_of(r#", "jsx": "react""#, &format!("{CLASSIC_IMPORTS}/** @jsx h */\nexport function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "react""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{quadratic(xs)}}</div>; }}\n"), &[]), "O(N^2)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "R.h""#, &format!("import * as R from \"./h\";\n{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(N^3)", false),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "R.h""#, &format!("import * as R from \"./h\";\n{AUTOMATIC_IMPORTS}export const lens = {{ get h() {{ return 1; }} }};\nexport function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(N^3)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "h""#, &format!("{AUTOMATIC_IMPORTS}let h = (type: any, props: any) => type(props);\nexport function swap() {{ h = () => 0; }}\nexport function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "react-jsx""#, &format!("/**\n * @jsxRuntime classic\n * @jsx h\n */\n{CLASSIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(N^3)", false),
        (jsx_project_of(r#", "jsx": "react-jsx""#, &format!("/** @jsxRuntime classic @jsx h */\n{CLASSIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(1)", true),
    ];

    support::assert_project_cases("src/index.tsx", &cases);
}

#[test]
fn automatic_jsx_runtimes_resolve_through_the_runtime_graph() {
    let automatic = |options: &str,
                     body: &str,
                     runtime: &str,
                     extra: &[(&'static str, &str)],
                     expected: &'static str,
                     partial: bool| {
        let mut files = jsx_project_of(options, &format!("{AUTOMATIC_IMPORTS}{body}\n"), extra);

        files.push(("node_modules/lib/package.json", LIBRARY_PACKAGE.to_string()));
        files.push(("node_modules/lib/jsx-runtime.js", runtime.to_string()));

        (files, expected, partial)
    };
    let calling = jsx_library_of(
        CALLING_RUNTIME,
        "export const jsxs = jsx;\n",
        RUNTIME_FRAGMENT,
    );
    let storing = jsx_library_of(
        STORING_RUNTIME,
        "export const jsxs = jsx;\n",
        RUNTIME_FRAGMENT,
    );
    let static_calling = jsx_library_of(
        STORING_RUNTIME,
        "export function jsxs(type, props, key) { return type(props); }\n",
        RUNTIME_FRAGMENT,
    );
    let fragment_calling = jsx_library_of(
        CALLING_RUNTIME,
        "export const jsxs = jsx;\n",
        "import { quadratic } from \"./work.js\";\nexport function Fragment(props) { return quadratic(props.xs); }\n",
    );
    let library_work = "export function quadratic(xs) { let t = 0; for (const a of xs) for (const b of xs) t += a * b; return t; }\n";
    let create =
        "export function createElement(type, props, ...children) { return type(props); }\n";
    let render = [
        (
            "node_modules/dom/package.json",
            r#"{ "name": "dom", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/dom/index.d.ts",
            "export declare function render(element: unknown): void;\n",
        ),
    ];
    let pragma = "/** @jsxImportSource lib */\nimport { Cube } from \"./work\";\nexport function selected(xs: number[]) { return <Cube xs={xs} />; }\n";
    let cases = [
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs} />; }", &calling, &[], "O(N^3)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs} />; }", &storing, &[], "O(1)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs}>{1}{2}</Cube>; }", &static_calling, &[], "O(N^3)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs}>{1}</Cube>; }", &static_calling, &[], "O(1)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs}>\n  {1}\n</Cube>; }", &static_calling, &[], "O(1)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <Cube xs={xs}>{...[1]}</Cube>; }", &static_calling, &[], "O(N^3)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[]) { return <>{1}</>; }", &fragment_calling, &[("node_modules/lib/work.js", library_work)], "O(1)", true),
        automatic(AUTOMATIC_OPTIONS, "function Fragment(props:{xs:number[]}){return quadratic(props.xs);} export function selected(xs:number[]){return <Fragment xs={xs}/>;}", &calling, &[], "O(N^2)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[], rest: {}) { return <Cube {...rest} xs={xs} key=\"k\" />; }", &storing, &[("node_modules/lib/index.js", create)], "O(N^3)", false),
        automatic(AUTOMATIC_OPTIONS, "export function selected(xs: number[], rest: {}) { return <Cube key=\"k\" {...rest} xs={xs} />; }", &storing, &[("node_modules/lib/index.js", create)], "O(N)", false),
        automatic(r#", "jsx": "react-jsxdev", "jsxImportSource": "lib""#, "export function selected(xs: number[]) { return <Cube xs={xs} />; }", &storing, &[("node_modules/lib/jsx-dev-runtime.js", "export function jsxDEV(type, props) { return type(props); }\n")], "O(N^3)", false),
        automatic(r#", "jsx": "react""#, "", &calling, &[("src/index.tsx", pragma)], "O(N^3)", false),
        automatic(AUTOMATIC_OPTIONS, "import { render } from \"dom\";\nexport function selected(xs: number[]) { render(<Cube xs={xs} />); }", &storing, &render, "O(1)", true),
        (jsx_project_of(r#", "jsx": "react-jsx""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{quadratic(xs)}}</div>; }}\n"), &[]), "O(N^2)", true),
        (jsx_project_of(r#", "jsx": "react-jsx""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("node_modules/react/package.json", r#"{ "name": "react", "exports": { ".": "./index.js", "./jsx-runtime": "./jsx-runtime.js" } }"#), ("node_modules/react/jsx-runtime.js", "'use strict';\nif (process.env.NODE_ENV === 'production') { module.exports = require('./production.js'); } else { module.exports = require('./development.js'); }\n"), ("node_modules/react/production.js", "exports.jsx = function (type, props) { return type(props); };\n"), ("node_modules/react/development.js", "exports.jsx = function (type, props) { return type(props); };\n")]), "O(1)", true),
    ];

    support::assert_project_cases("src/index.tsx", &cases);
}

#[test]
fn untransformed_jsx_keeps_element_creation_unknown() {
    let cases = [
        (jsx_project_of(r#", "jsx": "preserve""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[]), "O(1)", true),
        (jsx_project_of("", &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{quadratic(xs)}}</div>; }}\n"), &[]), "O(N^2)", true),
        (jsx_project_of(r#", "jsx": "react-native""#, &format!("{AUTOMATIC_IMPORTS}export function selected() {{ return <div />; }}\n"), &[]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "preserve""#, &format!("/** @jsx h */\n{CLASSIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(1)", true),
    ];

    support::assert_project_cases("src/index.tsx", &cases);

    let owned = |second: &str| {
        let runtime = jsx_library_of(
            CALLING_RUNTIME,
            "export const jsxs = jsx;\n",
            RUNTIME_FRAGMENT,
        );
        let owner = |options: &str| {
            format!(
                r#"{{ "compilerOptions": {{ "strict": true, "noEmit": true, "composite": true, "module": "esnext", "moduleResolution": "bundler"{options} }}, "include": ["../src"] }}"#
            )
        };

        vec![
            ("tsconfig.json", r#"{ "files": [], "references": [{ "path": "./a" }, { "path": "./b" }] }"#.to_string()),
            ("a/tsconfig.json", owner(AUTOMATIC_OPTIONS)),
            ("b/tsconfig.json", owner(second)),
            ("src/index.tsx", format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n")),
            ("src/work.ts", JSX_WORK.to_string()),
            ("node_modules/lib/package.json", LIBRARY_PACKAGE.to_string()),
            ("node_modules/lib/jsx-runtime.js", runtime),
        ]
    };
    let owners = [
        (owned(r#", "jsx": "preserve""#), "O(1)", true),
        (owned(AUTOMATIC_OPTIONS), "O(N^3)", false),
    ];

    support::assert_project_cases("src/index.tsx", &owners);
}

#[test]
fn jsx_factory_invocations_carry_their_effects() {
    let writing = "export function h(type: any, props: any, ...children: any[]) { props.items.add(props.items.size); return { type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
    let passing = "export function selected(s: Set<number>) { let t = 0; for (const x of s) { const e = <li items={s}>{x}</li>; t += 1; } return t; }";
    let plain = "export function selected(s: Set<number>) { let t = 0; for (const x of s) { const e = <li>{x}</li>; t += 1; } return t; }";
    let cases = [
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{passing}\n"),
                &[("src/h.ts", STORING_FACTORY)],
            ),
            "O(N)",
            false,
        ),
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{plain}\n"),
                &[("src/h.ts", STORING_FACTORY)],
            ),
            "O(N)",
            false,
        ),
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{passing}\n"),
                &[("src/h.ts", writing)],
            ),
            "O(1)",
            true,
        ),
        (
            jsx_project_of(
                r#", "jsx": "preserve""#,
                &format!("{AUTOMATIC_IMPORTS}{passing}\n"),
                &[],
            ),
            "O(1)",
            true,
        ),
    ];

    support::assert_project_cases("src/index.tsx", &cases);
}

#[test]
fn jsx_components_run_once_through_the_factory_and_runtimes_never_execute() {
    let files = jsx_project_of(
        AUTOMATIC_OPTIONS,
        &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"),
        &[],
    );
    let runtime = format!(
        "import {{ writeFileSync }} from \"node:fs\";\nwriteFileSync(new URL(\"./executed.txt\", import.meta.url), \"runtime\");\nthrow new Error(\"executed\");\n{}",
        jsx_library_of(CALLING_RUNTIME, "export const jsxs = jsx;\n", RUNTIME_FRAGMENT)
    );
    let mut sources: Vec<(&str, &str)> = files
        .iter()
        .map(|(name, source)| (*name, source.as_str()))
        .collect();

    sources.push(("node_modules/lib/package.json", LIBRARY_PACKAGE));
    sources.push(("node_modules/lib/jsx-runtime.js", runtime.as_str()));

    let directory = support::project_of(&sources);

    for types in [TypeMode::Syntactic, TypeMode::Tsc] {
        let (cost, reasons, labels) =
            support::project_result_in(directory.path(), "src/index.tsx", types);
        let factories = labels
            .iter()
            .filter(|label| label.contains("[jsx factory]"))
            .count();
        let components = labels
            .iter()
            .filter(|label| label.contains("[callback parameter]"))
            .count();

        assert_eq!(cost, Cost::parse("O(N^3)").unwrap(), "{types:?}");
        assert!(reasons.is_empty(), "{types:?}: {reasons:?}");
        assert_eq!((factories, components), (1, 1), "{types:?}: {labels:?}");
    }

    assert!(!directory
        .path()
        .join("node_modules/lib/executed.txt")
        .exists());
}

#[test]
fn jsx_factory_arguments_follow_the_emitted_call() {
    let cases = [
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "h""#, &format!("{AUTOMATIC_IMPORTS}function h(type: any, props: any) {{ return props.work(); }}\nexport function selected(xs: number[]) {{ return <div work={{() => quadratic(xs)}} />; }}\n"), &[]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "R.h""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ const R = {{ get h() {{ quadratic(xs); return (type: any, props: any) => props; }} }}; return <div />; }}\n"), &[]), "O(N^2)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "h", "jsxFragmentFactory": "R.Fragment""#, &format!("{CLASSIC_IMPORTS}export function selected(xs: number[]) {{ const R = {{ get Fragment() {{ quadratic(xs); return () => 1; }} }}; return <>{{1}}</>; }}\n"), &[("src/h.ts", STORING_FACTORY)]), "O(N^2)", false),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "h""#, &format!("import * as R from \"./h\";\n{AUTOMATIC_IMPORTS}const h = R.h;\nexport function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", CALLING_FACTORY)]), "O(N^3)", true),
        (jsx_project_of(r#", "jsx": "react""#, &format!("/**\n * @jsx h\n * @jsx g\n */\nimport {{ h, g }} from \"./h\";\n{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("src/h.ts", &format!("{CALLING_FACTORY}export function g(type: any, props: any) {{ return {{ type, props }}; }}\n"))]), "O(N^3)", false),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "R.h", "jsxFragmentFactory": "R.Fragment""#, &format!("import * as R from \"./h\";\n{AUTOMATIC_IMPORTS}export const lens = {{ get Fragment() {{ return 1; }} }};\nexport function selected(xs: number[]) {{ return <>{{1}}</>; }}\n"), &[("src/h.ts", STORING_FACTORY)]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "h""#, &format!("{AUTOMATIC_IMPORTS}function h(type: any, props: any) {{ return type(props); }}\nexport function swap() {{ (h as any) = () => 0; }}\nexport function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[]), "O(1)", true),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "k""#, &format!("import {{ k }} from \"./h\";\n{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{1}}{{() => quadratic(xs)}}</div>; }}\n"), &[("src/h.ts", "export function k(type: any, props: any, first: any, second: any) { return typeof second === \"function\" ? second() : 0; }\n")]), "O(N^2)", false),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "nest""#, &format!("import {{ nest }} from \"./h\";\n{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{...xs}}</div>; }}\n"), &[("src/h.ts", "export function nest(type: any, props: any, ...children: any[]) { let t = 0; for (const c of children) for (const d of children) t += 1; return t; }\n")]), "O(N^2)", false),
        (jsx_project_of(r#", "jsx": "react", "jsxFactory": "keys""#, &format!("import {{ keys }} from \"./h\";\n{AUTOMATIC_IMPORTS}export function selected(o: Record<string, number>) {{ return <div {{...o}} />; }}\n"), &[("src/h.ts", "export function keys(type: any, props: any, ...children: any[]) { let t = 0; for (const a in props) for (const b in props) t += 1; return t; }\n")]), "O(N^2)", false),
        (jsx_project_of(AUTOMATIC_OPTIONS, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}}>{{/* note */}}{{1}}</Cube>; }}\n"), &[("node_modules/lib/package.json", LIBRARY_PACKAGE), ("node_modules/lib/jsx-runtime.js", "export function jsx(type, props) { return { type, props }; }\nexport function jsxs(type, props) { return type(props); }\n")]), "O(1)", false),
        (jsx_project_of(r#", "jsx": "preserve""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <div>{{...xs}}</div>; }}\n"), &[]), "O(N)", true),
        (jsx_project_of(r#", "jsx": "preserve""#, &format!("{AUTOMATIC_IMPORTS}export function selected(xs: number[]) {{ return <Cube xs={{xs}} />; }}\n"), &[("node_modules/react/package.json", r#"{ "name": "react", "type": "module", "exports": { "./jsx-runtime": "./jsx-runtime.js" } }"#), ("node_modules/react/jsx-runtime.js", "export function jsx(type, props) { return type(props); }\nexport const jsxs = jsx;\n")]), "O(1)", true),
    ];

    support::assert_project_cases("src/index.tsx", &cases);
}

#[test]
fn jsx_spread_getters_follow_the_configured_output_target() {
    let mut cases = Vec::new();

    for (target, copied) in [("es2017", "O(N^2)"), ("es2018", "O(1)")] {
        for (attributes, expected) in [
            (
                "{...other} {...{get value() { quadratic(xs); return 0; }}}",
                copied,
            ),
            (
                "{...{...other, get value() { quadratic(xs); return 0; }}}",
                copied,
            ),
            (
                "a={1} {...other} z={2} {...{get value() { quadratic(xs); return 0; }}}",
                copied,
            ),
            (
                "{...{get value() { quadratic(xs); return 0; }}} {...other}",
                "O(1)",
            ),
            (
                "{...{get value() { quadratic(xs); return 0; }, ...other}}",
                "O(1)",
            ),
            ("{...other} {...{get value() { quadratic(xs); return 0; }}} value={0}", "O(1)"),
            ("{...other} {...{get value() { quadratic(xs); return 0; }}} {...{get value() { return 0; }}}", "O(1)"),
            ("{...other} {...{get value() { quadratic(xs); return 0; }, value: 0}}", "O(1)"),
            ("{...other} {...{get value() { quadratic(xs); return 0; }, set value(next: number) {}}}", copied),
            ("{...other} {...{get value() { quadratic(xs); return 0; }, [key]: 0}}", copied),
            ("{...other} {...{get [key]() { quadratic(xs); return 0; }, value: 0}}", copied),
        ] {
            let mut files = jsx_project_of(CLASSIC_OPTIONS, &format!("{CLASSIC_IMPORTS}export function selected(xs: number[], key: string) {{ const other = {{}}; return <div {attributes} />; }}\n"), &[("src/h.ts", STORING_FACTORY)]);

            files[0].1 = files[0].1.replace("es2022", target);

            cases.push((files, expected, false));
        }
    }

    for (files, expected, _) in cases {
        let sources: Vec<(&str, &str)> = files
            .iter()
            .map(|(name, text)| (*name, text.as_str()))
            .collect();

        for types in [TypeMode::Syntactic, TypeMode::Tsc] {
            let (cost, _, labels) = support::project_result_of(&sources, "src/index.tsx", types);
            let copied = expected == "O(N^2)";

            assert_eq!(
                labels
                    .iter()
                    .any(|label| label.contains("[jsx spread getter]")),
                copied,
                "{types:?}: {sources:?}: {labels:?}"
            );

            if copied {
                assert_eq!(
                    support::projected_class_of(&cost),
                    Cost::parse(expected).unwrap(),
                    "{types:?}: {sources:?}"
                );
            }
        }
    }
}

#[test]
fn jsx_passed_values_escape_into_the_factory() {
    let extending = "export function h(type: any, props: any, ...children: any[]) { props.extra = 1; return { type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
    let attribute = "export function selected(n: number) { const ys: number[] = []; let i = 0; while (i < ys.length + n && n >= 0 && n <= 1000000000) { const e = <li a={1} items={ys}>{i}</li>; i++; } return i; }";
    let child = "export function selected(n: number) { const ys: number[] = []; let i = 0; while (i < ys.length + n && n >= 0 && n <= 1000000000) { const e = <li>{i}{ys}</li>; i++; } return i; }";
    let plain = "export function selected(n: number) { const ys: number[] = []; let i = 0; while (i < ys.length + n && n >= 0 && n <= 1000000000) { const e = <li>{i}</li>; i++; } return i; }";
    let cases = [
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{attribute}\n"),
                &[("src/h.ts", STORING_FACTORY)],
            ),
            "O(N)",
            false,
        ),
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{attribute}\n"),
                &[("src/h.ts", extending)],
            ),
            "O(1)",
            true,
        ),
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{child}\n"),
                &[("src/h.ts", extending)],
            ),
            "O(1)",
            true,
        ),
        (
            jsx_project_of(
                CLASSIC_OPTIONS,
                &format!("{CLASSIC_IMPORTS}{plain}\n"),
                &[("src/h.ts", extending)],
            ),
            "O(N)",
            false,
        ),
        (
            jsx_project_of(
                r#", "jsx": "preserve""#,
                &format!("{AUTOMATIC_IMPORTS}{attribute}\n"),
                &[],
            ),
            "O(1)",
            true,
        ),
        (
            jsx_project_of(
                r#", "jsx": "preserve""#,
                &format!("{AUTOMATIC_IMPORTS}{plain}\n"),
                &[],
            ),
            "O(N)",
            true,
        ),
    ];

    for types in [TypeMode::Syntactic, TypeMode::Tsc] {
        for (files, expected, partial) in &cases {
            let files: Vec<_> = files
                .iter()
                .map(|(name, source)| (*name, source.as_str()))
                .collect();
            let (cost, reasons, _) = support::project_result_of(&files, "src/index.tsx", types);

            assert_eq!(
                support::projected_class_of(&cost),
                Cost::parse(expected).unwrap(),
                "{types:?} {files:?}"
            );
            assert_eq!(
                !reasons.is_empty(),
                *partial,
                "{types:?} {files:?}: {reasons:?}"
            );
        }
    }
}

fn assert_iteration_bounds(cases: &[support::SelectedCase<'_>], expected: &[(usize, bool)]) {
    for types in [TypeMode::Syntactic, TypeMode::Tsc] {
        for (index, unresolved) in expected {
            let (_, reasons) = support::selected_case_of(&cases[*index].0, types);

            assert_eq!(
                reasons.contains(&UnknownReason::Bound),
                *unresolved,
                "{types:?} {index}: {reasons:?}"
            );
        }
    }
}

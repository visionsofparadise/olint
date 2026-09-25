use olint::analysis::Analysis;
use olint::cost::Cost;
use olint::values::{Cardinality, Failure, Limits, Primitive, SizeQuantity};

use crate::support;

use support::{file_of, probe_results_of, probes_of, run_in_project, run_with_source, summary_of};

fn values_of(source: &str) -> Vec<Result<Primitive, Failure>> {
    probe_results_of(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |analysis, file, probe| {
            analysis
                .known_value(file, probe)
                .value
                .map(|value| (*value).clone())
        },
    )
}

#[test]
fn actual_primitives_and_computed_keys_preserve_language_distinctions() {
    let values = values_of("function f(){probe(2+3);probe(1n==1);probe(1n===1);probe(-0);probe(0/0);probe(1/0);probe('😀'.length);probe(1n+2);probe(+1n);probe(-'2');}");

    assert_eq!(values[0], Ok(Primitive::Number(5.0)));
    assert_eq!(values[1], Ok(Primitive::Boolean(true)));
    assert_eq!(values[2], Ok(Primitive::Boolean(false)));
    assert!(
        matches!(values[3], Ok(Primitive::Number(value)) if value.to_bits() == (-0.0f64).to_bits())
    );
    assert!(matches!(values[4], Ok(Primitive::Number(value)) if value.is_nan()));
    assert_eq!(values[5], Ok(Primitive::Number(f64::INFINITY)));
    assert_eq!(values[6], Ok(Primitive::Number(2.0)));
    assert!(values[7..].iter().all(Result::is_err));

    let keys = probe_results_of(&[("tsconfig.json", "{}"), ("index.ts", "function f(){probe(-0);probe(0/0);probe(1/0);probe(1n);probe(true);probe(void expensive());}")], |analysis, file, expression| analysis.known_key(file, expression));

    assert_eq!(
        keys,
        ["0", "NaN", "Infinity", "1", "true", "undefined"].map(|key| Ok(key.to_string()))
    );
}

#[test]
fn enum_initializers_and_computed_member_names_are_evaluated() {
    let values = values_of("enum E { Count=n, Fixed=2+3, Next, Copy=Fixed, Text='x', Again=Text } function f(){probe(E.Count);probe(E.Fixed);probe(E.Next);probe(E.Copy);probe(E['Fi'+'xed']);probe(E.Again);}");

    assert!(values[0].is_err());
    assert_eq!(
        values[1..5],
        [
            Ok(Primitive::Number(5.0)),
            Ok(Primitive::Number(6.0)),
            Ok(Primitive::Number(5.0)),
            Ok(Primitive::Number(5.0))
        ]
    );
    assert_eq!(values[5], Ok(Primitive::String("x".into())));

    let numeric = probe_results_of(&[("tsconfig.json", "{}"), ("index.ts", "enum E { Count=n, Fixed=5 } function f(){probe(E.Count);probe(E.Fixed);probe(1/0);probe(0/0);probe(true);probe(1n);probe(++E.Fixed);probe(E.Fixed=2);}")], |analysis, file, expression| analysis.is_numeric_constant(file, expression));

    assert_eq!(
        numeric,
        [false, true, false, false, false, false, false, false]
    );
}

#[test]
fn qualified_enum_counterexamples_and_mutation_fence_survive_integration() {
    let values = values_of("enum E { Power=1**(0/0), Plus=+'2', Not=~'2', Surrogate='\\uD800' } enum F { A=1, B=(mutate(),7), C=A, D=9 } function f(){probe(E.Power);probe(E.Plus);probe(E.Not);probe(E.Surrogate);probe(F.B);probe(F.C);probe(F.D);}");

    assert!(matches!(values[0], Ok(Primitive::Number(value)) if value.is_nan()));
    assert_eq!(values[1], Ok(Primitive::Number(2.0)));
    assert_eq!(values[2], Ok(Primitive::Number(-3.0)));
    assert!(values[3].is_err());
    assert_eq!(values[4], Ok(Primitive::Number(7.0)));
    assert!(values[5].is_err());
    assert_eq!(values[6], Ok(Primitive::Number(9.0)));
}

#[test]
fn imported_constants_and_enums_keep_source_identity() {
    let values = probe_results_of(&[("tsconfig.json", "{}"), ("a.ts", "export enum E { A=2 } export const N=4;"), ("b.ts", "export enum E { A=n }"), ("index.ts", "import {E as A,N} from './a'; import {E as B} from './b'; function f(){probe(A.A);probe(B.A);probe(N*2);}")], |analysis, file, probe| analysis.known_value(file, probe).value.map(|value| (*value).clone()));

    assert_eq!(values[0], Ok(Primitive::Number(2.0)));
    assert!(values[1].is_err());
    assert_eq!(values[2], Ok(Primitive::Number(8.0)));
}

#[test]
fn value_results_never_erase_cost_or_certify_coercion_hooks() {
    for body in [
        "return new Array((expensive(),7));",
        "enum E { A=(expensive(),7) } return new Array(E.A);",
    ] {
        let source = format!("/** @perf O(N^3) */ function expensive(){{return 7;}} export function root(){{{body}}}");

        run_with_source(&source, |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "root");
            let expected = analysis
                .bind_function_cost(file, function, &Cost::parse("O(N^3)").unwrap())
                .unwrap();

            assert_eq!(summary_of(analysis, file, "root").cost, expected);
        });
    }

    let values = values_of("function f(){probe((expensive(),7));probe(void expensive());probe(({valueOf(){return 1}})+2);probe(({toString(){return 'x'}})+'y');}");

    assert_eq!(values[0], Ok(Primitive::Number(7.0)));
    assert_eq!(values[1], Ok(Primitive::Undefined));
    assert!(values[2..].iter().all(Result::is_err));
}

#[test]
fn source_ownership_is_checked_before_cache_lookup() {
    run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", "const x=1; function f(){probe(x)}"),
            ("other.ts", "const y=2; function g(){probe(y)}"),
        ],
        |project, root| {
            let file = file_of(project, root, "index.ts");
            let other = file_of(project, root, "other.ts");
            let mut analysis = Analysis::new(project, support::SYNTACTIC);
            let own = probes_of(project, file)[0];
            let foreign = probes_of(project, other)[0];

            assert_eq!(
                analysis.known_value(file, own).value.as_deref(),
                Ok(&Primitive::Number(1.0))
            );

            let before = analysis.values.primitive_work(file).node_visits;

            assert_eq!(
                analysis.known_value(file, foreign).value.unwrap_err(),
                Failure::UncertifiedReference
            );
            assert_eq!(analysis.values.primitive_work(file).node_visits, before);
        },
    );
}

#[test]
fn cumulative_budget_and_cached_values_survive_recording_reset() {
    run_with_source(
        "function f(){probe('a'+'b');probe('c'+'d');}",
        |analysis, file| {
            assert!(analysis.values.set_primitive_limits(Limits {
                nodes: 8,
                ..Limits::default()
            }));

            let probes = probes_of(analysis.project, file);
            let first = analysis.known_value(file, probes[0]);

            assert!(first.value.is_ok());

            let before = analysis.values.primitive_work(file).node_visits;

            analysis.reset_between_passes();
            assert_eq!(analysis.known_value(file, probes[0]).value, first.value);
            assert_eq!(analysis.values.primitive_work(file).node_visits, before);
            assert_eq!(
                analysis.known_value(file, probes[1]).value.unwrap_err(),
                Failure::NodeLimit
            );
            assert!(!analysis.values.set_primitive_limits(Limits::default()));
        },
    );
}

#[test]
fn derived_payload_rejection_precedes_primitive_operations() {
    run_with_source(
        "function f(){probe('12345678'+'12345678');}",
        |analysis, file| {
            assert!(analysis.values.set_primitive_limits(Limits {
                value_bytes: 40,
                ..Limits::default()
            }));

            let expression = probes_of(analysis.project, file)[0];

            assert_eq!(
                analysis.known_value(file, expression).value.unwrap_err(),
                Failure::PayloadLimit
            );
            assert_eq!(analysis.values.primitive_work(file).primitive_operations, 0);
        },
    );
}

fn result_of(source: &str, name: &str) -> (Cost, bool) {
    let mut found = None;

    run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, name);
        let part = summary_of(analysis, file, name);
        let cost = support::legacy_class_of(analysis, file, function, &part.cost);

        found = Some((cost, part.is_complete()));
    });

    found.expect("summary result")
}

fn legacy_cost_of(source: &str, name: &str) -> Cost {
    result_of(source, name).0
}

fn cost(text: &str) -> Cost {
    Cost::parse(text).unwrap()
}

#[test]
fn growing_const_alias_and_readonly_collections_are_quadratic() {
    for source in [
        "export function f(n: number) { const values: number[] = []; let total = 0; for (let i = 0; i < n; i++) { values.push(i); for (const value of values) total += value; } return total; }",
        "export function f(n: number) { const values: number[] = []; const alias = values; let total = 0; for (let i = 0; i < n; i++) { alias.push(i); for (const value of values) total += value; } return total; }",
        "class Holder { readonly values: number[] = []; } export function f(n: number) { const holder = new Holder(); let total = 0; for (let i = 0; i < n; i++) { holder.values.push(i); for (const value of holder.values) total += value; } return total; }",
        "export function f(n: number) { const values = [0]; let total = 0; for (let i = 0; i < n; i++) { values[values.length] = i; for (let j = 0; j < values.length; j++) total += j; } return total; }",
    ] {
        assert_eq!(legacy_cost_of(source, "f"), cost("O(N^2)"), "{source}");
    }
}

#[test]
fn structural_objects_and_open_tuples_are_linear() {
    for source in [
        "export function f(xs: { anchor: number }) { let total = 0; for (const key in xs) total += key.length; return total; }",
        "export function f<T extends { anchor: number }>(xs: T) { let total = 0; for (const key in xs) total += key.length; return total; }",
        "export function f(xs: { anchor: number }) { let total = 0; for (const key of Object.keys(xs)) total += key.length; return total; }",
        "export function f(xs: [number, ...number[]]) { let total = 0; for (const x of xs) total += x; return total; }",
        "type Items<T> = [number, ...T[]]; export function f(xs: Items<string>) { let total = 0; for (const x of xs) total++; return total; }",
        "export function f(pair: [number, number]) { let total = 0; for (const x of pair) total += x; return total; }",
        "export function f(source: { anchor: number }) { return { ...source }; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(N)"), true), "{source}");
    }
}

#[test]
fn fixed_fresh_values_and_stable_aliases_stay_constant() {
    for source in [
        "const LIMITS = [1, 2, 3]; export function f() { let total = 0; for (const value of LIMITS) total += value; for (let i = 0; i < LIMITS.length; i++) total += i; return total; }",
        "export function f() { const values = [1, 2, 3]; const alias = values; let total = 0; for (const value of alias) total += value; for (const doubled of values.map((value) => value * 2)) total += doubled; return total; }",
        "export function f() { const table = { a: 1, b: 2 }; let total = 0; for (const key of Object.keys(table)) total += key.length; for (const key in table) total += key.length; return total; }",
        "export function f(n: number) { const bytes = new Uint8Array(4); bytes[1] = n; let total = 0; for (const value of bytes) total += value; return total; }",
        "export function f() { const text = 'abc'; let total = 0; for (const character of text) total += character.length; return total; }",
        "export function f() { const table = { a: 1 }; return { ...table, b: 2 }; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(1)"), true), "{source}");
    }

    let shrunk = "export function f() { const values = [1, 2, 3]; values.pop(); let total = 0; for (const value of values) total += value; return total; }";

    assert_eq!(legacy_cost_of(shrunk, "f"), cost("O(1)"));
}

#[test]
fn prototype_enumeration_is_closed_only_without_reachable_prototype_writes() {
    let enumeration = "export function f() { const table = { a: 1 }; let total = 0; for (const key in table) total += key.length; return total; }";
    let written = format!("export function tag(target: any) {{ target.extra = 1; }} {enumeration}");
    let array = "export function tag(target: any[]) { target.extra = 1; } export function f() { const values = [1, 2]; let total = 0; for (const key in values) total += key.length; return total; }";

    let inherited = "export function f(source: Record<string, number>) { const table = { __proto__: source, a: 1 }; let total = 0; for (const key in table) total += key.length; return total; }";
    let accessor = "export function f(n: number) { const table = { get a() { for (let i = 0; i < n; i++) (this as any)[i] = i; return 1; } }; let total = table.a; for (const key in table) total += key.length; return total; }";

    assert_eq!(result_of(enumeration, "f"), (cost("O(1)"), true));
    assert_eq!(legacy_cost_of(&written, "f"), cost("O(N)"));
    assert_eq!(legacy_cost_of(array, "f"), cost("O(N)"));
    assert_eq!(legacy_cost_of(inherited, "f"), cost("O(N)"));
    assert_eq!(legacy_cost_of(accessor, "f"), cost("O(N)"));
}

#[test]
fn aliases_share_symbolic_sizes_and_fixed_values_are_constant() {
    let found = probe_results_of(
        &[
            ("tsconfig.json", "{}"),
            (
                "index.ts",
                "export function f(n: number) {\n\tconst values = [1];\n\tconst alias = values;\n\talias.push(n);\n\tconst table = { a: 1 };\n\tconst fixed = [1, 2];\n\tprobe(values);\n\tprobe(alias);\n\tprobe(table);\n\tprobe([...fixed]);\n}",
            ),
        ],
        |analysis, file, probe| analysis.cardinality_of(file, probe),
    );
    let (Cardinality::Symbolic(values), Cardinality::Symbolic(alias), Cardinality::Symbolic(table)) =
        (found[0], found[1], found[2])
    else {
        panic!("{found:?}");
    };

    assert_eq!(values, alias);
    assert_eq!(values.quantity, SizeQuantity::Length);
    assert_eq!(table.quantity, SizeQuantity::Keys);
    assert_ne!(values.origin, table.origin);
    assert_eq!(found[3], Cardinality::Constant);
}

#[test]
fn exact_lengths_require_histories_without_shrinking() {
    let values = values_of("export function f(){const shrunk=[1,2];shrunk.pop();const fixed=[1,2];const grown=[1,2];grown.push(3);probe(shrunk.length);probe(fixed.length);probe(grown.length);}");

    assert!(values[0].is_err());
    assert_eq!(values[1], Ok(Primitive::Number(2.0)));
    assert!(values[2].is_err());
}

#[test]
fn awaited_values_alias_their_operand() {
    for source in [
        "export async function f(n: number) { const xs: number[] = [1, 2, 3]; const ys: number[] = await xs; let total = 0; for (let i = 0; i < n; i++) { ys[ys.length] = i; for (const x of xs) total += x; } return total; }",
        "export async function f(n: number) { const xs = [1, 2, 3]; const ys = await xs; let total = 0; for (let i = 0; i < n; i++) { ys.push(i); for (const x of xs) total += x; } return total; }",
    ] {
        assert_eq!(legacy_cost_of(source, "f"), cost("O(N^2)"), "{source}");
    }

    let control = "export async function f(n: number) { const xs = [1, 2, 3]; const ys = await xs; let total: number = ys.length; for (let i = 0; i < n; i++) { for (const x of xs) total += x; } return total; }";

    assert_eq!(result_of(control, "f"), (cost("O(N)"), true));
}

#[test]
fn implicit_coercions_respect_own_methods_and_replaced_intrinsics() {
    for source in [
        "export function f(n: number) { let count = 0; const o: Record<string, unknown> = { a: 1, toString(): string { (this as Record<string, unknown>)['k' + count++] = 1; return ''; } }; let total = 0; for (let i = 0; i < n; i++) { total += `${o}`.length; for (const k in o) total += k.length; } return total; }",
        "export function f(n: number) { let count = 0; const o: Record<string, unknown> = { a: 1, valueOf(): number { (this as Record<string, unknown>)['k' + count++] = 1; return 0; } }; let total = 0; for (let i = 0; i < n; i++) { total += +o; for (const k of Object.keys(o)) total += k.length; } return total; }",
        "(Array.prototype as { join: unknown }).join = function (this: number[]): string { this.push(1); return ''; }; export function f(n: number) { const xs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n; i++) { total += `${xs}`.length; for (const x of xs) total += x; } return total; }",
        "(Array.prototype as any)[Symbol.iterator] = function* (this: number[]) { this.push(1); yield 1; }; export function f(n: number) { const xs: number[] = [1, 2, 3]; let total = 0; for (let i = 0; i < n; i++) { total += [...xs].length; for (let j = 0; j < xs.length; j++) total += j; } return total; }",
    ] {
        assert_eq!(legacy_cost_of(source, "f"), cost("O(N^2)"), "{source}");
    }

    let inert = "export function f(n: number) { const xs = [1, 2, 3]; const o = { a: 1 }; let total = 0; for (let i = 0; i < n; i++) { total += `${xs}${o}`.length + [...xs].length + (xs + '').length; for (const x of xs) total += x; for (const k in o) total += k.length; } return total; }";

    assert_eq!(result_of(inert, "f"), (cost("O(N)"), true));
}

#[test]
fn string_concatenation_and_spread_insertion_are_not_constant_sized() {
    for source in [
        "export function f(text: string) { const s = [text] + ''; let total = 0; for (const c of text) { for (const d of s) total += c.length + d.length; } return total; }",
        "export function f(items: number[]) { const xs = [1, 2].toSpliced(0, 0, ...items); let total = 0; for (const x of items) { for (const y of xs) total += x + y; } return total; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(N^2)"), true), "{source}");
    }
}

#[test]
fn argument_facts_carry_computed_sizes() {
    let source = "/** @perf O(items^2) */ function heavy(items: number[]): number { return items.length; } export function literal(): number { return heavy([1, 2, 3]); } export function copied(xs: number[]): number { return heavy([...xs]); } export function passed(xs: number[]): number { const ys = xs; return heavy(ys); }";

    assert_eq!(result_of(source, "literal"), (cost("O(1)"), true));
    assert_eq!(result_of(source, "copied"), (cost("O(N)"), false));
    assert_eq!(result_of(source, "passed"), (cost("O(N^2)"), true));
}

const HELPERS: &str = "function cubic(xs: number[]) { let t = 0; for (const a of xs) for (const b of xs) for (const c of xs) t += a + b + c; return t; } function cheap(xs: number[]) { return xs.length; }";

fn helped(source: &str) -> String {
    format!("{HELPERS} {source}")
}

#[test]
fn destructured_element_callees_resolve_through_recorded_writes() {
    let element = helped(
        "const fns = [cubic]; export function f(xs: number[]) { const [run] = fns; return run(xs); }",
    );
    let written = helped(
        "const fns: ((xs: number[]) => number)[] = [cheap]; fns[0] = cubic; export function f(xs: number[]) { const [run = cheap] = fns; return run(xs); }",
    );
    let cleared = helped(
        "const fns: (((xs: number[]) => number) | undefined)[] = [cheap]; fns[0] = undefined; export function f(xs: number[]) { const [run = cubic] = fns; return run(xs); }",
    );
    let escaped = helped(
        "declare function leak(o: unknown): void; const fns: ((xs: number[]) => number)[] = [cheap]; leak(fns); export function f(xs: number[]) { const [run = cubic] = fns; return run(xs); }",
    );
    let nested = helped(
        "const holder: { a: ((xs: number[]) => number)[] } = { a: [cheap] }; holder.a[0] = cubic; export function f(xs: number[]) { const { a: [run] } = holder; return run(xs); }",
    );

    for source in [&element, &written, &cleared, &escaped, &nested] {
        assert_eq!(result_of(source, "f"), (cost("O(N^3)"), false), "{source}");
    }
}

#[test]
fn pattern_defaults_join_unless_a_fresh_source_supplies_the_key() {
    let fresh = helped(
        "export function f(xs: number[]) { const { run = cubic } = { run: cheap }; return run(xs); }",
    );
    let element = helped(
        "export function f(xs: number[]) { const [run = cubic] = [cheap]; return run(xs); }",
    );
    let aliased = helped(
        "const holder = { run: cheap }; export function f(xs: number[]) { const { run = cubic } = holder; return run(xs); }",
    );
    let deleted = helped(
        "const holder: { run?: (xs: number[]) => number } = { run: cheap }; delete holder.run; export function f(xs: number[]) { const { run = cubic } = holder; return run(xs); }",
    );
    let escaped = helped(
        "declare function leak(o: unknown): void; const holder = { run: cheap }; leak(holder); export function f(xs: number[]) { const { run = cubic } = holder; return run(xs); }",
    );
    let inherited = helped(
        "declare const outside: { run?: (xs: number[]) => number }; export function f(xs: number[]) { const holder = { __proto__: outside }; const { run = cubic } = holder; return run(xs); }",
    );
    let omitted = helped(
        "export function f(xs: number[]) { const { run = cubic } = {} as { run?: (xs: number[]) => number }; return run(xs); }",
    );

    assert_eq!(result_of(&fresh, "f"), (cost("O(1)"), false));
    assert_eq!(result_of(&element, "f"), (cost("O(1)"), false));

    for source in [&aliased, &deleted, &escaped, &inherited, &omitted] {
        assert_eq!(result_of(source, "f"), (cost("O(N^3)"), false), "{source}");
    }
}

#[test]
fn spread_object_copies_carry_their_source_members() {
    let copied = helped(
        "const base = { run: cubic }; const copy = { ...base }; export function f(xs: number[]) { return copy.run(xs); }",
    );
    let overridden = helped(
        "const base = { run: cubic }; const copy = { run: cheap, ...base }; export function f(xs: number[]) { return copy.run(xs); }",
    );
    let control = helped(
        "const base = { run: cheap }; const copy = { ...base }; export function f(xs: number[]) { return copy.run(xs); }",
    );

    assert_eq!(result_of(&copied, "f"), (cost("O(N^3)"), false));
    assert_eq!(result_of(&overridden, "f"), (cost("O(N^3)"), false));
    assert_eq!(result_of(&control, "f"), (cost("O(1)"), false));
}

#[test]
fn rest_copies_compose_getter_and_custom_iterator_work() {
    let getter = "export function f(n: number) { const source = { get a(): number { let t = 0; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) t += j; return t; } }; const { ...rest } = source; return rest; }";
    let iterated = "export function f(n: number) { const source = { *[Symbol.iterator](): Generator<number> { let t = 0; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) t += j; yield t; } }; const [, ...rest] = source; return rest; }";
    let inert = "export function f() { const source = { a: 1, b: 2 }; const { ...rest } = source; return rest; }";

    let copied = "export function f(n: number) { const source = { get a(): number { let t = 0; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) t += j; return t; } }; return { ...source }; }";
    let nested = "export function f(n: number) { const holder = { inner: { get a(): number { let t = 0; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) t += j; return t; } } }; const { inner: { ...rest } } = holder; return rest; }";

    assert_eq!(result_of(getter, "f"), (cost("O(N^2)"), false));
    assert_eq!(result_of(copied, "f"), (cost("O(N^2)"), false));
    assert_eq!(result_of(nested, "f"), (cost("O(N^2)"), false));
    assert_eq!(legacy_cost_of(iterated, "f"), cost("O(N^2)"));
    assert_eq!(result_of(inert, "f"), (cost("O(1)"), true));
}

fn reasons_of(
    source: &str,
    name: &str,
) -> std::collections::BTreeSet<olint::unknowns::UnknownReason> {
    support::legacy_result_of(source, name).2
}

#[test]
fn produced_sizes_reach_the_operations_that_visit_them() {
    for source in [
        "export function f(xs: number[]) { const m = xs.flatMap(() => xs); let t = 0; for (const a of xs) for (const v of m) t += a + v; return t; }",
        "export function f(xs: number[]) { const m = xs.map(() => xs).flat(); let t = 0; for (const a of xs) t += [...m].length + a; return t; }",
        "export function f(xs: number[]) { const m = xs.flatMap(() => xs); let t = 0; for (const a of xs) t += Array.from(m).length + a; return t; }",
        "export function f(xs: number[]) { let t = 0; xs.flatMap(() => xs).forEach(() => { for (const y of xs) t += y; }); return t; }",
        "export function f(xs: number[]) { const m = xs.flatMap(() => xs).filter((v) => v > 0); let t = 0; for (let i = 0; i < xs.length; i++) for (const v of m) t += v; return t; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(N^3)"), true), "{source}");
    }

    for source in [
        "export function f(xs: number[]) { const m = xs.slice(); if (xs.length > 5) m.length = 0; let t = 0; for (const a of xs) for (const v of m) t += a + v; return t; }",
        "export function f(xs: number[]) { const m = xs.map(() => 1); let t = 0; for (const a of xs) for (const v of m) t += a + v; return t; }",
        "export function f(xs: number[]) { const m = xs.filter((x) => x > 0).slice(1); let t = 0; for (const a of xs) for (const v of m) t += a + v; return t; }",
        "export function f(xs: number[]) { const m = [...xs, ...xs]; let t = 0; for (const a of xs) for (const v of m) t += a + v; return t; }",
    ] {
        assert_eq!(result_of(source, "f"), (cost("O(N^2)"), true), "{source}");
    }
}

#[test]
fn repeated_string_lengths_reach_later_scans() {
    let source = r#"export function f(s: string) { const t = s.repeat(s.length); let c = 0; for (let i = 0; i < s.length; i++) if (t.includes("a")) c++; return c; }"#;
    let fixed = r#"export function f(s: string) { const t = s.repeat(2); let c = 0; for (let i = 0; i < s.length; i++) if (t.includes("a")) c++; return c; }"#;

    assert_eq!(result_of(source, "f"), (cost("O(N^3)"), false));
    assert_eq!(result_of(fixed, "f"), (cost("O(N^2)"), true));
}

#[test]
fn pushes_grow_their_holder_by_every_visit() {
    let nested = "export function f(n: number) { const out: number[] = []; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) out.push(j); let c = 0; for (let i = 0; i < n; i++) if (out.includes(i)) c++; return c; }";
    let spread = "export function f(n: number) { const out: number[] = []; const row = [1, 2, 3]; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) out.push(...row); let c = 0; for (let i = 0; i < n; i++) c += out.indexOf(i); return c; }";
    let shifted = "export function f(n: number) { const out: number[] = []; for (let i = 0; i < n; i++) out.unshift(i); let c = 0; for (let i = 0; i < n; i++) c += out.indexOf(i); return c; }";
    let scoped = "export function f(n: number) { let c = 0; for (let i = 0; i < n; i++) { const out: number[] = []; for (let j = 0; j < n; j++) out.push(j); for (let k = 0; k < n; k++) c += out.indexOf(k); } return c; }";
    let once = "export function f(n: number) { const out: number[] = []; for (let i = 0; i < n; i++) out.push(i); return out.slice(); }";
    let produced = "export function f(xs: number[]) { const m = xs.flatMap(() => xs); const out: number[] = []; for (const v of m) out.push(v); const k = xs.length; let c = 0; for (let i = 0; i < k; i++) c += out.indexOf(i); return c; }";

    assert_eq!(legacy_cost_of(nested, "f"), cost("O(N^3)"));
    assert_eq!(legacy_cost_of(spread, "f"), cost("O(N^3)"));
    assert_eq!(legacy_cost_of(scoped, "f"), cost("O(N^3)"));
    assert_eq!(result_of(shifted, "f"), (cost("O(N^2)"), true));
    assert_eq!(legacy_cost_of(once, "f"), cost("O(N)"));
    assert_eq!(legacy_cost_of(produced, "f"), cost("O(N^3)"));
}

#[test]
fn growth_the_analysis_cannot_count_stays_unresolved() {
    for source in [
        "export function f(n: number) { const out: number[] = []; const alias = out; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) alias.push(j); out.push(1); let c = 0; for (let i = 0; i < n; i++) if (out.includes(i)) c++; return c; }",
        "export function f(n: number, xs: number[]) { const out: number[] = []; out.push(1); xs.forEach((x) => out.push(x)); let c = 0; for (let i = 0; i < n; i++) if (out.includes(i)) c++; return c; }",
    ] {
        let (found, complete) = result_of(source, "f");

        assert_eq!(found, cost("O(N^2)"), "{source}");
        assert!(!complete, "{source}");
        assert!(
            reasons_of(source, "f").contains(&olint::unknowns::UnknownReason::SizeRelation),
            "{source}"
        );
    }
}

mod support;

use support::probe_results_of;

fn constant_sizes_of(source: &str) -> Vec<bool> {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "lib.ts",
            "export enum Tone { Low, High }\nexport const WIDTH = 8;\nexport const SHARED = [1, 2];",
        ),
        ("index.ts", source),
    ];

    probe_results_of(&files, |analysis, file, probe| {
        analysis.is_constant_sized(file, probe)
    })
}

#[test]
fn each_constant_case_holds() {
    let found = constant_sizes_of(
        "const LIMITS = [1, 2];\nenum Color { Red, Green }\nexport function f(flag: boolean, g: (x: number) => number) {\n\tconst alias = LIMITS;\n\tconst table = { a: 1, ...{ b: 2 } };\n\tprobe([1, 2, ...[3]]);\n\tprobe(flag ? [1] : [2, 3]);\n\tprobe([1, 2].map(g));\n\tprobe([1, 2].flatMap((x) => [x, x]));\n\tprobe([1].concat([2]));\n\tprobe(\"text\");\n\tprobe(new Uint8Array(LIMITS.length * 4));\n\tprobe([...LIMITS]);\n\tprobe([...alias]);\n\tprobe(Object.keys(Color));\n\tprobe(Object.keys(table));\n}",
    );

    assert_eq!(found, vec![true; 11]);
}

#[test]
fn sizes_that_depend_on_input_are_not_constant() {
    let found = constant_sizes_of(
        "export function f(xs: number[], n: number, g: (x: number) => number) {\n\tconst { size } = { size: [1] };\n\tprobe(xs.map(g));\n\tprobe(new Array(n));\n\tprobe([1, ...xs]);\n\tprobe([1].flatMap((x) => xs));\n\tprobe(size);\n\tprobe(Array.from({ length: n }));\n\tprobe([...{ length: 2 }]);\n\tprobe([1, 2].toSpliced(0, 0, ...xs));\n\tprobe([String(n)] + \"\");\n\tprobe(Object.keys({ a: 1, toString() { return \"\"; } }));\n\tprobe(Object.keys({ a: 1, valueOf: function () { return 0; } }));\n}",
    );

    assert_eq!(found, vec![false; 11]);
}

#[test]
fn declared_shapes_and_tuples_are_not_size_evidence() {
    let found = constant_sizes_of(
        "interface Point { x: number; y: number }\ntype Items<T> = [number, ...T[]];\nexport function f<T extends Point>(point: Point, pair: [number, number], fixed: readonly [number, number], rest: [number, ...number[]], items: Items<string>, generic: T) {\n\tprobe(Object.values(point));\n\tprobe(Object.keys(generic));\n\tprobe(pair);\n\tprobe(fixed);\n\tprobe(rest);\n\tprobe(items);\n\tprobe([1, 2] as [number, number]);\n}",
    );

    assert_eq!(found, vec![false, false, false, false, false, false, true]);
}

#[test]
fn mutations_aliases_and_escapes_recover_growing_sizes() {
    let found = constant_sizes_of(
        "declare function sink(values: number[]): void;\nexport function f(n: number) {\n\tconst pushed = [1];\n\tpushed.push(n);\n\tprobe([...pushed]);\n\tconst aliased = [1];\n\tconst alias = aliased;\n\talias.push(n);\n\tprobe([...aliased]);\n\tprobe([...alias]);\n\tconst lengthened = [1];\n\tlengthened.length = n;\n\tprobe([...lengthened]);\n\tconst indexed = [1];\n\tindexed[n] = n;\n\tprobe([...indexed]);\n\tconst spliced = [1];\n\tspliced.splice(0, 0, n);\n\tprobe([...spliced]);\n\tconst escaped = [1];\n\tsink(escaped);\n\tprobe([...escaped]);\n\tconst stored = [1];\n\tconst box = { stored };\n\tprobe([...stored]);\n\tconst called = [1];\n\tcalled.forEach((x, i, all) => all.push(x));\n\tprobe([...called]);\n\tconst sorted = [1];\n\tsorted.sort().push(n);\n\tprobe([...sorted]);\n\tconst reassigned = [1];\n\tlet holder = reassigned;\n\tholder.push(n);\n\tprobe([...reassigned]);\n\tconst table = { a: 1 };\n\ttable[\"k\" + n] = n;\n\tprobe(Object.keys(table));\n\tconst merged = Object.assign({}, box);\n\tmerged.extra = n;\n\tprobe(Object.keys(merged));\n\tconst grown = { a: 1 };\n\tconst closure = () => { grown.b = n; };\n\tclosure();\n\tprobe(Object.keys(grown));\n}",
    );

    assert_eq!(found, vec![false; 14]);
}

#[test]
fn understood_histories_keep_fixed_fresh_sizes() {
    let found = constant_sizes_of(
        "export function f(n: number) {\n\tconst shrunk = [1, 2];\n\tshrunk.pop();\n\tshrunk.splice(0, 1);\n\tprobe([...shrunk]);\n\tconst read = [1, 2];\n\tread.map((x) => x).forEach((x) => x);\n\tread.includes(n);\n\tread.sort((a, b) => a - b);\n\tprobe([...read]);\n\tconst typed = new Uint8Array(4);\n\ttyped[1] = 2;\n\tconsume(typed);\n\tprobe(typed);\n\tconst frozen = Object.freeze([1, 2]);\n\tprobe([...frozen]);\n\tconst table = { a: 1 };\n\tconst keys = Object.keys(table);\n\tprobe([...keys]);\n\tprobe(Object.entries({ ...table, b: 2 }));\n}\nexport function g() {\n\tconst values = [1, 2];\n\tprobe([...values]);\n\treturn values;\n}",
    );

    assert_eq!(found, vec![true; 7]);
}

#[test]
fn shared_bindings_have_no_understood_history() {
    let found = constant_sizes_of(
        "import * as library from \"./lib\";\nimport { SHARED } from \"./lib\";\nexport const EXPORTED = [1, 2];\nconst NAMED = [1, 2];\nexport { NAMED };\nconst DEFAULTED = [1, 2];\nexport default DEFAULTED;\nlet later: () => number[];\nexport function f() {\n\tprobe([...EXPORTED]);\n\tprobe([...NAMED]);\n\tprobe([...DEFAULTED]);\n\tprobe([...SHARED]);\n\tprobe(Object.keys(library.Tone));\n\tconst captured = [1, 2];\n\tlater = () => captured;\n\tprobe([...captured]);\n\tconst returned = [1, 2];\n\tconst read = () => returned.length;\n\tread();\n\tprobe([...returned]);\n\treturn returned;\n}",
    );

    assert_eq!(found, vec![false; 7]);
}

#[test]
fn script_globals_and_direct_eval_have_no_understood_history() {
    let script = probe_results_of(
        &[
            ("tsconfig.json", "{}"),
            (
                "index.ts",
                "const LIMITS = [1, 2];\nfunction f() {\n\tprobe([...LIMITS]);\n}",
            ),
            (
                "other.ts",
                "function grow(n: number) {\n\tLIMITS.push(n);\n}",
            ),
        ],
        |analysis, file, probe| analysis.is_constant_sized(file, probe),
    );
    let evaluated: Vec<bool> = [
        "eval(code)",
        "(eval)(code)",
        "(eval as (source: string) => unknown)(code)",
        "eval!(code)",
        "(<(source: string) => unknown>eval)(code)",
    ]
    .iter()
    .flat_map(|call| {
        constant_sizes_of(&format!(
            "export function f(code: string) {{\n\tconst values = [1, 2];\n\t{call};\n\tprobe([...values]);\n}}"
        ))
    })
    .collect();
    let indirect = constant_sizes_of(
        "export function f(code: string) {\n\tconst values = [1, 2];\n\tconst run = eval;\n\trun(code);\n\tprobe([...values]);\n}",
    );

    assert_eq!(script, vec![false]);
    assert_eq!(evaluated, vec![false; 5]);
    assert_eq!(indirect, vec![true]);
}

#[test]
fn readonly_properties_are_not_size_evidence() {
    let found = constant_sizes_of(
        "export class Box {\n\treadonly items = [1, 2];\n\tloose: number[] = [1, 2];\n\tstatic readonly SIZES = [\"a\"];\n\tsize() {\n\t\tthis.items.push(3);\n\t\tprobe(this.items);\n\t\tprobe(this.loose);\n\t\tprobe(Box.SIZES);\n\t}\n}",
    );

    assert_eq!(found, vec![false, false, false]);
}

#[test]
fn inherited_members_and_namespace_exports_are_followed() {
    let found = constant_sizes_of(
        "import * as library from \"./lib\";\nclass Base {\n\treadonly items: number[] = [1, 2];\n}\nexport class Derived extends Base {\n\tsize(n: number) {\n\t\tprobe(this.items);\n\t\tprobe(new Uint8Array(library.Tone.High));\n\t\tprobe(new Uint8Array(library.WIDTH * 2));\n\t\tprobe(new Uint8Array(n));\n\t}\n}",
    );

    assert_eq!(found, vec![false, true, true, false]);
}

#[test]
fn declared_types_casts_and_static_placement_decide_member_constants() {
    let found = constant_sizes_of(
        "interface IEngine { readonly MAX: number }\nclass Engine implements IEngine { readonly MAX = 4; }\ntype Alias = Engine;\nexport class Twin {\n\tstatic size = 1;\n\treadonly size = 9;\n\tm() {\n\t\tconst a: IEngine = new Engine();\n\t\tconst b = new Engine() as IEngine;\n\t\tconst g: Alias = new Engine();\n\t\tprobe(new Uint8Array(a.MAX));\n\t\tprobe(new Uint8Array(b.MAX));\n\t\tprobe(new Uint8Array(g.MAX));\n\t\tprobe(new Uint8Array(this.size));\n\t}\n\tstatic s() {\n\t\tprobe(new Uint8Array(this.size));\n\t}\n}",
    );

    assert_eq!(found, vec![false, false, true, true, false]);
}

#[test]
fn a_cast_receiver_carries_no_readonly_collection_size() {
    let found = constant_sizes_of(
        "class Holder {
	readonly SIZES = [1, 2];
}
interface Shape {
	readonly SIZES: number[];
}
export function f(box: unknown) {
	probe((box as Holder).SIZES);
	probe((<Holder>box).SIZES);
	probe((box as Shape).SIZES);
}",
    );

    assert_eq!(found, vec![false, false, false]);
}

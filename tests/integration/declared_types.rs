use olint::declared_types::{DeclaredType, Kind};

use crate::support;

use support::probe_results_of;

fn probed_types_of(files: &[(&str, &str)]) -> Vec<DeclaredType> {
    probe_results_of(files, |analysis, file, probe| {
        analysis.declared_type_of_expression(file, probe)
    })
}

fn declared_types_of(types: &str, index: &str) -> Vec<DeclaredType> {
    probed_types_of(&[
        ("tsconfig.json", "{}"),
        ("types.ts", types),
        ("index.ts", index),
    ])
}

fn expected_type_of(kind: Kind) -> DeclaredType {
    DeclaredType { kind }
}

#[test]
fn parameters_read_their_annotations() {
    let found = declared_types_of(
        "export interface Point { x: number; y: number }\nexport interface Bag { [key: string]: number; size: number }\nexport interface Line { from: Point; to: Point }",
        "import type { Point, Bag, Line } from \"./types\";\nexport function f(pair: [number, string], names: readonly string[], bag: Bag, either: Point | Line, picked: Pick<Point, \"x\">, keys: keyof Point) {\n\tprobe(pair);\n\tprobe(names);\n\tprobe(bag);\n\tprobe(either);\n\tprobe(picked);\n\tprobe(keys);\n}",
    );

    assert_eq!(
        found,
        vec![
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
        ]
    );
}

#[test]
fn type_names_follow_aliases_imports_and_constraints() {
    let found = declared_types_of(
        "export interface Shape { width: number }\nexport type Alias = Shape;\nexport type Chain = Alias;",
        "import type { Chain } from \"./types\";\nexport function f<T extends string[]>(shape: Chain, items: T) {\n\tprobe(shape);\n\tprobe(items);\n}",
    );

    assert_eq!(
        found,
        vec![expected_type_of(Kind::Other), expected_type_of(Kind::Array),]
    );
}

#[test]
fn expressions_read_calls_constructors_and_patterns() {
    let found = declared_types_of(
        "export const holder = { size: [1, 2] };",
        "import { holder } from \"./types\";\nexport function f(text: string, { items }: { items: number[] }) {\n\tconst { size } = holder;\n\tprobe(text.split(\",\"));\n\tprobe(new Set<number>());\n\tprobe(items);\n\tprobe(size);\n\tprobe(holder.size);\n\tprobe([1, 2] as const);\n\tprobe(text as unknown as number[]);\n}",
    );

    assert_eq!(
        found,
        vec![
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Set),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Array),
        ]
    );
}

#[test]
fn package_declaration_aliases_resolve_and_lib_globals_read_as_other() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/pkg/index.d.ts",
            "export type Items = string[];\nexport interface Box { width: number }",
        ),
        (
            "index.ts",
            "import type { Items, Box } from \"pkg\";\nfunction make(): number[] {\n\treturn [1];\n}\nexport function f(items: Items, box: Box, r: ReturnType<typeof make>, p: Parameters<typeof make>, a: Awaited<Promise<string[]>>, d: Date) {\n\tprobe(items);\n\tprobe(box);\n\tprobe(r);\n\tprobe(p);\n\tprobe(a);\n\tprobe(d);\n}",
        ),
    ];

    assert_eq!(
        probed_types_of(&files),
        vec![
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
        ]
    );
}

#[test]
fn ambient_declarations_in_a_script_root_resolve() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "ambient.d.ts",
            "type AmbientList = string[];
interface AmbientShape {
	a: number;
}",
        ),
        (
            "index.ts",
            "export function f(list: AmbientList, shape: AmbientShape) {
	probe(list);
	probe(shape);
}",
        ),
    ];

    assert_eq!(
        probed_types_of(&files),
        vec![expected_type_of(Kind::Array), expected_type_of(Kind::Other),]
    );
}

#[test]
fn tuple_and_structural_annotations_describe_kinds_without_cardinality() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "interface Shape {
	a: number;
}
type Items<T> = [number, ...T[]];
export function f<T extends Shape>(pair: [number, number], rest: [number, ...number[]], items: Items<string>, fixed: readonly [number, number], shape: Shape, literal: { a: number }, generic: T) {
	probe(pair);
	probe(rest);
	probe(items);
	probe(fixed);
	probe(shape);
	probe(literal);
	probe(generic);
}",
        ),
    ];
    let found = probe_results_of(&files, |analysis, file, probe| {
        (
            analysis.declared_type_of_expression(file, probe).kind,
            analysis.is_constant_sized(file, probe),
            analysis.is_closed(file, probe),
        )
    });

    assert_eq!(
        found,
        vec![
            (Kind::Array, false, false),
            (Kind::Array, false, false),
            (Kind::Array, false, false),
            (Kind::Array, false, false),
            (Kind::Other, false, false),
            (Kind::Other, false, false),
            (Kind::Other, false, false),
        ]
    );
}

// G21: a built-in kind needs the name to denote the global; a same-named import or local type is
// another type, and only the built-in String and Array methods are known to return strings.
#[test]
fn built_in_kinds_resolve_only_to_the_global_names() {
    let found = declared_types_of(
        "export class Set<T> { forEach(f: (value: T) => void): void {} toString(): number[] { return []; } }",
        "import { Set } from \"lib\";\nimport { Set as Local } from \"./types\";\ntype Array<T> = { at(index: number): T };\nexport function f(s: Set<string>, local: Local<string>, a: Array<number>, g: ReadonlySet<string>, xs: string[]) {\n\tprobe(s);\n\tprobe(local);\n\tprobe(a);\n\tprobe(g);\n\tprobe(s.toString());\n\tprobe(xs.join());\n\tprobe(new Local());\n}",
    );

    assert_eq!(
        found,
        vec![
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Other),
            expected_type_of(Kind::Set),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::String),
            expected_type_of(Kind::Other),
        ]
    );
}

// G25: §2.5 gives a union's value only one of its parts' types, so its kind is known when the
// non-nullish parts agree; an intersection's value has every part's type.
#[test]
fn union_kinds_join_only_when_the_parts_agree() {
    let found = declared_types_of(
        "export interface Foo { forEach(f: (value: string) => void): void }",
        "import type { Foo } from \"./types\";\nexport function f(a: string[] | Foo, b: string[] | undefined, c: Set<string> | Map<string, number>, d: string & { brand: 1 }, flag: boolean, lib: () => any) {\n\tprobe(a);\n\tprobe(b);\n\tprobe(c);\n\tprobe(d);\n\tprobe(flag ? [] : lib());\n\tprobe(b ?? []);\n\tprobe(flag ? [] : null);\n\tprobe(flag ? \"a\" : [\"a\"]);\n}",
    );

    assert_eq!(
        found,
        vec![
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::String),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Unknown),
        ]
    );
}

// G26: `this` is the class instance only in an instance member; a non-arrow function or an
// object-literal method rebinds it, and a static member sees the constructor.
#[test]
fn this_reads_the_class_only_inside_instance_members() {
    let found = declared_types_of(
        "export {};",
        "export class C {\n\titems: number[] = [];\n\tstatic only: number[] = [];\n\tm() {\n\t\tprobe(this.items);\n\t\tconst arrow = () => probe(this.items);\n\t\tfunction inner(this: any) {\n\t\t\tprobe(this.items);\n\t\t}\n\t\tconst object = { items: \"x\", read() {\n\t\t\tprobe(this.items);\n\t\t} };\n\t\tprobe(this.only);\n\t\treturn [arrow, inner, object];\n\t}\n\tstatic s() {\n\t\tprobe(this.items);\n\t}\n}",
    );

    assert_eq!(
        found,
        vec![
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Array),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Unknown),
            expected_type_of(Kind::Unknown),
        ]
    );
}

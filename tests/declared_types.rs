use olint::declared_types::{DeclaredType, Kind};

mod support;

use support::probe_results_of;

fn declared_types_of(types: &str, index: &str) -> Vec<DeclaredType> {
    let files = [
        ("tsconfig.json", "{}"),
        ("types.ts", types),
        ("index.ts", index),
    ];

    probe_results_of(&files, |analysis, file, probe| {
        analysis.declared_type_of_expression(file, probe)
    })
}

fn declared(kind: Kind, tuple: bool, closed: bool) -> DeclaredType {
    DeclaredType {
        kind,
        tuple,
        closed,
    }
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
            declared(Kind::Array, true, false),
            declared(Kind::Array, false, false),
            declared(Kind::Other, false, false),
            declared(Kind::Other, false, true),
            declared(Kind::Other, false, true),
            declared(Kind::Other, false, true),
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
        vec![
            declared(Kind::Other, false, true),
            declared(Kind::Array, false, false),
        ]
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
            declared(Kind::Array, false, false),
            declared(Kind::Set, false, false),
            declared(Kind::Unknown, false, false),
            declared(Kind::Unknown, false, false),
            declared(Kind::Array, true, false),
            declared(Kind::Array, true, false),
            declared(Kind::Array, false, false),
        ]
    );
}

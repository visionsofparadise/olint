mod support;

use support::probe_results_of;

fn constant_sizes_of(source: &str) -> Vec<bool> {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "lib.ts",
            "export enum Tone { Low, High }\nexport const WIDTH = 8;",
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
        "const LIMITS = [1, 2];\nenum Color { Red, Green }\ninterface Point { x: number; y: number }\nexport function f(flag: boolean, point: Point, pair: [number, number], g: (x: number) => number) {\n\tprobe([1, 2, ...[3]]);\n\tprobe(flag ? [1] : [2, 3]);\n\tprobe([1, 2].map(g));\n\tprobe([1, 2].flatMap((x) => [x, x]));\n\tprobe([1].concat([2]));\n\tprobe(\"text\");\n\tprobe(new Uint8Array(LIMITS.length * 4));\n\tprobe(LIMITS);\n\tprobe(Object.keys(Color));\n\tprobe(Object.values(point));\n\tprobe(pair);\n}",
    );

    assert_eq!(found, vec![true; 11]);
}

#[test]
fn sizes_that_depend_on_input_are_not_constant() {
    let found = constant_sizes_of(
        "export function f(xs: number[], n: number, g: (x: number) => number) {\n\tconst { size } = { size: [1] };\n\tprobe(xs.map(g));\n\tprobe(new Array(n));\n\tprobe([1, ...xs]);\n\tprobe([1].flatMap((x) => xs));\n\tprobe(size);\n}",
    );

    assert_eq!(found, vec![false; 5]);
}

#[test]
fn a_readonly_property_with_a_constant_initializer_is_constant() {
    let found = constant_sizes_of(
        "export class Box {\n\treadonly items = [1, 2];\n\tloose: number[] = [1, 2];\n\tstatic readonly SIZES = [\"a\"];\n\tsize() {\n\t\tprobe(this.items);\n\t\tprobe(this.loose);\n\t\tprobe(Box.SIZES);\n\t}\n}",
    );

    assert_eq!(found, vec![true, false, true]);
}

#[test]
fn inherited_members_and_namespace_exports_are_followed() {
    let found = constant_sizes_of(
        "import * as library from \"./lib\";\nclass Base {\n\treadonly items: number[] = [1, 2];\n}\nexport class Derived extends Base {\n\tsize(n: number) {\n\t\tprobe(this.items);\n\t\tprobe(new Uint8Array(library.Tone.High));\n\t\tprobe(new Uint8Array(library.WIDTH * 2));\n\t\tprobe(new Uint8Array(n));\n\t}\n}",
    );

    assert_eq!(found, vec![true, true, true, false]);
}

#[test]
fn declared_types_casts_and_static_placement_decide_member_constants() {
    let found = constant_sizes_of(
        "interface IEngine { readonly MAX: number }\nclass Engine implements IEngine { readonly MAX = 4; }\ntype Alias = Engine;\nexport class Twin {\n\tstatic size = 1;\n\treadonly size = 9;\n\tm() {\n\t\tconst a: IEngine = new Engine();\n\t\tconst b = new Engine() as IEngine;\n\t\tconst g: Alias = new Engine();\n\t\tprobe(new Uint8Array(a.MAX));\n\t\tprobe(new Uint8Array(b.MAX));\n\t\tprobe(new Uint8Array(g.MAX));\n\t\tprobe(new Uint8Array(this.size));\n\t}\n\tstatic s() {\n\t\tprobe(new Uint8Array(this.size));\n\t}\n}",
    );

    assert_eq!(found, vec![false, false, true, true, false]);
}

#[test]
fn a_cast_receiver_resolves_members_through_its_class() {
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

    assert_eq!(found, vec![true, true, false]);
}

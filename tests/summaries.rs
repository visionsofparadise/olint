use olint::analysis::Analysis;
use olint::config::read_config;
use olint::cost::Cost;
use olint::public::public_functions;

mod support;

use support::{file_of, function_of_name, run_in_project, run_with_source, SYNTACTIC};

fn labels_of(chain: &[olint::cost::Factor]) -> Vec<String> {
    chain.iter().map(|factor| factor.label.clone()).collect()
}

#[test]
fn self_recursion_charges_one_n() {
    run_with_source(
        "export function walk(n: number): number {\n\treturn n > 0 ? walk(n - 1) : 0;\n}",
        |analysis, file| {
            let walk = function_of_name(analysis.project, file, "walk");
            let part = analysis.summarize(file, walk).total();

            assert_eq!(part.cost, Cost::N);
            assert_eq!(labels_of(&part.chain), vec!["recursive call walk()"]);
        },
    );
}

#[test]
fn a_cycle_member_takes_the_root_summary() {
    run_with_source(
        "export function ping(n: number): number {\n\treturn n > 0 ? pong(n - 1) : 0;\n}\nexport function pong(n: number): number {\n\treturn n > 0 ? ping(n - 1) : 0;\n}",
        |analysis, file| {
            let ping = function_of_name(analysis.project, file, "ping");
            let pong = function_of_name(analysis.project, file, "pong");
            let root = analysis.summarize(file, ping).total();
            let member = analysis.summarize(file, pong).total();

            assert_eq!(root.cost, Cost::N);
            assert_eq!(member.cost, Cost::N);
            assert_eq!(
                labels_of(&member.chain)[0],
                "[recursion cycle with ping()]"
            );
            assert_eq!(labels_of(&root.chain), labels_of(&member.chain)[1..]);
        },
    );
}

#[test]
fn a_costed_callback_multiplies_inside_its_caller() {
    run_with_source(
        "function each(xs: number[], visit: (x: number) => void) {\n\tfor (const x of xs) visit(x);\n}\nexport function f(xs: number[], ys: number[]) {\n\teach(xs, (x) => {\n\t\tys.indexOf(x);\n\t});\n}",
        |analysis, file| {
            let f = function_of_name(analysis.project, file, "f");
            let first = analysis.summarize(file, f);
            let second = analysis.summarize(file, f);

            assert_eq!(first.total().cost, Cost { n: 2, log: 0 });
            assert_eq!(first, second);
            assert_eq!(labels_of(&first.total().chain), vec!["call each()"]);
        },
    );
}

#[test]
fn functions_are_named_by_their_shape() {
    run_with_source(
        "export default function () {}\nexport function plain() {\n\treturn () => 1;\n}\nexport const arrow = () => 1;\nexport class Box {\n\tconstructor() {}\n\tget size() {\n\t\treturn 1;\n\t}\n\t#hidden() {}\n\thandler = () => 1;\n}\nexport const Anonymous = class {\n\trun() {}\n};\nexport const object = {\n\tmethod() {},\n\tproperty: function () {},\n};\nexport const named = function inner() {};\n[1].map(function () {});\n",
        |analysis, file| {
            let names: Vec<String> = analysis
                .project
                .file(file)
                .semantic
                .nodes()
                .iter()
                .filter_map(|node| match node.kind() {
                    oxc_ast::AstKind::Function(function) => {
                        Some(olint::declarations::FunctionNode::Function(function))
                    }
                    oxc_ast::AstKind::ArrowFunctionExpression(arrow) => {
                        Some(olint::declarations::FunctionNode::Arrow(arrow))
                    }
                    _ => None,
                })
                .map(|function| analysis.name_of(file, function))
                .collect();

            assert_eq!(
                names,
                vec![
                    "<default>",
                    "plain",
                    "<returned fn>",
                    "arrow",
                    "Box.constructor",
                    "Box.size",
                    "Box.#hidden",
                    "Box.handler",
                    "<class>.run",
                    "method",
                    "property",
                    "named",
                    "<callback>",
                ]
            );
        },
    );
}

#[test]
fn reportable_skips_inline_callbacks_and_ignored_functions() {
    run_with_source(
        "export function kept(xs: number[]) {\n\treturn xs.map((x) => x + 1);\n}\n// @perf ignore\nexport function skipped() {}\n",
        |analysis, _| {
            let names: Vec<String> = analysis
                .reportable()
                .into_iter()
                .map(|(target, function)| analysis.name_of(target, function))
                .collect();

            assert_eq!(names, vec!["kept"]);
        },
    );
}

#[test]
fn an_ignored_function_is_absent_and_its_calls_cost_nothing() {
    let files = [
        ("tsconfig.json", "{}"),
        ("olint.config.json", r#"{ "entrypoints": ["index.ts"] }"#),
        (
            "index.ts",
            "// @perf ignore\nexport function skipped(xs: number[]) {\n\treturn xs.indexOf(1);\n}\nexport function caller(xs: number[]) {\n\tfor (const x of xs) skipped(xs);\n}\n",
        ),
    ];

    run_in_project(&files, |project, root| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let file = file_of(project, root, "index.ts");
        let config = read_config(project, None).expect("config reads");
        let reportable: Vec<String> = analysis
            .reportable()
            .into_iter()
            .map(|(target, function)| analysis.name_of(target, function))
            .collect();
        let public: Vec<String> = public_functions(&mut analysis, &config)
            .into_iter()
            .map(|public| analysis.name_of(public.file, public.function))
            .collect();
        let caller = function_of_name(project, file, "caller");
        let part = analysis.summarize(file, caller).total();

        assert_eq!(reportable, vec!["caller"]);
        assert_eq!(public, vec!["caller"]);
        assert_eq!(part.cost, Cost::N);
        assert_eq!(labels_of(&part.chain), vec!["for-of"]);
    });
}

#[test]
fn a_cold_function_called_beside_a_linear_statement_cascades_linear() {
    run_with_source(
        "/** @perf cold */\nfunction rebuild(rows: number[][]) {\n\tfor (const row of rows) row.indexOf(1);\n}\nexport function f(rows: number[][]) {\n\trebuild(rows);\n\trows.indexOf([]);\n}",
        |analysis, file| {
            let rebuild = function_of_name(analysis.project, file, "rebuild");
            let f = function_of_name(analysis.project, file, "f");
            let own = analysis.summarize(file, rebuild).total();
            let part = analysis.summarize(file, f).total();

            assert_eq!(own.cost, Cost { n: 2, log: 0 });
            assert_eq!(part.cost, Cost::N);
            assert_eq!(labels_of(&part.chain), vec!["rows.indexOf()"]);
        },
    );
}

#[test]
fn a_hot_function_call_wins_over_a_costlier_sibling() {
    run_with_source(
        "/** @perf hot */\nconst lookup = (xs: number[]) => xs.indexOf(1);\nexport function f(rows: number[][], xs: number[]) {\n\tfor (const row of rows) row.indexOf(1);\n\treturn lookup(xs);\n}",
        |analysis, file| {
            let f = function_of_name(analysis.project, file, "f");
            let part = analysis.summarize(file, f).total();

            assert_eq!(part.cost, Cost::N);
            assert_eq!(labels_of(&part.chain), vec!["call lookup()"]);
        },
    );
}

fn total_of(source: &str, name: &str) -> (Cost, Vec<String>) {
    let mut found = (Cost::ONE, Vec::new());

    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, name);
        let part = analysis.summarize(file, function).total();

        found = (part.cost, labels_of(&part.chain));
    });

    found
}

const CALLBACK_SOURCE: &str = "/** @perf cold */\nfunction coldCubic(xs: number[][]): number {\n\tlet sum = 0;\n\tfor (const row of xs) for (const v of row) for (const w of row) sum += v * w;\n\treturn sum;\n}\n/** @perf hot */\nfunction hotConst(x: number[]): number {\n\treturn x.length;\n}\nfunction withHotInside(row: number[]): number {\n\t// @perf hot\n\treturn row.length;\n}\nfunction apply(f: (xs: number[][]) => number, xs: number[][]): number {\n\tconst a = f(xs);\n\tfor (const row of xs) row.at(0);\n\treturn a;\n}\nexport function coldViaMap(xss: number[][][]) {\n\tconst a = xss.map(coldCubic);\n\tfor (const xs of xss) xs.at(0);\n\treturn a;\n}\nexport function hotViaMap(xs: number[][]) {\n\tconst a = xs.map(hotConst);\n\tfor (const row of xs) for (const v of row) v.toFixed();\n\treturn a;\n}\nexport function bodyHotViaMap(xs: number[][]) {\n\tconst a = xs.map(withHotInside);\n\tfor (const row of xs) for (const v of row) v.toFixed();\n\treturn a;\n}\nexport function coldViaParameter(xs: number[][]) {\n\treturn apply(coldCubic, xs);\n}\n";

#[test]
fn a_cold_callback_through_a_stdlib_method_yields_to_a_linear_sibling() {
    assert_eq!(
        total_of(CALLBACK_SOURCE, "coldViaMap"),
        (Cost::N, vec!["for-of".to_string()])
    );
}

#[test]
fn a_hot_callback_through_a_stdlib_method_wins_over_a_costlier_sibling() {
    assert_eq!(
        total_of(CALLBACK_SOURCE, "hotViaMap"),
        (Cost::N, vec!["xs.map()".to_string()])
    );
}

#[test]
fn a_callback_keeps_its_body_preference_inside() {
    assert_eq!(
        total_of(CALLBACK_SOURCE, "bodyHotViaMap").0,
        Cost { n: 2, log: 0 }
    );
}

#[test]
fn a_cold_callback_parameter_call_yields_inside_its_caller() {
    assert_eq!(
        total_of(CALLBACK_SOURCE, "coldViaParameter"),
        (Cost::N, vec!["call apply()".to_string()])
    );
}

#[test]
fn a_cold_recursive_function_keeps_its_recursion_cost() {
    let source = "/** @perf cold */\nexport function walk(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + walk(xs, n - 1);\n}\n";

    assert_eq!(
        total_of(source, "walk"),
        (Cost::N, vec!["recursive call walk()".to_string()])
    );
}

#[test]
fn a_cold_cycle_member_keeps_the_cycle_cost() {
    let source = "export function ping(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + pong(xs, n - 1);\n}\n/** @perf cold */\nfunction pong(xs: number[], n: number): number {\n\treturn ping(xs, n);\n}\n";

    run_with_source(source, |analysis, file| {
        let ping = function_of_name(analysis.project, file, "ping");
        let pong = function_of_name(analysis.project, file, "pong");

        assert_eq!(analysis.summarize(file, ping).total().cost, Cost::N);
        assert_eq!(analysis.summarize(file, pong).total().cost, Cost::N);
    });
}

#[test]
fn a_cold_call_leaves_its_argument_costs_unmarked() {
    let source = "/** @perf cold */\nfunction rebuild(rows: number[][], at: number) {\n\tfor (const row of rows) row.indexOf(at);\n}\nexport function f(rows: number[][], xs: number[]) {\n\trebuild(rows, xs.indexOf(1));\n\treturn 0;\n}\n";

    assert_eq!(
        total_of(source, "f"),
        (Cost::N, vec!["xs.indexOf()".to_string()])
    );
}

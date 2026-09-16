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

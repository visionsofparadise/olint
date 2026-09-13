use olint::cost::Cost;

mod support;

use support::{function_named, with_source};

fn labels_of(chain: &[olint::cost::Factor]) -> Vec<String> {
    chain.iter().map(|factor| factor.label.clone()).collect()
}

#[test]
fn self_recursion_charges_one_n() {
    with_source(
        "export function walk(n: number): number {\n\treturn n > 0 ? walk(n - 1) : 0;\n}",
        |analysis, file| {
            let walk = function_named(analysis.project, file, "walk");
            let part = analysis.summarize(file, walk).total();

            assert_eq!(part.cost, Cost::N);
            assert_eq!(labels_of(&part.chain), vec!["recursive call walk()"]);
        },
    );
}

#[test]
fn a_cycle_member_takes_the_root_summary() {
    with_source(
        "export function ping(n: number): number {\n\treturn n > 0 ? pong(n - 1) : 0;\n}\nexport function pong(n: number): number {\n\treturn n > 0 ? ping(n - 1) : 0;\n}",
        |analysis, file| {
            let ping = function_named(analysis.project, file, "ping");
            let pong = function_named(analysis.project, file, "pong");
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
    with_source(
        "function each(xs: number[], visit: (x: number) => void) {\n\tfor (const x of xs) visit(x);\n}\nexport function f(xs: number[], ys: number[]) {\n\teach(xs, (x) => {\n\t\tys.indexOf(x);\n\t});\n}",
        |analysis, file| {
            let f = function_named(analysis.project, file, "f");
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
    with_source(
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
    with_source(
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

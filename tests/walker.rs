use olint::cost::{Cost, Reading};

mod support;

use support::{function_of_name, run_with_source};

fn reading_of(source: &str, name: &str) -> (Reading, Vec<String>) {
    let mut found = (Reading::empty(), Vec::new());

    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, name);
        let reading = analysis.cost_of_function_body(file, function);
        let labels = reading
            .total()
            .chain
            .iter()
            .map(|factor| factor.label.clone())
            .collect();

        found = (reading, labels);
    });

    found
}

#[test]
fn nested_loops_multiply() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\tfor (const row of rows) {\n\t\tfor (const cell of row) {\n\t\t\tcell.toFixed();\n\t\t}\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost { n: 2, log: 0 });
    assert_eq!(labels, vec!["for-of", "for-of"]);
}

#[test]
fn a_return_inside_a_loop_moves_its_cost_to_the_function_exit() {
    let (reading, _) = reading_of(
        "export function f(flags: boolean[], ys: number[]) {\n\tfor (const flag of flags) {\n\t\tif (flag) {\n\t\t\treturn ys.indexOf(1);\n\t\t}\n\t}\n\treturn -1;\n}",
        "f",
    );

    assert_eq!(reading.function_exit.cost, Cost::N);
    assert_eq!(reading.function_exit.chain[0].label, "ys.indexOf()");
}

#[test]
fn a_spread_of_a_rest_parameter_costs_nothing() {
    let (rest, _) = reading_of(
        "export function f(...xs: number[]) {\n\treturn Math.max(...xs);\n}",
        "f",
    );
    let (plain, labels) = reading_of(
        "export function g(xs: number[]) {\n\treturn Math.max(...xs);\n}",
        "g",
    );

    assert_eq!(rest.total().cost, Cost::ONE);
    assert_eq!(plain.total().cost, Cost::N);
    assert_eq!(labels, vec!["spread ...xs"]);
}

#[test]
fn sorting_a_declared_array_reads_n_log_n() {
    let (reading, labels) = reading_of("export function f(xs: number[]) {\n\txs.sort();\n}", "f");

    assert_eq!(reading.total().cost, Cost::N_LOG_N);
    assert_eq!(labels, vec!["xs.sort() [n log n]"]);
}

#[test]
fn a_set_of_a_parameter_is_linear() {
    let (reading, labels) = reading_of(
        "export function f(xs: number[]) {\n\treturn new Set(xs);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["new Set(xs)"]);
}

#[test]
fn a_hot_branch_drops_the_other_branch() {
    let (reading, _) = reading_of(
        "export function f(flag: boolean, xs: number[]) {\n\tif (flag) {\n\t\t// @perf hot\n\t\tflag = false;\n\t} else {\n\t\txs.indexOf(1);\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
}

#[test]
fn a_cost_tag_on_a_loop_reads_as_its_tag() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf O(N)\n\tfor (const row of rows) {\n\t\tfor (const cell of row) cell.toFixed();\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["@perf O(N)"]);
}

#[test]
fn a_method_on_a_constructed_instance_charges_its_summary() {
    let (reading, labels) = reading_of(
        "class Engine {\n\trun(xs: number[]) {\n\t\treturn xs.indexOf(1);\n\t}\n}\nexport function f(xs: number[]) {\n\tconst engine = new Engine();\n\treturn engine.run(xs);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["call Engine.run()"]);
}

#[test]
fn a_string_method_on_a_literal_receiver_is_constant() {
    let (reading, _) = reading_of(
        "export function f() {\n\treturn \"a,b\".split(\",\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
}

#[test]
fn a_string_method_on_a_const_of_a_literal_is_constant() {
    let (reading, _) = reading_of(
        "const SEPARATED = `a,b`;\nenum Tone {\n\tLow = \"low\",\n}\nexport function f() {\n\tconst text = \"a,b\";\n\ttext.split(\",\");\n\tSEPARATED.split(\",\");\n\treturn Tone.Low.includes(\"o\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
}

#[test]
fn a_string_method_on_a_parameter_is_linear() {
    let (reading, labels) = reading_of(
        "export function f(text: string) {\n\treturn text.split(\",\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["text.split() [string]"]);
}

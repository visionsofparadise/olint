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
fn a_cold_statement_yields_to_an_unmarked_sibling() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf cold\n\tfor (const row of rows) for (const cell of row) cell.toFixed();\n\tfor (const row of rows) row.at(0);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["for-of"]);
}

#[test]
fn an_all_cold_block_cascades_its_cold_maximum() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf cold\n\tfor (const row of rows) row.at(0);\n\t// @perf cold\n\tfor (const row of rows) for (const cell of row) cell.toFixed();\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost { n: 2, log: 0 });
    assert_eq!(labels, vec!["for-of", "for-of"]);
}

#[test]
fn a_hot_constant_branch_beats_a_linear_branch() {
    let (reading, _) = reading_of(
        "export function f(flag: boolean, xs: number[]) {\n\tif (flag) {\n\t\t// @perf hot\n\t\tflag = false;\n\t} else {\n\t\txs.indexOf(1);\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
}

#[test]
fn a_cold_else_branch_yields_to_the_other_branch() {
    let (reading, labels) = reading_of(
        "export function f(flag: boolean, rows: number[][]) {\n\tif (flag) {\n\t\trows.indexOf([]);\n\t} else {\n\t\t// @perf cold\n\t\tfor (const row of rows) row.indexOf(1);\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["rows.indexOf()"]);
}

#[test]
fn an_ignored_statement_contributes_nothing() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf ignore\n\tfor (const row of rows) for (const cell of row) cell.toFixed();\n\t// @perf cold\n\tfor (const row of rows) row.at(0);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["for-of"]);
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

#[test]
fn hot_and_cold_on_one_node_take_no_preference_and_warn() {
    run_with_source(
        "export function f(rows: number[][]) {\n\t// @perf hot\n\t// @perf cold\n\tfor (const row of rows) row.at(0);\n\tfor (const row of rows) for (const cell of row) cell.toFixed();\n}",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "f");
            let reading = analysis.cost_of_function_body(file, function);
            let warnings: Vec<String> = analysis.warnings.iter().cloned().collect();

            assert_eq!(reading.total().cost, Cost { n: 2, log: 0 });
            assert_eq!(
                warnings,
                vec!["@perf hot and @perf cold conflict at index.ts:4; the node takes no preference"]
            );
        },
    );
}

#[test]
fn a_concatenation_of_static_strings_is_constant() {
    let (reading, _) = reading_of(
        "const PREFIX = \"a\";\nexport function f() {\n\tconst text = PREFIX + \",\" + `b`;\n\ttext.split(\",\");\n\treturn (\"a\" + 1).split(\",\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
}

#[test]
fn a_concatenation_with_a_parameter_is_linear() {
    let (reading, _) = reading_of(
        "export function f(tail: string) {\n\treturn (\"a,\" + tail).split(\",\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
}

#[test]
fn a_string_method_on_a_readonly_field_is_constant() {
    let (reading, _) = reading_of(
        "class Holder {\n\treadonly separated = \"a,b\";\n\tloose = \"a,b\";\n}\nexport function f(holder: Holder) {\n\tholder.separated.split(\",\");\n\treturn holder.loose.split(\",\");\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(
        reading.total().chain[0].label,
        "holder.loose.split() [string]"
    );
}

#[test]
fn a_loop_keeps_its_cold_body_mark_beside_a_linear_sibling() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\tfor (const row of rows) {\n\t\t// @perf cold\n\t\tfor (const cell of row) cell.toFixed();\n\t}\n\trows.indexOf([]);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["rows.indexOf()"]);
}

#[test]
fn an_if_without_else_yields_its_cold_branch_to_the_empty_else() {
    let (reading, labels) = reading_of(
        "export function f(flag: boolean, rows: number[][]) {\n\tif (flag) {\n\t\t// @perf cold\n\t\tfor (const row of rows) row.indexOf(1);\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::ONE);
    assert!(labels.is_empty());
}

#[test]
fn a_cold_scoped_budget_loop_yields_to_its_linear_sibling() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][], width: number) {\n\tfor (let r = 0; r < rows.length; r++) {\n\t\tconst row = rows[r];\n\t\tlet i = 0;\n\t\t// @perf cold\n\t\twhile (i < width) {\n\t\t\tfor (const v of row) v;\n\t\t\ti++;\n\t\t}\n\t\tfor (const v of row) v;\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost { n: 2, log: 0 });
    assert_eq!(labels, vec!["for", "for-of"]);
}

#[test]
fn a_cold_drained_budget_loop_yields_to_its_linear_sibling() {
    let (reading, labels) = reading_of(
        "export function f(n: number, xs: number[]) {\n\tlet i = 0;\n\tfor (let j = 0; j < xs.length; j++) {\n\t\t// @perf cold\n\t\twhile (i < n) {\n\t\t\tfor (const x of xs) x;\n\t\t\ti++;\n\t\t}\n\t}\n\treturn xs.indexOf(1);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["xs.indexOf()"]);
}

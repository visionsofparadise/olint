use olint::cost::{Cost, Part, Reading};
use olint::unknowns::Unknowns;
use std::cell::RefCell;
use std::ops::Deref;

struct TestReading {
    reading: Reading,
    unknowns: RefCell<Unknowns>,
    traces: RefCell<olint::trace::TraceArena>,
}
impl TestReading {
    fn total(&self) -> Part {
        self.reading.total(
            &mut self.unknowns.borrow_mut(),
            &mut self.traces.borrow_mut(),
        )
    }
}
impl Deref for TestReading {
    type Target = Reading;
    fn deref(&self) -> &Reading {
        &self.reading
    }
}

mod support;

#[test]
fn set_callback_fixture_declarations_typecheck() {
    let script = r#"
const path = require('node:path');
const fs = require('node:fs');
const root = process.argv[1];
const ts = require(path.join(root, 'node_modules/typescript'));
const file = path.join(root, 'tests/fixtures/model/src/methods.ts');
const parsed = ts.createSourceFile(file, fs.readFileSync(file, 'utf8'), ts.ScriptTarget.ES2022, true);
const names = new Set(['makeCallbackSet', 'makeDoubled', 'setCallback', 'RoundEngine', 'makeRoundEngine', 'setCallbackCallsMethod']);
const selected = parsed.statements.filter(node => node.name && names.has(node.name.text));
if (selected.length !== names.size) throw new Error('callback fixture declarations missing');
const source = selected.map(node => node.getText(parsed)).join('\n');
const virtual = path.join(root, 'callback-fixture.ts');
const options = { strict: true, noEmit: true, target: ts.ScriptTarget.ES2022, types: [] };
const host = ts.createCompilerHost(options);
const read = host.readFile.bind(host);
host.readFile = name => path.resolve(name) === virtual ? source : read(name);
const program = ts.createProgram([virtual], options, host);
const diagnostics = ts.getPreEmitDiagnostics(program);
if (diagnostics.length) throw new Error(ts.formatDiagnosticsWithColorAndContext(diagnostics, {
    getCanonicalFileName: name => name,
    getCurrentDirectory: () => root,
    getNewLine: () => '\n'
}));
"#;
    let output = std::process::Command::new("node")
        .arg("-e")
        .arg(script)
        .arg(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Node and TypeScript are required to verify callback fixtures");

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

use support::{function_of_name, run_with_source};

fn reading_of(source: &str, name: &str) -> (TestReading, Vec<String>) {
    let mut found = (
        TestReading {
            reading: Reading::empty(),
            unknowns: RefCell::new(Unknowns::default()),
            traces: RefCell::new(Default::default()),
        },
        Vec::new(),
    );

    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, name);
        let reading = support::legacy_reading_of(analysis, file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let labels = support::trace_nodes(&analysis.traces, part.trace)
            .iter()
            .map(|node| node.label.clone())
            .collect();

        found = (
            TestReading {
                reading,
                unknowns: RefCell::new(std::mem::take(&mut analysis.unknowns)),
                traces: RefCell::new(std::mem::take(&mut analysis.traces)),
            },
            labels,
        );
    });

    found
}

#[test]
fn nested_loops_multiply() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\tfor (const row of rows) {\n\t\tfor (const cell of row) {\n\t\t\tvoid cell;\n\t\t}\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::parse("O(N^2)").unwrap());
    assert_eq!(labels, vec!["for-of", "for-of"]);
}

#[test]
fn a_return_inside_a_loop_moves_its_cost_to_the_function_exit() {
    let (reading, _) = reading_of(
        "export function f(flags: boolean[], ys: number[]) {\n\tfor (const flag of flags) {\n\t\tif (flag) {\n\t\t\treturn ys.indexOf(1);\n\t\t}\n\t}\n\treturn -1;\n}",
        "f",
    );

    assert_eq!(reading.function_exit.cost, Cost::N);
    assert_eq!(
        reading
            .traces
            .borrow()
            .node(reading.function_exit.trace.unwrap())
            .unwrap()
            .label,
        "ys.indexOf()"
    );
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
fn set_union_uses_a_callable_set_like_object_as_data() {
    let (reading, _) = reading_of(
        r"export function f(s: Set<number>, xs: number[]) {
            function other() { return xs.map(x => x); }
            other.size = 0;
            other.has = () => false;
            other.keys = function* () {};
            return s.union(other);
        }",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
}

#[test]
fn a_cold_statement_yields_to_an_unmarked_sibling() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf cold\n\tfor (const row of rows) for (const cell of row) void cell;\n\tfor (const row of rows) void row;\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["for-of"]);
}

#[test]
fn an_all_cold_block_cascades_its_cold_maximum() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf cold\n\tfor (const row of rows) void row;\n\t// @perf cold\n\tfor (const row of rows) for (const cell of row) void cell;\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::parse("O(N^2)").unwrap());
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
        "export function f(flag: boolean, rows: number[][]) {\n\tif (flag) {\n\t\trows.indexOf([]);\n\t} else {\n\t\t// @perf cold\n\t\tfor (const row of rows) for (const value of row) void value;\n\t}\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["rows.indexOf()"]);
}

#[test]
fn an_ignored_statement_contributes_nothing() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf ignore\n\tfor (const row of rows) for (const cell of row) void cell;\n\t// @perf cold\n\tfor (const row of rows) void row;\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["for-of"]);
}

#[test]
fn a_cost_tag_on_a_loop_reads_as_its_tag() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\t// @perf O(N)\n\tfor (const row of rows) {\n\t\tfor (const cell of row) void cell;\n\t}\n}",
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
        "export function f(rows: number[][]) {\n\t// @perf hot\n\t// @perf cold\n\tfor (const row of rows) void row;\n\tfor (const row of rows) for (const cell of row) void cell;\n}",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "f");
            let reading = support::legacy_reading_of(analysis, file, function);
            let warnings: Vec<String> = analysis.warnings.iter().cloned().collect();

            assert_eq!(reading.total(&mut analysis.unknowns, &mut analysis.traces).cost, Cost::parse("O(N^2)").unwrap());
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

    let trace = reading.total().trace.unwrap();

    assert_eq!(
        reading.traces.borrow().node(trace).unwrap().label,
        "holder.loose.split() [string]"
    );
}

#[test]
fn a_loop_keeps_its_cold_body_mark_beside_a_linear_sibling() {
    let (reading, labels) = reading_of(
        "export function f(rows: number[][]) {\n\tfor (const row of rows) {\n\t\t// @perf cold\n\t\tfor (const cell of row) void cell;\n\t}\n\trows.indexOf([]);\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);
    assert_eq!(labels, vec!["rows.indexOf()"]);
}

#[test]
fn an_if_without_else_yields_its_cold_branch_to_the_empty_else() {
    let (reading, labels) = reading_of(
        "export function f(flag: boolean, rows: number[][]) {\n\tif (flag) {\n\t\t// @perf cold\n\t\tfor (const row of rows) for (const value of row) void value;\n\t}\n}",
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

    assert_eq!(reading.total().cost, Cost::parse("O(N^2)").unwrap());
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

#[test]
fn an_erased_this_parameter_keeps_the_callback_work_in_its_call() {
    let (reading, labels) = reading_of(
        "function invoke(this: void, callback: () => number): number {\n\treturn callback();\n}\nexport function f(values: number[]) {\n\treturn invoke(() => {\n\t\tlet total = 0;\n\t\tfor (const x of values) total += x;\n\t\treturn total;\n\t});\n}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::parse("O(N)").unwrap());
    assert_eq!(labels, vec!["call invoke()"]);
}

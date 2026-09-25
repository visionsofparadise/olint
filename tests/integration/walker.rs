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

    fn channel(&self, completion: olint::flow::Completion) -> Part {
        self.reading
            .part_of(olint::cost::ExecutionPhase::Immediate, completion)
    }

    fn function_exit(&self) -> Part {
        self.channel(olint::flow::Completion::Return).max(
            self.channel(olint::flow::Completion::Throw),
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

use crate::support;

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

use support::{
    assert_projected_selected as assert_dispatched, function_of_name, index_of, run_with_source,
    selected_result_in as dispatched_result_in, SelectedResult as DispatchedResult,
};

fn projected_reading(mut reading: Reading) -> Reading {
    for (_, _, part) in &mut reading.completions {
        part.cost = support::projected_class_of(&part.cost);
    }

    reading
}

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
        let reading = projected_reading(support::legacy_reading_of(analysis, file, function));

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

    let exit = reading.function_exit();

    assert_eq!(exit.cost, Cost::N);
    assert_eq!(
        reading
            .traces
            .borrow()
            .node(exit.trace.unwrap())
            .unwrap()
            .label,
        "ys.indexOf()"
    );
}

#[test]
fn a_spread_of_a_rest_parameter_copies_its_collected_arguments() {
    let (rest, rest_labels) = reading_of(
        "export function f(...xs: number[]) {\n\treturn Math.max(...xs);\n}",
        "f",
    );
    let (plain, labels) = reading_of(
        "export function g(xs: number[]) {\n\treturn Math.max(...xs);\n}",
        "g",
    );

    assert_eq!(rest.total().cost, Cost::N);
    assert_eq!(rest_labels, vec!["spread ...xs"]);
    assert_eq!(plain.total().cost, Cost::N);
    assert_eq!(labels, vec!["spread ...xs"]);
}

#[test]
fn rest_parameter_allocation_enters_the_function_summary() {
    let (rest, labels) = reading_of(
        "export function f(...xs: number[]) {\n\treturn xs.length;\n}",
        "f",
    );
    let (pattern, pattern_labels) = reading_of(
        "export function g(...[head]: number[]) {\n\treturn head;\n}",
        "g",
    );

    assert_eq!(rest.total().cost, Cost::N);
    assert_eq!(labels, vec!["spread ...xs"]);
    assert_eq!(pattern.total().cost, Cost::N);
    assert_eq!(pattern_labels, vec!["spread ...[head]"]);
}

#[test]
fn binding_rests_copy_their_source_and_fixed_sources_stay_constant() {
    let (array, array_labels) = reading_of(
        "export function f(xs: number[]) {\n\tconst [head, ...rest] = xs;\n\treturn head + rest.length;\n}",
        "f",
    );
    let (object, object_labels) = reading_of(
        "export function g(o: Record<string, number>) {\n\tconst { a, ...rest } = o;\n\treturn a;\n}",
        "g",
    );
    let (fixed_array, _) = reading_of(
        "export function h() {\n\tconst [head, ...rest] = [1, 2, 3];\n\treturn head + rest.length;\n}",
        "h",
    );
    let (fixed_object, _) = reading_of(
        "export function k() {\n\tconst { a, ...rest } = { a: 1, b: 2 };\n\treturn a;\n}",
        "k",
    );

    assert_eq!(array.total().cost, Cost::N);
    assert_eq!(array_labels, vec!["spread ...rest"]);
    assert_eq!(object.total().cost, Cost::N);
    assert_eq!(object_labels, vec!["spread ...rest"]);
    assert_eq!(fixed_array.total().cost, Cost::ONE);
    assert_eq!(fixed_object.total().cost, Cost::ONE);
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
fn an_object_assign_is_charged_by_every_argument_it_copies() {
    let (fresh_target, fresh_labels) = reading_of(
        "export function f(source: Record<string, number>) {\n\treturn Object.assign({}, source);\n}",
        "f",
    );
    let (constant_sources, _) = reading_of(
        "export function g() {\n\treturn Object.assign({}, { a: 1 }, { b: 2 });\n}",
        "g",
    );
    let (named_target, named_labels) = reading_of(
        "export function h(out: Record<string, number>, a: Record<string, number>, b: Record<string, number>) {\n\treturn Object.assign(out, a, b);\n}",
        "h",
    );

    assert_eq!(fresh_target.total().cost, Cost::N);
    assert_eq!(fresh_labels, vec!["Object.assign({})"]);
    assert_eq!(constant_sources.total().cost, Cost::ONE);
    assert_eq!(named_target.total().cost, Cost::N);
    assert_eq!(named_labels, vec!["Object.assign(out)"]);
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
            let reading = projected_reading(support::legacy_reading_of(analysis, file, function));


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
fn a_string_method_on_a_readonly_field_is_linear() {
    let (reading, _) = reading_of(
        "class Holder {
	readonly separated = \"a,b\";
	constructor(text?: string) {
		if (text) this.separated = text;
	}
}
export function f(holder: Holder) {
	return holder.separated.split(\",\");
}",
        "f",
    );

    assert_eq!(reading.total().cost, Cost::N);

    let trace = reading.total().trace.unwrap();

    assert_eq!(
        reading.traces.borrow().node(trace).unwrap().label,
        "holder.separated.split() [string]"
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
        "export function f(rows: number[][], width: number) {\n\tfor (let r = 0; r < rows.length && rows.length >= 0 && rows.length <= 4294967295; r++) {\n\t\tconst row = rows[r];\n\t\tlet i = 0;\n\t\t// @perf cold\n\t\twhile (i >= 0 && i < width && width >= 0 && width <= 1000000000) {\n\t\t\tfor (const v of row) v;\n\t\t\ti++;\n\t\t}\n\t\tfor (const v of row) v;\n\t}\n}",
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

const CUBIC: &str = "for (const a of xs) for (const b of xs) for (const c of xs) void c;";
const INDEXED_CUBIC: &str = "if (xs.length >= 0 && xs.length <= 4294967295) { for (let a = 0; a < xs.length; a++) for (let b = 0; b < xs.length; b++) for (let c = 0; c < xs.length; c++) void c; }";

fn dispatched_result_of(source: &str, types: olint::analysis::TypeMode) -> DispatchedResult {
    dispatched_result_in(&[("index.ts", source)], types)
}

#[test]
fn runtime_dispatch_includes_known_expensive_bodies_in_both_type_modes() {
    let quadratic = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }";
    let cases = [
        (
            format!("class Base {{ work(xs: number[]) {{}} }}\nclass Derived extends Base {{ work(xs: number[]) {{ {CUBIC} }} }}\nexport function selected(x: Base, xs: number[]) {{ x.work(xs); }}\nselected(new Derived(), []);"),
            "O(N^3)",
        ),
        (
            format!("function make(flag: boolean) {{ return flag ? {{ work(xs: number[]) {{}} }} : {{ work(xs: number[]) {{ {CUBIC} }} }}; }}\nexport function selected(flag: boolean, xs: number[]) {{ make(flag).work(xs); }}"),
            "O(N^3)",
        ),
        (
            format!("function expensive(xs: number[]) {{ {CUBIC} }}\nconst obj = {{ work(xs: number[]) {{}} }};\nobj.work = expensive;\nexport function selected(xs: number[]) {{ obj.work(xs); }}"),
            "O(N^3)",
        ),
        (
            format!("{quadratic}\nexport function selected(xs: number[]) {{ xs.includes = () => quadratic(xs) > 0; return xs.includes(0); }}"),
            "O(N^2)",
        ),
        (
            format!("function expensive(xs: number[]) {{ {CUBIC} }}\nclass K {{ get run() {{ return expensive; }} }}\nexport function selected(k: K, xs: number[]) {{ k.run(xs); }}"),
            "O(N^3)",
        ),
        (
            "declare const replacement: (value: number) => boolean;\n(Array.prototype as any).includes = replacement;\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string(),
            "O(N)",
        ),
    ];

    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for (source, expected) in &cases {
            let (cost, reasons) = dispatched_result_of(source, types);

            assert_eq!(cost, Cost::parse(expected).unwrap(), "{types:?} {source}");
            assert!(
                reasons.contains(&olint::unknowns::UnknownReason::Target),
                "{types:?} {source}: {reasons:?}"
            );
        }
    }
}

#[test]
fn exact_calls_and_unreplaced_intrinsics_stay_precise() {
    let cases = [
        format!("function cubic(xs: number[]) {{ {CUBIC} }}\nconst alias = cubic;\nexport function selected(xs: number[]) {{ alias(xs); }}"),
        format!("function a(xs: number[]) {{ {CUBIC} }}\nfunction b(xs: number[]) {{}}\nconst pick = Math.random() > 0.5 ? a : b;\nexport function selected(xs: number[]) {{ pick(xs); }}"),
        "const other = { includes: (value: number) => true };\nother.includes = (value: number) => false;\nconst unrelated: number[] = [];\n(unrelated as any).indexOf = () => 0;\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string(),
    ];
    let expected = ["O(N^3)", "O(N^3)", "O(N)"];

    for (source, expected) in cases.iter().zip(expected) {
        let (cost, reasons) = dispatched_result_of(source, olint::analysis::TypeMode::Syntactic);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{source}");
        assert!(reasons.is_empty(), "{source}: {reasons:?}");
    }
}

#[test]
fn replacements_resolve_keys_prototypes_and_builtin_subclasses() {
    let slow = format!("function slow(xs: number[]) {{ {INDEXED_CUBIC} return true; }}");
    let cube = format!("function cube(xs: number[]) {{ {INDEXED_CUBIC} return 0; }}");
    let cases = [
        (index_of(format!("{slow}\nconst k = 'includes';\nexport function selected(xs: number[]) {{ (xs as any)[k] = () => slow(xs); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ (xs as any)[`includes`] = () => slow(xs); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ (xs as any).__proto__ = {{ includes: () => slow(xs) }}; return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ Object.setPrototypeOf(xs, {{ includes: () => slow(xs) }}); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[], ys: number[], flag: boolean) {{ if (flag) (ys as any).map = () => []; return xs.map(() => cube(xs)); }}")), "O(N^4)", true),
        (index_of(format!("class MyArr extends Array<number> {{ includes(v: number): boolean {{ const xs: number[] = this; {CUBIC} return true; }} }}\nexport function selected(xs: number[]) {{ return xs.includes(0); }}\nselected(new MyArr());")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn unresolved_replacements_invalidate_intrinsics_and_keep_known_work() {
    let loop_over = "for (const x of xs) void x;";
    let cases = [
        (index_of("function install(target: any, name: string, value: unknown) { target[name] = value; }\nexport function selected(xs: number[]) { install(xs, 'includes', () => true); return xs.includes(0); }".to_string()), "O(N)", true),
        (index_of("function install(target: object, name: string, value: unknown) { Object.defineProperty(target, name, { value }); }\nexport function selected(xs: number[]) { install(xs, 'includes', () => true); return xs.includes(0); }".to_string()), "O(N)", true),
        (index_of("const proto: any = Array.prototype;\nfunction patch(name: string, f: unknown) { proto[name] = f; }\npatch('includes', () => true);\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string()), "O(N)", true),
        (index_of("function patch(name: string, f: unknown) { (Array.prototype as any)[name] = f; }\npatch('includes', () => true);\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string()), "O(N)", true),
        (index_of(format!("const proto: any = Array.prototype;\nproto.includes = function () {{ return true; }};\nexport function selected(xs: number[]) {{ const zs = [1, 2, 3]; zs.includes(0); {loop_over} }}")), "O(N)", true),
        (index_of(format!("(globalThis as any).Array.prototype.includes = function () {{ return true; }};\nexport function selected(xs: number[]) {{ const zs = [1, 2, 3]; zs.includes(0); {loop_over} }}")), "O(N)", true),
        (vec![("index.ts", format!("import './patch';\nexport function selected(xs: number[]) {{ const zs = [1, 2]; zs.includes(0); {loop_over} }}")), ("patch.ts", "export {}; const p: any = Array.prototype; p.includes = () => true;".to_string())], "O(N)", true),
        (index_of("function patch(k: string, f: unknown) { (String.prototype as any)[k] = f; }\npatch('trim', () => '');\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string()), "O(N)", false),
        (index_of("function fill(ys: unknown[], v: unknown) { for (let i = 0; i < 3; i++) ys[i] = v; ys[0] = v; }\nfill([], () => 0);\nexport function selected(xs: number[]) { return xs.includes(0); }".to_string()), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn dispatch_follows_mixins_computed_symbol_and_created_members() {
    let base = "class Base { work(xs: number[]) {} }";
    let run = "export function selected(x: Base, xs: number[]) { x.work(xs); }";
    let cases = [
        (index_of(format!("{base}\nconst Mixin = <T extends new (...args: any[]) => Base>(B: T) => class extends B {{ work(xs: number[]) {{ {CUBIC} }} }};\nclass D extends Mixin(Base) {{}}\n{run}\nselected(new D(), []);")), "O(N^3)", true),
        (index_of(format!("{base}\nconst D = class extends Base {{ work(xs: number[]) {{ {CUBIC} }} }};\n{run}\nselected(new D(), []);")), "O(N^3)", true),
        (index_of(format!("{base}\nclass D extends Base {{ ['work'](xs: number[]) {{ {CUBIC} }} }}\n{run}\nselected(new D(), []);")), "O(N^3)", true),
        (index_of(format!("const k = 'work';\n{base}\nclass D extends Base {{ [k](xs: number[]) {{ {CUBIC} }} }}\n{run}\nselected(new D(), []);")), "O(N^3)", true),
        (index_of(format!("const s = Symbol('work');\nclass Base {{ [s](xs: number[]) {{}} }}\nclass D extends Base {{ [s](xs: number[]) {{ {CUBIC} }} }}\nexport function selected(x: Base, xs: number[]) {{ x[s](xs); }}\nselected(new D(), []);")), "O(N^3)", true),
        (index_of(format!("function expensive(xs: number[]) {{ {CUBIC} }}\nexport function selected(xs: number[]) {{ const o = Object.create({{ work: expensive }}); o.work(xs); }}")), "O(N^3)", true),
        (vec![("index.ts", format!("import {{ Base }} from './base';\nimport './derived';\n{run}")), ("base.ts", format!("export {base}")), ("derived.ts", format!("import {{ Base }} from './base'; export class D extends Base {{ work(xs: number[]) {{ {CUBIC} }} }}"))], "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn replacements_follow_prototype_provenance_globals_and_proven_numeric_keys() {
    let slow = format!("function slow(xs: number[]) {{ {INDEXED_CUBIC} return true; }}");
    let fresh = "export function selected(xs: number[]) { const zs = [1, 2, 3]; zs.includes(0); for (const x of xs) void x; }";
    let cases = [
        (index_of(format!("{slow}\nfunction install(target: any, k: number, value: unknown) {{ target[k] = value; }}\nexport function selected(xs: number[]) {{ install(xs, 'includes' as any, () => slow(xs)); return xs.includes(0); }}")), "O(N)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ let k: number = 'includes' as any; (xs as any)[k] = () => slow(xs); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\ndeclare const k: number;\nexport function selected(xs: number[]) {{ (xs as any)[k] = () => slow(xs); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("function cube(xs: number[]) {{ {CUBIC} }}\nexport function selected(xs: number[], i: number) {{ const t: Record<number, (ys: number[]) => void> = {{ 0: () => {{}} }}; t[i] = cube; t[0](xs); }}")), "O(N^3)", true),
        (index_of(format!("function cube(xs: number[]) {{ {CUBIC} }}\nexport function selected(xs: number[], i: number) {{ const t: Array<(ys: number[]) => void> = [() => {{}}]; t[i] = cube; t[0](xs); }}")), "O(N^3)", true),
        (index_of(format!("function patch(p: any, k: string, f: unknown) {{ p[k] = f; }}\npatch(Array.prototype, 'includes', () => true);\n{fresh}")), "O(N)", true),
        (index_of(format!("function patch(p: any) {{ p.includes = function () {{ return true; }}; }}\npatch(Array.prototype);\n{fresh}")), "O(N)", true),
        (index_of(format!("(Object.getPrototypeOf([]) as any).includes = function () {{ return true; }};\n{fresh}")), "O(N)", true),
        (index_of(format!("(Array as any)['prototype'].includes = function () {{ return true; }};\n{fresh}")), "O(N)", true),
        (index_of(format!("const protos = {{ array: Array.prototype as any }};\nprotos.array.includes = function () {{ return true; }};\n{fresh}")), "O(N)", true),
        (index_of("export function selected(xs: number[]) { const ys: any = []; ys.__proto__.includes = function () { return true; }; const zs = [1, 2, 3]; zs.includes(0); for (const x of xs) void x; }".to_string()), "O(N)", true),
        (index_of(format!("function slowKeys(xs: number[]) {{ {CUBIC} return []; }}\n(globalThis as any).Object = {{ keys: (o: any) => slowKeys(o) }};\nexport function selected(xs: number[]) {{ return Object.keys(xs); }}")), "O(N^3)", true),
        (index_of("function install(name: string, value: unknown) { (globalThis as any)[name] = value; }\ninstall('Object', { keys: () => [] });\nexport function selected(xs: number[]) { return Object.keys(xs); }".to_string()), "O(N)", true),
        (index_of("function install(name: string, value: unknown) { (globalThis as any)[name] = value; }\ninstall('structuredClone', () => 0);\nexport function selected(xs: number[]) { return structuredClone(xs); }".to_string()), "O(N)", true),
        (index_of("function place(ys: unknown[], at: number, v: unknown) { ys[at] = v; }\nplace([], 0, () => 0);\nexport function selected(xs: number[], ys: unknown[]) { for (let i = 0; i < 3; i++) (xs as any)[i] = ys[i]; let j = 0; j = j + 1; (xs as any)[j * 2] = ys[0]; return xs.includes(0); }".to_string()), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn class_prototypes_supply_created_and_replaced_prototype_members() {
    let classes = format!("function cube(xs: number[]) {{ {CUBIC} }}\nclass Base {{ work(xs: number[]) {{}} }}\nclass D extends Base {{ work(xs: number[]) {{ {CUBIC} }} }}");
    let cases = [
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ const o = Object.create(D.prototype); o.work(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ const o = {{ work(ys: number[]) {{}} }}; Object.setPrototypeOf(o, D.prototype); o.work(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ const b = new Base(); Object.setPrototypeOf(b, D.prototype); b.work(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ const p = {{ run: cube }}; const q = Object.create(p); const r = Object.create(q); r.run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ const o: any = {{ __proto__: {{ run: cube }} }}; o.run(xs); }}")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn statically_typed_object_owners_may_hold_any_builtin_kind() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let call = "export function selected(xs: number[]) { set(xs, 'includes', () => slow(xs)); return xs.includes(0); }";
    let cases = [
        (index_of(format!("{slow}\nfunction set(target: object, key: string, value: unknown) {{ (target as Record<string, unknown>)[key] = value; }}\n{call}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction set<T extends object>(target: T, key: keyof T, value: unknown) {{ (target as any)[key] = value; }}\n{call}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction set(target: Record<string, unknown>, key: string, value: unknown) {{ target[key] = value; }}\nexport function selected(xs: number[]) {{ set(xs as any, 'includes', () => slow(xs)); return xs.includes(0); }}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction set(target: object, value: unknown) {{ (target as any).includes = value; }}\nexport function selected(xs: number[]) {{ set(xs, () => slow(xs)); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(target: any, key: string, value: unknown) {{ const t: object = target; (t as any)[key] = value; }}\n{call}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction set(target: Set<number>, key: string, value: unknown) {{ (target as any)[key] = value; }}\nexport function selected(xs: number[]) {{ set(new Set(xs), 'includes', () => slow(xs)); return xs.includes(0); }}")), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn declared_builtin_kinds_need_construction_or_call_evidence() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cases = [
        (index_of(format!("{slow}\nfunction set(target: Set<number>, key: string, value: unknown) {{ (target as any)[key] = value; }}\nexport function selected(xs: number[]) {{ set(xs as any, 'includes', () => slow(xs)); return xs.includes(0); }}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction set(target: Set<number>, value: unknown) {{ (target as any).includes = value; }}\nexport function selected(xs: number[]) {{ set(xs as any, () => slow(xs)); return xs.includes(0); }}")), "O(N^3)", true),
        (index_of("function set(target: string, value: unknown) { (target as any).includes = value; }\nset(Array.prototype as any, () => true);\nexport function selected(xs: number[]) { const zs = [1, 2]; return zs.includes(0) && xs.includes(0); }".to_string()), "O(N)", true),
        (index_of(format!("{slow}\nfunction set(target: Set<number>, value: unknown) {{ (target as any).includes = value; }}\nexport function selected(xs: number[]) {{ set(new Set(xs), () => slow(xs)); return xs.includes(0); }}")), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn dispatch_depth_limits_report_resource_exhaustion() {
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}");
    let mut prototypes = vec![
        cube.clone(),
        "export function selected(xs: number[]) {".to_string(),
        "const p0: any = { run: cube };".to_string(),
    ];

    for index in 1..30 {
        prototypes.push(format!(
            "const p{index}: any = Object.create(p{});",
            index - 1
        ));
    }

    prototypes.push("p29.run(xs); }".to_string());

    let mut returns = vec![
        cube,
        "function f0(xs: number[]) { return { run: cube }; }".to_string(),
    ];

    for index in 1..30 {
        returns.push(format!(
            "function f{index}(xs: number[]) {{ return f{}(xs); }}",
            index - 1
        ));
    }

    returns.push("export function selected(xs: number[]) { f29(xs).run(xs); }".to_string());

    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for source in [prototypes.join("\n"), returns.join("\n")] {
            let (_, reasons) = dispatched_result_of(&source, types);

            assert!(
                reasons.contains(&olint::unknowns::UnknownReason::ResourceExhaustion),
                "{types:?} {source}: {reasons:?}"
            );
        }
    }
}

#[test]
fn reassigned_prototypes_and_replaced_constructors_lose_kind_proof() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cases = [
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ const s: any = new Set<number>(); s.__proto__ = Array.prototype; s.__proto__.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nconst s: any = new Set<number>();\nexport function init() {{ s.__proto__ = Array.prototype; }}\nexport function selected(xs: number[]) {{ s.__proto__.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\n(globalThis as any).Set = function () {{ return Array.prototype; }};\nexport function selected(xs: number[]) {{ const s: any = new Set<number>(); s.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{}}\nexport function selected(xs: number[]) {{ const base: any = {{ next: {{ next: {{ run: cube }} }}, run: cheap }}; const o: any = {{}}; Object.setPrototypeOf(o, base); for (let i = 0; i < 2; i++) Object.setPrototypeOf(o, o.next); o.run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ const s: any = new Set<number>(); s.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn global_object_aliases_and_assigned_prototypes_replace_constructors() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let selected = "export function selected(xs: number[]) { const s: any = new Set<number>(); s.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }";
    let cases = [
        (index_of(format!("{slow}\nconst G: any = globalThis;\nG.Set = function () {{ return Array.prototype; }};\n{selected}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction patch(g: any) {{ g.Set = function () {{ return Array.prototype; }}; }}\npatch(globalThis);\n{selected}")), "O(N^3)", true),
        (index_of(format!("{slow}\nconst G: any = globalThis;\nReflect.set(G, 'Set', function () {{ return Array.prototype; }});\n{selected}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function selected(xs: number[]) {{ const s: any = new Set<number>(); Object.assign(s, {{ ['__proto__']: Array.prototype }}); s.__proto__.includes = () => slow(xs); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nconst G: any = {{}};\nG.Set = function () {{ return Array.prototype; }};\n{selected}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn nearer_members_shadow_prototype_writes_and_rebound_prototypes_stay_open() {
    let slow = format!("function slow(xs: number[]) {{ {INDEXED_CUBIC} return true; }}");
    let cube = format!("function cube(xs: number[]) {{ {INDEXED_CUBIC} }}");
    let selected = "export function selected(xs: number[]) { const zs = [1]; return zs.includes(0) && xs.includes(0); }";
    let cases = [
        (index_of(format!("{slow}\nfunction F() {{}}\nconst G: any = F;\nG.prototype = Array.prototype;\n(F as any).prototype.includes = function () {{ return slow([1]); }};\n{selected}")), "O(N)", true),
        (index_of(format!("{slow}\nfunction F() {{}}\nfunction rebind(f: any) {{ f.prototype = Array.prototype; }}\nrebind(F);\n(F as any).prototype.includes = function () {{ return slow([1]); }};\n{selected}")), "O(N)", true),
        (index_of(format!("{cube}\nconst base = {{ m(xs: number[]) {{ cube(xs); }} }};\nexport function link(o: object) {{ Object.setPrototypeOf(o, base); }}\nclass K0 {{ m(xs: number[]) {{}} }}\nexport function selected(xs: number[]) {{ const c = new K0(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\n(C1 as any).prototype.m = function (xs: number[]) {{}};\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nexport function selected(xs: number[]) {{ const c = new (C1 as any)(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nclass K0 {{ m(xs: number[]) {{}} }}\nexport function selected(xs: number[]) {{ const c = new K0(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nexport function selected(xs: number[]) {{ const c = new (C1 as any)(); c.m(xs); }}")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn replaced_array_iteration_leaves_for_of_multiplicity_unproven() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}");
    let fresh = "export function selected(xs: number[]) { const zs = [1, 2, 3]; zs.includes(0); for (const x of xs) void x; }";
    let classes = format!(
        "{cube}
class K0 {{ m(xs: number[]) {{}} }}
class Costly {{ constructor(xs: number[]) {{ cube(xs); }} }}"
    );
    let cases = [
        format!("{cube}
function C0() {{}}
(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};
function C1() {{}}
Object.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);
export function selected(xs: number[]) {{ const c = new (C1 as any)(); c.m(xs); }}"),
        format!("{classes}
export const table: any = {{ B: Costly }};
export function set(t: any, k: string, v: any) {{ t[k] = v; }}
class D extends table.B {{}}
export function selected(xs: number[]) {{ return new D(xs); }}"),
        format!("{slow}
export function selected(xs: number[]) {{ let k: number = 'includes' as any; (xs as any)[k] = () => slow(xs); return xs.includes(0); }}"),
        format!("{slow}
declare const k: number;
export function selected(xs: number[]) {{ (xs as any)[k] = () => slow(xs); return xs.includes(0); }}"),
        format!("function patch(p: any, k: string, f: unknown) {{ p[k] = f; }}
patch(Array.prototype, 'includes', () => true);
{fresh}"),
        format!("{slow}
export function selected(xs: number[]) {{ (xs as any).__proto__ = {{ includes: () => slow(xs) }}; return xs.includes(0); }}"),
        format!("{slow}
export function selected(xs: number[]) {{ Object.setPrototypeOf(xs, {{ includes: () => slow(xs) }}); return xs.includes(0); }}"),
    ];
    let expected = ["O(1)", "O(1)", "O(N)", "O(N)", "O(N)", "O(N)", "O(N)"];

    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for (source, expected) in cases.iter().zip(expected) {
            let (cost, reasons) = dispatched_result_in(&[("index.ts", source.as_str())], types);

            assert_eq!(cost, Cost::parse(expected).unwrap(), "{types:?} {source}");
            assert!(
                reasons.contains(&olint::unknowns::UnknownReason::Bound)
                    && reasons.contains(&olint::unknowns::UnknownReason::Target),
                "{types:?} {source}: {reasons:?}"
            );
        }
    }
}

const QUADRATIC: &str = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }";

#[test]
fn callee_and_constructor_subexpressions_run_before_their_invocation() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const table = {{ run() {{ return 1; }} }}; return table[(quadratic(xs), 'run')](); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function factory() {{ quadratic(xs); return () => 1; }} return factory()(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function factory() {{ return () => quadratic(xs); }} return factory()(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function constructor() {{ quadratic(xs); return class {{}}; }} return new (constructor())(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function constructor() {{ return class {{ constructor() {{ quadratic(xs); }} }}; }} return new (constructor())(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ return xs['map'](() => quadratic(xs)); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nconst k = 'map';\nexport function selected(xs: number[]) {{ return xs[k](() => quadratic(xs)); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ return (() => quadratic(xs))(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ return (function () {{ return quadratic(xs); }})(); }}")), "O(N^2)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn creating_a_function_costs_nothing_until_it_is_invoked() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const f = () => quadratic(xs); return f; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function factory() {{ return () => quadratic(xs); }} return factory(); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const f = () => quadratic(xs); f(); return f; }}")), "O(N^2)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn optional_calls_and_side_effecting_arguments_keep_their_conditional_work() {
    let scan = "function scan(xs: number[]) { for (const x of xs) void x; }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const obj = {{ run() {{ return quadratic(xs); }} }}; return obj?.run?.(); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], run?: (n: number) => number) {{ return run?.(quadratic(xs)); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], f?: () => number) {{ return (f ?? (() => quadratic(xs)))(); }}")), "O(N^2)", true),
        (index_of(format!("{scan}\nexport function selected(xs: number[], run?: (n: number) => void) {{ let n = 1; run?.(n = xs.length); for (let i = 0; i < n && n >= 0 && n <= 4294967295; i++) scan(xs); }}")), "O(N^2)", true),
        (index_of(format!("{scan}\nexport function selected(xs: number[]) {{ let n = 1; const table = {{ run() {{}} }}; table[(n = xs.length, 'run')](); for (let i = 0; i < n && n >= 0 && n <= 4294967295; i++) scan(xs); }}")), "O(N^2)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn destructured_method_callees_recover_their_known_bodies() {
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{}}\nconst o = {{ run: cube }};\nclass K {{ work(xs: number[]) {{ cube(xs); }} }}");
    let cases = [
        (index_of(format!("{cube}\nexport function selected(xs: number[]) {{ const {{ run }} = o; run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[]) {{ const {{ run: r }} = o; r(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(k: K, xs: number[]) {{ const {{ work }} = k; work(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[]) {{ const {{ work }} = new K(); work(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected({{ run }}: {{ run: (xs: number[]) => void }}, xs: number[]) {{ run(xs); }}\nselected(o, []);")), "O(N^3)", true),
        (index_of(format!("{cube}\nfunction use({{ run }}: {{ run: (xs: number[]) => void }}, xs: number[]) {{ run(xs); }}\nexport function selected(xs: number[]) {{ use(o, xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nfunction use({{ run }}: {{ run: (xs: number[]) => void }}, xs: number[]) {{ run(xs); }}\nuse(o, []);\nexport function selected(xs: number[]) {{ use({{ run: cheap }}, xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction use({{ run }}: {{ run: (xs: number[]) => void }}, xs: number[]) {{ run = cube; run(xs); }}\nexport function selected(xs: number[]) {{ use({{ run: cheap }}, xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[]) {{ const {{ inner: {{ run }} }} = {{ inner: o }}; run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[], p: {{ run?: (xs: number[]) => void }}) {{ const {{ run = cube }} = p; run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nconst key = 'run';\nexport function selected(xs: number[]) {{ const {{ [key]: run }} = o; run(xs); }}")), "O(N^3)", true),
        (index_of(format!("{cube}\nexport function selected(xs: number[]) {{ const {{ run, other }} = {{ run: cheap, other: cube }}; run(xs); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn super_member_calls_resolve_the_nearest_base_member() {
    let classes = format!("function cube(xs: number[]) {{ {CUBIC} }}\nclass K0 {{ m(xs: number[]) {{ cube(xs); }} static s(xs: number[]) {{ cube(xs); }} }}\nclass K1 extends K0 {{ m(xs: number[]) {{}} }}");
    let cases = [
        (index_of(format!("{classes}\nclass K2 extends K0 {{ m(xs: number[]) {{ super.m(xs); }} }}\nexport function selected(xs: number[]) {{ new K2().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass K2 extends K1 {{ m(xs: number[]) {{ super.m(xs); }} }}\nexport function selected(xs: number[]) {{ new K2().m(xs); }}")), "O(1)", true),
        (index_of(format!("{classes}\nclass K2 extends K1 {{ static s(xs: number[]) {{ super.s(xs); }} }}\nexport function selected(xs: number[]) {{ K2.s(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass K2 extends K0 {{ m(xs: number[]) {{ const run = () => super.m(xs); run(); }} }}\nexport function selected(xs: number[]) {{ new K2().m(xs); }}")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn imported_destructured_exports_resolve_their_own_declaring_bindings() {
    let exports = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\nconst o = {{ cheapo: cheap, run: cube }};\nexport const {{ cheapo, run }} = o;\nexport const {{ run: renamed }} = o;");
    let mut cases = vec![
        (vec![("index.ts", "import { run } from './a';\nexport function selected(xs: number[]) { run(xs); }".to_string()), ("a.ts", exports.clone())], "O(N^3)", true),
        (vec![("index.ts", "import { renamed } from './a';\nexport function selected(xs: number[]) { renamed(xs); }".to_string()), ("a.ts", exports.clone())], "O(N^3)", true),
        (vec![("index.ts", "import { cheapo } from './a';\nexport function selected(xs: number[]) { cheapo(xs); }".to_string()), ("a.ts", exports)], "O(1)", true),
    ];
    let colliding = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\nconst o = {{ c: cheap, x: cube }};\nexport const {{ x, c }} = o;");

    for padding in 0..16 {
        let declarations: String = (0..padding)
            .map(|index| format!("const d{index} = 0; "))
            .collect();

        cases.push((vec![("index.ts", format!("{declarations}\nimport {{ c }} from './a';\nexport function selected(xs: number[]) {{ c(xs); }}")), ("a.ts", colliding.clone())], "O(1)", true));
    }

    assert_dispatched(&cases);
}

#[test]
fn super_lookups_start_at_the_rewritten_home_prototype() {
    let classes = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\nclass K0 {{ m(xs: number[]) {{ cheap(xs); }} static s(xs: number[]) {{ cheap(xs); }} }}\nclass Other {{ m(xs: number[]) {{ cube(xs); }} static s(xs: number[]) {{ cube(xs); }} }}\nconst other = {{ m(xs: number[]) {{ cube(xs); }} }};");
    let cases = [
        (index_of(format!("{classes}\nclass A extends K0 {{ m(xs: number[]) {{ super.m(xs); }} }}\nObject.setPrototypeOf(A.prototype, Other.prototype);\nexport function selected(xs: number[]) {{ new A().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass A extends K0 {{ m(xs: number[]) {{ super.m(xs); }} }}\n(A.prototype as any).__proto__ = Other.prototype;\nexport function selected(xs: number[]) {{ new A().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass Mid extends K0 {{}}\nclass A extends Mid {{ m(xs: number[]) {{ super.m(xs); }} }}\nObject.setPrototypeOf(Mid.prototype, Other.prototype);\nexport function selected(xs: number[]) {{ new A().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass A extends K0 {{ static s(xs: number[]) {{ super.s(xs); }} }}\nObject.setPrototypeOf(A, Other);\nexport function selected(xs: number[]) {{ A.s(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nconst lit = {{ __proto__: other, m(xs: number[]) {{ super.m(xs); }} }};\nexport function selected(xs: number[]) {{ lit.m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nconst lit = {{ m(xs: number[]) {{ super.m(xs); }} }};\nObject.setPrototypeOf(lit, other);\nexport function selected(xs: number[]) {{ lit.m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass A extends K0 {{ m(xs: number[]) {{ super.m(xs); }} }}\nexport function selected(xs: number[]) {{ new A().m(xs); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn member_constructor_callees_join_runtime_member_dispatch() {
    let constructors = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheapCtor(this: any, _xs: number[]) {{}}\nfunction cubeCtor(this: any, xs: number[]) {{ cube(xs); }}");
    let cases = [
        (index_of(format!("{constructors}\nconst ns = {{ F: cheapCtor }};\nexport function swap() {{ ns.F = cubeCtor; }}\nexport function selected(xs: number[]) {{ return new ((ns.F) as any)(xs); }}")), "O(N^3)", true),
        (index_of(format!("{constructors}\nconst ns = {{ F: cheapCtor }};\nexport function swap() {{ ns.F = cubeCtor; }}\nexport function selected(xs: number[]) {{ return new (ns as any).F(xs); }}")), "O(N^3)", true),
        (index_of(format!("{constructors}\nconst ns = {{ F: cheapCtor }};\nexport function swap() {{ ns['F'] = cubeCtor; }}\nexport function selected(xs: number[]) {{ return new (ns['F'] as any)(xs); }}")), "O(N^3)", true),
        (index_of(format!("{constructors}\nconst ns = {{ C: class {{ constructor(xs: number[]) {{ cube(xs); }} }} }};\nexport function selected(xs: number[]) {{ return new ns.C(xs); }}")), "O(N^3)", true),
        (index_of(format!("{constructors}\nclass D {{ constructor(xs: number[]) {{ cube(xs); }} }}\nconst ns = {{ D }};\nexport function selected(xs: number[]) {{ return new ns.D(xs); }}")), "O(N^3)", true),
        (index_of(format!("{constructors}\nexport function selected(xs: number[]) {{ const C = class {{ constructor(ys: number[]) {{ cube(ys); }} }}; return new C(xs); }}")), "O(N^3)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn destructured_callback_arguments_keep_their_known_bodies() {
    let helpers = format!("{QUADRATIC}\nconst qs = {{ f(ys: number[]) {{ return quadratic(ys); }} }};\nfunction each(xs: number[], cb: (ys: number[]) => number) {{ return cb(xs); }}");
    let cases = [
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ const {{ f }} = qs; return each(xs, f); }}")), "O(N^2)", true),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ const f = qs.f; return each(xs, f); }}")), "O(N^2)", true),
        (index_of(format!("{helpers}\nfunction use({{ run }}: {{ run: (ys: number[]) => number }}, xs: number[]) {{ return each(xs, run); }}\nexport function selected(xs: number[]) {{ return use({{ run: quadratic }}, xs); }}")), "O(N^2)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn parameter_defaults_run_when_omitted_or_undefined() {
    let default = format!(
        "{QUADRATIC}\nfunction defaultParameter(xs: number[], n = quadratic(xs)) {{ return n; }}"
    );
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], n = quadratic(xs)) {{ return n; }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(xs); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(xs, undefined); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(xs, void 0); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(xs, 1); }}")), "O(1)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(xs, null as any); }}")), "O(1)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[], m: number) {{ return defaultParameter(xs, m); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return defaultParameter(...([xs] as [number[]])); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nfunction forward(xs: number[], m?: number) {{ return defaultParameter(xs, m); }}\nexport function selected(xs: number[]) {{ return forward(xs, 2); }}")), "O(1)", false),
        (index_of(format!("{default}\nfunction forward(xs: number[], m?: number) {{ return defaultParameter(xs, m); }}\nexport function selected(xs: number[]) {{ return forward(xs); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nfunction forward(xs: number[], m?: number) {{ m = undefined; return defaultParameter(xs, m); }}\nexport function selected(xs: number[]) {{ return forward(xs, 2); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nconst one = 1;\nexport function selected(xs: number[]) {{ return defaultParameter(xs, one); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn later_parameter_defaults_see_earlier_parameters() {
    let helpers = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\ntype F = (xs: number[]) => unknown;\nfunction later(xs: number[], g: F = cube, run = () => g(xs)) {{ return run(); }}");
    let cases = [
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return later(xs); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return later(xs, undefined); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return later(xs, cheap); }}")), "O(1)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return later(xs, undefined, () => 0); }}")), "O(1)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[], g: F) {{ return later(xs, g); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn destructured_parameters_initialize_their_bindings_at_invocation() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nfunction use(xs: number[], {{ n = quadratic(xs) }}: {{ n?: number }} = {{}}) {{ return n; }}\nexport function selected(xs: number[]) {{ return use(xs); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nfunction use(xs: number[], [n = quadratic(xs)]: number[]) {{ return n; }}\nexport function selected(xs: number[]) {{ return use(xs, []); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], {{ [quadratic(xs)]: n }}: Record<number, number>) {{ return n; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], ...[n = quadratic(xs)]: number[]) {{ return n; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nfunction use(xs: number[], {{ n }}: {{ n: number }}) {{ return n; }}\nexport function selected(xs: number[]) {{ return use(xs, {{ n: 1 }}); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn parameter_initialization_is_charged_once_per_invocation() {
    for (source, expected) in [
        (format!("{QUADRATIC}\nexport function selected(xs: number[], n = quadratic(xs)) {{ return n; }}"), vec!["call quadratic()"]),
        (format!("{QUADRATIC}\nfunction use(xs: number[], n = quadratic(xs)) {{ return n; }}\nexport function selected(xs: number[]) {{ return use(xs); }}"), vec!["call use()"]),
        (format!("{QUADRATIC}\nexport function selected(xs: number[], {{ n = quadratic(xs) }}: {{ n?: number }}) {{ return n; }}"), vec!["call quadratic()"]),
    ] {
        let (reading, labels) = reading_of(&source, "selected");

        assert_eq!(reading.total().cost, Cost::parse("O(N^2)").unwrap(), "{source}");
        assert_eq!(labels, expected, "{source}");
    }
}

#[test]
fn functions_returned_through_parameters_invoke_the_supplied_body() {
    let helpers = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\ntype F = (xs: number[]) => unknown;\nfunction wrap(f: F) {{ return f; }}\nfunction factory(f: F, xs: number[]) {{ return () => f(xs); }}\nfunction curry(f: F) {{ return (xs: number[]) => f(xs); }}\nexport function other(xs: number[]) {{ wrap(cube)(xs); factory(cube, xs)(); curry(cube)(xs); }}");
    let cases = [
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return wrap(cube)(xs); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return wrap(cheap)(xs); }}")), "O(1)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return factory(cube, xs)(); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return factory(cheap, xs)(); }}")), "O(1)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ for (const _ of xs) curry(cheap)(xs); return curry(cube)(xs); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ for (const _ of xs) curry(cube)(xs); }}")), "O(N^4)", false),
        (index_of(format!("{helpers}\nfunction fallback(f: F = cube) {{ return f; }}\nexport function selected(xs: number[]) {{ return fallback()(xs); }}")), "O(N^3)", false),
        (index_of(format!("{helpers}\nfunction pick(f: F, k: number) {{ return k > 0 ? f : ((globalThis as any).other as F); }}\nexport function selected(xs: number[]) {{ return pick(cube, 1)(xs); }}")), "O(N^3)", true),
        (index_of(format!("{helpers}\nexport function selected(xs: number[], f: F) {{ return wrap(f)(xs); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn replacement_writes_join_the_values_supplied_to_their_parameters() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cases = [
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ t.includes = v; }}\nexport function selected(xs: number[]) {{ set(new Set<number>(), null); [Array.prototype].forEach((p) => set(p, () => slow(xs))); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(v: unknown, t: any = Array.prototype) {{ t.includes = v; }}\nexport function selected(xs: number[]) {{ set(() => slow(xs)); set(null, new Set<number>()); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set([t]: any[], v: unknown) {{ t.includes = v; }}\nexport function selected(xs: number[]) {{ set([Array.prototype], () => slow(xs)); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nexport function set(t: any, v: unknown) {{ t.includes = v; }}\nexport function selected(xs: number[]) {{ set(new Set<number>(), () => slow(xs)); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown = () => slow([])) {{ t.includes = v; }}\nexport function selected(xs: number[]) {{ set(Array.prototype); const zs = [1]; return zs.includes(0); }}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction set(t: any, v: unknown) {{ v = null; t.includes = v; }}\nexport function selected(xs: number[]) {{ set(Array.prototype, () => slow(xs)); const zs = [1]; return zs.includes(0) && xs.includes(0); }}")), "O(N)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn argument_definedness_follows_each_invocation_context() {
    let default = format!(
        "{QUADRATIC}\nfunction h(xs: number[], n: unknown = quadratic(xs)) {{ return n; }}"
    );
    let cases = [
        (index_of(format!("{default}\nfunction g(xs: number[], p: number | undefined, c: boolean) {{ return h(xs, c ? p : 1); }}\nexport function selected(xs: number[]) {{ g(xs, 5, true); return g(xs, undefined, true); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nfunction g(xs: number[], p: number | undefined, c: boolean) {{ return h(xs, c ? p : 1); }}\nexport function selected(xs: number[]) {{ g(xs, undefined, true); return g(xs, 5, true); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nfunction g(xs: number[], p: number | undefined, c: boolean) {{ return h(xs, c ? p : 1); }}\nexport function selected(xs: number[]) {{ return g(xs, 5, true); }}")), "O(1)", false),
        (index_of(format!("{default}\nfunction g(xs: number[], p: number | undefined) {{ return h(xs, (p, p)); }}\nexport function selected(xs: number[], p?: number) {{ g(xs, 5); return g(xs, p); }}")), "O(N^2)", false),
        (index_of(format!("{default}\ntype F = (xs: number[]) => unknown;\nfunction cheap(xs: number[]) {{ return xs; }}\nfunction inner({{ fn }}: {{ fn?: F }}, xs: number[]) {{ return h(xs, fn); }}\nexport function selected(xs: number[]) {{ inner({{ fn: cheap }}, xs); return inner({{}}, xs); }}")), "O(N^2)", false),
        (index_of(format!("{default}\ntype F = (xs: number[]) => unknown;\nfunction cheap(xs: number[]) {{ return xs; }}\nexport function selected(xs: number[]) {{ return h(xs, cheap); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn conjunctions_are_undefined_only_after_a_known_truthy_left_side() {
    let default = format!(
        "{QUADRATIC}\nfunction h(xs: number[], n: unknown = quadratic(xs)) {{ return n; }}"
    );
    let cases = [
        (index_of(format!("{default}\nexport function selected(xs: number[], k: number) {{ return h(xs, (k + 1) && undefined); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return h(xs, {{}} && undefined); }}")), "O(N^2)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[]) {{ return h(xs, 0 && undefined); }}")), "O(1)", false),
        (index_of(format!("{default}\nexport function selected(xs: number[], k: number) {{ return h(xs, (k + 1) && 2); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn arguments_after_a_spread_bind_open_facts() {
    let helpers = format!("function cube(xs: number[]) {{ {CUBIC} }}\nfunction cheap(xs: number[]) {{ return xs; }}\ntype F = (xs: number[]) => unknown;\nfunction run(xs: number[], g: F = cube) {{ return g(xs); }}\nfunction wrap(a: unknown, f: F) {{ return f; }}");
    let cases = [
        (index_of(format!("{helpers}\nexport function selected(xs: number[], rest: any[]) {{ return (run as any)(...rest, cheap); }}")), "O(N)", true),
        (index_of(format!("{helpers}\nexport function selected(xs: number[], rest: any[]) {{ return (wrap as any)(...rest, cheap)(xs); }}")), "O(N)", true),
        (index_of(format!("{helpers}\nexport function selected(xs: number[]) {{ return run(xs, cheap); }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn collected_rest_arguments_specialize_their_length() {
    let helpers = "function sum(...xs: number[]) { return Math.max(...xs) + xs.length; }";
    let cases = [
        (
            index_of(format!(
                "{helpers}\nexport function selected() {{ return sum(1, 2, 3); }}"
            )),
            "O(1)",
            false,
        ),
        (
            index_of(format!(
                "{helpers}\nexport function selected() {{ return sum(...[1, 2]); }}"
            )),
            "O(1)",
            false,
        ),
        (
            index_of(format!(
                "{helpers}\nexport function selected(ys: number[]) {{ return sum(...ys); }}"
            )),
            "O(N)",
            false,
        ),
        (
            index_of(format!(
                "{helpers}\nexport function selected(ys: number[]) {{ return sum(1, ...ys, 2); }}"
            )),
            "O(N)",
            false,
        ),
    ];

    assert_dispatched(&cases);
}

#[test]
fn sloppy_arguments_writes_rebind_their_parameters() {
    let helpers = format!("function quadratic(xs) {{ var t = 0; if (xs.length >= 0 && xs.length <= 4294967295) {{ for (var i = 0; i < xs.length; i++) for (var j = 0; j < xs.length; j++) t += i + j; }} return t; }}\nfunction cube(xs) {{ {CUBIC} }}\nfunction cheap(xs) {{ return xs; }}\nfunction h(xs, n = quadratic(xs)) {{ return n; }}");
    let script = |name: &'static str, source: String| vec![(name, source)];
    let cases = [
        (script("cases.js", format!("{helpers}\nfunction alias(xs, d) {{ arguments[1] = undefined; return h(xs, d); }}\nfunction selected(xs) {{ return alias(xs, 1); }}")), "O(N^2)", false),
        (script("cases.js", format!("{helpers}\nfunction alias(xs, d) {{ eval('d = undefined'); return h(xs, d); }}\nfunction selected(xs) {{ return alias(xs, 1); }}")), "O(N^2)", true),
        (script("cases.js", format!("{helpers}\nfunction control(xs, d) {{ return h(xs, d); }}\nfunction selected(xs) {{ return control(xs, 1); }}")), "O(1)", false),
        (script("cases.js", format!("{helpers}\nfunction aliasCb(xs, g) {{ arguments[1] = cube; return g(xs); }}\nfunction selected(xs) {{ return aliasCb(xs, cheap); }}")), "O(1)", true),
        (script("cases.js", format!("{helpers}\nfunction retAlias(g) {{ arguments[0] = cube; return g; }}\nfunction selected(xs) {{ return retAlias(cheap)(xs); }}")), "O(1)", true),
        (script("cases.cjs", format!("{helpers}\nfunction retAlias(g) {{ arguments[0] = cube; return g; }}\nfunction selected(xs) {{ return retAlias(cheap)(xs); }}\nmodule.exports = {{ selected }};")), "O(1)", true),
        (script("cases.js", format!("{helpers}\nfunction retControl(g) {{ return g; }}\nfunction selected(xs) {{ return retControl(cube)(xs); }}")), "O(N^3)", false),
        (script("cases.js", format!("{helpers}\nfunction set(t, v) {{ arguments[1] = null; t.includes = v; }}\nfunction selected(xs) {{ set(Array.prototype, () => cube(xs)); return xs.includes(0); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn class_definition_work_runs_once_where_the_class_is_evaluated() {
    let key = "function key(xs: number[]) { quadratic(xs); return 'k'; }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static value = quadratic(xs); }} return Box.value; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static {{ quadratic(xs); }} }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\n{key}\nexport function selected(xs: number[]) {{ class Box {{ [key(xs)]() {{ return 1; }} }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\n{key}\nexport function selected(xs: number[]) {{ class Box {{ [key(xs)] = 1; }} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nfunction base(xs: number[]) {{ quadratic(xs); return class {{}}; }}\nexport function selected(xs: number[]) {{ class Box extends base(xs) {{}} return Box; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ return class {{ static {{ quadratic(xs); }} }}; }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ for (const x of xs) {{ class Box {{ static value = quadratic(xs); }} }} }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static value = quadratic(xs); }} for (const x of xs) new Box(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ m() {{ return quadratic(xs); }} static s() {{ return quadratic(xs); }} }} return new Box(); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ value = quadratic(xs); }} return Box; }}")), "O(1)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn instance_initialization_repeats_for_every_construction() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ value = quadratic(xs); }} return new Box(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const Box = class {{ value = quadratic(xs); }}; return new Box(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ return new (class {{ value = quadratic(xs); }})(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ value = quadratic(xs); constructor(ys: number[]) {{}} }} return new Box(xs); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ static seed = quadratic(xs); value = quadratic(xs); }} for (const x of xs) new Box(); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{ accessor value = quadratic(xs); }} for (const x of xs) new Box(); }}")), "O(N^3)", false),
        (index_of(format!("{QUADRATIC}\nclass Box {{ value = 1; }}\nexport function selected(xs: number[]) {{ for (const x of xs) new Box(); }}")), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn inherited_initialization_follows_implicit_and_explicit_super_calls() {
    let base = format!("{QUADRATIC}\nclass A {{ constructor(ys: number[]) {{ quadratic(ys); }} }}");
    let cases = [
        (index_of(format!("{base}\nclass B extends A {{}}\nexport function selected(xs: number[]) {{ return new B(xs); }}")), "O(N^2)", false),
        (index_of(format!("{base}\nclass B extends A {{}}\nclass C extends B {{}}\nexport function selected(xs: number[]) {{ return new C(xs); }}")), "O(N^2)", false),
        (index_of(format!("{base}\nclass B extends A {{ constructor(ys: number[]) {{ super(ys); }} }}\nexport function selected(xs: number[]) {{ return new B(xs); }}")), "O(N^2)", false),
        (index_of(format!("{base}\nclass B extends A {{ constructor(ys: number[]) {{ const run = () => super(ys); run(); }} }}\nexport function selected(xs: number[]) {{ return new B(xs); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{ value = quadratic(xs); }} class B extends A {{}} return new B(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{ value = quadratic(xs); }} class B extends A {{}} class C extends B {{ constructor() {{ super(); }} }} return new C(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{}} class B extends A {{ value = quadratic(xs); constructor() {{ super(); }} }} return new B(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class A {{ value = quadratic(xs); }} class B extends A {{ m() {{ return quadratic(xs); }} }} for (const x of xs) new B(); }}")), "O(N^3)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn rebound_superclasses_join_their_possible_bases() {
    let classes = format!("function cube(xs: number[]) {{ {INDEXED_CUBIC} }}\nclass K0 {{ m(xs: number[]) {{}} }}\nclass Other {{ m(xs: number[]) {{ cube(xs); }} }}\nclass Cheap {{ constructor(xs: number[]) {{}} }}\nclass Costly {{ constructor(xs: number[]) {{ cube(xs); }} }}");
    let cases = [
        (index_of(format!("{classes}\nlet B: any = K0;\nB = Other;\nclass A extends B {{}}\nexport function selected(xs: number[]) {{ new A().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nlet B: any = Cheap;\nB = Costly;\nclass A extends B {{}}\nexport function selected(xs: number[]) {{ return new A(xs); }}")), "O(N^3)", false),
        (index_of(format!("{classes}\nconst table: any = {{ B: K0 }};\ntable.B = Other;\nclass D extends table.B {{}}\nexport function selected(xs: number[]) {{ new D().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nconst table: any = {{ B: Cheap }};\ntable.B = Costly;\nclass D extends table.B {{}}\nexport function selected(xs: number[]) {{ return new D(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport const table: any = {{ B: Costly }};\nexport function set(t: any, k: string, v: any) {{ t[k] = v; }}\nclass D extends table.B {{}}\nexport function selected(xs: number[]) {{ return new D(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[], B: any) {{ class A extends B {{}} return new A(xs); }}")), "O(1)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn instance_fields_shadow_prototype_methods_until_deleted() {
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}");
    let classes = format!("{cube}\nclass K0 {{ m(xs: number[]) {{ cube(xs); }} }}\nclass K1 extends K0 {{ m(xs: number[]) {{}} }}");
    let fields = format!("{cube}\nclass G0 {{ m(xs: number[]) {{ cube(xs); }} }}\nclass G1 extends G0 {{ m = (xs: number[]) => {{}}; }}");
    let cases = [
        (index_of(format!("{cube}\nclass F0 {{ m = (xs: number[]) => cube(xs); }}\nclass F1 extends F0 {{ m(xs: number[]) {{}} }}\nexport function selected(xs: number[]) {{ new F1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{fields}\nexport function selected(xs: number[]) {{ new G1().m(xs); }}")), "O(1)", true),
        (index_of(format!("{fields}\nexport function selected(xs: number[]) {{ const g = new G1(); delete (g as any).m; g.m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function selected(xs: number[]) {{ new K1().m(xs); }}")), "O(1)", true),
        (index_of(format!("{classes}\ndelete (K1.prototype as any).m;\nexport function selected(xs: number[]) {{ new K1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nconst p: any = K1.prototype;\ndelete p.m;\nexport function selected(xs: number[]) {{ new K1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nexport function drop(k: string) {{ delete (K1.prototype as any)[k]; }}\nexport function selected(xs: number[]) {{ new K1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nReflect.deleteProperty(K1.prototype, 'm');\nexport function selected(xs: number[]) {{ new K1().m(xs); }}")), "O(N^3)", true),
        (vec![("index.ts", "import { K1 } from './classes';\nimport './drop';\nexport function selected(xs: number[]) { new K1().m(xs); }".to_string()), ("classes.ts", format!("function cube(xs: number[]) {{ {CUBIC} }}\nexport class K0 {{ m(xs: number[]) {{ cube(xs); }} }}\nexport class K1 extends K0 {{ m(xs: number[]) {{}} }}")), ("drop.ts", "import { K1 } from './classes';\ndelete (K1.prototype as any).m;".to_string())], "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn self_constructing_fields_stop_as_recurrence() {
    let sources = [
        "class Node { child = new Node(); }\nexport function selected() { return new Node(); }",
        "class Left { right = new Right(); }\nclass Right extends Left {}\nexport function selected() { return new Left(); }",
    ];

    for source in sources {
        let (cost, reasons) = dispatched_result_in(
            &[("index.ts", source)],
            olint::analysis::TypeMode::Syntactic,
        );

        assert_eq!(cost, Cost::parse("O(1)").unwrap(), "{source}");
        assert!(
            reasons.contains(&olint::unknowns::UnknownReason::Recurrence),
            "{source}: {reasons:?}"
        );
    }
}

#[test]
fn unresolved_bases_stay_partial_beside_instance_fields() {
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}");
    let cold = "class Cold {\n// @perf cold\nconstructor(ys: number[]) { quadratic(ys); }\n}";
    let cases = [
        (index_of(format!("{QUADRATIC}\n{cold}\nexport function selected(xs: number[], flag: boolean, B: any) {{ class A extends (flag ? Cold : B) {{ v = [1]; }} return new A(xs); }}")), "O(1)", true),
        (index_of(format!("{QUADRATIC}\n{cold}\nexport function selected(xs: number[], flag: boolean, B: any) {{ class A extends (flag ? Cold : B) {{}} return new A(xs); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], B: any) {{ class A extends B {{ v = quadratic(xs); }} return new A(xs); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[], B: any) {{ class A extends B {{ v = quadratic(xs); constructor(ys: number[]) {{ super(ys); }} }} return new A(xs); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class E extends Error {{ v = quadratic(xs); }} return new E(); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class E extends Error {{ v = quadratic(xs); constructor() {{ super('x'); }} }} return new E(); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\n{cube}\nfunction withField(xs: number[], B: any) {{ class A extends B {{ v = quadratic(xs); }} return new A(xs); }}\nexport function selected(xs: number[]) {{ return withField(xs, class {{ constructor(ys: number[]) {{ cube(ys); }} }}); }}")), "O(N^3)", false),
        (index_of(format!("{cube}\nfunction noField(xs: number[], B: any) {{ class A extends B {{}} return new A(xs); }}\nexport function selected(xs: number[]) {{ return noField(xs, class {{ constructor(ys: number[]) {{ cube(ys); }} }}); }}")), "O(N^3)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn type_only_members_leave_inherited_methods_visible() {
    let classes = format!(
        "function cube(xs: number[]) {{ {CUBIC} }}\nclass G0 {{ m(xs: number[]) {{ cube(xs); }} }}"
    );
    let cases = [
        (index_of(format!("{classes}\nclass G1 extends G0 {{}}\nexport function selected(xs: number[]) {{ new G1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nclass G1 extends G0 {{ declare m: (xs: number[]) => void; }}\nexport function selected(xs: number[]) {{ new G1().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nabstract class G1 extends G0 {{ abstract m: (xs: number[]) => void; }}\nclass G2 extends G1 {{}}\nexport function selected(xs: number[]) {{ new G2().m(xs); }}")), "O(N^3)", true),
        (index_of(format!("{classes}\nabstract class G1 extends G0 {{ abstract m(xs: number[]): void; }}\nclass G2 extends G1 {{}}\nexport function selected(xs: number[]) {{ new G2().m(xs); }}")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

#[test]
fn class_field_directives_apply_to_their_initializers() {
    let linear = "function linear(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }";
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf ignore\nv = quadratic(xs);\n}} return new Box(); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf ignore\nstatic v = quadratic(xs);\n}} return Box; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf O(1)\nv = quadratic(xs);\n}} return new Box(); }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf O(1)\nstatic v = quadratic(xs);\n}} return Box; }}")), "O(1)", false),
        (index_of(format!("{QUADRATIC}\n{linear}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf cold\nv = quadratic(xs);\nw = linear(xs);\n}} return new Box(); }}")), "O(N)", false),
        (index_of(format!("{QUADRATIC}\n{linear}\nexport function selected(xs: number[]) {{ class Box {{\n// @perf cold\nstatic v = quadratic(xs);\nstatic w = linear(xs);\n}} return Box; }}")), "O(N)", false),
    ];

    assert_dispatched(&cases);
}

#[test]
fn parameter_decorators_are_unsupported_class_definition_syntax() {
    let decorator = "function quadratic(zs: number[]) { return (..._: unknown[]) => { for (const a of zs) for (const b of zs) void b; }; }";
    let sources = [
        format!("{decorator}\nexport function selected(xs: number[]) {{ class Box {{ constructor(@quadratic(xs) v: number) {{}} }} return Box; }}"),
        format!("{decorator}\nexport function selected(xs: number[]) {{ class Box {{ m(@quadratic(xs) v: number) {{}} }} return Box; }}"),
    ];

    for source in &sources {
        let (_, reasons) = dispatched_result_in(
            &[("index.ts", source.as_str())],
            olint::analysis::TypeMode::Syntactic,
        );

        assert!(
            reasons.contains(&olint::unknowns::UnknownReason::UnsupportedSyntax),
            "{source}: {reasons:?}"
        );
    }
}

#[test]
fn decorated_classes_keep_unsupported_syntax_at_every_construction() {
    let decorator =
        "function decorate(value: unknown, context: unknown): undefined { return undefined; }";
    let construct = "export function selected() { return new Decorated(); }";
    let cases = [
        (
            index_of(format!(
                "{decorator}\nclass Decorated {{ @decorate value = 1; }}\n{construct}"
            )),
            true,
        ),
        (
            vec![
                (
                    "index.ts",
                    format!("import {{ Decorated }} from './other';\n{construct}"),
                ),
                (
                    "other.ts",
                    format!("{decorator}\nexport class Decorated {{ @decorate value = 1; }}"),
                ),
            ],
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Base {{ @decorate value = 1; }}\nclass Decorated extends Base {{}}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Base {{ @decorate value = 1; }}\nclass Decorated extends Base {{ constructor() {{ super(); }} }}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\n@decorate\nclass Decorated {{ value = 1; }}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Decorated {{ value = 1;\n@decorate\nmethod(): void {{}} }}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Decorated {{ value = 1;\nmethod(@decorate v: number): void {{ void v; }} }}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Decorated {{ @decorate accessor value = 1; }}\n{construct}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nexport function selected() {{ class Decorated {{ @decorate value = 1; }} return new Decorated(); }}"
            )),
            true,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Decorated {{ value = 1; }}\n{construct}"
            )),
            false,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Base {{ value = 1; }}\nclass Decorated extends Base {{ other = 2; }}\n{construct}"
            )),
            false,
        ),
        (
            index_of(format!(
                "{decorator}\nclass Base {{ constructor() {{ void 0; }} }}\nclass Decorated extends Base {{ other = 2; }}\n{construct}"
            )),
            false,
        ),
    ];

    let mut found = Vec::new();

    for (sources, unsupported) in &cases {
        let (cost, reasons) =
            support::selected_case_of(sources, olint::analysis::TypeMode::Syntactic);

        assert_eq!(cost, Cost::parse("O(1)").unwrap(), "{sources:?}");

        if !unsupported {
            assert!(reasons.is_empty(), "{sources:?}: {reasons:?}");
        }

        found.push(reasons.contains(&olint::unknowns::UnknownReason::UnsupportedSyntax));
    }

    let expected: Vec<bool> = cases.iter().map(|(_, unsupported)| *unsupported).collect();

    assert_eq!(found, expected);
}

const LOOP_QUADRATIC: &str = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\treturn total;\n}\n";
const LOOP_SCAN: &str = "function scan(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) total += x;\n\treturn total;\n}\n";
const LOOP_TAPPED_VALUES: &str = "function tappedValues(xs: number[]) {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\tvoid total;\n\treturn xs;\n}\n";
const LOOP_TAPPED_KEYS: &str = "function tappedKeys(o: Record<string, number>) {\n\tlet total = 0;\n\tfor (const a in o) for (const b in o) total += a.length + b.length;\n\tvoid total;\n\treturn o;\n}\n";

fn loop_cost_of(source: &str) -> (Cost, Vec<String>) {
    let (reading, labels) = reading_of(source, "f");

    (reading.total().cost, labels)
}

#[test]
fn loop_tests_and_updates_repeat_at_the_iteration_count() {
    let cubic = Cost::parse("O(N^3)").unwrap();
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (test, test_labels) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 4294967295 && quadratic(xs) >= 0; i++) total += i;\n\treturn total;\n}}"
    ));
    let (update, update_labels) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 4294967295; quadratic(xs), i++) total += i;\n\treturn total;\n}}"
    ));
    let (while_test, while_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[]) {{\n\tlet i = 0;\n\twhile (i >= 0 && i < xs.length && xs.length >= 0 && xs.length <= 4294967295 && scan(xs) >= 0) i++;\n\treturn i;\n}}"
    ));
    let (do_while_test, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[]) {{\n\tlet i = 0;\n\tdo {{\n\t\ti++;\n\t}} while (i >= 0 && i < xs.length && xs.length >= 0 && xs.length <= 4294967295 && scan(xs) >= 0);\n\treturn i;\n}}"
    ));

    assert_eq!(test, cubic);
    assert_eq!(test_labels, vec!["for", "call quadratic()"]);
    assert_eq!(update, cubic);
    assert_eq!(update_labels, vec!["for", "call quadratic()"]);
    assert_eq!(while_test, quadratic);
    assert_eq!(
        while_labels,
        vec!["while [budget: i < xs.length]", "call scan()"]
    );
    assert_eq!(do_while_test, quadratic);
}

#[test]
fn opaque_loop_endpoints_keep_known_test_work_partial() {
    for (helper, body, expected) in [
        (
            LOOP_QUADRATIC,
            "for (let i = 0; i < quadratic(xs); i++) void i;",
            "O(N^2)",
        ),
        (LOOP_SCAN, "let i = 0; while (i < scan(xs)) i++;", "O(N)"),
        (
            LOOP_SCAN,
            "let i = 0; do { i++; } while (i < scan(xs));",
            "O(N)",
        ),
    ] {
        let (reading, _) = reading_of(
            &format!("{helper}export function f(xs: number[]) {{ {body} }}"),
            "f",
        );

        assert_eq!(reading.total().cost, Cost::parse(expected).unwrap());
        assert!(!reading.total().is_complete());
    }
}

#[test]
fn loop_initialization_and_iterable_evaluation_stay_once() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (initialization, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (let i = quadratic(xs); i < xs.length; i++) total += i;\n\treturn total;\n}}"
    ));
    let (iterated, _) = loop_cost_of(&format!(
        "{LOOP_TAPPED_VALUES}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const value of tappedValues(xs)) total += value;\n\treturn total;\n}}"
    ));
    let (enumerated, _) = loop_cost_of(&format!(
        "{LOOP_TAPPED_KEYS}export function f(o: Record<string, number>) {{\n\tlet total = 0;\n\tfor (const key in tappedKeys(o)) total += key.length;\n\treturn total;\n}}"
    ));

    assert_eq!(initialization, quadratic);
    assert_eq!(iterated, quadratic);
    assert_eq!(enumerated, quadratic);
}

#[test]
fn zero_trip_and_short_circuit_loops_keep_their_test_work() {
    let (zero_trip, zero_trip_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], n: number) {{\n\tlet total = 0;\n\twhile (scan(xs) > n) {{\n\t\ttotal += 1;\n\t\tbreak;\n\t}}\n\treturn total;\n}}"
    ));
    let (short_circuit, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], n: number) {{\n\tlet i = 0;\n\twhile (i >= 0 && i < n && n >= 0 && n <= 1000000000 && scan(xs) >= 0) i++;\n\treturn i;\n}}"
    ));

    assert_eq!(zero_trip, Cost::N);
    assert_eq!(zero_trip_labels, vec!["call scan()"]);
    assert_eq!(short_circuit, Cost::parse("O(N^2)").unwrap());
}

#[test]
fn a_continue_keeps_its_branch_and_the_update_inside_the_loop() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (updated, updated_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], flag: boolean) {{\n\tlet total = 0;\n\tfor (let i = 0; i < xs.length && xs.length >= 0 && xs.length <= 4294967295; scan(xs), i++) {{\n\t\tif (flag) continue;\n\t\ttotal += 1;\n\t}}\n\treturn total;\n}}"
    ));
    let (branched, branched_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], flag: boolean) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\tif (flag) {{\n\t\t\ttotal += scan(xs);\n\t\t\tcontinue;\n\t\t}}\n\t\ttotal += x;\n\t}}\n\treturn total;\n}}"
    ));

    assert_eq!(updated, quadratic);
    assert_eq!(updated_labels, vec!["for", "call scan()"]);
    assert_eq!(branched, quadratic);
    assert_eq!(branched_labels, vec!["for-of", "call scan()"]);
}

#[test]
fn break_targets_decide_whether_a_branch_leaves_its_loop() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (switched, switched_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], flag: boolean) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\tswitch (x) {{\n\t\t\tcase 1:\n\t\t\t\tif (flag) {{\n\t\t\t\t\ttotal += scan(xs);\n\t\t\t\t\tbreak;\n\t\t\t\t}}\n\t\t\t\ttotal += 1;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (blocked, blocked_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(xs: number[], flag: boolean) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\tinner: {{\n\t\t\tif (flag) {{\n\t\t\t\ttotal += scan(xs);\n\t\t\t\tbreak inner;\n\t\t\t}}\n\t\t\ttotal += x;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (labelled_break, labelled_break_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][], flag: boolean) {{\n\tlet total = 0;\n\touter: for (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (flag) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tbreak outer;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (labelled_continue, labelled_continue_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][], flag: boolean) {{\n\tlet total = 0;\n\touter: for (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (flag) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tcontinue outer;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));

    assert_eq!(switched, quadratic);
    assert_eq!(switched_labels, vec!["for-of", "call scan()"]);
    assert_eq!(blocked, quadratic);
    assert_eq!(blocked_labels, vec!["for-of", "call scan()"]);
    assert_eq!(labelled_break, quadratic);
    assert_eq!(
        labelled_break_labels,
        vec![
            "[break branch: runs once per loop]",
            "call scan()",
            "for-of",
            "for-of"
        ]
    );
    assert_eq!(labelled_continue, quadratic);
    assert_eq!(
        labelled_continue_labels,
        vec![
            "for-of",
            "[continue branch: runs once per loop]",
            "call scan()",
            "for-of"
        ]
    );
}

#[test]
fn a_branch_that_can_return_to_its_loop_keeps_its_work_inside() {
    let cubic = Cost::parse("O(N^3)").unwrap();
    let (continued, continued_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\touter: for (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tif (value > 0) continue;\n\t\t\t\tcontinue outer;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (broken, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tif (value > 0) continue;\n\t\t\t\tbreak;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (returned, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tif (value > 0) continue;\n\t\t\t\treturn total;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));

    assert_eq!(continued, cubic);
    assert!(continued_labels
        .iter()
        .all(|label| !label.contains("runs once per")));
    assert_eq!(broken, cubic);
    assert_eq!(returned, cubic);
}

#[test]
fn a_branch_that_only_transfers_within_itself_still_leaves_its_loop() {
    let label_of = |reading: &TestReading, part: &Part| {
        reading
            .traces
            .borrow()
            .node(part.trace.unwrap())
            .unwrap()
            .label
            .clone()
    };
    let (inner_loop, inner_loop_labels) = reading_of(
        &format!(
            "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\touter: for (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tfor (let index = 0; index < 3; index++) {{\n\t\t\t\t\ttotal += 1;\n\t\t\t\t\tif (total > 10) break;\n\t\t\t\t}}\n\t\t\t\tcontinue outer;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
        ),
        "f",
    );
    let (inner_switch, _) = reading_of(
        &format!(
            "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\tif (row.length > 0) {{\n\t\t\ttotal += scan(row);\n\t\t\tswitch (row.length) {{\n\t\t\t\tcase 1:\n\t\t\t\t\tbreak;\n\t\t\t}}\n\t\t\treturn total;\n\t\t}}\n\t\ttotal += 1;\n\t}}\n\treturn total;\n}}"
        ),
        "f",
    );
    let (downgraded, downgraded_labels) = reading_of(
        &format!(
            "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\tif (value > 0) break;\n\t\t\t\treturn total;\n\t\t\t}}\n\t\t\ttotal += value;\n\t\t}}\n\t}}\n\treturn total;\n}}"
        ),
        "f",
    );

    assert_eq!(inner_loop.total().cost, Cost::parse("O(N^2)").unwrap());
    assert!(inner_loop_labels.contains(&"[continue branch: runs once per loop]".to_string()));
    assert_eq!(inner_switch.total().cost, Cost::N);
    assert_eq!(inner_switch.function_exit().cost, Cost::N);
    assert_eq!(
        label_of(&inner_switch, &inner_switch.function_exit()),
        "[return branch: runs once per call]"
    );
    assert_eq!(downgraded.total().cost, Cost::parse("O(N^2)").unwrap());
    assert!(downgraded_labels.contains(&"[return branch: runs once per loop]".to_string()));
}

#[test]
fn caught_throws_and_overridden_returns_stay_at_their_loop_frequency() {
    let cubic = Cost::parse("O(N^3)").unwrap();
    let (caught, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\tthrow quadratic(xs);\n\t\t}} catch (error) {{\n\t\t\ttotal += 1;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (continued, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\treturn quadratic(xs);\n\t\t}} finally {{\n\t\t\tcontinue;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (nested, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\ttry {{\n\t\t\t\treturn quadratic(xs);\n\t\t\t}} finally {{\n\t\t\t\ttotal += 1;\n\t\t\t}}\n\t\t}} finally {{\n\t\t\tcontinue;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));

    assert_eq!(caught, cubic);
    assert_eq!(continued, cubic);
    assert_eq!(nested, cubic);
}

#[test]
fn genuine_exits_rethrows_and_plain_finalizers_still_run_once_per_call() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (returned, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\ttotal += 1;\n\t\tif (row.length > 0) {{\n\t\t\treturn scan(row);\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (rethrown, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\ttotal += x;\n\t\t}} catch (error) {{\n\t\t\tthrow quadratic(xs);\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (finalized, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\treturn quadratic(xs);\n\t\t}} finally {{\n\t\t\ttotal += 1;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));

    assert_eq!(returned, Cost::N);
    assert_eq!(rethrown, quadratic);
    assert_eq!(finalized, quadratic);
}

#[test]
fn an_overridden_exit_is_charged_at_the_boundary_it_crosses() {
    let (continued, continued_labels) = reading_of(
        &format!(
            "{LOOP_QUADRATIC}export function f(rows: number[][]) {{\n\tlet total = 0;\n\touter: for (const row of rows) {{\n\t\tfor (const value of row) {{\n\t\t\ttry {{\n\t\t\t\treturn quadratic(row);\n\t\t\t}} finally {{\n\t\t\t\tcontinue outer;\n\t\t\t}}\n\t\t}}\n\t}}\n\treturn total;\n}}"
        ),
        "f",
    );

    assert!(continued.function_exit().cost.is_one());
    assert_eq!(
        continued_labels,
        vec!["for-of", "call quadratic()", "for-of"]
    );
}

#[test]
fn a_branch_a_catch_or_finally_can_re_enter_keeps_its_work_inside() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (caught, caught_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\ttry {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\treturn total;\n\t\t\t}}\n\t\t\ttotal += 1;\n\t\t}} catch (error) {{\n\t\t\ttotal += 1;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (overridden, _) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\ttry {{\n\t\t\tif (row.length > 0) {{\n\t\t\t\ttotal += scan(row);\n\t\t\t\treturn total;\n\t\t\t}}\n\t\t}} finally {{\n\t\t\tcontinue;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (within, within_labels) = loop_cost_of(&format!(
        "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\tif (row.length > 0) {{\n\t\t\ttotal += scan(row);\n\t\t\ttry {{\n\t\t\t\tthrow new Error('stop');\n\t\t\t}} catch (error) {{\n\t\t\t\ttotal += 1;\n\t\t\t}}\n\t\t\treturn total;\n\t\t}}\n\t\ttotal += 1;\n\t}}\n\treturn total;\n}}"
    ));
    let (outside, outside_labels) = reading_of(
        &format!(
            "{LOOP_SCAN}export function f(rows: number[][]) {{\n\tlet total = 0;\n\tfor (const row of rows) {{\n\t\ttry {{\n\t\t\tfor (const value of row) {{\n\t\t\t\tif (row.length > 0) {{\n\t\t\t\t\ttotal += scan(row);\n\t\t\t\t\treturn total;\n\t\t\t\t}}\n\t\t\t\ttotal += value;\n\t\t\t}}\n\t\t}} catch (error) {{\n\t\t\ttotal += 1;\n\t\t}}\n\t}}\n\treturn total;\n}}"
        ),
        "f",
    );

    assert_eq!(caught, quadratic);
    assert!(caught_labels
        .iter()
        .all(|label| !label.contains("runs once per")));
    assert_eq!(overridden, quadratic);
    assert_eq!(within, Cost::N);
    assert!(within_labels.contains(&"[return branch: runs once per call]".to_string()));
    assert!(outside.function_exit().cost.is_one());
    assert!(outside_labels.contains(&"[return branch: runs once per loop]".to_string()));
}

#[test]
fn a_finalizer_transfer_that_lands_inside_it_does_not_replace_the_completion() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (looped, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\treturn quadratic(xs);\n\t\t}} finally {{\n\t\t\tfor (const y of xs) if (y > 0) break;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (caught, _) = loop_cost_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\treturn quadratic(xs);\n\t\t}} finally {{\n\t\t\ttry {{\n\t\t\t\tthrow new Error('stop');\n\t\t\t}} catch (error) {{\n\t\t\t\ttotal += 1;\n\t\t\t}}\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ));
    let (escaping, _) = reading_of(&format!(
        "{LOOP_QUADRATIC}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\ttry {{\n\t\t\treturn quadratic(xs);\n\t\t}} finally {{\n\t\t\tfor (const y of xs) if (y > 0) total += 1;\n\t\t\tcontinue;\n\t\t}}\n\t}}\n\treturn total;\n}}"
    ), "f");

    assert_eq!(looped, quadratic);
    assert_eq!(caught, quadratic);
    assert!(escaping.function_exit().cost.is_one());
}

const NESTED_QUADRATIC: &str = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\n\treturn total;\n}\n";

fn escape_target_cost_of(transfer: &str, labels: &str) -> (Cost, Vec<String>) {
    loop_cost_of(&format!(
        "{NESTED_QUADRATIC}export function f(xs: number[], flag: boolean) {{\n\t{labels}for (const a of xs) {{\n\t\tfor (const b of xs) {{\n\t\t\tif (flag) {{\n\t\t\t\tquadratic(xs);\n\n\t\t\t\t{transfer}\n\t\t\t}}\n\t\t}}\n\t}}\n}}"
    ))
}

#[test]
fn an_escaping_branch_is_charged_at_the_loop_its_completion_targets() {
    let quadratic = Cost::parse("O(N^2)").unwrap();
    let (outer_break, outer_break_labels) = escape_target_cost_of("break outer;", "outer: ");
    let (inner_break, inner_break_labels) = escape_target_cost_of("break;", "");
    let (outer_continue, outer_continue_labels) =
        escape_target_cost_of("continue outer;", "outer: ");

    assert_eq!(outer_break, quadratic);
    assert_eq!(
        outer_break_labels,
        vec![
            "[break branch: runs once per loop]",
            "call quadratic()",
            "for-of",
            "for-of"
        ]
    );
    assert_ne!(inner_break, quadratic);
    assert_eq!(
        inner_break_labels,
        vec![
            "for-of",
            "[break branch: runs once per loop]",
            "call quadratic()",
            "for-of"
        ]
    );
    assert_ne!(outer_continue, quadratic);
    assert_eq!(
        outer_continue_labels,
        vec![
            "for-of",
            "[continue branch: runs once per loop]",
            "call quadratic()",
            "for-of"
        ]
    );
}

#[test]
fn a_transfer_leaving_three_loops_is_charged_once_per_call() {
    let (cost, labels) = loop_cost_of(&format!(
        "{NESTED_QUADRATIC}export function f(xs: number[], flag: boolean) {{\n\touter: for (const a of xs) {{\n\t\tfor (const b of xs) {{\n\t\t\tfor (const c of xs) {{\n\t\t\t\tif (flag) {{\n\t\t\t\t\tquadratic(xs);\n\n\t\t\t\t\tbreak outer;\n\t\t\t\t}}\n\t\t\t}}\n\t\t}}\n\t}}\n}}"
    ));

    assert_eq!(cost, Cost::parse("O(N^3)").unwrap());
    assert_eq!(
        labels,
        vec![
            "[break branch: runs once per loop]",
            "call quadratic()",
            "for-of",
            "for-of",
            "for-of"
        ]
    );
}

#[test]
fn a_caught_throw_is_charged_at_the_loop_its_handler_sits_outside() {
    let (outside, outside_labels) = loop_cost_of(&format!(
        "{NESTED_QUADRATIC}export function f(xs: number[]) {{
	try {{
		for (const a of xs) {{
			for (const b of xs) {{
				if (a > b) {{
					throw quadratic(xs);
				}}
			}}
		}}
	}} catch {{}}
}}"
    ));
    let (inside, inside_labels) = loop_cost_of(&format!(
        "{NESTED_QUADRATIC}export function f(xs: number[]) {{
	for (const a of xs) {{
		for (const b of xs) {{
			try {{
				if (a > b) {{
					throw quadratic(xs);
				}}
			}} catch {{}}
		}}
	}}
}}"
    ));

    assert_eq!(outside, Cost::parse("O(N^2)").unwrap());
    assert_eq!(outside_labels, vec!["call quadratic()", "for-of", "for-of"]);
    assert_eq!(inside, Cost::parse("O(N^4)").unwrap());
    assert_eq!(inside_labels, vec!["for-of", "for-of", "call quadratic()"]);
}

#[test]
fn standard_api_callbacks_run_inside_their_native_operation() {
    for (source, expected, labels) in [
        (
            "export function f(s: string, xs: number[]) { return s.replaceAll(\"x\", () => `${quadratic(xs)}`); }",
            "O(N^3)",
            vec!["s.replaceAll() [string]", "call quadratic()"],
        ),
        (
            "export function f(s: string, xs: number[]) { return s.replace(\"x\", () => `${quadratic(xs)}`); }",
            "O(N^2)",
            vec!["s.replace() [string]", "call quadratic()"],
        ),
        (
            "export function f(xs: number[]) { return Object.groupBy(xs, () => quadratic(xs)); }",
            "O(N^3)",
            vec!["Object.groupBy(xs)", "call quadratic()"],
        ),
        (
            "export function f(xs: number[]) { return JSON.stringify(xs, (_, value) => { quadratic(xs); return value; }); }",
            "O(N^3)",
            vec!["JSON.stringify(xs)", "call quadratic()"],
        ),
        (
            "export function f(xs: number[]) { return new Promise<number>(resolve => resolve(quadratic(xs))); }",
            "O(N^2)",
            vec!["call quadratic()"],
        ),
    ] {
        let (reading, found) = reading_of(&format!("{QUADRATIC}\n{source}"), "f");
        let total = reading.total();

        assert_eq!(total.cost, Cost::parse(expected).unwrap(), "{source}");
        assert!(total.is_complete(), "{source}");
        assert_eq!(found, labels, "{source}");
    }
}

const JSX_WORK: &str = "export function quadratic(xs: number[]) { let t = 0; for (const a of xs) for (const b of xs) t += a * b; return t; }\n";
const JSX_FACTORY: &str = "export function h(type: any, props: any, ...children: any[]) { return { type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
const JSX_CLASSIC: &str = r#"{ "compilerOptions": { "strict": true, "noEmit": true, "jsx": "react", "jsxFactory": "h", "jsxFragmentFactory": "Fragment", "module": "esnext", "moduleResolution": "bundler", "target": "es2022", "types": [] }, "include": ["src"] }"#;
const JSX_PRESERVE: &str = r#"{ "compilerOptions": { "strict": true, "noEmit": true, "jsx": "preserve", "module": "esnext", "moduleResolution": "bundler", "target": "es2022", "types": [] }, "include": ["src"] }"#;

fn jsx_case(
    tsconfig: &str,
    body: &str,
    expected: &'static str,
    partial: bool,
) -> support::ProjectCase<'static> {
    let index = format!(
        "import {{ h, Fragment }} from \"./h\";\nimport {{ quadratic }} from \"./work\";\n{body}\n"
    );

    (
        vec![
            ("tsconfig.json", tsconfig.to_string()),
            ("src/index.tsx", index),
            ("src/h.ts", JSX_FACTORY.to_string()),
            ("src/work.ts", JSX_WORK.to_string()),
        ],
        expected,
        partial,
    )
}

#[test]
fn jsx_expressions_are_evaluated_and_stay_visible() {
    let cases = [
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div title={quadratic(xs)} />; }", "O(N^2)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div>{quadratic(xs)}</div>; }", "O(N^2)", false),
        jsx_case(JSX_CLASSIC, "export function selected(props: Record<string, number>) { return <div {...props} />; }", "O(N)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div>{...xs}</div>; }", "O(N)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div title={<span>{quadratic(xs)}</span>} />; }", "O(N^2)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <ul>{xs.map((x) => <li key={x}>{quadratic(xs)}</li>)}</ul>; }", "O(N^3)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <>{quadratic(xs)}</>; }", "O(N^2)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { const o = { get v() { return quadratic(xs); } }; return <div {...o} />; }", "O(N^2)", true),
        jsx_case(JSX_CLASSIC, "export function selected(props: Record<string, number>) { return <div {...{ ...props }} />; }", "O(N)", false),
        jsx_case(JSX_CLASSIC, "export function selected(p: object) { return <div {...{ __proto__: p, a: 1 }} />; }", "O(N)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { const ui = { get Box() { quadratic(xs); return () => 1; } }; return <ui.Box />; }", "O(N^2)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { const ui = { inner: { get Box() { quadratic(xs); return () => 1; } } }; return <ui.inner.Box />; }", "O(N^2)", false),
        jsx_case(JSX_PRESERVE, "export function selected(xs: number[]) { return <div>{quadratic(xs)}</div>; }", "O(N^2)", true),
        jsx_case(JSX_PRESERVE, "export function selected(props: Record<string, number>) { return <div {...props} />; }", "O(N)", true),
    ];

    support::assert_project_cases("src/index.tsx", &cases);

    let controls = [
        jsx_case(JSX_CLASSIC, "export function selected() { return <div title=\"x\">text</div>; }", "O(1)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div title={xs.length}>{xs[0]}</div>; }", "O(1)", false),
        jsx_case(JSX_CLASSIC, "export function selected() { return <div {...{ a: 1 }} />; }", "O(1)", false),
        jsx_case(JSX_CLASSIC, "const ui = { Box(props: any) { return props; } };\nexport function selected() { return <ui.Box></ui.Box>; }", "O(1)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <div {...{ get v() { return quadratic(xs); } }} />; }", "O(1)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { return <ul>{xs.map((x) => <li key={x}>{x}</li>)}</ul>; }", "O(N)", false),
    ];

    support::assert_project_cases("src/index.tsx", &controls);

    let counting = "let count = 0;\nexport function h(type: any, props: any, ...children: any[]) { count += 1; return { n: count, type, props, children }; }\nexport function Fragment(props: any) { return props; }\n";
    let mut endpoint = jsx_case(JSX_CLASSIC, "export function selected() { let t = 0; for (let i = 0; i < (<div /> as any).n; i++) t += i; return t; }", "O(1)", true);

    endpoint.0[2].1 = counting.to_string();

    let flows = [
        jsx_case(JSX_CLASSIC, "export function selected(n: number) { let t = 0; for (let i = 1; i < (<div />, n); i *= 2) t += i; return t; }", "O(1)", true),
        jsx_case(JSX_CLASSIC, "export function selected(s: Set<number>) { let t = 0; for (const x of s) { const e = <div {...{ get v() { s.add(1); return 1; } }} />; t += 1; } return t; }", "O(N)", false),
        jsx_case(JSX_CLASSIC, "export function selected(xs: number[]) { for (const x of xs) { try { const e = <div />; } catch { return quadratic(xs); } } return 0; }", "O(N^2)", false),
        endpoint,
    ];

    support::assert_project_cases("src/index.tsx", &flows);
}

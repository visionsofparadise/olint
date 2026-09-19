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

const CUBIC: &str = "for (const a of xs) for (const b of xs) for (const c of xs) void c;";

type DispatchedResult = (
    Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
);

fn dispatched_result_of(source: &str, types: olint::analysis::TypeMode) -> DispatchedResult {
    dispatched_result_in(&[("index.ts", source)], types)
}

fn dispatched_result_in(
    sources: &[(&str, &str)],
    types: olint::analysis::TypeMode,
) -> DispatchedResult {
    let mut files = vec![(
        "tsconfig.json",
        r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["index.ts"]}"#,
    )];

    files.extend_from_slice(sources);

    let mut result = (Cost::ONE, std::collections::BTreeSet::new());

    support::run_in_project(&files, |project, root| {
        let file = support::file_of(project, root, "index.ts");
        let mut analysis = olint::analysis::Analysis::new(
            project,
            olint::analysis::Options {
                minimum_exponent: 2,
                types,
            },
        );

        if types == olint::analysis::TypeMode::Tsc {
            let functions = analysis.reportable();
            let tsconfig = root.join("tsconfig.json");

            analysis
                .gather_answers(&functions, |queries| {
                    olint::tsc::ask(
                        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
                        &tsconfig,
                        queries,
                    )
                })
                .expect("the compiler helper answers");
        }

        let part = support::summary_of(&mut analysis, file, "selected");
        let reasons = support::unknown_reasons(&analysis, part.unknowns);
        let selected = function_of_name(analysis.project, file, "selected");
        let cost = support::legacy_class_of(&mut analysis, file, selected, &part.cost);

        result = (cost, reasons);
    });

    result
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

type DispatchCase<'s> = (Vec<(&'s str, String)>, &'s str, bool);

fn assert_dispatched(cases: &[DispatchCase<'_>]) {
    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for (sources, expected, partial) in cases {
            let sources: Vec<(&str, &str)> = sources
                .iter()
                .map(|(name, source)| (*name, source.as_str()))
                .collect();
            let (cost, reasons) = dispatched_result_in(&sources, types);

            assert_eq!(
                cost,
                Cost::parse(expected).unwrap(),
                "{types:?} {sources:?}"
            );
            assert_eq!(
                reasons.contains(&olint::unknowns::UnknownReason::Target),
                *partial,
                "{types:?} {sources:?}: {reasons:?}"
            );
        }
    }
}

fn index_of(source: String) -> Vec<(&'static str, String)> {
    vec![("index.ts", source)]
}

#[test]
fn replacements_resolve_keys_prototypes_and_builtin_subclasses() {
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} return 0; }}");
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
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
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
        (index_of(format!("{slow}\nfunction set(target: object, value: unknown) {{ (target as any).includes = value; }}\nexport function selected(xs: number[]) {{ set(xs, () => slow(xs)); return xs.includes(0); }}")), "O(N)", true),
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
        (index_of(format!("{slow}\nfunction set(target: Set<number>, value: unknown) {{ (target as any).includes = value; }}\nexport function selected(xs: number[]) {{ set(xs as any, () => slow(xs)); return xs.includes(0); }}")), "O(N)", true),
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
    let slow = format!("function slow(xs: number[]) {{ {CUBIC} return true; }}");
    let cube = format!("function cube(xs: number[]) {{ {CUBIC} }}");
    let selected = "export function selected(xs: number[]) { const zs = [1]; return zs.includes(0) && xs.includes(0); }";
    let cases = [
        (index_of(format!("{slow}\nfunction F() {{}}\nconst G: any = F;\nG.prototype = Array.prototype;\n(F as any).prototype.includes = function () {{ return slow([1]); }};\n{selected}")), "O(N^3)", true),
        (index_of(format!("{slow}\nfunction F() {{}}\nfunction rebind(f: any) {{ f.prototype = Array.prototype; }}\nrebind(F);\n(F as any).prototype.includes = function () {{ return slow([1]); }};\n{selected}")), "O(N^3)", true),
        (index_of(format!("{cube}\nconst base = {{ m(xs: number[]) {{ cube(xs); }} }};\nexport function link(o: object) {{ Object.setPrototypeOf(o, base); }}\nclass K0 {{ m(xs: number[]) {{}} }}\nexport function selected(xs: number[]) {{ const c = new K0(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\n(C1 as any).prototype.m = function (xs: number[]) {{}};\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nexport function selected(xs: number[]) {{ const c = new (C1 as any)(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nclass K0 {{ m(xs: number[]) {{}} }}\nexport function selected(xs: number[]) {{ const c = new K0(); c.m(xs); }}")), "O(1)", true),
        (index_of(format!("{cube}\nfunction C0() {{}}\n(C0 as any).prototype.m = function (xs: number[]) {{ cube(xs); }};\nfunction C1() {{}}\nObject.setPrototypeOf((C1 as any).prototype, (C0 as any).prototype);\nexport function selected(xs: number[]) {{ const c = new (C1 as any)(); c.m(xs); }}")), "O(N^3)", true),
    ];

    assert_dispatched(&cases);
}

const QUADRATIC: &str = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }";

#[test]
fn callee_and_constructor_subexpressions_run_before_their_invocation() {
    let cases = [
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ const table = {{ run() {{ return 1; }} }}; return table[(quadratic(xs), 'run')](); }}")), "O(N^2)", true),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function factory() {{ quadratic(xs); return () => 1; }} return factory()(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function factory() {{ return () => quadratic(xs); }} return factory()(); }}")), "O(N^2)", false),
        (index_of(format!("{QUADRATIC}\nexport function selected(xs: number[]) {{ function constructor() {{ quadratic(xs); return class {{}}; }} return new (constructor())(); }}")), "O(N^2)", true),
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
        (index_of(format!("{scan}\nexport function selected(xs: number[], run?: (n: number) => void) {{ let n = 1; run?.(n = xs.length); for (let i = 0; i < n; i++) scan(xs); }}")), "O(N^2)", true),
        (index_of(format!("{scan}\nexport function selected(xs: number[]) {{ let n = 1; const table = {{ run() {{}} }}; table[(n = xs.length, 'run')](); for (let i = 0; i < n; i++) scan(xs); }}")), "O(N^2)", true),
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

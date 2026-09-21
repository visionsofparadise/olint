use olint::analysis::{Analysis, Options, TypeMode};
use olint::config::read_config;
use olint::cost::Cost;
use olint::public::public_functions;
use std::path::Path;

mod support;

#[test]
fn recovered_alias_and_overload_calls_retain_known_work() {
    let cubic = "for(const a of xs) for(const b of xs) for(const c of xs) void c;";

    for (declarations, call, partial) in [
        (
            format!("function work(xs:number[]):void; function work(xs:number[]){{{cubic}}}"),
            "work(xs)",
            false,
        ),
        (
            format!("function work(xs:number[]){{{cubic}}} const a=work; const alias=a;"),
            "alias(xs)",
            false,
        ),
        (
            format!("class API {{work(xs:number[]):void; work(xs:number[]){{{cubic}}}}}"),
            "new API().work(xs)",
            true,
        ),
        (
            format!("class API {{/** @perf hot */\nwork(xs:number[]){{{cubic}}}}}"),
            "new API().work(xs)",
            true,
        ),
    ] {
        let source = format!("{declarations} export function selected(xs:number[]){{{call};}}");

        let (cost, reasons) = selected_result(&source);

        assert_eq!(cost, Cost::parse("O(N^3)").unwrap(), "{call}");
        assert_eq!(!reasons.is_empty(), partial, "{call}");
    }
}

#[test]
fn duplicate_function_declarations_bind_the_runtime_winner() {
    let cubic = "for(const a of xs) for(const b of xs) for(const c of xs) void c;";
    let constant = "return 0;";
    let selected = "function selected(xs){return work(xs);}";
    let block = format!("function work(xs){{{constant}}} {{ function work(xs){{{cubic}}} }}");
    let mut cases = vec![
        (format!("{block} {selected}"), "O(N^3)", true),
        (format!("\"use strict\"; {block} {selected}"), "O(1)", false),
        (format!("{block} export {selected}"), "O(1)", false),
    ];

    for (declarations, expected, partial) in [
        (format!("function work(xs){{{constant}}} function work(xs){{{cubic}}}"), "O(N^3)", false),
        (format!("function work(xs){{{cubic}}} function work(xs){{{constant}}}"), "O(1)", false),
        (format!("function work(xs){{{cubic}}} var work = function(xs){{{constant}}};"), "O(N^3)", true),
        (format!("var work = function(xs){{{constant}}}; function work(xs){{{cubic}}}"), "O(N^3)", true),
        (format!("function work(xs){{{constant}}} var work = function(xs){{{cubic}}};"), "O(N^3)", true),
        (format!("function work(xs){{{cubic}}} function work(xs){{{constant}}} work = function(xs){{{constant}}};"), "O(1)", true),
    ] {
        cases.push((format!("{declarations} {selected}"), expected, partial));
        cases.push((format!("{declarations} export {selected}"), expected, partial));
    }

    for (source, expected, partial) in cases {
        let files = [
            (
                "tsconfig.json",
                r#"{"compilerOptions":{"allowJs":true},"files":["index.js"]}"#,
            ),
            ("index.js", source.as_str()),
        ];
        let (cost, reasons) = selected_result_in(&files, "index.js");
        let expected_reasons = match partial {
            true => vec![olint::unknowns::UnknownReason::Target],
            false => Vec::new(),
        };

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{source}");
        assert_eq!(
            reasons.into_iter().collect::<Vec<_>>(),
            expected_reasons,
            "{source}"
        );
    }

    let (cost, reasons) = selected_result(&format!("function work(xs:number[]):number; function work(xs:number[]):number; function work(xs:number[]){{{cubic} return 0;}} export function selected(xs:number[]){{return work(xs);}}"));

    assert_eq!(cost, Cost::parse("O(N^3)").unwrap());
    assert!(reasons.is_empty());
}

#[test]
fn immutable_callback_alias_uses_the_parameter_substitution() {
    let (cost,reasons) = selected_result("function invoke(cb:()=>void){const alias=cb;alias();}\n/** @perf O(N^3) */\nfunction work(){} export function selected(){invoke(work);}");

    assert_eq!(cost, Cost::parse("O(N^3)").unwrap());
    assert!(reasons.is_empty());
}

const ERASED_THIS_CALLBACKS: [(&str, &str); 2] = [
    (
        "function invoke(this: void, callback: () => number): number { return callback(); } export function selected(values: number[]) { return invoke(() => { let total = 0; for (const x of values) total += x; return total; }); }",
        "O(N)",
    ),
    (
        "function invoke(this: void, callback: () => number): number { return callback(); } export function selected(values: number[]) { return invoke(() => { let total = 0; for (const x of values) for (const y of values) total += x * y; return total; }); }",
        "O(N^2)",
    ),
];

#[test]
fn an_erased_this_parameter_consumes_no_callback_argument() {
    for (source, expected) in ERASED_THIS_CALLBACKS {
        let (cost, reasons) = selected_result(source);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{source}");
        assert!(reasons.is_empty(), "{source}: {reasons:?}");
    }
}

#[test]
fn an_erased_this_parameter_consumes_no_callback_argument_with_compiler_types() {
    for (source, expected) in ERASED_THIS_CALLBACKS {
        let files = [
            (
                "tsconfig.json",
                r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["index.ts"]}"#,
            ),
            ("index.ts", source),
        ];

        run_in_project(&files, |project, root| {
            let file = file_of(project, root, "index.ts");
            let mut analysis = Analysis::new(
                project,
                Options {
                    minimum_exponent: 2,
                    types: TypeMode::Tsc,
                },
            );
            let functions = analysis.reportable();
            let tsconfig = root.join("tsconfig.json");

            analysis
                .gather_answers(&functions, |queries| {
                    olint::tsc::ask(Path::new(env!("CARGO_MANIFEST_DIR")), &tsconfig, queries)
                })
                .expect("the compiler helper answers");

            let function = function_of_name(analysis.project, file, "selected");
            let part = support::summary_of(&mut analysis, file, "selected");

            assert_eq!(
                support::legacy_class_of(&mut analysis, file, function, &part.cost),
                Cost::parse(expected).unwrap(),
                "{source}"
            );
            assert!(
                support::unknown_reasons(&analysis, part.unknowns).is_empty(),
                "{source}"
            );
        });
    }
}

#[test]
fn an_omitted_callback_after_an_erased_this_parameter_stays_unknown() {
    let (cost, reasons) = selected_result(
        "function invoke(this: void, callback?: () => number): number { return callback ? callback() : 0; } export function selected() { return invoke(); }",
    );

    assert_eq!(cost, Cost::ONE);
    assert!(
        reasons.contains(&olint::unknowns::UnknownReason::Target),
        "{reasons:?}"
    );
}

#[test]
fn method_and_function_callbacks_bind_their_first_argument() {
    let linear = "{ let total = 0; for (const x of values) total += x; return total; }";

    for (declarations, call) in [
        (
            "function invoke(callback: () => number): number { return callback(); }",
            "invoke",
        ),
        (
            "const invoke = (callback: () => number): number => callback();",
            "invoke",
        ),
        (
            "const runner = { invoke(callback: () => number): number { return callback(); } };",
            "runner.invoke",
        ),
        (
            "const runner = { invoke(this: { tag: string }, callback: () => number): number { return callback(); }, tag: 'x' };",
            "runner.invoke",
        ),
    ] {
        let source = format!(
            "{declarations} export function selected(values: number[]) {{ return {call}(() => {linear}); }}"
        );

        let (cost, _) = selected_result(&source);

        assert_eq!(cost, Cost::parse("O(N)").unwrap(), "{source}");
    }
}

#[test]
fn hot_open_dispatch_retains_its_call_owned_uncertainty() {
    let source = "class API {\n/** @perf hot */\nwork(){}} export function selected(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c; new API().work();}";

    let (cost, reasons) = selected_result(source);

    assert_eq!(cost, Cost::ONE);
    assert!(reasons.contains(&olint::unknowns::UnknownReason::Target));
}

#[test]
fn recovered_call_effects_fence_dependent_loop_proofs() {
    for declaration in [
        "function mutate(){xs.length=0;} const alias=mutate;",
        "function mutate():void;function mutate(){xs.length=0;} const alias=mutate;",
    ] {
        let source = format!("let xs:number[]=[]; {declaration} export function selected(){{for(const x of xs){{alias();}}}}");

        let (_, reasons) = selected_result(&source);

        assert!(reasons.contains(&olint::unknowns::UnknownReason::Bound));
    }
}

#[test]
fn written_callback_alias_retains_open_cost_and_effects() {
    let source = "declare const opaque:()=>void; function invoke(cb:()=>void){cb=opaque;const alias=cb;alias();}\n/** @perf O(N^3) */\nfunction supplied(){} export function selected(xs:number[]){for(const x of xs){invoke(supplied);}}";

    let (cost, reasons) = selected_result(source);

    assert!(reasons.contains(&olint::unknowns::UnknownReason::Target));
    assert!(reasons.contains(&olint::unknowns::UnknownReason::Bound));
    assert_eq!(cost, Cost::ONE);
}

fn selected_result(
    source: &str,
) -> (
    Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
) {
    selected_result_in(&[("tsconfig.json", "{}"), ("index.ts", source)], "index.ts")
}

fn selected_result_in(
    files: &[(&str, &str)],
    relative: &str,
) -> (
    Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
) {
    let mut result = (Cost::ONE, std::collections::BTreeSet::new());

    run_in_project(files, |project, root| {
        let file = file_of(project, root, relative);
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let function = function_of_name(analysis.project, file, "selected");
        let part = support::summary_of(&mut analysis, file, "selected");

        result = (
            support::legacy_class_of(&mut analysis, file, function, &part.cost),
            support::unknown_reasons(&analysis, part.unknowns),
        );
    });

    result
}

use support::{file_of, function_of_name, run_in_project, run_with_source, SYNTACTIC};

fn labels_of(
    traces: &olint::trace::TraceArena,
    root: Option<olint::trace::TraceId>,
) -> Vec<String> {
    support::trace_nodes(traces, root)
        .into_iter()
        .map(|node| node.label.clone())
        .collect()
}

#[test]
fn self_recursion_retains_known_work_and_reports_recurrence() {
    run_with_source(
        "export function walk(n: number): number {\n\treturn n > 0 ? walk(n - 1) : 0;\n}",
        |analysis, file| {
            let walk = function_of_name(analysis.project, file, "walk");
            let part = analysis
                .summarize(file, walk)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(
                support::legacy_class_of(analysis, file, walk, &part.cost),
                Cost::ONE
            );
            assert!(part.trace.is_none());
            assert_recurrence(analysis, &part);
        },
    );
}

#[test]
fn separate_cycle_roots_keep_their_own_summary_context() {
    run_with_source(
        "export function ping(n: number): number {\n\treturn n > 0 ? pong(n - 1) : 0;\n}\nexport function pong(n: number): number {\n\treturn n > 0 ? ping(n - 1) : 0;\n}",
        |analysis, file| {
            let ping = function_of_name(analysis.project, file, "ping");
            let pong = function_of_name(analysis.project, file, "pong");
            let root = analysis.summarize(file, ping).total(&mut analysis.unknowns, &mut analysis.traces);
            let member = analysis.summarize(file, pong).total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(support::legacy_class_of(analysis, file, ping, &root.cost), Cost::ONE);
            assert_eq!(support::legacy_class_of(analysis, file, pong, &member.cost), Cost::ONE);
            assert_recurrence(analysis, &root);
            assert_recurrence(analysis, &member);
        },
    );
}

#[test]
fn a_costed_callback_multiplies_inside_its_caller() {
    run_with_source(
        "function each(xs: number[], visit: (x: number) => void) {\n\tfor (const x of xs) visit(x);\n}\nexport function f(xs: number[], ys: number[]) {\n\teach(xs, (x) => {\n\t\tfor (const y of ys) void y;\n\t});\n}",
        |analysis, file| {
            let f = function_of_name(analysis.project, file, "f");
            let first = analysis.summarize(file, f);
            let second = analysis.summarize(file, f);

            let actual = first.total(&mut analysis.unknowns, &mut analysis.traces).cost;

            assert_eq!(support::legacy_class_of(analysis, file, f, &actual), Cost::parse("O(N^2)").unwrap());
            assert_eq!(first, second);
            assert_eq!(labels_of(&analysis.traces,first.main().trace), vec!["call each()"]);
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
            "// @perf ignore\nexport function skipped(xs: number[]) {\n\treturn xs.indexOf(1);\n}\nexport function caller(xs: number[]) {\n\tfor (const x of xs) void x;\n\tskipped(xs);\n}\n",
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
            .expect("valid selection")
            .functions
            .into_iter()
            .map(|public| analysis.name_of(public.file, public.function))
            .collect();
        let caller = function_of_name(project, file, "caller");
        let part = analysis
            .summarize(file, caller)
            .total(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(reportable, vec!["caller"]);
        assert_eq!(public, vec!["caller"]);
        assert_eq!(
            support::legacy_class_of(&mut analysis, file, caller, &part.cost),
            Cost::N
        );
        assert_eq!(labels_of(&analysis.traces, part.trace), vec!["for-of"]);
    });
}

#[test]
fn a_cold_function_called_beside_a_linear_statement_cascades_linear() {
    run_with_source(
        "/** @perf cold */\nfunction rebuild(rows: number[][]) {\n\tfor (const row of rows) for (const value of row) void value;\n}\nexport function f(rows: number[][]) {\n\trebuild(rows);\n\trows.indexOf([]);\n}",
        |analysis, file| {
            let rebuild = function_of_name(analysis.project, file, "rebuild");
            let f = function_of_name(analysis.project, file, "f");
            let own = analysis.summarize(file, rebuild).total(&mut analysis.unknowns, &mut analysis.traces);
            let part = analysis.summarize(file, f).total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(support::legacy_class_of(analysis, file, rebuild, &own.cost), Cost::parse("O(N^2)").unwrap());
            assert_eq!(support::legacy_class_of(analysis, file, f, &part.cost), Cost::N);
            assert_eq!(labels_of(&analysis.traces,part.trace), vec!["rows.indexOf()"]);
        },
    );
}

#[test]
fn a_hot_function_call_wins_over_a_costlier_sibling() {
    run_with_source(
        "/** @perf hot */\nconst lookup = (xs: number[]) => xs.indexOf(1);\nexport function f(rows: number[][], xs: number[]) {\n\tfor (const row of rows) for (const value of row) void value;\n\treturn lookup(xs);\n}",
        |analysis, file| {
            let f = function_of_name(analysis.project, file, "f");
            let part = analysis.summarize(file, f).total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(support::legacy_class_of(analysis, file, f, &part.cost), Cost::N);
            assert_eq!(labels_of(&analysis.traces,part.trace), vec!["call lookup()"]);
        },
    );
}

fn total_of(source: &str, name: &str) -> (Cost, Vec<String>) {
    let mut found = (Cost::ONE, Vec::new());

    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, name);
        let part = analysis
            .summarize(file, function)
            .total(&mut analysis.unknowns, &mut analysis.traces);

        found = (
            support::legacy_class_of(analysis, file, function, &part.cost),
            labels_of(&analysis.traces, part.trace),
        );
    });

    found
}

const CALLBACK_SOURCE: &str = "/** @perf cold */\nfunction coldCubic(xs: number[][]): number {\n\tlet sum = 0;\n\tfor (const row of xs) for (const v of row) for (const w of row) sum += v * w;\n\treturn sum;\n}\n/** @perf hot */\nfunction hotConst(x: number[]): number {\n\treturn x.length;\n}\nfunction withHotInside(row: number[]): number {\n\t// @perf hot\n\treturn row.length;\n}\nfunction apply(f: (xs: number[][]) => number, xs: number[][]): number {\n\tconst a = f(xs);\n\tfor (const row of xs) void row;\n\treturn a;\n}\nexport function coldViaMap(xss: number[][][]) {\n\tfor (const xs of xss) void xs;\n\tconst a = xss.map(coldCubic);\n\treturn a;\n}\nexport function hotViaMap(xs: number[][]) {\n\tfor (const row of xs) for (const v of row) void v;\n\tconst a = xs.map(hotConst);\n\treturn a;\n}\nexport function bodyHotViaMap(xs: number[][]) {\n\tfor (const row of xs) for (const v of row) void v;\n\tconst a = xs.map(withHotInside);\n\treturn a;\n}\nexport function coldViaParameter(xs: number[][]) {\n\treturn apply(coldCubic, xs);\n}\n";

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
        Cost::parse("O(N^2)").unwrap()
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
fn a_cold_recursive_function_keeps_its_recurrence_uncertainty() {
    let source = "/** @perf cold */\nexport function walk(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + walk(xs, n - 1);\n}\n";

    run_with_source(source, |analysis, file| {
        let part = support::summary_of(analysis, file, "walk");

        assert_eq!(part.cost, Cost::ONE);
        assert_recurrence(analysis, &part);
    });
}

#[test]
fn a_cold_cycle_member_keeps_the_cycle_uncertainty() {
    let source = "export function ping(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + pong(xs, n - 1);\n}\n/** @perf cold */\nfunction pong(xs: number[], n: number): number {\n\treturn ping(xs, n);\n}\n";

    run_with_source(source, |analysis, file| {
        let ping = function_of_name(analysis.project, file, "ping");
        let pong = function_of_name(analysis.project, file, "pong");

        for function in [ping, pong] {
            let part = analysis
                .summarize(file, function)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(
                support::legacy_class_of(analysis, file, function, &part.cost),
                Cost::ONE
            );
            assert_recurrence(analysis, &part);
        }
    });
}

fn assert_recurrence(analysis: &Analysis<'_, '_>, part: &olint::cost::Part) {
    assert!(!part.is_complete());
    assert!(support::unknown_reasons(analysis, part.unknowns)
        .contains(&olint::unknowns::UnknownReason::Recurrence));
}

#[test]
fn a_cold_call_leaves_its_argument_costs_unmarked() {
    let source = "/** @perf cold */\nfunction rebuild(rows: number[][], at: number) {\n\tfor (const row of rows) row.indexOf(at);\n}\nexport function f(rows: number[][], xs: number[]) {\n\trebuild(rows, xs.indexOf(1));\n\treturn 0;\n}\n";

    assert_eq!(
        total_of(source, "f"),
        (Cost::N, vec!["xs.indexOf()".to_string()])
    );
}

#[test]
fn callee_member_writes_compose_through_parameter_substitution() {
    for (argument, expected) in [("box", "O(N^2)"), ("other", "O(N)")] {
        let source = format!("function grow(target: {{ limit: number }}, n: number) {{ target.limit += n; }} export function selected(n: number) {{ const box = {{ limit: n }}; const other = {{ limit: n }}; let i = 0, total = 0; for (let j = 0; j < n; j++) {{ while (i < box.limit) {{ i++; total++; }} grow({argument}, n); }} return total; }}");

        let (cost, reasons) = selected_result(&source);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{argument}");
        assert!(reasons.is_empty(), "{argument}: {reasons:?}");
    }
}

#[test]
fn published_effects_keep_reachable_writes_and_drop_activation_locals() {
    let source = "declare function opaque(value: unknown): void;\nexport function outer(n: number) { let i = 0; const reset = () => { let local = 0; local++; i = local; }; reset(); return i + n; }\nfunction grow(target: { limit: number }) { let k = 0; k++; target.limit += k; }\nfunction leak(target: object) { opaque(target); }";

    run_with_source(source, |analysis, file| {
        let records_of = |analysis: &mut Analysis<'_, '_>, name: &str| {
            let function = function_of_name(analysis.project, file, name);

            analysis.summarize(file, function);

            let records: Vec<_> = analysis
                .summary_records_for(olint::declarations::FunctionId {
                    file,
                    node: function.node_id(),
                })
                .into_iter()
                .cloned()
                .collect();

            assert_eq!(records.len(), 1, "{name}");

            records.into_iter().next().unwrap().effects
        };
        let outer = records_of(analysis, "outer");
        let reset = records_of(analysis, "reset");
        let grow = records_of(analysis, "grow");
        let leak = records_of(analysis, "leak");
        let names = |analysis: &Analysis<'_, '_>, effects: &olint::effects::Effects| {
            let mut names: Vec<_> = effects
                .binding_writes
                .iter()
                .map(|binding| match binding {
                    olint::declarations::Binding::Symbol { file, symbol } => analysis
                        .project
                        .file(*file)
                        .semantic
                        .scoping()
                        .symbol_name(*symbol)
                        .to_string(),
                })
                .collect();

            names.sort();

            names
        };

        assert_eq!(names(analysis, &reset), ["i"]);
        assert!(names(analysis, &outer).is_empty());
        assert!(names(analysis, &grow).is_empty());
        assert_eq!(grow.member_writes.len(), 1);
        assert!(grow.unknown_reachable.is_empty() && !grow.unknown_global);
        assert!(!leak.unknown_reachable.is_empty());
        assert!(leak.escapes.len() == 1 && !leak.unknown_global);
    });
}

#[test]
fn rebound_callee_parameters_keep_their_writes_unattributed() {
    let source = "function grow(target: { limit: number }, spare: { limit: number }, n: number) { target = spare; target.limit += n; } export function selected(n: number) { const box = { limit: n }; const other = { limit: n }; let i = 0, total = 0; for (let j = 0; j < n; j++) { while (i < box.limit) { i++; total++; } grow(other, box, n); } return total; }";

    let (cost, _) = selected_result(source);

    assert_eq!(cost, Cost::parse("O(N^2)").unwrap());
}

fn record_costs_of(
    analysis: &mut Analysis<'_, '_>,
    file: olint::project::FileId,
    name: &str,
) -> Vec<Cost> {
    let function = function_of_name(analysis.project, file, name);
    let root = function_of_name(analysis.project, file, "selected");
    let id = olint::declarations::FunctionId {
        file,
        node: function.node_id(),
    };
    let mut costs: Vec<Cost> = analysis
        .summary_records_for(id)
        .into_iter()
        .map(|record| record.reading.clone())
        .collect::<Vec<_>>()
        .into_iter()
        .map(|reading| {
            let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

            support::legacy_class_of(analysis, file, root, &part.cost)
        })
        .collect();

    costs.sort_by_key(|cost| cost.text());

    costs
}

#[test]
fn omitted_and_undefined_arguments_share_the_defaulted_specialization() {
    let source = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }\nfunction defaultParameter(xs: number[], n = quadratic(xs)) { return n; }\nexport function selected(xs: number[]) { defaultParameter(xs); defaultParameter(xs, undefined); defaultParameter(xs, void 0); return defaultParameter(xs, 1); }";

    run_with_source(source, |analysis, file| {
        let part = support::summary_of(analysis, file, "selected");

        assert!(part.is_complete());
        assert_eq!(
            record_costs_of(analysis, file, "defaultParameter"),
            [Cost::parse("O(1)").unwrap(), Cost::parse("O(N^2)").unwrap()]
        );
        support::assert_scheduler_terminal(analysis.scheduler_stats());
    });
}

#[test]
fn returned_closures_specialize_on_their_factory_arguments() {
    let source = "function cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }\nfunction cheap(xs: number[]) { return xs; }\nfunction factory(f: (xs: number[]) => unknown, xs: number[]) { return function run() { return f(xs); }; }\nexport function selected(xs: number[]) { factory(cheap, xs)(); return factory(cube, xs)(); }";

    run_with_source(source, |analysis, file| {
        let selected = function_of_name(analysis.project, file, "selected");
        let part = support::summary_of(analysis, file, "selected");

        assert!(part.is_complete());
        assert_eq!(
            support::legacy_class_of(analysis, file, selected, &part.cost),
            Cost::parse("O(N^3)").unwrap()
        );
        assert_eq!(
            record_costs_of(analysis, file, "run"),
            [Cost::parse("O(1)").unwrap(), Cost::parse("O(N^3)").unwrap()]
        );
        support::assert_scheduler_terminal(analysis.scheduler_stats());
    });
}

#[test]
fn a_default_callback_joins_the_invocation_effects() {
    let source = "let counter = 0;\nfunction bump() { counter++; }\nfunction run(f: () => void = bump) { f(); }\nexport function selected(xs: number[]) { counter = 0; run(); for (let i = 0; i < counter; i++) void xs; }";

    let (_, reasons) = selected_result(source);

    assert!(
        !reasons.contains(&olint::unknowns::UnknownReason::Target),
        "{reasons:?}"
    );
}

fn constructor_of<'a>(
    project: &olint::project::Project<'a>,
    file: olint::project::FileId,
    class: &str,
) -> olint::declarations::FunctionNode<'a> {
    support::first_node_of(project, file, |kind| match kind {
        oxc_ast::AstKind::Class(found) if found.id.as_ref().is_some_and(|id| id.name == class) => {
            found.body.body.iter().find_map(|element| match element {
                oxc_ast::ast::ClassElement::MethodDefinition(method)
                    if method.kind == oxc_ast::ast::MethodDefinitionKind::Constructor =>
                {
                    Some(olint::declarations::FunctionNode::Function(&method.value))
                }
                _ => None,
            })
        }
        _ => None,
    })
}

fn complete_selected_class_of(
    analysis: &mut Analysis<'_, '_>,
    file: olint::project::FileId,
) -> Cost {
    let selected = function_of_name(analysis.project, file, "selected");
    let part = support::summary_of(analysis, file, "selected");

    assert!(part.is_complete());

    support::legacy_class_of(analysis, file, selected, &part.cost)
}

fn constructor_costs_of(
    analysis: &mut Analysis<'_, '_>,
    file: olint::project::FileId,
    class: &str,
) -> Vec<Cost> {
    let function = constructor_of(analysis.project, file, class);
    let root = function_of_name(analysis.project, file, "selected");
    let readings: Vec<_> = analysis
        .summary_records_for(olint::declarations::FunctionId {
            file,
            node: function.node_id(),
        })
        .into_iter()
        .map(|record| record.reading.clone())
        .collect();

    readings
        .into_iter()
        .map(|reading| {
            let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

            assert!(part.is_complete(), "{class}");

            support::legacy_class_of(analysis, file, root, &part.cost)
        })
        .collect()
}

#[test]
fn constructor_summaries_initialize_fields_once_per_instance() {
    let source = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }\nexport function selected(xs: number[]) { class Box { value = quadratic(xs); constructor() {} } new Box(); new Box(); return new Box(); }";

    run_with_source(source, |analysis, file| {
        assert_eq!(
            complete_selected_class_of(analysis, file),
            Cost::parse("O(N^2)").unwrap()
        );
        assert_eq!(
            constructor_costs_of(analysis, file, "Box"),
            [Cost::parse("O(N^2)").unwrap()]
        );
        support::assert_scheduler_terminal(analysis.scheduler_stats());
    });
}

#[test]
fn derived_constructor_summaries_include_base_construction_at_super() {
    let source = "function quadratic(xs: number[]): number { let total = 0; for (const a of xs) for (const b of xs) total += a + b; return total; }\nclass A { constructor(ys: number[]) { quadratic(ys); } }\nclass B extends A {}\nclass C extends B { constructor(ys: number[]) { super(ys); } }\nexport function selected(xs: number[]) { return new C(xs); }";

    run_with_source(source, |analysis, file| {
        assert_eq!(
            complete_selected_class_of(analysis, file),
            Cost::parse("O(N^2)").unwrap()
        );
        assert_eq!(
            constructor_costs_of(analysis, file, "C"),
            [Cost::parse("O(N^2)").unwrap()]
        );
        assert_eq!(
            constructor_costs_of(analysis, file, "A"),
            [Cost::parse("O(N^2)").unwrap()]
        );
        support::assert_scheduler_terminal(analysis.scheduler_stats());
    });
}

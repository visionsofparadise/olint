use olint::analysis::{Analysis, Options, TypeMode};
use olint::config::read_config;
use olint::cost::{Cost, CostComparison, ExecutionPhase};
use olint::public::public_functions;
use std::path::Path;

use crate::support;

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

#[test]
fn implicit_construction_charges_fields_and_base_construction() {
    let quadratic = "function quadratic(xs:number[]):number{let total=0;for(const a of xs) for(const b of xs) total+=a*b; return total;} const xs:number[]=[];";

    for (source, name, expected) in [
        (
            format!("{quadratic} export class Heavy {{ value=quadratic(xs); }}"),
            "new Heavy()",
            Some("O(N^2)"),
        ),
        (
            format!("{quadratic} class Base {{ value=quadratic(xs); }} export class Derived extends Base {{}}"),
            "new Derived()",
            Some("O(N^2)"),
        ),
        (
            format!("{quadratic} export class Light {{ value=1; }}"),
            "new Light()",
            Some("O(1)"),
        ),
        (
            format!("{quadratic} class Base {{ constructor(){{quadratic(xs);}} }} export class Derived extends Base {{ label=1; }}"),
            "new Derived()",
            None,
        ),
    ] {
        let reported = reported_result(&source, name);

        assert_eq!(
            reported.map(|(cost, _)| cost),
            expected.map(|text| Cost::parse(text).unwrap()),
            "{source}"
        );
    }
}

fn reported_result(
    source: &str,
    name: &str,
) -> Option<(
    Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
)> {
    let mut result = None;

    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |project, _| {
            let mut analysis = Analysis::new(project, SYNTACTIC);
            let found = analysis
                .reportable()
                .into_iter()
                .find(|(target, function)| analysis.name_of(*target, *function) == name);
            let Some((target, function)) = found else {
                return;
            };
            let part = analysis
                .summarize(target, function)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            result = Some((
                support::legacy_class_of(&mut analysis, target, function, &part.cost),
                support::unknown_reasons(&analysis, part.unknowns),
            ));
        },
    );

    result
}

#[test]
fn decorated_construction_surfaces_keep_their_unsupported_syntax() {
    let decorator =
        "function decorate(value: unknown, context: unknown): undefined { return undefined; }";

    let mut partials = Vec::new();

    for (source, name, unsupported) in [
        (
            format!("{decorator} export class Decorated {{ @decorate value = 1; }}"),
            "new Decorated()",
            true,
        ),
        (
            format!("{decorator} @decorate export class Decorated {{ value = 1; }}"),
            "new Decorated()",
            true,
        ),
        (
            format!("{decorator} class Base {{ @decorate value = 1; }} export class Derived extends Base {{}}"),
            "new Derived()",
            true,
        ),
        (
            format!("{decorator} export class Plain {{ value = 1; }}"),
            "new Plain()",
            false,
        ),
    ] {
        let Some((cost, reasons)) = reported_result(&source, name) else {
            panic!("{source}: the construction surface is reported");
        };

        assert_eq!(cost, Cost::parse("O(1)").unwrap(), "{source}");

        if !unsupported {
            assert!(reasons.is_empty(), "{source}: {reasons:?}");
        }

        partials.push(reasons.contains(&olint::unknowns::UnknownReason::UnsupportedSyntax));
    }

    assert_eq!(partials, vec![true, true, true, false]);
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
fn self_recursion_charges_its_body_at_every_guarded_level() {
    run_with_source(
        "export function walk(n: number): number {\n\treturn n > 0 ? walk(n - 1) : 0;\n}",
        |analysis, file| {
            let walk = function_of_name(analysis.project, file, "walk");
            let part = analysis
                .summarize(file, walk)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(
                support::legacy_class_of(analysis, file, walk, &part.cost),
                Cost::N
            );
            assert!(part.is_complete());
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

            assert_eq!(support::legacy_class_of(analysis, file, ping, &root.cost), Cost::N);
            assert_eq!(support::legacy_class_of(analysis, file, pong, &member.cost), Cost::N);
            assert!(root.is_complete());
            assert!(member.is_complete());
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

const GUARDED_CYCLE: &str = "export function ping(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + pong(xs, n - 1);\n}\n/** @perf cold */\nfunction pong(xs: number[], n: number): number {\n\treturn ping(xs, n);\n}\n";
const SKIPPING_CYCLE: &str = "export function ping(xs: number[], n: number): number {\n\tif (n === 0) return 0;\n\tconst s = xs.length;\n\treturn s + pong(xs, n - 1);\n}\n/** @perf cold */\nfunction pong(xs: number[], n: number): number {\n\treturn ping(xs, n);\n}\n";

fn assert_solved_depth(analysis: &mut Analysis<'_, '_>, file: olint::project::FileId, name: &str) {
    let function = function_of_name(analysis.project, file, name);
    let part = support::summary_of(analysis, file, name);
    let envelope = analysis
        .bind_function_cost(file, function, &Cost::N)
        .expect("the envelope binds to the declared inputs");

    assert_eq!(
        part.cost.compare(&envelope),
        CostComparison::Within,
        "{name}"
    );
    assert_ne!(
        part.cost.compare(&Cost::ONE),
        CostComparison::Within,
        "{name}"
    );
    assert!(part.is_complete(), "{name}");
}

#[test]
fn a_cold_recursive_function_keeps_its_solved_depth() {
    let source = "/** @perf cold */\nexport function walk(xs: number[], n: number): number {\n\tif (n <= 0) return 0;\n\tconst s = xs.length;\n\treturn s + walk(xs, n - 1);\n}\n";

    run_with_source(source, |analysis, file| {
        assert_solved_depth(analysis, file, "walk");
    });
}

#[test]
fn a_cold_cycle_member_keeps_the_cycle_depth() {
    run_with_source(GUARDED_CYCLE, |analysis, file| {
        for name in ["ping", "pong"] {
            assert_solved_depth(analysis, file, name);
        }
    });
}

#[test]
fn an_unguarded_cycle_member_keeps_the_cycle_uncertainty() {
    run_with_source(SKIPPING_CYCLE, |analysis, file| {
        for name in ["ping", "pong"] {
            let function = function_of_name(analysis.project, file, name);
            let part = support::summary_of(analysis, file, name);

            assert_eq!(
                support::legacy_class_of(analysis, file, function, &part.cost),
                Cost::ONE,
                "{name}"
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

const LAZY_HELPERS: &str = "function quadratic(xs: number[]) { let total = 0; for (const x of xs) for (const y of xs) total += x + y; return total; }\nfunction scan(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }\nfunction* single(xs: number[]) { for (const x of xs) yield x; }\nfunction* square(xs: number[]) { for (const x of xs) for (const y of xs) yield x + y; }\nfunction* heavy(xs: number[]) { for (const x of xs) { quadratic(xs); yield x; } }";

type LazyResult = (
    Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
);

fn lazy_selected_of(declarations: &str, body: &str) -> LazyResult {
    selected_result(&format!(
        "{LAZY_HELPERS}\n{declarations}\nexport function selected{body}"
    ))
}

fn assert_lazy_selected(cases: &[(&str, &str, &str, bool)]) {
    for (declarations, body, expected, partial) in cases {
        let (cost, reasons) = lazy_selected_of(declarations, body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}: {reasons:?}");
        assert_eq!(!reasons.is_empty(), *partial, "{body}: {reasons:?}");
    }
}

fn phase_costs_of(source: &str, name: &str) -> Vec<(ExecutionPhase, Cost)> {
    let mut found = Vec::new();

    run_with_source(source, |analysis, file| {
        let function = function_of_name(analysis.project, file, name);
        let reading = analysis.summarize(file, function);

        for (phase, _, part) in &reading.completions {
            let cost = support::legacy_class_of(analysis, file, function, &part.cost);

            found.push((*phase, cost));
        }
    });

    found
}

#[test]
fn async_continuations_after_an_await_are_scheduled() {
    let phases = phase_costs_of(
        &format!("{LAZY_HELPERS}\nexport async function selected(xs: number[], p: Promise<number>) {{ const n = scan(xs); await p; return quadratic(xs) + n; }}"),
        "selected",
    );

    assert!(
        phases.contains(&(ExecutionPhase::Immediate, Cost::parse("O(N)").unwrap())),
        "{phases:?}"
    );
    assert!(
        phases.contains(&(ExecutionPhase::Scheduled, Cost::parse("O(N^2)").unwrap())),
        "{phases:?}"
    );

    let unsuspended = phase_costs_of(
        &format!("{LAZY_HELPERS}\nexport async function selected(xs: number[]) {{ return quadratic(xs); }}"),
        "selected",
    );

    assert!(
        unsuspended
            .iter()
            .all(|(phase, _)| *phase == ExecutionPhase::Immediate),
        "{unsuspended:?}"
    );

    let (cost, reasons) = selected_result(&format!("{LAZY_HELPERS}\nasync function work(xs: number[]) {{ await 0; return quadratic(xs); }}\nexport async function selected(xs: number[]) {{ return await work(xs); }}"));

    assert_eq!(cost, Cost::parse("O(N^2)").unwrap(), "{reasons:?}");
    assert!(reasons.is_empty(), "{reasons:?}");
}

#[test]
fn generator_functions_defer_their_body_to_the_lazy_channel() {
    run_with_source(LAZY_HELPERS, |analysis, file| {
        let function = function_of_name(analysis.project, file, "square");
        let reading = analysis.summarize(file, function);
        let total = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let latent = reading.latent(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(
            support::legacy_class_of(analysis, file, function, &total.cost),
            Cost::ONE
        );
        assert_eq!(
            support::legacy_class_of(analysis, file, function, &latent.cost),
            Cost::parse("O(N^2)").unwrap()
        );
        assert!(total.is_complete() && latent.is_complete());
    });
}

#[test]
fn generator_creation_differs_from_zero_partial_and_full_consumption() {
    assert_lazy_selected(&[
        ("", "(xs: number[]) { return single(xs); }", "O(1)", false),
        ("", "(xs: number[]) { single(xs); return 0; }", "O(1)", false),
        ("", "(xs: number[]) { return single(xs).next(); }", "O(N)", false),
        (
            "",
            "(xs: number[]) { let t = 0; for (const v of single(xs)) t += quadratic(xs); return t; }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[]) { let t = 0; for (const v of square(xs)) t += quadratic(xs); return t; }",
            "O(N^4)",
            false,
        ),
        (
            "",
            "(xs: number[]) { let t = 0; for (const v of square(xs)) t += v; return t; }",
            "O(N^2)",
            false,
        ),
        (
            "",
            "(xs: number[]) { for (const v of single(xs)) { if (v > 3) break; } }",
            "O(N)",
            false,
        ),
        ("", "(xs: number[]) { return [...square(xs)]; }", "O(N^2)", false),
        (
            "function* outer(xs: number[]) { yield* square(xs); }",
            "(xs: number[]) { let t = 0; for (const v of outer(xs)) t += quadratic(xs); return t; }",
            "O(N^4)",
            false,
        ),
    ]);
}

#[test]
fn repeated_consumer_calls_multiply_proven_resume_work() {
    assert_lazy_selected(&[
        (
            "function take(it: Iterator<number>) { return it.next(); }",
            "(xs: number[]) { const it = heavy(xs); for (const x of xs) take(it); }",
            "O(N^4)",
            false,
        ),
        (
            "function consume(it: Iterable<number>) { let t = 0; for (const v of it) t += v; return t; }",
            "(xs: number[]) { for (const x of xs) consume(heavy(xs)); }",
            "O(N^4)",
            false,
        ),
        (
            "",
            "(xs: number[]) { const it = heavy(xs); it.next(); it.next(); }",
            "O(N^3)",
            false,
        ),
    ]);
}

#[test]
fn unknown_consumption_and_yield_counts_stay_incomplete() {
    let escaped = lazy_selected_of(
        "const hold: unknown[] = [];",
        "(xs: number[]) { hold.push(heavy(xs)); }",
    );

    assert_eq!(escaped.0, Cost::parse("O(N^3)").unwrap(), "{escaped:?}");
    assert!(
        escaped
            .1
            .contains(&olint::unknowns::UnknownReason::Multiplicity),
        "{escaped:?}"
    );

    let unresolved = lazy_selected_of(
        "function* grown(set: Set<number>) { for (const v of set) { set.add(v + 1); yield v; } }",
        "(set: Set<number>, xs: number[]) { let t = 0; for (const v of grown(set)) t += quadratic(xs); return t; }",
    );

    assert!(
        unresolved
            .1
            .contains(&olint::unknowns::UnknownReason::Bound),
        "{unresolved:?}"
    );
    assert_eq!(
        unresolved.0,
        Cost::parse("O(N^2)").unwrap(),
        "{unresolved:?}"
    );

    let called = lazy_selected_of(
        "function run(make: (xs: number[]) => Iterable<number>, xs: number[]) { return make(xs); }",
        "(xs: number[]) { return run(heavy, xs); }",
    );

    assert_eq!(called.0, Cost::parse("O(N^3)").unwrap(), "{called:?}");
    assert!(
        called
            .1
            .contains(&olint::unknowns::UnknownReason::Multiplicity),
        "{called:?}"
    );
}

#[test]
fn returned_aliased_and_passed_generators_keep_latent_work_until_consumed() {
    let make = "function make(xs: number[]) { return square(xs); }";

    assert_lazy_selected(&[
        (make, "(xs: number[]) { return make(xs); }", "O(1)", false),
        (
            make,
            "(xs: number[]) { let t = 0; for (const v of make(xs)) t += quadratic(xs); return t; }",
            "O(N^4)",
            false,
        ),
        (
            make,
            "(xs: number[]) { const it = make(xs); const other = it; let t = 0; for (const v of other) t += quadratic(xs); return t; }",
            "O(N^4)",
            false,
        ),
        (
            "function consume(it: Iterable<number>, xs: number[]) { let t = 0; for (const v of it) t += quadratic(xs); return t; }",
            "(xs: number[]) { return consume(square(xs), xs); }",
            "O(N^4)",
            false,
        ),
        (
            "function pass(it: Iterable<number>) { return it; }",
            "(xs: number[]) { let t = 0; for (const v of pass(square(xs))) t += quadratic(xs); return t; }",
            "O(N^4)",
            false,
        ),
    ]);

    run_with_source(&format!("{LAZY_HELPERS}\n{make}"), |analysis, file| {
        let function = function_of_name(analysis.project, file, "make");
        let reading = analysis.summarize(file, function);
        let latent = reading.latent(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(
            support::legacy_class_of(analysis, file, function, &latent.cost),
            Cost::parse("O(N^2)").unwrap()
        );
    });
}

#[test]
fn every_consumer_charges_the_lazy_body_it_runs() {
    assert_lazy_selected(&[
        (
            "",
            "(xs: number[]) { for (const v of heavy(xs)) void v; }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[]) { for (const v of heavy(xs)) { if (v > 3) break; } }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[]) { return [...heavy(xs)]; }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[]) { const [first] = heavy(xs); return first; }",
            "O(N^3)",
            false,
        ),
        (
            "",
            "(xs: number[]) { let first = 0; [first] = heavy(xs); return first; }",
            "O(N^3)",
            false,
        ),
        (
            "function* outer(xs: number[]) { yield* heavy(xs); }",
            "(xs: number[]) { for (const v of outer(xs)) void v; }",
            "O(N^3)",
            false,
        ),
    ]);
}

#[test]
fn a_generator_with_any_untracked_use_is_charged_where_it_is_created() {
    assert_lazy_selected(&[
        (
            "",
            "(xs: number[]) { const it = heavy(xs); for (const v of it) void v; return { it }; }",
            "O(N^3)",
            true,
        ),
        (
            "function keep(it: Iterable<number>) { return { it }; }",
            "(xs: number[]) { return keep(heavy(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            "function keep(it: Iterable<number>) { return { it }; }\nfunction drain(it: Iterable<number>) { for (const v of it) void v; return { it: [0] }; }",
            "(xs: number[], flag: boolean) { const use = flag ? drain : keep; return use(heavy(xs)); }",
            "O(N^3)",
            true,
        ),
        (
            "function drain(it: Iterable<number>) { for (const v of it) void v; }",
            "(xs: number[]) { drain(heavy(xs)); }",
            "O(N^3)",
            false,
        ),
    ]);
}

#[test]
fn distinct_latent_arguments_keep_distinct_specializations() {
    let consume = "function consume(it: Iterable<number>, xs: number[]) { let t = 0; for (const v of it) t += quadratic(xs); return t; }";

    assert_lazy_selected(&[
        (
            consume,
            "(xs: number[]) { return consume(single(xs), xs) + consume(square(xs), xs); }",
            "O(N^4)",
            false,
        ),
        (
            consume,
            "(xs: number[], flag: boolean) { return consume(flag ? square(xs) : square(xs), xs); }",
            "O(N^4)",
            false,
        ),
    ]);
}

#[test]
fn a_function_returning_a_generator_on_some_paths_leaves_the_count_unresolved() {
    let (cost, reasons) = lazy_selected_of(
        "function pick(flag: boolean, xs: number[]): Iterable<number> { if (flag) return square(xs); return xs; }",
        "(xs: number[], flag: boolean) { let t = 0; for (const v of pick(flag, xs)) t += quadratic(xs); return t; }",
    );

    assert!(
        reasons.contains(&olint::unknowns::UnknownReason::Bound),
        "{cost:?} {reasons:?}"
    );
}

#[test]
fn expression_await_keeps_known_work_and_marks_phase_placement_uncertain() {
    let source = format!("{LAZY_HELPERS}\nexport async function selected(xs: number[], p: Promise<number>) {{ const m = quadratic(xs) + (await p); return scan(xs) + m; }}");
    let phases = phase_costs_of(&source, "selected");

    assert!(
        phases.contains(&(ExecutionPhase::Immediate, Cost::parse("O(N^2)").unwrap())),
        "{phases:?}"
    );
    assert!(
        phases.contains(&(ExecutionPhase::Scheduled, Cost::parse("O(N^2)").unwrap())),
        "{phases:?}"
    );

    run_with_source(&source, |analysis, file| {
        let function = function_of_name(analysis.project, file, "selected");
        let reading = analysis.summarize(file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(
            support::legacy_class_of(analysis, file, function, &part.cost),
            Cost::parse("O(N^2)").unwrap()
        );
        assert!(support::unknown_reasons(analysis, part.unknowns)
            .contains(&olint::unknowns::UnknownReason::UnsupportedModel));
    });
}

#[test]
fn a_possible_non_generator_alternative_leaves_the_count_unresolved() {
    for (declarations, body) in [
        (
            "",
            "(xs: number[], flag: boolean) { let t = 0; for (const v of flag ? square(xs) : xs) t += quadratic(xs); return t; }",
        ),
        (
            "",
            "(xs: number[], flag: boolean) { const make = flag ? square : (ys: number[]) => ys; let t = 0; for (const v of make(xs)) t += quadratic(xs); return t; }",
        ),
    ] {
        let (cost, reasons) = lazy_selected_of(declarations, body);

        assert!(
            reasons.contains(&olint::unknowns::UnknownReason::Bound),
            "{body}: {cost:?} {reasons:?}"
        );
    }
}

#[test]
fn a_resumption_that_may_reach_analysed_methods_is_not_a_tracked_consumer() {
    let (cost, reasons) = lazy_selected_of(
        "class Other { next() { return 0; } }",
        "(xs: number[]) { const it: Other = heavy(xs) as any; it.next(); return it; }",
    );

    assert_eq!(cost, Cost::parse("O(N^3)").unwrap(), "{reasons:?}");
    assert!(
        reasons.contains(&olint::unknowns::UnknownReason::Multiplicity),
        "{reasons:?}"
    );
}

#[test]
fn one_latent_argument_site_specializes_on_its_latent_work() {
    assert_lazy_selected(&[(
        "function consume(it: Iterable<number>) { let t = 0; for (const v of it) t += v; return t; }
function make(a: number[]) { return consume(square(a)); }",
        "(xs: number[]) { return make([1, 2, 3]) + make(xs); }",
        "O(N^2)",
        false,
    ), (
        "function consume(it: Iterable<number>) { let t = 0; for (const v of it) t += v; return t; }
function make(a: number[]) { return consume(square(a)); }",
        "(xs: number[]) { return make(xs) + make([1, 2, 3]); }",
        "O(N^2)",
        false,
    ), (
        "function consume(it: Iterable<number>) { let t = 0; for (const v of it) t += v; return t; }
function make(a: number[]) { return consume(square(a)); }
function first() { return make([1, 2, 3]); }",
        "(xs: number[]) { first(); return make(xs); }",
        "O(N^2)",
        false,
    )]);
}

#[test]
fn latent_arguments_with_equal_effects_but_different_work_keep_distinct_keys() {
    run_with_source(
        "function consume(it: Iterable<number>) { let t = 0; for (const v of it) t += v; return t; }",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "consume");
            let olint::declarations::FunctionNode::Function(inner) = function else {
                panic!("ordinary function")
            };
            let oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) =
                &inner.params.items[0].pattern
            else {
                panic!("plain parameter")
            };
            let binding = olint::declarations::Binding::Symbol {
                file,
                symbol: identifier.symbol_id.get().unwrap(),
            };
            let origin = olint::unknowns::SourceSpan {
                file,
                start: identifier.span.start,
                end: identifier.span.end,
            };
            let value = analysis.values.at(origin);
            let yields = Cost::dimension(7, olint::cost::Domain::Size);
            let mut costs = Vec::new();

            for (work, count) in [(Cost::ONE, Cost::ONE), (yields.clone(), yields.clone())] {
                let id = olint::summaries::SummaryId(analysis.summaries_arena.len() as u32);
                let mut result = value.clone();

                result.latent = Some(id);
                result.size = Some(count);

                analysis
                    .summaries_arena
                    .push(olint::summaries::SummaryRecord {
                        reading: olint::cost::Reading::of_completion(
                            ExecutionPhase::Lazy,
                            olint::flow::Completion::Normal,
                            olint::cost::Part::unmarked(work, None),
                        ),
                        result,
                        effects: olint::effects::Effects::default(),
                    });

                let mut argument = value.clone();

                argument.latent = Some(id);

                let facts = olint::values::ArgumentFacts {
                    value: argument,
                    callback: None,
                    preference: olint::cost::Preference::Absent,
                    definedness: olint::values::Definedness::Unknown,
                };
                let reading = analysis.summarize_with(
                    file,
                    function,
                    olint::summaries::Substitutions::from([(binding, facts)]),
                    false,
                );

                costs.push(
                    reading
                        .total(&mut analysis.unknowns, &mut analysis.traces)
                        .cost,
                );
            }

            assert_ne!(costs[0], costs[1], "{costs:?}");
        },
    );
}

#[test]
fn a_recursive_generator_keeps_its_solved_lazy_work_while_its_count_stays_unresolved() {
    let source = "export function* walk(n: number, xs: number[]): Generator<number> { if (n <= 0) return; for (const x of xs) yield x; yield* walk(n - 1, xs); }\nexport function drain(n: number, xs: number[]): number { let t = 0; for (const v of walk(n, xs)) t += v; return t; }";

    run_with_source(source, |analysis, file| {
        let drain = function_of_name(analysis.project, file, "drain");
        let part = support::summary_of(analysis, file, "drain");
        let linear = analysis
            .bind_function_cost(file, drain, &Cost::parse("O(N)").unwrap())
            .unwrap();
        let reasons = support::unknown_reasons(analysis, part.unknowns);

        assert_ne!(
            part.cost.compare(&linear),
            CostComparison::Within,
            "{part:?}"
        );
        assert!(
            reasons.contains(&olint::unknowns::UnknownReason::Bound),
            "{reasons:?}"
        );
    });
}

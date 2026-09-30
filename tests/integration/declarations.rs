use olint::analysis::{Analysis, Stats};
use olint::declarations::{Declaration, Declarations, FunctionNode};
use olint::project::{FileId, Project};
use oxc_ast::ast::IdentifierReference;
use oxc_ast::AstKind;
use oxc_span::GetSpan;

use crate::support;

fn calls_in<'a>(project: &Project<'a>, file: FileId) -> Vec<&'a oxc_ast::ast::CallExpression<'a>> {
    project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .filter_map(|node| match node.kind() {
            AstKind::CallExpression(call) => Some(call),
            _ => None,
        })
        .collect()
}

#[test]
fn import_equals_index_visits_each_symbol_once_in_deep_chains_and_cycles() {
    for count in [128, 2048] {
        for reverse in [false, true] {
            for base in [
                "N.work".to_string(),
                format!("a{}", count - 1),
                "missing.work".to_string(),
            ] {
                let source = format!("namespace N {{export function work(){{}}}} import a0={base};{} function selected(){{{}}}",(1..count).map(|i|format!("import a{i}=a{};",i-1)).collect::<String>(),(0..count).map(|i|format!("a{i}();")).collect::<String>());
                let files = [("tsconfig.json", "{}"), ("index.ts", source.as_str())];

                run_in_project(&files, |project, root| {
                    let file = file_of(project, root, "index.ts");
                    let mut calls = calls_in(project, file);
                    let mut analysis = Analysis::new(project, SYNTACTIC);

                    if reverse {
                        calls.reverse();
                    }

                    for call in &calls {
                        let target = analysis.callee_targets_of(file, call);

                        assert_eq!(target.known.len(), usize::from(base == "N.work"));
                        assert!(target.open);
                    }

                    let cold = analysis.declarations.resolution_stats();

                    assert!(cold.symbol_visits <= count + 2, "{cold:?}");
                    assert!(cold.helper_visits <= 1, "{cold:?}");
                    assert!(cold.stack_peak <= count + 4, "{cold:?}");

                    for call in calls {
                        analysis.callee_targets_of(file, call);
                    }

                    assert_eq!(analysis.declarations.resolution_stats(), cold);
                });
            }
        }
    }
}

#[test]
fn many_import_aliases_share_one_write_reference_scan() {
    let count = 512;
    let helper = format!("export function work(){{{}}}", "work();".repeat(count));
    let source = format!(
        "import {{{}}} from './helper'; function selected(){{{}}}",
        (0..count)
            .map(|i| format!("work as a{i}"))
            .collect::<Vec<_>>()
            .join(","),
        (0..count).map(|i| format!("a{i}();")).collect::<String>()
    );
    let files = [
        ("tsconfig.json", "{}"),
        ("index.ts", source.as_str()),
        ("helper.ts", helper.as_str()),
    ];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let calls = calls_in(project, file);
        let mut analysis = Analysis::new(project, SYNTACTIC);

        for call in &calls {
            assert!(!analysis.callee_targets_of(file, call).open);
        }

        let cold = analysis.declarations.resolution_stats();

        assert_eq!(cold.write_reference_visits, count);
        assert!(cold.symbol_visits <= count + 1, "{cold:?}");

        for call in calls {
            analysis.callee_targets_of(file, call);
        }

        assert_eq!(analysis.declarations.resolution_stats(), cold);
    });
}

use support::{call_of, file_of, first_node_of, run_in_project, SYNTACTIC, TYPED_PACKAGE};

fn reference_of<'a>(
    project: &Project<'a>,
    file: FileId,
    name: &str,
) -> &'a IdentifierReference<'a> {
    first_node_of(project, file, |kind| match kind {
        AstKind::IdentifierReference(reference) if reference.name == name => Some(reference),
        _ => None,
    })
}

fn function_name_of(declaration: Option<Declaration<'_>>) -> String {
    match declaration {
        Some(Declaration::Function {
            function: FunctionNode::Function(function),
            ..
        }) => function
            .id
            .as_ref()
            .map(|id| id.name.to_string())
            .unwrap_or_default(),
        other => panic!("expected a function declaration, found {other:?}"),
    }
}

fn shape_of(declaration: &Declaration<'_>) -> &'static str {
    match declaration {
        Declaration::Function {
            function: FunctionNode::Function(function),
            ..
        } if function.body.is_none() => "signature",
        Declaration::Function { .. } => "function",
        Declaration::Interface { .. } => "interface",
        Declaration::Class { .. } => "class",
        _ => "other",
    }
}

fn declaration_of_reference<'a>(
    project: &Project<'a>,
    declarations: &Declarations<'a>,
    file: FileId,
    name: &str,
) -> Option<Declaration<'a>> {
    declarations.of_reference(project, file, reference_of(project, file, name))
}

fn imported_function_name_of(files: &[(&str, &str)], name: &str) -> String {
    let mut found = String::new();

    run_in_project(files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");

        found = function_name_of(declaration_of_reference(
            project,
            &declarations,
            index,
            name,
        ));
    });

    found
}

#[test]
fn of_export_follows_a_named_re_export_chain() {
    let files = [
        ("tsconfig.json", "{}"),
        ("a.ts", "export function target() {}"),
        ("b.ts", "export { target as renamed } from \"./a\";"),
        ("c.ts", "export { renamed as last } from \"./b\";"),
        ("index.ts", "import { last } from \"./c\";\nlast();"),
    ];

    assert_eq!(imported_function_name_of(&files, "last"), "target");
}

#[test]
fn star_exports_terminate_through_a_cycle() {
    let files = [
        ("tsconfig.json", "{}"),
        ("a.ts", "export * from \"./b\";\nexport const fromA = 1;"),
        ("b.ts", "export * from \"./a\";\nexport function fromB() {}"),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let a = file_of(project, root, "a.ts");
        let names: Vec<String> = declarations
            .exports_of(project, a)
            .into_iter()
            .map(|(name, _)| name)
            .collect();

        assert_eq!(
            function_name_of(declarations.of_export(project, a, "fromB").pop()),
            "fromB"
        );
        assert!(declarations.of_export(project, a, "missing").is_empty());
        assert_eq!(names, vec!["fromA", "fromB"]);
    });
}

#[test]
fn namespace_import_reaches_its_members() {
    let files = [
        ("tsconfig.json", "{}"),
        ("lib.ts", "export function run() {}"),
        (
            "index.ts",
            "import * as library from \"./lib\";\nlibrary.run();",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");
        let lib = file_of(project, root, "lib.ts");

        match declaration_of_reference(project, &declarations, index, "library") {
            Some(Declaration::Namespace { file }) => {
                assert_eq!(file, lib);
                assert_eq!(
                    function_name_of(declarations.of_export(project, file, "run").pop()),
                    "run"
                );
            }
            other => panic!("expected a namespace, found {other:?}"),
        }
    });
}

#[test]
fn default_import_reaches_the_default_export() {
    let files = [
        ("tsconfig.json", "{}"),
        ("lib.ts", "export default function run() {}"),
        ("index.ts", "import go from \"./lib\";\ngo();"),
    ];

    assert_eq!(imported_function_name_of(&files, "go"), "run");
}

#[test]
fn package_declarations_have_no_function_and_javascript_packages_supply_bodies() {
    let files = [
        &[
            ("tsconfig.json", "{}"),
            (
                "index.ts",
                "import { run } from \"pkg\";\nimport plain from \"plain\";\nrun();\nplain();",
            ),
            (
                "node_modules/plain/package.json",
                r#"{ "name": "plain", "main": "index.js" }"#,
            ),
            ("node_modules/plain/index.js", "module.exports = () => 1;"),
        ][..],
        &TYPED_PACKAGE,
    ]
    .concat();

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");
        let run = declaration_of_reference(project, &declarations, index, "run");

        let plain = declaration_of_reference(project, &declarations, index, "plain")
            .expect("the package implementation is loaded");
        let (file, _) = declarations
            .function_of(plain)
            .expect("the module.exports arrow is executable");

        assert!(matches!(run, Some(Declaration::Function { .. })));
        assert!(declarations.function_of(run.expect("declared")).is_none());
        assert_eq!(project.file(file).relative, "node_modules/plain/index.js");
    });
}

#[test]
fn exports_of_follows_typescript_binding_order() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "export * from \"./star\";
export const first = 1;
export { reexported } from \"./other\";
export function hoisted() {}
import value from \"./other\";
export { value };
export default function () {}
export interface Shape { x: number }",
        ),
        (
            "star.ts",
            "export function fromStar() {}
export const first = 2;",
        ),
        (
            "other.ts",
            "export function reexported() {}
export default function named() {}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");
        let names: Vec<String> = declarations
            .exports_of(project, index)
            .into_iter()
            .map(|(name, _)| name)
            .collect();

        assert_eq!(
            names,
            vec![
                "hoisted",
                "default",
                "first",
                "reexported",
                "value",
                "Shape",
                "fromStar"
            ]
        );
        assert_eq!(
            function_name_of(declarations.of_export(project, index, "value").pop()),
            "named"
        );
        assert_eq!(
            function_name_of(declarations.of_export(project, index, "default").pop()),
            ""
        );
    });
}

#[test]
fn exports_carry_every_declaration_in_typescript_order() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "export interface Merged { x: number }\nexport class Merged { run() { return 1; } }\nexport function over(a: string): void;\nexport function over(a: number): void;\nexport function over(a: any) { return a; }\nover(1);",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");
        let exports = declarations.exports_of(project, index);
        let shapes: Vec<(String, Vec<&str>)> = exports
            .iter()
            .map(|(name, found)| (name.clone(), found.iter().map(shape_of).collect()))
            .collect();

        assert_eq!(
            shapes,
            vec![
                (
                    "over".to_string(),
                    vec!["signature", "signature", "function"]
                ),
                ("Merged".to_string(), vec!["interface", "class"]),
            ]
        );
        assert_eq!(
            declaration_of_reference(project, &declarations, index, "over")
                .as_ref()
                .map(shape_of),
            Some("function")
        );
    });
}

#[test]
fn stats_lines_order_by_count_then_insertion() {
    let mut stats = Stats::default();

    for label in ["first", "second", "third", "second"] {
        stats.count(label);
    }

    assert_eq!(
        stats.lines(),
        vec!["    2  second", "    1  first", "    1  third"]
    );
}

#[test]
fn package_declaration_files_resolve_callees_without_bodies() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "node_modules/engine/package.json",
            r#"{ "name": "engine", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/engine/index.d.ts",
            "export declare function run(xs: number[]): number;\nexport declare class Engine {\n\trun(): number;\n\tstatic make(): Engine;\n}",
        ),
        (
            "index.ts",
            "import { run, Engine } from \"engine\";\nexport function f() {\n\trun([1]);\n\tconst engine = new Engine();\n\tengine.run();\n\tEngine.make();\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let index = file_of(project, root, "index.ts");
        let package = file_of(project, root, "node_modules/engine/index.d.ts");
        let resolved: Vec<(bool, bool)> = ["run", "engine.run", "Engine.make"]
            .iter()
            .map(|callee| {
                let declaration =
                    analysis.callee_declaration_of(index, call_of(project, index, callee));
                let function = declaration
                    .and_then(|declaration| analysis.declarations.function_of(declaration));

                (declaration.is_some(), function.is_some())
            })
            .collect();

        assert!(project.file(package).external_library);
        assert!(!project.is_project_file(package));
        assert_eq!(resolved, vec![(true, false); 3]);
    });
}

fn work_targets_of(relative: &str, source: &str) -> (Vec<usize>, bool) {
    let files = [
        ("tsconfig.json", r#"{"compilerOptions":{"allowJs":true}}"#),
        (relative, source),
    ];
    let mut found = (Vec::new(), true);

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, relative);
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let bodies: Vec<_> = project
            .file(file)
            .semantic
            .nodes()
            .iter()
            .filter(|node| match node.kind() {
                AstKind::Function(function) => {
                    function.body.is_some()
                        && function.id.as_ref().is_none_or(|name| name.name != "run")
                }
                _ => false,
            })
            .map(|node| node.id())
            .collect();
        let targets = analysis.callee_targets_of(file, call_of(project, file, "work"));

        found = (
            targets
                .known
                .iter()
                .map(|known| {
                    bodies
                        .iter()
                        .position(|body| *body == known.node)
                        .expect("known body")
                })
                .collect(),
            targets.open,
        );
    });

    found
}

// G28: a direct eval can assign any mutable binding in scope, a sloppy one can declare a `var`
// that shadows an outer name, and `with` resolves every name against its object first, so none of
// them leaves a callable binding closed.
#[test]
fn direct_eval_and_with_open_callable_bindings() {
    for (relative, source, known, open) in [
        (
            "index.ts",
            "function work(){return 1} export function load(code: string){eval(code);} export function run(){work();}",
            vec![0],
            true,
        ),
        (
            "index.ts",
            "const work = function(){return 1}; export function load(code: string){eval(code);} export function run(){work();}",
            vec![0],
            false,
        ),
        (
            "index.ts",
            "export function run(){ function work(){return 1} work(); } export function load(code: string){eval(code);}",
            vec![0],
            false,
        ),
        (
            "index.js",
            "const work = function(){return 1}; function run(code){ eval(code); work(); }",
            vec![0],
            true,
        ),
        (
            "index.js",
            "const work = function(){return 1}; function run(o){ with (o) { work(); } }",
            vec![0],
            true,
        ),
        (
            "index.js",
            "const work = function(){return 1}; function run(){ work(); }",
            vec![0],
            false,
        ),
    ] {
        assert_eq!(
            work_targets_of(relative, source),
            (known, open),
            "{relative}: {source}"
        );
    }
}

#[test]
fn duplicate_function_declarations_target_the_runtime_winner() {
    for (relative, source, known, open) in [
        (
            "index.js",
            "function work(){return 1} function work(){return 2} function run(){work();}",
            vec![1],
            false,
        ),
        (
            "index.js",
            "function work(){return 1} function work(){return 2} export function run(){work();}",
            vec![1],
            false,
        ),
        (
            "index.ts",
            "function work(): number; function work(): number { return 1; } function run(){work();}",
            vec![0],
            false,
        ),
        (
            "index.js",
            "function work(){return 1} var work = function(){return 2}; function run(){work();}",
            vec![0, 1],
            true,
        ),
        (
            "index.js",
            "function work(){return 1} function work(){return 2} work = null; function run(){work();}",
            vec![1],
            true,
        ),
        (
            "index.js",
            "function work(){return 1} { function work(){return 2} } function run(){work();}",
            vec![0, 1],
            true,
        ),
    ] {
        assert_eq!(
            work_targets_of(relative, source),
            (known, open),
            "{source}"
        );
    }
}

fn reference_declaration_within(
    project: &Project<'_>,
    file: FileId,
    start: u32,
    end: u32,
) -> Option<oxc_semantic::NodeId> {
    let mut best: Option<(oxc_span::Span, oxc_semantic::NodeId)> = None;

    for node in project.file(file).semantic.nodes().iter() {
        let kind = node.kind();

        if !olint::declarations::is_declaration_kind(&kind) {
            continue;
        }

        let span = oxc_span::GetSpan::span(&kind);

        if span.start < start || span.end > end {
            continue;
        }

        let better = match best {
            None => true,
            Some((current, _)) => {
                span.start < current.start
                    || (span.start == current.start && span.size() > current.size())
            }
        };

        if better {
            best = Some((span, node.id()));
        }
    }

    best.map(|(_, node)| node)
}

fn assert_span_index_matches_reference(project: &Project<'_>) -> usize {
    let declarations = Declarations::new(project);
    let mut compared = 0;

    for source in &project.files {
        let length = source.text.len() as u32;
        let spans: Vec<_> = source
            .semantic
            .nodes()
            .iter()
            .map(|node| oxc_span::GetSpan::span(&node.kind()))
            .collect();

        for span in spans {
            for (start, end) in [
                (span.start, span.end),
                (span.start.saturating_sub(1), (span.end + 1).min(length)),
                ((span.start + 1).min(span.end), span.end),
                (span.start, span.start),
                (0, length),
            ] {
                assert_eq!(
                    declarations.declaration_within(project, source.id, start, end),
                    reference_declaration_within(project, source.id, start, end),
                    "{} {start}..{end}",
                    source.relative
                );

                compared += 1;
            }
        }
    }

    compared
}

#[test]
fn declaration_span_index_matches_the_reference_scan() {
    for fixture in ["model", "tags"] {
        let allocator = oxc_allocator::Allocator::default();
        let project = Project::load(
            &allocator,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures")
                .join(fixture)
                .join("tsconfig.json"),
        )
        .expect("fixture loads");

        assert!(assert_span_index_matches_reference(&project) > 1000);
    }

    let text = "\u{feff}// é ☃ 𝒳\r\nexport const café = (xs: number[]) => xs.length;\r\nexport class Überall<T> {\r\n\t#hidden = 1;\r\n\tstatic ok(): void {}\r\n\tget ünïcode() { return \"𝒳\"; }\r\n}\r\nfunction ƒ(a: string, ...rest: string[]): void; function ƒ(a: string) { const { b = \"é\" } = { b: a }; return b; }\r\nenum Ω { A = 1, B }\r\ninterface Ψ { x: number }\r\ntype Φ = Ψ;\r\nexport default { key: () => \"☃\", [\"𝒳\"]: 1 };\r\n";

    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", text)],
        |project, _| {
            assert!(assert_span_index_matches_reference(project) > 100);
        },
    );
}

fn implementation_of_reference(files: &[(&str, &str)], name: &str) -> Option<(String, u32)> {
    let mut found = None;

    run_in_project(files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");

        found = declaration_of_reference(project, &declarations, index, name)
            .and_then(|declaration| declarations.function_of(declaration))
            .map(|(file, function)| {
                let start = project
                    .file(file)
                    .semantic
                    .nodes()
                    .kind(function.node_id())
                    .span()
                    .start;

                (
                    project.file(file).relative.clone(),
                    project.line_of(file, start),
                )
            });
    });

    found
}

fn package_files<'f>(
    manifest: &'f str,
    files: &[(&'f str, &'f str)],
    consumer: &'f str,
) -> Vec<(&'f str, &'f str)> {
    let mut all = vec![
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" } }"#,
        ),
        ("index.ts", consumer),
        ("node_modules/pkg/package.json", manifest),
        (
            "node_modules/pkg/index.d.ts",
            "export declare function run(xs: number[]): number;\nexport interface Box { items: number[] }\ndeclare const fallback: (xs: number[]) => number;\nexport default fallback;",
        ),
    ];

    all.extend_from_slice(files);

    all
}

const COMMONJS_MANIFEST: &str = r#"{ "name": "pkg", "main": "index.js", "types": "index.d.ts" }"#;

type ExportCase<'c> = (&'c str, &'c str, &'c str, Option<(&'c str, u32)>);

#[test]
fn commonjs_export_forms_supply_package_implementations() {
    let named = "import { run } from \"pkg\";\nrun([1]);";
    let default = "import run from \"pkg\";\nrun([1]);";
    let cases: [ExportCase<'_>; 10] = [
        (
            "exports property",
            named,
            "exports.run = function (xs) { return xs.length; };",
            Some(("node_modules/pkg/index.js", 1)),
        ),
        (
            "module.exports property",
            named,
            "\nmodule.exports.run = (xs) => xs.length;",
            Some(("node_modules/pkg/index.js", 2)),
        ),
        (
            "compiled assignment after a void initializer",
            named,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.run = void 0;\nfunction run(xs) { return xs.length; }\nexports.run = run;",
            Some(("node_modules/pkg/index.js", 4)),
        ),
        (
            "compiled getter reexport",
            named,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst impl_1 = require(\"./impl\");\nObject.defineProperty(exports, \"run\", { enumerable: true, get: function () { return impl_1.run; } });",
            Some(("node_modules/pkg/impl.js", 1)),
        ),
        (
            "object literal shorthand",
            named,
            "function run(xs) { return xs.length; }\nmodule.exports = { run };",
            Some(("node_modules/pkg/index.js", 1)),
        ),
        (
            "object literal method",
            named,
            "module.exports = {\n\trun(xs) { return xs.length; },\n};",
            Some(("node_modules/pkg/index.js", 2)),
        ),
        (
            "replaced function as the default",
            default,
            "\n\nmodule.exports = function run(xs) { return xs.length; };",
            Some(("node_modules/pkg/index.js", 3)),
        ),
        (
            "required reexport",
            named,
            "module.exports = require(\"./impl\");",
            Some(("node_modules/pkg/impl.js", 1)),
        ),
        (
            "compiled default export",
            default,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.default = function run(xs) { return xs.length; };",
            Some(("node_modules/pkg/index.js", 3)),
        ),
        (
            "destructured require",
            named,
            "const { work: run } = require(\"./impl\");\nexports.run = run;",
            Some(("node_modules/pkg/impl.js", 2)),
        ),
    ];

    for (label, consumer, source, expected) in cases {
        let files = package_files(
            COMMONJS_MANIFEST,
            &[
                ("node_modules/pkg/index.js", source),
                (
                    "node_modules/pkg/impl.js",
                    "exports.run = function (xs) { return xs.length; };\nexports.work = function (xs) { return xs.length; };",
                ),
            ],
            consumer,
        );
        let found = implementation_of_reference(&files, "run");

        assert_eq!(
            found.as_ref().map(|(file, line)| (file.as_str(), *line)),
            expected,
            "{label}"
        );
    }
}

#[test]
fn commonjs_writes_beyond_recognized_statements_leave_exports_open() {
    let named = "import { run } from \"pkg\";\nrun([1]);";
    let cases = [
        (
            "escaping exports object",
            "exports.run = (xs) => xs.length;\nfunction patch(target) { target.run = () => 0; }\npatch(exports);",
        ),
        (
            "nested write",
            "exports.run = (xs) => xs.length;\nfunction later() { exports.run = () => 0; }",
        ),
        (
            "conditional replacement",
            "exports.run = (xs) => xs.length;\nif (Math.random() > 0.5) module.exports = {};",
        ),
        (
            "write to the replaced object through the stale alias",
            "module.exports = { run: (xs) => xs.length };\nexports.run = () => 0;",
        ),
        (
            "top-level this write",
            "exports.run = (xs) => xs.length;\nthis.run = () => 0;",
        ),
        (
            "computed export key",
            "const key = \"run\";\nexports.run = (xs) => xs.length;\nexports[key] = () => 0;",
        ),
        (
            "aliased module.exports",
            "const api = module.exports;\nexports.run = (xs) => xs.length;\napi.run = () => 0;",
        ),
        (
            "deleted export",
            "exports.run = (xs) => xs.length;\ndelete exports.run;",
        ),
        (
            "spread after the property",
            "const other = { run: () => 0 };\nmodule.exports = { run: (xs) => xs.length, ...other };",
        ),
    ];

    for (label, source) in cases {
        let files = package_files(
            COMMONJS_MANIFEST,
            &[("node_modules/pkg/index.js", source)],
            named,
        );

        assert_eq!(implementation_of_reference(&files, "run"), None, "{label}");
    }

    let control = package_files(
        COMMONJS_MANIFEST,
        &[(
            "node_modules/pkg/index.js",
            "exports.run = (xs) => exports.size(xs);\nexports.size = (xs) => xs.length;\nif (typeof module === \"object\" && module.id) exports.size(module.exports.run);",
        )],
        named,
    );

    assert_eq!(
        implementation_of_reference(&control, "run"),
        Some(("node_modules/pkg/index.js".to_string(), 1)),
        "reads keep exports closed"
    );
}

#[test]
fn reassigned_require_bindings_are_not_followed() {
    let files = package_files(
        COMMONJS_MANIFEST,
        &[
            (
                "node_modules/pkg/index.js",
                "let impl = require(\"./impl\");\nimpl = { run: () => 0 };\nexports.run = impl.run;",
            ),
            (
                "node_modules/pkg/impl.js",
                "exports.run = function (xs) { return xs.length; };",
            ),
        ],
        "import { run } from \"pkg\";\nrun([1]);",
    );

    assert_eq!(implementation_of_reference(&files, "run"), None);
}

#[test]
fn declarations_keep_types_beside_package_implementations() {
    let files = package_files(
        COMMONJS_MANIFEST,
        &[(
            "node_modules/pkg/index.js",
            "exports.run = function (xs) { return xs.length; };",
        )],
        "import { run, type Box } from \"pkg\";\nimport fallback from \"pkg\";\nexport function go(box: Box) { return run(box.items) + fallback(box.items); }",
    );

    assert_eq!(
        implementation_of_reference(&files, "run"),
        Some(("node_modules/pkg/index.js".to_string(), 1))
    );
    assert_eq!(implementation_of_reference(&files, "fallback"), None);
    assert_box_is_declared(
        "exports.run = function (xs) { return xs.length; };",
        "import { run, type Box } from \"pkg\";\nexport function go(box: Box) { return run(box.items); }",
    );
}

fn assert_box_is_declared(implementation: &str, consumer: &str) {
    let files = package_files(
        COMMONJS_MANIFEST,
        &[("node_modules/pkg/index.js", implementation)],
        consumer,
    );

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");
        let declared = file_of(project, root, "node_modules/pkg/index.d.ts");
        let box_type = declaration_of_reference(project, &declarations, index, "Box");

        assert!(
            matches!(box_type, Some(Declaration::Interface { file, .. }) if file == declared),
            "{consumer}: {box_type:?}"
        );
    });
}

#[test]
fn type_names_resolve_to_declarations_in_both_import_forms() {
    assert_box_is_declared(
        "exports.run = function (xs) { return xs.length; };\nexports.Box = class Box {};",
        "import { run } from \"pkg\";\nimport type { Box } from \"pkg\";\nexport function go(box: Box) { return run(box.items); }",
    );
    assert_box_is_declared(
        "exports.run = function (xs) { return xs.length; };",
        "import { run, Box } from \"pkg\";\nexport function go(box: Box) { return run(box.items); }",
    );
}

#[test]
fn a_typescript_package_body_is_not_substituted_for_a_missing_runtime_export() {
    let files = [
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" } }"#,
        ),
        ("index.ts", "import { run } from \"pkg\";\nrun([1]);"),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "main": "dist/index.js", "types": "src/index.ts" }"#,
        ),
        (
            "node_modules/pkg/src/index.ts",
            "export function run(xs: number[]) { return xs.length; }",
        ),
        (
            "node_modules/pkg/dist/index.js",
            "exports.other = function () { return 0; };",
        ),
    ];

    assert_eq!(implementation_of_reference(&files, "run"), None);
}

#[test]
fn package_implementation_resolution_is_counted() {
    let files = package_files(
        COMMONJS_MANIFEST,
        &[(
            "node_modules/pkg/index.js",
            "exports.run = function (xs) { return xs.length; };\nexports.size = (xs) => xs.length;",
        )],
        "import { run } from \"pkg\";\nrun([1]);\nrun([2]);",
    );

    run_in_project(&files, |project, root| {
        let index = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(project, SYNTACTIC);

        for call in calls_in(project, index) {
            analysis.callee_targets_of(index, call);
        }

        let cold = analysis.declarations.resolution_stats();

        assert_eq!(cold.implementation_visits, 8, "{cold:?}");

        for call in calls_in(project, index) {
            analysis.callee_targets_of(index, call);
        }

        assert_eq!(analysis.declarations.resolution_stats(), cold);
    });
}

#[test]
fn package_implementations_are_module_scoped() {
    let files = package_files(
        COMMONJS_MANIFEST,
        &[(
            "node_modules/pkg/index.js",
            "function helper(xs) { return xs.length; }\nexports.run = helper;",
        )],
        "import { run } from \"pkg\";\nrun([1]);\nhelper([1]);",
    );

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");

        assert!(declaration_of_reference(project, &declarations, index, "run").is_some());
        assert!(declaration_of_reference(project, &declarations, index, "helper").is_none());
    });
}

#[test]
fn writes_into_a_commonjs_module_object_reopen_its_exports() {
    let implementation = "exports.run = function (xs) { return xs.length; };";
    let cases = [
        (
            "import-equals member write",
            "import pkg = require(\"pkg\");\nimport { run } from \"pkg\";\npkg.run = () => 0;\nrun([1]);",
            implementation,
            None,
        ),
        (
            "default import passed away",
            "import pkg from \"pkg\";\nimport { run } from \"pkg\";\nObject.assign(pkg, {});\nrun([1]);",
            implementation,
            None,
        ),
        (
            "require call member write inside a package",
            "import { run } from \"pkg\";\nrun([1]);",
            "require(\"./impl\").run = () => 0;\nexports.run = require(\"./impl\").run;",
            None,
        ),
        (
            "forwarded module written through the forwarding module",
            "import pkg = require(\"pkg\");\nimport { run } from \"pkg\";\npkg.run = () => 0;\nrun([1]);",
            "module.exports = require(\"./impl\");",
            None,
        ),
        (
            "second require call escapes",
            "import { run } from \"pkg\";\nrun([1]);",
            "const other = require(\"./other\");\nrequire(\"./impl\").run = () => 0;\nexports.run = require(\"./impl\").run;",
            None,
        ),
        (
            "forwarded module imported directly",
            "import pkg = require(\"pkg\");\nimport { run } from \"pkg/impl\";\npkg.run = () => 0;\nrun([1]);",
            "module.exports = require(\"./impl\");",
            None,
        ),
        (
            "reads only",
            "import pkg = require(\"pkg\");\nimport { run } from \"pkg\";\npkg.run([1]);\nrun([1]);",
            "module.exports = require(\"./impl\");",
            Some(("node_modules/pkg/impl.js".to_string(), 1)),
        ),
    ];

    for (label, consumer, index, expected) in cases {
        let files = package_files(
            COMMONJS_MANIFEST,
            &[
                ("node_modules/pkg/index.js", index),
                ("node_modules/pkg/impl.js", implementation),
            ],
            consumer,
        );
        let mut files = files;

        files.push(("node_modules/pkg/other.js", "exports.other = 1;"));

        assert_eq!(
            implementation_of_reference(&files, "run"),
            expected,
            "{label}"
        );
    }
}

use olint::analysis::{Analysis, Stats};
use olint::declarations::{Declaration, Declarations, FunctionNode};
use olint::project::{FileId, Project};
use oxc_ast::ast::IdentifierReference;
use oxc_ast::AstKind;

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
fn package_declarations_have_no_function_and_javascript_packages_are_external() {
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

        assert!(matches!(run, Some(Declaration::Function { .. })));
        assert!(declarations.function_of(run.expect("declared")).is_none());
        assert!(matches!(
            declaration_of_reference(project, &declarations, index, "plain"),
            Some(Declaration::External)
        ));
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

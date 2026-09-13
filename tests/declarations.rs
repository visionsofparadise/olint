use olint::analysis::{Analysis, Stats};
use olint::declarations::{Declaration, Declarations, FunctionNode};
use olint::project::{FileId, Project};
use oxc_ast::ast::{Class, ClassElement, IdentifierReference, PropertyKey};
use oxc_ast::AstKind;

mod support;

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

fn first_class_of<'a>(project: &Project<'a>, file: FileId) -> &'a Class<'a> {
    first_node_of(project, file, |kind| match kind {
        AstKind::Class(class) => Some(class),
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
fn member_of_finds_a_private_name() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "box.ts",
            "export class Box {\n\tsecret() {}\n\t#secret() {}\n\topen() { this.#secret(); }\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let file = file_of(project, root, "box.ts");
        let class = first_class_of(project, file);

        match declarations.member_of(project, file, class, "#secret") {
            Some(Declaration::Member {
                element: ClassElement::MethodDefinition(method),
                ..
            }) => assert!(matches!(method.key, PropertyKey::PrivateIdentifier(_))),
            other => panic!("expected the private method, found {other:?}"),
        }
    });
}

#[test]
fn is_written_sees_nested_reassignment_and_member_writes() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "state.ts",
            "let count = 0;\nconst fixed = 1;\nexport function bump() {\n\tconst inner = () => { count = count + fixed; };\n\tinner();\n}\nexport class Counter {\n\tsize = 0;\n\tlimit = 1;\n\tgrow() { this.size += this.limit; }\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let file = file_of(project, root, "state.ts");
        let class = first_class_of(project, file);
        let written = |name: &str| {
            let reference = reference_of(project, file, name);
            let binding = declarations
                .binding_of_reference(project, file, reference)
                .expect("a binding");

            declarations.is_written(project, binding)
        };
        let member_written = |name: &str| {
            let binding = declarations
                .member_binding(project, file, class, name)
                .expect("a member");

            declarations.is_written(project, binding)
        };

        assert!(written("count"));
        assert!(!written("fixed"));
        assert!(member_written("size"));
        assert!(!member_written("limit"));
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
            Some("signature")
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

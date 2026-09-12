use olint::analysis::Stats;
use olint::declarations::{Declaration, Declarations, FunctionNode};
use olint::project::{FileId, Project};
use oxc_ast::ast::{Class, ClassElement, IdentifierReference, PropertyKey};
use oxc_ast::AstKind;

mod support;

use support::{file_of, first_node_of, run_in_project, TYPED_PACKAGE};

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
            function_name_of(declarations.of_export(project, a, "fromB")),
            "fromB"
        );
        assert!(declarations.of_export(project, a, "missing").is_none());
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
                    function_name_of(declarations.of_export(project, file, "run")),
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
fn node_modules_import_is_external() {
    let files = [
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", "import { run } from \"pkg\";\nrun();"),
        ][..],
        &TYPED_PACKAGE,
    ]
    .concat();

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let index = file_of(project, root, "index.ts");

        assert!(matches!(
            declaration_of_reference(project, &declarations, index, "run"),
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
            function_name_of(declarations.of_export(project, index, "value")),
            "named"
        );
        assert_eq!(
            function_name_of(declarations.of_export(project, index, "default")),
            ""
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

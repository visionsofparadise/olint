use olint::project::{canonical_path, Resolved};
use olint::tsconfig::select_files;
use oxc_ast::AstKind;

mod support;

use support::{file_of, first_node, project_of, with_project, TYPED_PACKAGE};

fn selected(files: &[(&str, &str)]) -> Vec<String> {
    let directory = project_of(files);
    let root = canonical_path(directory.path()).expect("root");
    let selection = select_files(&root.join("tsconfig.json")).expect("selection");

    selection
        .files
        .iter()
        .map(|file| {
            file.strip_prefix(&root)
                .expect("under root")
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect()
}

#[test]
fn select_files_merges_the_extends_chain() {
    let files = selected(&[
        ("configs/base.json", r#"{ "include": ["../lib"] }"#),
        ("configs/middle.json", r#"{ "extends": "./base" }"#),
        ("tsconfig.json", r#"{ "extends": "./configs/middle.json" }"#),
        ("lib/a.ts", "export const a = 1;"),
        ("src/b.ts", "export const b = 1;"),
    ]);

    assert_eq!(files, vec!["lib/a.ts"]);
}

#[test]
fn select_files_prunes_an_excluded_directory() {
    let files = selected(&[
        ("tsconfig.json", r#"{ "exclude": ["src/generated"] }"#),
        ("src/a.ts", "export const a = 1;"),
        ("src/generated/b.ts", "export const b = 1;"),
        ("src/generated/deep/c.ts", "export const c = 1;"),
        ("node_modules/pkg/index.ts", "export const d = 1;"),
    ]);

    assert_eq!(files, vec!["src/a.ts"]);
}

#[test]
fn select_files_joins_files_and_include() {
    let files = selected(&[
        (
            "tsconfig.json",
            r#"{ "files": ["tools/run.ts"], "include": ["src/**/*.ts"] }"#,
        ),
        ("tools/run.ts", "export const run = 1;"),
        ("tools/other.ts", "export const other = 1;"),
        ("src/a.ts", "export const a = 1;"),
        ("src/b.tsx", "export const b = 1;"),
    ]);

    assert_eq!(files, vec!["src/a.ts", "tools/run.ts"]);
}

#[test]
fn load_follows_imports_outside_include() {
    let files = [
        ("tsconfig.json", r#"{ "include": ["src"] }"#),
        (
            "src/index.ts",
            "import { helper } from \"../lib/helper.js\";\nexport const run = helper;",
        ),
        (
            "lib/helper.ts",
            "import { deep } from \"./deep\";\nexport const helper = deep;",
        ),
        ("lib/deep.ts", "export const deep = 1;"),
    ];

    with_project(&files, |project, _| {
        let mut relatives: Vec<&str> = project
            .files
            .iter()
            .map(|file| file.relative.as_str())
            .collect();

        relatives.sort_unstable();

        assert_eq!(
            relatives,
            vec!["lib/deep.ts", "lib/helper.ts", "src/index.ts"]
        );
    });
}

#[test]
fn resolve_maps_a_js_specifier_to_the_ts_file() {
    let files = [
        ("tsconfig.json", "{}"),
        ("src/index.ts", "export * from \"./other.js\";"),
        ("src/other.ts", "export const other = 1;"),
    ];

    with_project(&files, |project, root| {
        let index = file_of(project, root, "src/index.ts");
        let other = file_of(project, root, "src/other.ts");

        assert_eq!(project.resolve(index, "./other.js"), Resolved::File(other));
    });
}

#[test]
fn resolve_reports_node_modules_as_external() {
    let files = [
        &[
            ("tsconfig.json", r#"{ "include": ["src"] }"#),
            ("src/index.ts", "import { run } from \"pkg\";\nrun();"),
        ][..],
        &TYPED_PACKAGE,
    ]
    .concat();

    with_project(&files, |project, root| {
        let index = file_of(project, root, "src/index.ts");

        assert_eq!(project.files.len(), 1);
        assert!(matches!(
            project.resolve(index, "pkg"),
            Resolved::External(_)
        ));
    });
}

#[test]
fn line_of_starts_a_line_after_its_break() {
    let files = [
        ("tsconfig.json", "{}"),
        ("a.ts", "const a = 1;\nconst b = 2;\n"),
    ];

    with_project(&files, |project, root| {
        let file = file_of(project, root, "a.ts");
        let second = first_node(project, file, |kind| match kind {
            AstKind::VariableDeclarator(declarator) if declarator.span.start > 12 => {
                Some(declarator.span)
            }
            _ => None,
        });

        assert_eq!(project.line_of(file, 12), 1);
        assert_eq!(project.line_of(file, 13), 2);
        assert_eq!(project.site_of(file, second).line, 2);
    });
}

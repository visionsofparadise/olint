use olint::project::{canonical_path_of, Resolved};
use olint::tsconfig::select_files;
use oxc_ast::AstKind;

mod support;

use support::{file_of, first_node_of, project_of, run_in_project, TYPED_PACKAGE};

fn selected_files_of(files: &[(&str, &str)]) -> Vec<String> {
    let directory = project_of(files);
    let root = canonical_path_of(directory.path()).expect("root");
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
    let files = selected_files_of(&[
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
    let files = selected_files_of(&[
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
    let files = selected_files_of(&[
        (
            "tsconfig.json",
            r#"{ "files": ["tools/run.ts"], "include": ["src/**/*.ts"] }"#,
        ),
        ("tools/run.ts", "export const run = 1;"),
        ("tools/other.ts", "export const other = 1;"),
        ("src/a.ts", "export const a = 1;"),
        ("src/b.tsx", "export const b = 1;"),
    ]);

    assert_eq!(files, vec!["tools/run.ts", "src/a.ts"]);
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

    run_in_project(&files, |project, _| {
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

    run_in_project(&files, |project, root| {
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

    run_in_project(&files, |project, root| {
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

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "a.ts");
        let second = first_node_of(project, file, |kind| match kind {
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

#[test]
fn load_stores_files_in_program_order() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "b.ts",
            "import { z } from \"./z\";
export const b = z;",
        ),
        ("B2.ts", "export const B2 = 1;"),
        ("sub/a.ts", "export const a = 1;"),
        (
            "z.ts",
            "import { a } from \"./sub/a\";
export const z = a;",
        ),
    ];

    run_in_project(&files, |project, _| {
        let relatives: Vec<&str> = project
            .files
            .iter()
            .map(|file| file.relative.as_str())
            .collect();

        assert_eq!(relatives, vec!["B2.ts", "sub/a.ts", "z.ts", "b.ts"]);
    });
}

#[test]
fn load_follows_javascript_imports_only_with_allow_js() {
    let relatives_of = |options: &str| {
        let tsconfig =
            format!(r#"{{ "compilerOptions": {options}, "include": ["src/index.ts"] }}"#);
        let files = [
            ("tsconfig.json", tsconfig.as_str()),
            (
                "src/index.ts",
                "import { legacy } from \"./legacy.js\";
export const run = legacy;",
            ),
            ("src/legacy.js", "export function legacy() {}"),
        ];
        let mut relatives = Vec::new();

        run_in_project(&files, |project, _| {
            relatives = project
                .files
                .iter()
                .map(|file| file.relative.clone())
                .collect();
        });

        relatives
    };

    assert_eq!(relatives_of("{}"), vec!["src/index.ts"]);
    assert_eq!(
        relatives_of(r#"{ "allowJs": true }"#),
        vec!["src/legacy.js", "src/index.ts"]
    );
}

#[test]
fn select_files_follows_typescript_wildcard_rules() {
    let files = selected_files_of(&[
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "allowJs": true }, "include": ["src/**/*", ".hidden/*.ts", "node_modules/pkg/*.ts"] }"#,
        ),
        ("src/a.ts", "export const x = 1;"),
        ("src/a.js", "export const x = 1;"),
        ("src/b.js", "export const x = 1;"),
        ("src/b.min.js", "export const x = 1;"),
        ("src/c.min.js", "export const x = 1;"),
        ("src/.dot/d.ts", "export const x = 1;"),
        ("src/e.tsx", "export const x = 1;"),
        ("src/e.ts", "export const x = 1;"),
        (".hidden/h.ts", "export const x = 1;"),
        ("node_modules/pkg/p.ts", "export const x = 1;"),
    ]);

    assert_eq!(
        files,
        vec![
            "src/a.ts",
            "src/b.js",
            "src/e.ts",
            ".hidden/h.ts",
            "node_modules/pkg/p.ts"
        ]
    );
}

#[test]
fn extends_with_a_dotted_name_resolves_as_a_package() {
    let files = selected_files_of(&[
        ("tsconfig.json", r#"{ "extends": ".shared/base" }"#),
        (".shared/base.json", r#"{ "include": ["../lib"] }"#),
        (
            "node_modules/.shared/base.json",
            r#"{ "include": ["../../src"] }"#,
        ),
        ("lib/a.ts", "export const a = 1;"),
        ("src/b.ts", "export const b = 1;"),
    ]);

    assert_eq!(files, vec!["src/b.ts"]);
}

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
fn resolve_loads_a_package_declaration_file_outside_the_project() {
    let files = [
        &[
            ("tsconfig.json", r#"{ "include": ["src", "types"] }"#),
            (
                "src/index.ts",
                "import { run } from \"pkg\";\nimport { plain } from \"plain\";\nrun(plain);",
            ),
            ("types/global.d.ts", "declare const unused: number;"),
            (
                "node_modules/plain/package.json",
                r#"{ "name": "plain", "main": "index.js" }"#,
            ),
            ("node_modules/plain/index.js", "exports.plain = 1;"),
        ][..],
        &TYPED_PACKAGE,
    ]
    .concat();

    run_in_project(&files, |project, root| {
        let index = file_of(project, root, "src/index.ts");
        let Resolved::File(package) = project.resolve(index, "pkg") else {
            panic!("the package's declaration file is loaded");
        };

        let global = file_of(project, root, "types/global.d.ts");

        assert_eq!(project.files.len(), 3);
        assert!(!project.is_project_file(global));
        assert!(project.file(package).external_library);
        assert!(!project.is_project_file(package));
        assert!(matches!(
            project.resolve(index, "plain"),
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

#[cfg(unix)]
fn link_directory(target: &std::path::Path, link: &std::path::Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, link)
}

#[cfg(windows)]
fn link_directory(target: &std::path::Path, link: &std::path::Path) -> std::io::Result<()> {
    std::os::windows::fs::symlink_dir(target, link)
}

#[test]
fn load_follows_imports_outside_the_tsconfig_directory() {
    let directory = project_of(&[
        ("app/tsconfig.json", r#"{ "include": ["src"] }"#),
        (
            "app/src/index.ts",
            "import { shared } from \"shared\";\nimport { rel } from \"../../shared/src/rel\";\nexport const run = () => shared([1]) + rel;",
        ),
        (
            "shared/package.json",
            r#"{ "name": "shared", "exports": { ".": "./src/index.ts" } }"#,
        ),
        (
            "shared/src/index.ts",
            "export function shared(xs: number[]) { return xs.length; }",
        ),
        ("shared/src/rel.ts", "export const rel = 1;"),
    ]);
    let root = canonical_path_of(directory.path()).expect("root");

    std::fs::create_dir_all(root.join("app/node_modules")).expect("node_modules");

    let linked =
        link_directory(&root.join("shared"), &root.join("app/node_modules/shared")).is_ok();
    let allocator = oxc_allocator::Allocator::default();
    let project = olint::project::Project::load(&allocator, &root.join("app/tsconfig.json"))
        .expect("project loads");
    let relatives: Vec<&str> = project
        .files
        .iter()
        .map(|file| file.relative.as_str())
        .collect();
    let index = file_of(&project, &root, "app/src/index.ts");
    let rel = file_of(&project, &root, "shared/src/rel.ts");

    assert!(project.is_project_file(rel));
    assert_eq!(
        project.resolve(index, "../../shared/src/rel"),
        Resolved::File(rel)
    );

    if linked {
        let shared = file_of(&project, &root, "shared/src/index.ts");

        assert_eq!(
            relatives,
            vec![
                "../shared/src/index.ts",
                "../shared/src/rel.ts",
                "src/index.ts"
            ]
        );
        assert_eq!(project.resolve(index, "shared"), Resolved::File(shared));
        assert!(!project.is_project_file(shared));
    } else {
        eprintln!("directory symlinks are unavailable here; the package import is not exercised");
        assert_eq!(relatives, vec!["../shared/src/rel.ts", "src/index.ts"]);
    }
}

fn linked_tree_of(
    files: &[(&str, &str)],
    links: &[(&str, &str)],
) -> (tempfile::TempDir, std::path::PathBuf, bool) {
    let directory = project_of(files);
    let root = canonical_path_of(directory.path()).expect("root");
    let linked = links.iter().all(|(link, target)| {
        let link = root.join(link);

        std::fs::create_dir_all(link.parent().expect("parent")).expect("link parent");

        link_directory(&root.join(target), &link).is_ok()
    });

    if !linked {
        eprintln!("directory symlinks are unavailable here; the linked tree is not exercised");
    }

    (directory, root, linked)
}

fn project_flags_of<'p>(project: &'p olint::project::Project<'_>) -> Vec<(&'p str, bool)> {
    project
        .files
        .iter()
        .map(|file| (file.relative.as_str(), project.is_project_file(file.id)))
        .collect()
}

fn loaded_files_of(tsconfig: &std::path::Path) -> Vec<(String, bool)> {
    let allocator = oxc_allocator::Allocator::default();
    let project = olint::project::Project::load(&allocator, tsconfig).expect("project loads");

    project_flags_of(&project)
        .into_iter()
        .map(|(relative, flag)| (relative.to_string(), flag))
        .collect()
}

#[test]
fn load_resets_a_package_file_reached_again_from_the_project() {
    let (_directory, root, linked) = linked_tree_of(
        &[
            (
                "tsconfig.json",
                r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["a.ts", "packages/lib/src/**/*"] }"#,
            ),
            (
                "a.ts",
                "import { lib } from \"lib\";\nexport const a = () => lib([1]);",
            ),
            (
                "packages/lib/package.json",
                r#"{ "name": "lib", "exports": { ".": "./src/index.ts" } }"#,
            ),
            (
                "packages/lib/src/index.ts",
                "export function lib(xs: number[]) { return xs.length; }",
            ),
        ],
        &[("node_modules/lib", "packages/lib")],
    );

    if linked {
        assert_eq!(
            loaded_files_of(&root.join("tsconfig.json")),
            vec![
                ("packages/lib/src/index.ts".to_string(), true),
                ("a.ts".to_string(), true)
            ]
        );
    }
}

#[test]
fn load_keeps_a_paths_mapping_out_of_the_external_libraries() {
    let (_directory, root, _) = linked_tree_of(
        &[
            (
                "app/tsconfig.json",
                r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler", "baseUrl": ".", "paths": { "shared": ["../shared/src/index.ts"] } }, "include": ["src"] }"#,
            ),
            (
                "app/src/index.ts",
                "import { shared } from \"shared\";\nexport const run = () => shared([1]);",
            ),
            (
                "shared/package.json",
                r#"{ "name": "shared", "exports": { ".": "./src/index.ts" } }"#,
            ),
            (
                "shared/src/index.ts",
                "export function shared(xs: number[]) { return xs.length; }",
            ),
        ],
        &[("app/node_modules/shared", "shared")],
    );

    assert_eq!(
        loaded_files_of(&root.join("app/tsconfig.json")),
        vec![
            ("../shared/src/index.ts".to_string(), true),
            ("src/index.ts".to_string(), true)
        ]
    );
}

#[test]
fn load_marks_typescript_under_node_modules_external() {
    let files = [
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["src"] }"#,
        ),
        (
            "src/index.ts",
            "import { run } from \"pkg\";\nimport { typed } from \"typed\";\nexport const go = () => run([1]) + typed();",
        ),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "exports": { ".": "./index.ts" } }"#,
        ),
        (
            "node_modules/pkg/index.ts",
            "import { helper } from \"./helper\";\nexport function run(xs: number[]) { return helper(xs); }",
        ),
        (
            "node_modules/pkg/helper.ts",
            "export function helper(xs: number[]) { return xs.length; }",
        ),
        (
            "node_modules/typed/package.json",
            r#"{ "name": "typed", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/typed/index.d.ts",
            "export declare function typed(): number;",
        ),
    ];

    run_in_project(&files, |project, root| {
        let index = file_of(project, root, "src/index.ts");
        let loaded = project_flags_of(project);

        assert_eq!(
            loaded,
            vec![
                ("node_modules/pkg/helper.ts", false),
                ("node_modules/pkg/index.ts", false),
                ("node_modules/typed/index.d.ts", false),
                ("src/index.ts", true)
            ]
        );
        assert!(matches!(project.resolve(index, "pkg"), Resolved::File(_)));
        assert!(matches!(project.resolve(index, "typed"), Resolved::File(_)));
    });
}

#[test]
fn resolve_prefers_a_package_typings_field_over_a_typescript_main() {
    let files = [
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["src"] }"#,
        ),
        (
            "src/index.ts",
            "import patch from \"patch\";\nexport const go = () => patch();",
        ),
        (
            "node_modules/patch/package.json",
            r#"{ "name": "patch", "main": "index.js", "types": "types.d.ts", "typings": "index.d.ts" }"#,
        ),
        (
            "node_modules/patch/types.d.ts",
            "export default function patch(): string;",
        ),
        ("node_modules/patch/index.js", "module.exports = () => 1;"),
        (
            "node_modules/patch/index.ts",
            "export default function patch(xs: number[] = []) { return xs.length; }",
        ),
        (
            "node_modules/patch/index.d.ts",
            "export default function patch(): number;",
        ),
    ];

    run_in_project(&files, |project, root| {
        let resolved = project.resolve(file_of(project, root, "src/index.ts"), "patch");
        let loaded: Vec<&str> = project
            .files
            .iter()
            .map(|file| file.relative.as_str())
            .collect();

        assert_eq!(
            loaded,
            vec!["node_modules/patch/index.d.ts", "src/index.ts"]
        );
        assert!(
            matches!(resolved, Resolved::File(id) if project.file(id).relative == "node_modules/patch/index.d.ts")
        );
    });
}

#[test]
fn load_keys_a_doubly_reachable_file_to_its_canonical_path() {
    let tree = [
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["src"] }"#,
        ),
        (
            "linked-first.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "files": ["src/linked/util.ts", "src/index.ts"] }"#,
        ),
        (
            "src/index.ts",
            "import { util } from \"../real/util\";\nexport const run = () => util([1]);",
        ),
        (
            "real/util.ts",
            "export function util(xs: number[]) { for (const x of xs) { x; } }",
        ),
    ];
    let (_directory, root, linked) = linked_tree_of(&tree, &[("src/linked", "real")]);

    if !linked {
        return;
    }

    for (tsconfig, order) in [
        (
            "tsconfig.json",
            vec!["real/util.ts", "src/index.ts", "src/linked/util.ts"],
        ),
        (
            "linked-first.json",
            vec!["src/linked/util.ts", "real/util.ts", "src/index.ts"],
        ),
    ] {
        let allocator = oxc_allocator::Allocator::default();
        let project =
            olint::project::Project::load(&allocator, &root.join(tsconfig)).expect("project loads");
        let id_of = |relative: &str| {
            project
                .files
                .iter()
                .find(|file| file.relative == relative)
                .map(|file| file.id)
                .expect("loaded")
        };
        let relatives: Vec<&str> = project
            .files
            .iter()
            .map(|file| file.relative.as_str())
            .collect();

        assert_eq!(relatives, order);
        assert_eq!(
            project.resolve(id_of("src/index.ts"), "../real/util"),
            Resolved::File(id_of("real/util.ts"))
        );
    }
}

#[test]
fn select_files_keeps_files_under_a_symlinked_directory() {
    let (_directory, root, linked) = linked_tree_of(
        &[
            ("tsconfig.json", r#"{ "include": ["src"] }"#),
            ("src/x.ts", "export const x = 1;"),
            ("elsewhere/y.ts", "export const y = 1;"),
        ],
        &[("src/linked", "elsewhere")],
    );
    let selection = select_files(&root.join("tsconfig.json")).expect("selection");
    let relatives: Vec<String> = selection
        .files
        .iter()
        .map(|file| {
            file.strip_prefix(&root)
                .expect("under root")
                .to_string_lossy()
                .replace('\\', "/")
        })
        .collect();

    if linked {
        assert_eq!(relatives, vec!["src/x.ts", "src/linked/y.ts"]);
    } else {
        assert_eq!(relatives, vec!["src/x.ts"]);
    }
}

#[test]
fn load_walks_a_declaration_file_with_its_importer_flag() {
    let files = [
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["src"] }"#,
        ),
        (
            "src/index.ts",
            "import type { Shape } from \"./shapes\";
export function area(s: Shape) { return s.w; }",
        ),
        (
            "src/shapes.d.ts",
            "export { helper } from \"../extra/helper\";
export interface Shape { w: number }",
        ),
        (
            "extra/helper.ts",
            "export function helper(xs: number[]) { return xs.map((x) => x); }",
        ),
        ("src/ambient.d.ts", "type AmbientList = string[];"),
    ];

    run_in_project(&files, |project, _| {
        let loaded = project_flags_of(project);

        assert_eq!(
            loaded,
            vec![
                ("src/ambient.d.ts", false),
                ("extra/helper.ts", true),
                ("src/shapes.d.ts", false),
                ("src/index.ts", true)
            ]
        );
    });
}

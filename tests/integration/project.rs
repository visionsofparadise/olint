use olint::paths::{canonical_path_of, forward_slashes_of};
use olint::project::{RequestKind, Resolved};
use olint::tsconfig::select_files;
use oxc_ast::AstKind;

use crate::support;

use support::{file_of, first_node_of, project_of, run_in_project, TYPED_PACKAGE};

#[test]
fn declaration_suffixes_do_not_hide_implementation_names() {
    run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("part.d.worker.ts", "export function implementation() {}"),
            ("types.d.ts", "export declare function typed(): void;"),
            ("types.d.mts", "export declare function esm(): void;"),
            ("types.d.cts", "export declare function common(): void;"),
        ],
        |project, root| {
            assert!(project.is_project_file(file_of(project, root, "part.d.worker.ts")));

            for path in ["types.d.ts", "types.d.mts", "types.d.cts"] {
                assert!(
                    !project.is_project_file(file_of(project, root, path)),
                    "{path}"
                );
            }
        },
    );
}

#[test]
fn literal_selection_preserves_jsonc_overrides_and_empty_references() {
    for config in [
        "\u{feff}/* config */{\"files\":[\"index.ts\",],\"references\":[],}",
        r#"{"extends":"./base.json","files":["index.ts"]}"#,
    ] {
        let selected = selected_files_of(&[
            ("tsconfig.json", config),
            ("base.json", r#"{"files":["missing.ts"]}"#),
            ("index.ts", "export const value=1"),
        ]);

        assert_eq!(selected, ["index.ts"]);
    }
}

#[test]
fn literal_roots_reject_unusable_suffixes_and_missing_references() {
    for config in [
        r#"{"files":["data.json"]}"#,
        r#"{"files":["source.js"]}"#,
        r#"{"files":["index.ts"],"references":[{"path":"./child"}]}"#,
    ] {
        let directory = project_of(&[
            ("tsconfig.json", config),
            ("index.ts", "export const value=1"),
            ("source.js", "export const value=1"),
            ("data.json", "{}"),
        ]);

        assert!(select_files(&directory.path().join("tsconfig.json")).is_err());
    }

    assert_eq!(
        selected_files_of(&[
            (
                "tsconfig.json",
                r#"{"compilerOptions":{"allowJs":true},"files":["source.js"]}"#
            ),
            ("source.js", "export const value=1")
        ]),
        ["source.js"]
    );
}

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
        let Resolved::File(plain) = project.implementation_of(index, "plain", RequestKind::Static)
        else {
            panic!("the package implementation is loaded");
        };

        assert_eq!(project.files.len(), 4);
        assert!(!project.is_project_file(global));
        assert!(project.file(package).external_library);
        assert!(!project.is_project_file(package));
        assert_eq!(project.file(plain).relative, "node_modules/plain/index.js");
        assert!(project.file(plain).implementation);
        assert!(!project.is_project_file(plain));
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

        let implementation = project.implementation_of(
            file_of(project, root, "src/index.ts"),
            "patch",
            RequestKind::Static,
        );

        assert_eq!(
            loaded,
            vec![
                "node_modules/patch/index.d.ts",
                "node_modules/patch/index.js",
                "src/index.ts"
            ]
        );
        assert!(
            matches!(resolved, Resolved::File(id) if project.file(id).relative == "node_modules/patch/index.d.ts")
        );
        assert!(
            matches!(implementation, Resolved::File(id) if project.file(id).relative == "node_modules/patch/index.js")
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

#[test]
fn check_js_is_inherited_and_explicit_allow_js_wins() {
    for (options, expected) in [
        (r#"{}"#, vec!["index.js"]),
        (r#"{"checkJs":false}"#, vec![]),
        (r#"{"allowJs":false}"#, vec![]),
        (r#"{"checkJs":false,"allowJs":true}"#, vec!["index.js"]),
    ] {
        let config = format!(r#"{{"extends":"./base.json","compilerOptions":{options}}}"#);

        assert_eq!(
            selected_files_of(&[
                ("tsconfig.json", &config),
                ("base.json", r#"{"compilerOptions":{"checkJs":true}}"#),
                ("index.js", "export function selected() {}"),
            ]),
            expected
        );
    }
}

#[test]
fn references_enumerate_roots_and_terminate_cycles() {
    run_in_project(
        &[
            (
                "tsconfig.json",
                r#"{"files":[],"references":[{"path":"./child"},{"path":"./child/tsconfig.json"}]}"#,
            ),
            (
                "child/tsconfig.json",
                r#"{"files":["index.js"],"compilerOptions":{"checkJs":true},"references":[{"path":".."}]}"#,
            ),
            ("child/index.js", "export function child() {}"),
        ],
        |project, _| {
            assert_eq!(project.files.len(), 1);
            assert_eq!(project.files[0].relative, "child/index.js");
            assert_eq!(project.files[0].owners.len(), 1);
        },
    );
}

#[test]
fn shared_sources_load_every_owner_dependency_and_require_agreement() {
    run_in_project(
        &[
            (
                "tsconfig.json",
                r#"{"files":[],"references":[{"path":"./left"},{"path":"./right"}]}"#,
            ),
            (
                "left/tsconfig.json",
                r#"{"files":["../shared.ts"],"compilerOptions":{"paths":{"@dep":["../a.ts"]}}}"#,
            ),
            (
                "right/tsconfig.json",
                r#"{"files":["../shared.ts"],"compilerOptions":{"paths":{"@dep":["../b.ts"]}}}"#,
            ),
            (
                "shared.ts",
                "import { other } from '@dep'; export function selected(){other()}",
            ),
            ("a.ts", "export function other() {}"),
            ("b.ts", "export function other() {}"),
        ],
        |project, _| {
            let file = file_of(project, &project.root, "shared.ts");

            assert_eq!(project.files.len(), 3);
            assert_eq!(project.file(file).owners.len(), 2);
            assert_eq!(project.resolve(file, "@dep"), Resolved::Unresolved);
        },
    );
}

#[test]
fn triple_paths_load_outside_roots_and_keep_declarations_distinct() {
    run_in_project(&[
        ("tsconfig.json", r#"{"files":["index.ts"]}"#),
        ("index.ts", "/// <reference path='./helper.ts' />\n/// <reference path='./types.d.ts' />\nexport function selected(){helper()}"),
        ("helper.ts", "/// <reference path='./index.ts' />\nfunction helper() {}"),
        ("types.d.ts", "declare const value: number;"),
    ], |project, _| {
        assert_eq!(project.files.len(), 3);
        assert!(project.is_project_file(file_of(project, &project.root, "helper.ts")));
        assert!(!project.is_project_file(file_of(project, &project.root, "types.d.ts")));
    });

    for reference in ["missing.ts", "data.json", "folder", "script.js", ".hidden"] {
        let source = format!("/// <reference path='./{reference}' />\nexport const value=1;");
        let directory = project_of(&[
            ("tsconfig.json", r#"{"files":["index.ts"]}"#),
            ("index.ts", &source),
            ("data.json", "{}"),
            ("script.js", "export const value=1;"),
            (".hidden.ts", "export const hidden=1;"),
            ("folder/child.ts", "export const child=1;"),
        ]);
        let allocator = oxc_allocator::Allocator::default();

        assert!(
            olint::project::Project::load(&allocator, &directory.path().join("tsconfig.json"))
                .is_err(),
            "{reference}"
        );
    }
}

#[test]
fn extensionless_references_use_typescript_extension_priority() {
    for (allow_js, expected) in [(false, "helper.ts"), (true, "helper.ts")] {
        let config =
            format!(r#"{{"files":["index.ts"],"compilerOptions":{{"allowJs":{allow_js}}}}}"#);

        run_in_project(
            &[
                ("tsconfig.json", &config),
                (
                    "index.ts",
                    "/// <reference path='./helper' />\nexport const value=1;",
                ),
                ("helper.ts", "const ts=1;"),
                ("helper.tsx", "const tsx=1;"),
                ("helper.d.ts", "declare const declaration: number;"),
                ("helper.js", "const js=1;"),
            ],
            |project, _| {
                assert_eq!(project.files.len(), 2);
                assert_eq!(project.files[0].relative, expected);
            },
        );
    }
}

#[test]
fn global_lookup_is_scoped_to_every_applicable_project() {
    run_in_project(
        &[
            (
                "tsconfig.json",
                r#"{"files":[],"references":[{"path":"./left"},{"path":"./right"}]}"#,
            ),
            ("left/tsconfig.json", r#"{"files":["index.ts"]}"#),
            ("right/tsconfig.json", r#"{"files":["global.ts"]}"#),
            ("left/index.ts", "export function selected(){other()}"),
            ("right/global.ts", "function other() {}"),
        ],
        |project, _| {
            let file = file_of(project, &project.root, "left/index.ts");
            let call = support::call_of(project, file, "other");
            let analysis = olint::analysis::Analysis::new(project, support::SYNTACTIC);
            let oxc_ast::ast::Expression::Identifier(reference) = &call.callee else {
                panic!("identifier")
            };

            assert!(analysis
                .declarations
                .of_reference(project, file, reference)
                .is_none());
        },
    );
}

const BUNDLER: &str = r#"{ "compilerOptions": { "module": "esnext", "moduleResolution": "bundler" }, "include": ["src"] }"#;

fn implementation_flags_of<'p>(
    project: &'p olint::project::Project<'_>,
) -> Vec<(&'p str, bool, bool)> {
    project
        .files
        .iter()
        .map(|file| {
            (
                file.relative.as_str(),
                file.implementation,
                project.is_project_file(file.id),
            )
        })
        .collect()
}

fn implementation_relative_of(
    project: &olint::project::Project<'_>,
    from: olint::project::FileId,
    specifier: &str,
    kind: RequestKind,
) -> Option<String> {
    match project.implementation_of(from, specifier, kind) {
        Resolved::File(id) => Some(project.file(id).relative.clone()),
        Resolved::External(path) => Some(olint::paths::relative_path_of(&project.root, &path)),
        Resolved::Unresolved => None,
    }
}

#[test]
fn load_walks_runtime_implementations_beside_declarations() {
    let files = [
        ("tsconfig.json", BUNDLER),
        (
            "src/index.ts",
            "import { run } from \"pkg\";\nexport const go = (xs: number[]) => run(xs);",
        ),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "type": "module", "main": "index.js", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/pkg/index.d.ts",
            "export declare function run(xs: number[]): number;",
        ),
        (
            "node_modules/pkg/index.js",
            "import { helper } from \"./helper.js\";\nexport function run(xs) { return helper(xs); }",
        ),
        (
            "node_modules/pkg/helper.d.ts",
            "export declare function helper(xs: number[]): number;",
        ),
        (
            "node_modules/pkg/helper.js",
            "export function helper(xs) { return xs.length; }",
        ),
    ];

    run_in_project(&files, |project, root| {
        let index = file_of(project, root, "src/index.ts");
        let declared = file_of(project, root, "node_modules/pkg/index.d.ts");
        let implementation = file_of(project, root, "node_modules/pkg/index.js");

        assert_eq!(
            implementation_flags_of(project),
            vec![
                ("node_modules/pkg/index.d.ts", false, false),
                ("node_modules/pkg/helper.js", true, false),
                ("node_modules/pkg/index.js", true, false),
                ("src/index.ts", false, true)
            ]
        );
        assert_eq!(project.resolve(index, "pkg"), Resolved::File(declared));
        assert_eq!(
            project.implementation_of(index, "pkg", RequestKind::Static),
            Resolved::File(implementation)
        );
        assert_eq!(project.counterpart_of(implementation), Some(declared));
        assert_eq!(project.counterpart_of(declared), None);
        assert!(project.file(implementation).external_library);
    });
}

#[test]
fn runtime_conditions_follow_the_request_and_the_emitted_module_format() {
    let package = [
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "types": "./index.d.ts", "exports": { ".": { "types": "./index.d.ts", "import": "./esm.mjs", "require": "./cjs.cjs" } } }"#,
        ),
        (
            "node_modules/pkg/index.d.ts",
            "export declare function run(): number;",
        ),
        (
            "node_modules/pkg/esm.mjs",
            "export function run() { return 1; }",
        ),
        ("node_modules/pkg/cjs.cjs", "exports.run = () => 2;"),
    ];
    let cases = [
        (
            "esnext",
            "src/index.ts",
            None,
            Some("node_modules/pkg/esm.mjs"),
        ),
        (
            "commonjs",
            "src/index.ts",
            None,
            Some("node_modules/pkg/cjs.cjs"),
        ),
        (
            "nodenext",
            "src/index.ts",
            Some(r#"{ "type": "module" }"#),
            Some("node_modules/pkg/esm.mjs"),
        ),
        (
            "nodenext",
            "src/index.ts",
            Some("{}"),
            Some("node_modules/pkg/cjs.cjs"),
        ),
        (
            "nodenext",
            "src/index.mts",
            Some("{}"),
            Some("node_modules/pkg/esm.mjs"),
        ),
        ("", "src/index.ts", None, None),
    ];

    for (module, entry, manifest, expected) in cases {
        let tsconfig = match module {
            "" => r#"{ "include": ["src"] }"#.to_string(),
            module => format!(
                r#"{{ "compilerOptions": {{ "module": "{module}" }}, "include": ["src"] }}"#
            ),
        };
        let mut files = vec![
            ("tsconfig.json", tsconfig.as_str()),
            (
                entry,
                "import { run } from \"pkg\";\nexport const go = () => run();",
            ),
        ];

        files.extend(package);

        if let Some(manifest) = manifest {
            files.push(("package.json", manifest));
        }

        run_in_project(&files, |project, root| {
            let index = file_of(project, root, entry);

            assert_eq!(
                implementation_relative_of(project, index, "pkg", RequestKind::Static).as_deref(),
                expected,
                "{module} {entry}"
            );
            assert_eq!(
                implementation_relative_of(project, index, "pkg", RequestKind::Require).as_deref(),
                Some("node_modules/pkg/cjs.cjs"),
                "{module} {entry}"
            );
        });
    }
}

#[test]
fn runtime_graph_follows_literal_requires_and_terminates_cycles() {
    let files = [
        ("tsconfig.json", BUNDLER),
        (
            "src/index.ts",
            "import { run } from \"pkg\";\nexport const go = () => run();",
        ),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "main": "a.js", "types": "index.d.ts" }"#,
        ),
        (
            "node_modules/pkg/index.d.ts",
            "export declare function run(): number;",
        ),
        (
            "node_modules/pkg/a.js",
            "const b = require(\"./b\");\nconst addon = require(\"./addon.node\");\nconst util = require(\"node:util\");\nconst name = \"./c\";\nconst dynamic = require(name);\nexports.run = () => b.run();",
        ),
        (
            "node_modules/pkg/b.js",
            "const a = require(`./a.js`);\nexports.run = () => a.run();",
        ),
        ("node_modules/pkg/c.js", "exports.run = () => 3;"),
        ("node_modules/pkg/addon.node", "binary"),
    ];

    run_in_project(&files, |project, root| {
        let a = file_of(project, root, "node_modules/pkg/a.js");

        assert_eq!(
            implementation_flags_of(project),
            vec![
                ("node_modules/pkg/index.d.ts", false, false),
                ("node_modules/pkg/b.js", true, false),
                ("node_modules/pkg/a.js", true, false),
                ("src/index.ts", false, true)
            ]
        );
        assert!(matches!(
            project.implementation_of(a, "./addon.node", RequestKind::Require),
            Resolved::External(_)
        ));
        assert_eq!(
            project.implementation_of(a, "node:util", RequestKind::Require),
            Resolved::Unresolved
        );
        assert!(project
            .file_by_path(&root.join("node_modules/pkg/c.js"))
            .is_none());
    });
}

#[test]
fn implementation_walk_is_bounded_and_counted() {
    let files = [
        ("tsconfig.json", BUNDLER),
        (
            "src/index.ts",
            "import { run } from \"pkg\";\nexport const go = () => run();",
        ),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "main": "a.js" }"#,
        ),
        (
            "node_modules/pkg/a.js",
            "exports.run = require(\"./b\").run;",
        ),
        (
            "node_modules/pkg/b.js",
            "exports.run = require(\"./c\").run;",
        ),
        (
            "node_modules/pkg/c.js",
            "exports.run = require(\"./d\").run;",
        ),
        ("node_modules/pkg/d.js", "exports.run = () => 4;"),
    ];
    let directory = project_of(&files);
    let tsconfig = directory.path().join("tsconfig.json");
    let counted = |limit: usize| {
        let allocator = oxc_allocator::Allocator::default();
        let project = olint::project::Project::load_with_limit(&allocator, &tsconfig, limit)
            .expect("project loads");

        (project.files.len(), project.implementation_stats())
    };

    assert_eq!(
        counted(2),
        (
            3,
            olint::project::ImplementationStats {
                resolutions: 3,
                files: 2,
                exhausted: true
            }
        )
    );
    assert_eq!(
        counted(olint::project::IMPLEMENTATION_FILE_LIMIT),
        (
            5,
            olint::project::ImplementationStats {
                resolutions: 4,
                files: 4,
                exhausted: false
            }
        )
    );
}

#[test]
fn loading_package_implementations_never_executes_them() {
    let directory = tempfile::tempdir().expect("temporary directory");
    let marker = directory.path().join("executed.txt");
    let marker_text = forward_slashes_of(&marker);
    let commonjs = format!(
        "require(\"fs\").writeFileSync(\"{marker_text}\", \"cjs\");\nexports.run = () => 1;"
    );
    let module = format!(
        "import {{ writeFileSync }} from \"node:fs\";\nwriteFileSync(\"{marker_text}\", \"esm\");\nthrow new Error(\"executed\");\nexport function other() {{ return 2; }}"
    );
    let files = [
        ("tsconfig.json", BUNDLER),
        (
            "src/index.ts",
            "import { run } from \"pkg\";\nimport { other } from \"other\";\nexport const go = () => run() + other();",
        ),
        (
            "node_modules/pkg/package.json",
            r#"{ "name": "pkg", "main": "index.js" }"#,
        ),
        ("node_modules/pkg/index.js", commonjs.as_str()),
        (
            "node_modules/other/package.json",
            r#"{ "name": "other", "type": "module", "exports": "./index.js" }"#,
        ),
        ("node_modules/other/index.js", module.as_str()),
    ];

    for (relative, text) in files {
        let path = directory.path().join(relative);

        std::fs::create_dir_all(path.parent().expect("parent")).expect("directories");
        std::fs::write(path, text).expect("file");
    }

    let allocator = oxc_allocator::Allocator::default();
    let project =
        olint::project::Project::load(&allocator, &directory.path().join("tsconfig.json"))
            .expect("project loads");
    let mut analysis = olint::analysis::Analysis::new(&project, support::SYNTACTIC);

    for (file, function) in analysis.reportable() {
        analysis.summarize(file, function);
    }

    assert_eq!(project.implementation_stats().files, 2);
    assert!(!marker.exists());
}

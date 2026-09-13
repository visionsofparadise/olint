use olint::config::{package_entries, read_config, ConfigError};

mod support;

use support::run_in_project;

const TSCONFIG: (&str, &str) = ("tsconfig.json", r#"{ "include": ["src"] }"#);

fn entries_of(files: &[(&str, &str)]) -> Vec<String> {
    let mut entries = Vec::new();

    run_in_project(files, |project, _| {
        entries = package_entries(project)
            .iter()
            .map(|entry| olint::project::relative_path_of(&project.root, entry))
            .collect();
    });

    entries
}

#[test]
fn package_exports_nested_by_condition_resolve_to_source() {
    let entries = entries_of(&[
        TSCONFIG,
        (
            "package.json",
            r#"{ "main": "dist/other.js", "exports": { ".": { "types": "./dist/index.d.ts", "import": "./dist/index.js" } } }"#,
        ),
        ("src/index.ts", "export const a = 1;"),
        ("src/other.ts", "export const b = 1;"),
    ]);

    assert_eq!(entries, vec!["src/index.ts"]);
}

#[test]
fn package_main_resolves_to_a_directory_index() {
    let entries = entries_of(&[
        TSCONFIG,
        ("package.json", r#"{ "main": "./dist/x.js" }"#),
        ("src/x/index.ts", "export const a = 1;"),
    ]);

    assert_eq!(entries, vec!["src/x/index.ts"]);
}

#[test]
fn read_config_keeps_entrypoints_in_file_order_with_their_limits() {
    run_in_project(
        &[
            TSCONFIG,
            (
                "olint.config.json",
                r#"{ "max": "O(N  log N)", "entrypoints": { "./src/z.ts": "O(N)", "src/a.ts": "O(N^3)" }, "ignore": ["src/gen/**"] }"#,
            ),
            ("src/z.ts", "export const z = 1;"),
            ("src/a.ts", "export const a = 1;"),
        ],
        |project, _| {
            let config = read_config(project, None).expect("config reads");
            let entries: Vec<(String, String)> = config
                .entrypoints
                .iter()
                .map(|(path, limit)| {
                    (
                        olint::project::relative_path_of(&project.root, path),
                        limit.text.clone(),
                    )
                })
                .collect();

            assert_eq!(config.max.text, "O(N log N)");
            assert_eq!(config.source, "olint.config.json");
            assert_eq!(
                entries,
                vec![
                    ("src/z.ts".to_string(), "O(N)".to_string()),
                    ("src/a.ts".to_string(), "O(N^3)".to_string())
                ]
            );
            assert!(config.is_ignored("src/gen/types.ts"));
        },
    );
}

#[test]
fn a_config_path_that_is_a_directory_fails_to_read() {
    run_in_project(
        &[
            TSCONFIG,
            ("olint.config.json/keep.txt", ""),
            ("src/a.ts", "export const a = 1;"),
        ],
        |project, _| {
            assert!(matches!(
                read_config(project, None),
                Err(ConfigError::Read { .. })
            ));
        },
    );
}

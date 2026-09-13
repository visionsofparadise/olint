use olint::config::{package_entries, read_config, Config, ConfigError};

mod support;

use support::run_in_project;

const TSCONFIG: (&str, &str) = ("tsconfig.json", r#"{ "include": ["src"] }"#);

fn entries_of(files: &[(&str, &str)]) -> Vec<String> {
    let mut entries = Vec::new();

    run_in_project(files, |project, _| {
        entries = package_entries(project)
            .iter()
            .map(|entry| olint::paths::relative_path_of(&project.root, entry))
            .collect();
    });

    entries
}

fn with_config(files: &[(&str, &str)], body: impl FnOnce(&Config, Vec<(String, String)>)) {
    run_in_project(files, |project, _| {
        let config = read_config(project, None).expect("config reads");
        let limits = config
            .entrypoints
            .iter()
            .map(|(path, limit)| {
                (
                    olint::paths::relative_path_of(&project.root, path),
                    limit.text.clone(),
                )
            })
            .collect();

        body(&config, limits);
    });
}

fn read_error_of(files: &[(&str, &str)]) -> Option<ConfigError> {
    let mut error = None;

    run_in_project(files, |project, _| {
        error = read_config(project, None).err();
    });

    error
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
fn read_config_keeps_entrypoints_in_array_order_with_their_limits() {
    let files = [
        TSCONFIG,
        (
            "olint.config.json",
            r#"{ "max": "O(N  log N)", "entrypoints": [{ "path": "./src/z.ts", "max": "O(N)" }, "src/a.ts"], "ignore": ["src/gen/**"] }"#,
        ),
        ("src/z.ts", "export const z = 1;"),
        ("src/a.ts", "export const a = 1;"),
    ];

    with_config(&files, |config, limits| {
        assert_eq!(config.max.text, "O(N log N)");
        assert_eq!(config.source, "olint.config.json");
        assert_eq!(
            limits,
            vec![
                ("src/z.ts".to_string(), "O(N)".to_string()),
                ("src/a.ts".to_string(), "O(N log N)".to_string())
            ]
        );
        assert!(config.is_ignored("src/gen/types.ts"));
    });
}

#[test]
fn read_config_without_entrypoints_gives_package_entries_the_top_level_max() {
    let files = [
        TSCONFIG,
        ("package.json", r#"{ "main": "dist/index.js" }"#),
        ("olint.config.json", r#"{ "max": "O(N)" }"#),
        ("src/index.ts", "export const a = 1;"),
    ];

    with_config(&files, |_, limits| {
        assert_eq!(
            limits,
            vec![("src/index.ts".to_string(), "O(N)".to_string())]
        );
    });
}

#[test]
fn read_config_rejects_the_keyed_entrypoints_object() {
    let error = read_error_of(&[
        TSCONFIG,
        (
            "olint.config.json",
            r#"{ "entrypoints": { "src/index.ts": "O(N)" } }"#,
        ),
        ("src/index.ts", "export const index = 1;"),
    ]);

    assert!(matches!(error, Some(ConfigError::Entrypoints { .. })));
}

#[test]
fn a_config_path_that_is_a_directory_fails_to_read() {
    let error = read_error_of(&[
        TSCONFIG,
        ("olint.config.json/keep.txt", ""),
        ("src/a.ts", "export const a = 1;"),
    ]);

    assert!(matches!(error, Some(ConfigError::Read { .. })));
}

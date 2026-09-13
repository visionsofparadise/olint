use std::path::{Path, PathBuf};

use super::*;

fn config_of(json: &str) -> TsConfig {
    let path = Path::new("/repo/tsconfig.json");

    TsConfig::parse(false, path, path, json.to_string()).expect("tsconfig parses")
}

#[test]
fn merge_extends_prefers_the_child_and_inherits_the_rest() {
    let parent = config_of(
        r#"{ "include": ["lib"], "exclude": ["dist"], "compilerOptions": { "allowJs": true } }"#,
    );
    let child = config_of(r#"{ "include": ["src"] }"#);
    let merged = merge_extends(child, &parent);

    assert_eq!(merged.include, Some(vec![PathBuf::from("src")]));
    assert_eq!(merged.exclude, Some(vec![PathBuf::from("dist")]));
    assert_eq!(merged.compiler_options.allow_js, Some(true));
}

fn components_of(pattern: &str) -> Vec<String> {
    pattern.split('/').map(str::to_string).collect()
}

fn file_matches(pattern: &str, path: &str) -> bool {
    include_matches(
        &components_of(pattern),
        &path.split('/').collect::<Vec<_>>(),
        false,
    )
}

#[test]
fn wildcards_skip_dot_names_and_package_folders_that_literals_name() {
    assert!(!file_matches("/r/src/**/*", "/r/src/.dot/d.ts"));
    assert!(!file_matches("/r/**/*", "/r/node_modules/pkg/p.ts"));
    assert!(file_matches("/r/.hidden/*.ts", "/r/.hidden/h.ts"));
    assert!(file_matches(
        "/r/node_modules/pkg/*.ts",
        "/r/node_modules/pkg/p.ts"
    ));
    assert!(!include_matches(
        &components_of("/r/src/**/*"),
        &["", "r", "src", ".dot"],
        true
    ));
    assert!(include_matches(
        &components_of("/r/src/**/*"),
        &["", "r"],
        true
    ));
}

#[test]
fn a_star_does_not_match_a_minified_script() {
    assert!(!file_matches("/r/src/*", "/r/src/b.min.js"));
    assert!(file_matches("/r/src/*", "/r/src/b.min.ts"));
    assert!(file_matches("/r/src/*.js", "/r/src/b.js"));
}

#[test]
fn a_question_mark_skips_a_leading_dot_only() {
    assert!(file_matches("/r/src/a?ts", "/r/src/a.ts"));
    assert!(!file_matches("/r/src/?hidden.ts", "/r/src/.hidden.ts"));
    assert!(file_matches("/r/src/?hidden.ts", "/r/src/xhidden.ts"));
}

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

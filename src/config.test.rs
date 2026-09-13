use super::*;

#[test]
fn limit_of_names_the_field_it_rejects() {
    match limit_of("O(M)", "max") {
        Err(ConfigError::Limit { field, text }) => {
            assert_eq!(field, "max");
            assert_eq!(text, "\"O(M)\"");
        }
        _ => panic!("O(M) is rejected"),
    }

    let limit = limit_of("O(N^3)", "max").expect("O(N^3) is a limit");

    assert_eq!(limit.cost, Cost { n: 3, log: 0 });
    assert_eq!(limit.text, "O(N^3)");
}

#[test]
fn ignore_globs_read_as_the_reference_regular_expressions() {
    let generated = IgnorePattern::parse("src/generated/**").expect("pattern");

    assert!(generated.matches("src/generated/schema.ts"));
    assert!(!generated.matches("src/generated/deep/schema.ts"));
    assert!(!generated.matches("src/generated/"));
    assert!(!generated.matches("src/other.ts"));

    let nested = IgnorePattern::parse("**/*.gen.ts").expect("pattern");

    assert!(nested.matches("a.gen.ts"));
    assert!(nested.matches("src/a.gen.ts"));
    assert!(!nested.matches("src/deep/a.gen.ts"));
    assert!(!nested.matches("src/agen.ts"));

    let optional = IgnorePattern::parse("src/a?b.ts").expect("pattern");

    assert!(optional.matches("src/b.ts"));
    assert!(optional.matches("src/ab.ts"));
    assert!(IgnorePattern::parse("?a").is_none());
}

fn entries_of(value: Value) -> Result<Vec<(String, String)>, ConfigError> {
    let root = Path::new("project");
    let max = limit_of("O(N^2)", "max").expect("O(N^2) is a limit");

    entrypoints_of(&value, root, &max).map(|entrypoints| {
        entrypoints
            .into_iter()
            .map(|(path, limit)| (relative_path_of(root, &path), limit.text))
            .collect()
    })
}

fn pairs_of(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(path, limit)| (path.to_string(), limit.to_string()))
        .collect()
}

#[test]
fn entrypoint_strings_take_the_top_level_max() {
    let entries = entries_of(serde_json::json!(["./src/z.ts", "src/a.ts"])).expect("entrypoints");

    assert_eq!(
        entries,
        pairs_of(&[("src/z.ts", "O(N^2)"), ("src/a.ts", "O(N^2)")])
    );
}

#[test]
fn entrypoint_objects_take_their_own_max() {
    let entries = entries_of(serde_json::json!([
        { "path": "src/z.ts", "max": "O(N)" },
        { "max": "O(N^3)", "path": "src/a.ts" }
    ]))
    .expect("entrypoints");

    assert_eq!(
        entries,
        pairs_of(&[("src/z.ts", "O(N)"), ("src/a.ts", "O(N^3)")])
    );
}

#[test]
fn entrypoint_strings_and_objects_mix_in_array_order() {
    let entries = entries_of(serde_json::json!([
        "src/z.ts",
        { "path": "src/a.ts", "max": "O(N)" },
        "src/m.ts"
    ]))
    .expect("entrypoints");

    assert_eq!(
        entries,
        pairs_of(&[
            ("src/z.ts", "O(N^2)"),
            ("src/a.ts", "O(N)"),
            ("src/m.ts", "O(N^2)")
        ])
    );
}

#[test]
fn a_duplicate_entrypoint_keeps_its_first_position_and_the_stricter_limit() {
    let entries = entries_of(serde_json::json!([
        { "path": "src/a.ts", "max": "O(N^3)" },
        "src/b.ts",
        { "path": "./src/a.ts", "max": "O(N)" },
        { "path": "src/b.ts", "max": "O(N^4)" }
    ]))
    .expect("entrypoints");

    assert_eq!(
        entries,
        pairs_of(&[("src/a.ts", "O(N)"), ("src/b.ts", "O(N^2)")])
    );
}

#[test]
fn an_entrypoint_of_another_shape_names_its_item() {
    for item in [
        serde_json::json!(3),
        serde_json::json!({ "path": "src/a.ts" }),
        serde_json::json!({ "max": "O(N)" }),
        serde_json::json!({ "path": 3, "max": "O(N)" }),
        serde_json::json!({ "path": "src/a.ts", "max": "O(N)", "limit": "O(N)" }),
    ] {
        match entries_of(serde_json::json!(["src/z.ts", item])) {
            Err(ConfigError::Entrypoint { field, text }) => {
                assert_eq!(field, "entrypoints[1]");
                assert_eq!(text, item.to_string());
            }
            _ => panic!("{item} is rejected"),
        }
    }
}

#[test]
fn an_entrypoint_max_that_is_not_a_limit_names_its_item() {
    match entries_of(serde_json::json!([
        "src/z.ts",
        { "path": "src/a.ts", "max": "O(M)" }
    ])) {
        Err(ConfigError::Limit { field, text }) => {
            assert_eq!(field, "entrypoints[1].max");
            assert_eq!(text, "\"O(M)\"");
        }
        _ => panic!("O(M) is rejected"),
    }
}

#[test]
fn entrypoints_that_are_not_an_array_are_rejected() {
    for value in [
        serde_json::json!({ "src/a.ts": "O(N)" }),
        serde_json::json!("src/a.ts"),
        Value::Null,
    ] {
        assert!(matches!(
            entries_of(value),
            Err(ConfigError::Entrypoints { .. })
        ));
    }
}

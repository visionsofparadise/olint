use super::*;

#[test]
fn unknown_policy_has_exact_values_and_warn_default() {
    assert_eq!(unknown_policy_of(None).unwrap(), UnknownPolicy::Warn);

    for (text, expected) in [
        ("ignore", UnknownPolicy::Ignore),
        ("warn", UnknownPolicy::Warn),
        ("error", UnknownPolicy::Error),
    ] {
        assert_eq!(
            unknown_policy_of(Some(&serde_json::json!(text))).unwrap(),
            expected
        );
    }

    for value in [
        serde_json::json!("WARN"),
        serde_json::json!("true"),
        serde_json::json!(false),
        Value::Null,
        serde_json::json!([]),
        serde_json::json!({}),
        serde_json::json!(1),
    ] {
        assert!(matches!(
            unknown_policy_of(Some(&value)),
            Err(ConfigError::Unknown { .. })
        ));
    }
}

#[test]
fn limit_of_names_the_field_it_rejects() {
    match limit_of("O(N+)", "max") {
        Err(ConfigError::Limit { field, text }) => {
            assert_eq!(field, "max");
            assert_eq!(text, "\"O(N+)\"");
        }
        _ => panic!("O(N+) is rejected"),
    }

    let limit = limit_of("O(N^3)", "max").expect("O(N^3) is a limit");

    assert_eq!(limit.cost, Cost::parse("O(N^3)").unwrap());
    assert_eq!(limit.text, "O(N^3)");
}

#[test]
fn ignore_globs_distinguish_recursive_and_single_directory_wildcards() {
    let generated = ignore_pattern_of(&serde_json::json!("src/generated/**")).expect("pattern");

    assert!(generated.is_match("src/generated/schema.ts"));
    assert!(generated.is_match("src/generated/deep/schema.ts"));
    assert!(!generated.is_match("src/other.ts"));

    let nested = ignore_pattern_of(&serde_json::json!("**/*.gen.ts")).expect("pattern");

    assert!(nested.is_match("a.gen.ts"));
    assert!(nested.is_match("src/deep/a.gen.ts"));

    let direct = ignore_pattern_of(&serde_json::json!("src/*.gen.ts")).expect("pattern");

    assert!(direct.is_match("src/a.gen.ts"));
    assert!(!direct.is_match("src/deep/a.gen.ts"));
}

#[test]
fn ignore_globs_match_question_marks_as_one_character_and_allow_escaping() {
    let single = ignore_pattern_of(&serde_json::json!("src/a?b.ts")).expect("pattern");

    assert!(single.is_match("src/axb.ts"));
    assert!(!single.is_match("src/ab.ts"));
    assert!(!single.is_match("src/axyb.ts"));
    assert!(!single.is_match("src/a/b.ts"));

    let literal = ignore_pattern_of(&serde_json::json!(r"src/a\[b\].ts")).expect("pattern");

    assert!(literal.is_match("src/a[b].ts"));
    assert!(!literal.is_match("src/ab.ts"));
}

fn entries_of(value: Value) -> Result<Vec<(String, String)>, ConfigError> {
    let root = Path::new("project");
    let max = limit_of("O(N^2)", "max").expect("O(N^2) is a limit");

    entrypoints_of(&value, root, &max).map(|entrypoints| {
        entrypoints
            .into_iter()
            .flat_map(|(path, limits)| {
                limits
                    .into_iter()
                    .map(move |limit| (relative_path_of(root, &path), limit.text))
            })
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
fn a_duplicate_entrypoint_keeps_its_first_position_and_all_constraints() {
    let entries = entries_of(serde_json::json!([
        { "path": "src/a.ts", "max": "O(N^3)" },
        "src/b.ts",
        { "path": "./src/a.ts", "max": "O(N)" },
        { "path": "src/b.ts", "max": "O(N^4)" }
    ]))
    .expect("entrypoints");

    assert_eq!(
        entries,
        pairs_of(&[
            ("src/a.ts", "O(N^3)"),
            ("src/a.ts", "O(N)"),
            ("src/b.ts", "O(N^2)"),
            ("src/b.ts", "O(N^4)")
        ])
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
        { "path": "src/a.ts", "max": "O(N+)" }
    ])) {
        Err(ConfigError::Limit { field, text }) => {
            assert_eq!(field, "entrypoints[1].max");
            assert_eq!(text, "\"O(N+)\"");
        }
        _ => panic!("O(N+) is rejected"),
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

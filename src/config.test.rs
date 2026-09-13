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

use super::short;

#[test]
fn short_truncates_beyond_forty_characters() {
    let text = "abcdefghij".repeat(4) + "klmno";

    assert_eq!(short(&text), format!("{}...", &text[..37]));
    assert_eq!(short(&text[..40]), text[..40]);
}

#[test]
fn short_collapses_whitespace_runs() {
    assert_eq!(short("xs\n\t  .map(f)"), "xs .map(f)");
}

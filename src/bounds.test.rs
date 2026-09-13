use super::short;

#[test]
fn short_truncates_beyond_forty_characters() {
    let text = "abcdefghij".repeat(4) + "klmno";

    assert_eq!(short(&text), format!("{}...", &text[..37]));
    assert_eq!(short(&text[..40]), text[..40]);
}

#[test]
fn short_replaces_a_surrogate_pair_split_by_the_cut() {
    let text = format!("{}\u{1F600}{}", "a".repeat(36), "b".repeat(10));

    assert_eq!(short(&text), format!("{}\u{FFFD}...", "a".repeat(36)));
}

#[test]
fn short_keeps_a_next_line_character() {
    assert_eq!(short("a\u{85}  b"), "a\u{85} b");
}

#[test]
fn short_collapses_whitespace_runs() {
    assert_eq!(short("xs\n\t  .map(f)"), "xs .map(f)");
}

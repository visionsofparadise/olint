use super::*;

#[test]
fn tags_in_comment_reads_a_jsdoc_block() {
    let comment = "*\n * Sums the rows.\n * @perf max   O(N^3)\n * @perf hot\n ";

    assert_eq!(
        tags_in_comment(comment),
        vec![PerfTag::Max("O(N^3)".to_string()), PerfTag::Hot]
    );
}

#[test]
fn tags_in_comment_reads_a_line_comment() {
    assert_eq!(
        tags_in_comment(" @perf O(N  log N) because the rows arrive sorted"),
        vec![PerfTag::Cost("O(N log N)".to_string())]
    );
}

#[test]
fn tags_in_comment_requires_a_word_boundary() {
    assert_eq!(tags_in_comment("@perf hotter @perfhot"), Vec::new());
}

#[test]
fn cost_tag_of_skips_a_max_tag() {
    let tags = vec![
        PerfTag::Max("O(N^3)".to_string()),
        PerfTag::Cost("O(N)".to_string()),
    ];

    assert_eq!(cost_tag_of(&tags), Some((Cost::N, "O(N)".to_string())));
}

#[test]
fn max_tag_of_rejects_an_unparsable_limit() {
    assert_eq!(max_tag_of(&[PerfTag::Max("O(M)".to_string())]), None);
}

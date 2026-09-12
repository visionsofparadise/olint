use super::*;

#[test]
fn test_suffixes_match_every_extension_form() {
    for path in [
        "/repo/src/a.test.ts",
        "/repo/src/a.spec.tsx",
        "/repo/src/a.bench.mjs",
        "/repo/src/a.benchmark.cts",
        "/repo/src/a.stories.jsx",
    ] {
        assert!(is_test_relative(path, "src/a.ts"), "{path}");
    }

    assert!(!is_test_relative("/repo/src/a.test.d", "src/a.test.d"));
    assert!(!is_test_relative("/repo/src/latest.ts", "src/latest.ts"));
}

#[test]
fn test_segments_match_directories_only() {
    for relative in [
        "test/a.ts",
        "src/tests/a.ts",
        "src/__tests__/a.ts",
        "fixtures/a.ts",
        "scripts/a.ts",
        "src/mock/a.ts",
        "src/mocks/a.ts",
    ] {
        assert!(is_test_relative("/repo/a.ts", relative), "{relative}");
    }

    assert!(!is_test_relative("/repo/src/tests.ts", "src/tests.ts"));
    assert!(!is_test_relative(
        "/repo/src/contest/a.ts",
        "src/contest/a.ts"
    ));
}

#[test]
fn line_starts_count_bytes_and_every_line_break() {
    let text = "é\nb\r\nc\rd\u{2028}e";
    let starts = line_starts_of(text);

    assert_eq!(starts, vec![0, 3, 6, 8, 12]);
    assert_eq!(line_of_offset(&starts, 2), 1);
    assert_eq!(line_of_offset(&starts, 3), 2);
    assert_eq!(line_of_offset(&starts, 12), 5);
}

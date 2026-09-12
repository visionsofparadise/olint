use super::*;
use crate::project::{FileId, Site};

fn part_of(cost: Cost, label: &str) -> Part {
    Part {
        cost,
        chain: vec![Factor {
            label: label.to_string(),
            site: Site {
                file: FileId(0),
                line: 1,
            },
            cost,
            inner: Vec::new(),
        }],
    }
}

#[test]
fn text_round_trips_through_parse() {
    for text in [
        "O(1)",
        "O(log N)",
        "O(N)",
        "O(N log N)",
        "O(N^3)",
        "O(N^2 log N)",
    ] {
        let cost = Cost::parse(text).unwrap_or_else(|| panic!("{text} parses"));

        assert_eq!(cost.text(), text);
    }
}

#[test]
fn parse_rejects_other_variables_and_log_powers() {
    assert_eq!(Cost::parse("O(M)"), None);
    assert_eq!(Cost::parse("O(log^2 N)"), None);
}

#[test]
fn exceeds_is_strict_and_lexicographic() {
    assert!(Cost { n: 2, log: 0 }.exceeds(Cost { n: 1, log: 5 }));
    assert!(Cost { n: 1, log: 1 }.exceeds(Cost::N));
    assert!(!Cost::N.exceeds(Cost::N));
    assert!(!Cost::N.exceeds(Cost::N_LOG_N));
}

#[test]
fn part_max_keeps_the_first_on_ties() {
    let first = part_of(Cost::N, "first");
    let second = part_of(Cost::N, "second");

    assert_eq!(first.clone().max(second), first);
}

#[test]
fn reading_total_takes_the_largest_part() {
    let reading = Reading {
        main: part_of(Cost::N, "main"),
        function_exit: part_of(Cost::LOG, "function exit"),
        loop_exit: part_of(Cost::N_LOG_N, "loop exit"),
    };

    assert_eq!(reading.total(), part_of(Cost::N_LOG_N, "loop exit"));
}

#[test]
fn kind_join_ranks_array_over_unknown_over_string() {
    use crate::declared_types::Kind;

    assert_eq!(Kind::Unknown.join(Kind::Array), Kind::Array);
    assert_eq!(Kind::Array.join(Kind::Unknown), Kind::Array);
    assert_eq!(Kind::String.join(Kind::Unknown), Kind::Unknown);
    assert_eq!(Kind::Unknown.join(Kind::String), Kind::Unknown);
}

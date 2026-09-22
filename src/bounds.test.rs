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

use super::{constant_bound_of, linear_bound_of, logarithmic_bound_of, unresolved_bound_of, Bound};
use crate::cost::Cost;
use crate::unknowns::UnknownReason;

#[test]
fn a_proven_bound_reports_its_factor_and_an_unresolved_one_reports_its_reason() {
    let constant = constant_bound_of("constant bound");
    let unresolved = unresolved_bound_of();

    assert_eq!(constant.factor(), Some(&Cost::ONE));
    assert_eq!(constant.proof(), Some("constant bound"));
    assert_eq!(constant.reason(), None);
    assert!(!constant.is_unresolved());
    assert_eq!(unresolved.factor(), None);
    assert_eq!(unresolved.proof(), None);
    assert_eq!(unresolved.reason(), Some(UnknownReason::Bound));
    assert!(unresolved.is_unresolved());
}

#[test]
fn a_label_names_the_proof_the_factor_or_the_unknown() {
    assert_eq!(
        constant_bound_of("single iteration").label(),
        "single iteration"
    );
    assert_eq!(logarithmic_bound_of("halving").label(), "halving");
    assert_eq!(linear_bound_of().label(), "N");
    assert_eq!(
        Bound::Proven {
            factor: Cost::LOG,
            proof: None
        }
        .label(),
        "log"
    );
    assert_eq!(unresolved_bound_of().label(), "iteration bound");
}

#[test]
fn a_stronger_bound_wins_a_conjunction_of_comparisons() {
    let ordered = [
        constant_bound_of("constant bound"),
        logarithmic_bound_of("halving"),
        linear_bound_of(),
        unresolved_bound_of(),
    ];

    for (index, bound) in ordered.iter().enumerate() {
        for stronger in &ordered[..index] {
            assert!(
                stronger.strength() < bound.strength(),
                "{stronger:?} {bound:?}"
            );
        }
    }
}

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

use super::{
    constant_bound_of, logarithmic_bound_of, unresolved_bound_of, untracked_bound_of, Bound,
    Verdict,
};
use crate::cost::{Cost, Domain};
use crate::derivation::{DerivationArena, Fact};
use crate::project::FileId;
use crate::unknowns::{SourceSpan, UnknownReason};

fn linear_bound_of() -> Verdict {
    Verdict::Proven {
        factor: Cost::dimension(0, Domain::Size),
        rule: "bound-additive",
        condition: None,
    }
}

fn recorded(derivations: &mut DerivationArena, factor: Cost, condition: Option<&str>) -> Bound {
    let syntax = SourceSpan {
        file: FileId(0),
        start: 0,
        end: 1,
    };
    let facts = condition
        .map(|condition| vec![Fact::Name(condition.to_string())])
        .unwrap_or_default();
    let derivation = derivations.leaf("bound-exact-additive", syntax, facts, factor.clone());

    Bound::Proven { factor, derivation }
}

#[test]
fn a_proven_bound_reports_its_factor_and_derivation_and_an_unresolved_one_its_reason() {
    let mut derivations = DerivationArena::default();
    let constant = recorded(&mut derivations, Cost::ONE, Some("constant bound"));
    let unresolved = Bound::Unresolved {
        reason: UnknownReason::Bound,
    };
    let derivation = derivations.get(constant.derivation().unwrap()).unwrap();

    assert_eq!(constant.factor(), Some(&Cost::ONE));
    assert_eq!(derivation.rule, "bound-exact-additive");
    assert_eq!(derivation.cost, Cost::ONE);
    assert_eq!(constant.proof(&derivations), Some("constant bound"));
    assert_eq!(constant.reason(), None);
    assert!(!constant.is_unresolved());
    assert_eq!(unresolved.factor(), None);
    assert_eq!(unresolved.derivation(), None);
    assert_eq!(unresolved.proof(&derivations), None);
    assert_eq!(unresolved.reason(), Some(UnknownReason::Bound));
    assert!(unresolved.is_unresolved());
}

#[test]
fn a_label_names_the_side_condition_the_factor_or_the_unknown() {
    let mut derivations = DerivationArena::default();
    let halving = recorded(
        &mut derivations,
        Cost::logarithm(Cost::dimension(0, Domain::Size)).unwrap(),
        Some("halving"),
    );
    let linear = recorded(&mut derivations, Cost::dimension(0, Domain::Size), None);
    let logarithmic = recorded(&mut derivations, Cost::LOG, None);
    let untracked = Bound::Unresolved {
        reason: UnknownReason::SizeRelation,
    };

    assert_eq!(halving.label(&derivations), "halving");
    assert_eq!(linear.label(&derivations), "N");
    assert_eq!(logarithmic.label(&derivations), "log");
    assert_eq!(untracked.label(&derivations), "input size relation");
    assert_eq!(
        constant_bound_of("bound-single-iteration", "single iteration").label(),
        "single iteration"
    );
    assert_eq!(
        logarithmic_bound_of(
            "bound-bisection",
            "halving",
            Cost::dimension(0, Domain::Size)
        )
        .label(),
        "halving"
    );
    assert_eq!(linear_bound_of().label(), "N");
    assert_eq!(untracked_bound_of().label(), "input size relation");
    assert_eq!(unresolved_bound_of().label(), "iteration bound");
}

#[test]
fn a_stronger_bound_wins_a_conjunction_of_comparisons() {
    let ordered = [
        constant_bound_of("bound-exact-additive", "constant bound"),
        logarithmic_bound_of(
            "bound-bisection",
            "halving",
            Cost::dimension(0, Domain::Size),
        ),
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

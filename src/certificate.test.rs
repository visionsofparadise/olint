use super::*;
use crate::derivation::{is_rule, RULES};

fn certificate_source() -> String {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/proofs/Olint/Certificate.lean");

    std::fs::read_to_string(path).unwrap()
}

fn declares(source: &str, constructor: &str) -> bool {
    let prefix = format!("  | {constructor}");

    source.lines().any(|line| {
        line.strip_prefix(&prefix)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with(' '))
    })
}

#[test]
fn a_constructor_name_is_the_rule_id_in_lower_camel_case() {
    assert_eq!(constructor_of("seq-max"), "seqMax");
    assert_eq!(constructor_of("bound-for-of-native"), "boundForOfNative");
    assert_eq!(constructor_of("rec-markers"), "recMarkers");
}

#[test]
fn every_ledger_rule_outside_the_unconstructed_has_its_cert_constructor() {
    let source = certificate_source();

    for rule in UNCONSTRUCTED.iter().chain(SHAPED) {
        assert!(is_rule(rule), "{rule} is not a ledger rule");
    }

    for rule in RULES {
        assert_eq!(
            declares(&source, &constructor_of(rule)),
            !UNCONSTRUCTED.contains(rule),
            "{rule}"
        );
    }

    assert!(declares(&source, "seqUnit"));
}

#[test]
fn the_generic_constructors_take_premises_at_their_nodes_facts_and_a_bound() {
    let source = certificate_source();

    for rule in RULES
        .iter()
        .filter(|rule| !UNCONSTRUCTED.contains(rule) && !SHAPED.contains(rule))
    {
        let line = format!(
            "  | {} (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)",
            constructor_of(rule)
        );

        assert!(source.lines().any(|found| found == line), "{rule}");
    }
}

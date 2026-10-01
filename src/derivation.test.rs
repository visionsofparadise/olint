use super::*;
use crate::analysis::work::{Event, Limits, WorkBudget};
use crate::project::FileId;

fn span(start: u32) -> SourceSpan {
    SourceSpan {
        file: FileId(0),
        start,
        end: start + 1,
    }
}

fn leaf(start: u32) -> Derivation {
    Derivation {
        rule: "seq-max",
        syntax: span(start),
        premises: Vec::new(),
        facts: Vec::new(),
        cost: Cost::ONE,
    }
}

#[test]
fn the_rules_are_the_ledger_rule_ids_in_ledger_order() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/corpus/ledger.json");
    let ledger: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let names: Vec<&str> = ledger["rules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|rule| rule["name"].as_str().unwrap())
        .collect();

    assert_eq!(names, RULES);
}

#[test]
fn an_equal_derivation_shares_its_id_and_is_charged_once() {
    let mut arena = DerivationArena::default();
    let first = arena.record(leaf(0)).unwrap();
    let again = arena.record(leaf(0)).unwrap();
    let other = arena.record(leaf(1)).unwrap();

    assert_eq!(first, again);
    assert_ne!(first, other);
    assert_eq!(arena.len(), 2);
    assert_eq!(arena.charged(), 2);
}

#[test]
fn a_node_is_charged_one_unit_per_premise_and_fact() {
    let mut arena = DerivationArena::default();
    let left = arena.record(leaf(0)).unwrap();
    let right = arena.record(leaf(1)).unwrap();
    let parent = arena
        .record(Derivation {
            rule: "branch-join",
            syntax: span(2),
            premises: vec![left, right],
            facts: vec![Fact::Flag(true)],
            cost: Cost::ONE,
        })
        .unwrap();

    assert_eq!(arena.charged(), 2 + 4);
    assert_eq!(arena.get(parent).unwrap().premises, vec![left, right]);
}

#[test]
fn a_record_past_the_limit_or_over_an_unrecorded_premise_is_refused() {
    let mut arena = DerivationArena::new(2);

    arena.record(leaf(0)).unwrap();
    assert!(arena
        .record(Derivation {
            premises: vec![DerivationId(7)],
            ..leaf(1)
        })
        .is_none());
    assert!(!arena.exhausted());

    arena.record(leaf(1)).unwrap();
    assert!(arena.record(leaf(2)).is_none());
    assert!(arena.exhausted());
    assert_eq!(arena.charged(), 2);
}

#[test]
fn a_new_generation_restarts_the_count_and_keeps_the_nodes() {
    let mut arena = DerivationArena::new(2);
    let id = arena.record(leaf(0)).unwrap();

    arena.record(leaf(1)).unwrap();
    assert!(arena.record(leaf(2)).is_none());
    arena.begin_generation();

    assert_eq!(arena.charged(), 0);
    assert!(!arena.exhausted());
    assert_eq!(arena.record(leaf(0)), Some(id));
    assert!(arena.record(leaf(2)).is_none());
}

#[test]
fn the_work_snapshot_includes_the_arena_charges_under_the_derivation_event() {
    let mut arena = DerivationArena::default();

    arena.record(leaf(0)).unwrap();

    let snapshot = WorkBudget::new(Limits::uniform(10)).snapshot().including(
        Event::Derivation,
        arena.charged(),
        arena.exhausted(),
    );

    assert_eq!(snapshot.consumed(Event::Derivation), 1);
    assert!(!snapshot.exhausted(Event::Derivation));
}

use super::*;
use crate::analysis::work::{Event, Limits, WorkBudget};
use crate::cost::{nest, Domain, ExecutionPhase, Multiplicity, Part, Preference, Reading};
use crate::flow::Completion;
use crate::project::{FileId, Site};
use crate::trace::TraceArena;
use crate::unknowns::Unknowns;

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

fn derived_part(traces: &mut TraceArena, cost: Cost, start: u32) -> Part {
    let derivation = traces
        .derivations
        .leaf("seq-max", span(start), Vec::new(), cost.clone());

    Part::unmarked(cost, None).derived(derivation)
}

fn premises_of(traces: &TraceArena, part: &Part) -> (&'static str, Vec<DerivationId>) {
    let derivation = traces.derivations.get(part.derivation.unwrap()).unwrap();

    (derivation.rule, derivation.premises.clone())
}

#[test]
fn a_join_keeps_both_sides_whichever_it_selects() {
    let mut traces = TraceArena::default();
    let mut unknowns = Unknowns::default();
    let x = Cost::dimension(1, Domain::Size);
    let y = Cost::dimension(2, Domain::Size);
    let unit = derived_part(&mut traces, Cost::ONE, 0);
    let linear = derived_part(&mut traces, x.clone(), 1);
    let other = derived_part(&mut traces, y, 2);
    let (unit_id, linear_id, other_id) = (
        unit.derivation.unwrap(),
        linear.derivation.unwrap(),
        other.derivation.unwrap(),
    );

    let dominated = unit.clone().max(linear.clone(), &mut unknowns, &mut traces);

    assert_eq!(dominated.cost, x);
    assert_eq!(
        premises_of(&traces, &dominated),
        ("max-dominance", vec![unit_id, linear_id])
    );

    let both = linear
        .clone()
        .max(other.clone(), &mut unknowns, &mut traces);

    assert_eq!(
        premises_of(&traces, &both),
        ("max-normalise", vec![linear_id, other_id])
    );

    let ranked = linear
        .preferred(Preference::Cold)
        .max(unit, &mut unknowns, &mut traces);

    assert_eq!(ranked.cost, Cost::ONE);
    assert_eq!(
        premises_of(&traces, &ranked),
        ("preference-rank", vec![linear_id, unit_id])
    );
}

#[test]
fn a_join_over_an_underived_cost_is_underived_and_a_unit_needs_no_derivation() {
    let mut traces = TraceArena::default();
    let mut unknowns = Unknowns::default();
    let x = Cost::dimension(1, Domain::Size);
    let linear = derived_part(&mut traces, x.clone(), 1);
    let underived = Part::unmarked(x.clone(), None);

    let lost = linear.clone().max(underived, &mut unknowns, &mut traces);
    let kept = linear
        .clone()
        .max(Part::unmarked(Cost::ONE, None), &mut unknowns, &mut traces);

    assert_eq!(lost.derivation, None);
    assert_eq!(kept.derivation, linear.derivation);
}

#[test]
fn parts_compare_without_their_derivations() {
    let mut traces = TraceArena::default();
    let part = derived_part(&mut traces, Cost::ONE, 0).preferred(Preference::Absent);

    assert_eq!(part, Part::none());
}

#[test]
fn a_total_is_derived_from_every_channel_by_channel_total() {
    let mut traces = TraceArena::default();
    let mut unknowns = Unknowns::default();
    let main = derived_part(&mut traces, Cost::dimension(1, Domain::Size), 0);
    let returned = derived_part(&mut traces, Cost::dimension(2, Domain::Size), 1);
    let mut reading = Reading::of_part(main.clone());

    reading.set(
        ExecutionPhase::Immediate,
        Completion::Return,
        returned.clone(),
    );

    let total = reading.total(&mut unknowns, &mut traces);

    assert_eq!(
        premises_of(&traces, &total),
        (
            "channel-total",
            vec![main.derivation.unwrap(), returned.derivation.unwrap()]
        )
    );
}

#[test]
fn a_repetition_is_derived_from_its_witness_and_its_body() {
    let mut traces = TraceArena::default();
    let mut unknowns = Unknowns::default();
    let x = Cost::dimension(1, Domain::Size);
    let body = derived_part(&mut traces, x.clone(), 0);
    let witness = traces
        .derivations
        .leaf("loop-nest", span(1), Vec::new(), x.clone());
    let site = Site {
        file: FileId(0),
        line: 1,
    };
    let looped = nest(
        "loop".to_string(),
        site,
        span(1),
        Multiplicity::looped(x.clone(), witness),
        body.clone(),
        &mut unknowns,
        &mut traces,
    );
    let unwitnessed = nest(
        "loop".to_string(),
        site,
        span(1),
        Multiplicity::nested(x.clone(), None),
        body.clone(),
        &mut unknowns,
        &mut traces,
    );

    assert_eq!(
        premises_of(&traces, &looped),
        (
            "loop-nest",
            vec![witness.unwrap(), body.derivation.unwrap()]
        )
    );
    assert_eq!(unwitnessed.derivation, None);

    let nested = nest(
        "per element".to_string(),
        site,
        span(1),
        Multiplicity::nested(x, witness),
        body.clone(),
        &mut unknowns,
        &mut traces,
    );

    assert_eq!(premises_of(&traces, &nested).0, "nest-product");
}

#[test]
fn a_rule_set_holds_every_rule_beneath_a_derivation_in_ledger_order() {
    let mut arena = DerivationArena::default();
    let bound = arena
        .leaf("bound-additive", span(0), Vec::new(), Cost::ONE)
        .unwrap();
    let body = arena.record(leaf(1)).unwrap();
    let looped = arena
        .derive(
            "loop-nest",
            Some(span(2)),
            &[bound, body],
            Vec::new(),
            Cost::ONE,
        )
        .unwrap();
    let mut sets = RuleSets::default();

    assert_eq!(
        sets.of(&arena, looped),
        ["seq-max", "bound-additive", "loop-nest"]
    );
    assert_eq!(sets.of(&arena, body), ["seq-max"]);
}

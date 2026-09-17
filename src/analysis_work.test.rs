use super::*;

#[test]
fn task_admission_and_fallback_reservation_are_atomic() {
    let mut budget = WorkBudget::new(Limits::uniform(2));

    assert!(budget
        .admit_and_reserve(
            Charges::one(Event::TaskKey, 1),
            Charges::one(Event::WalkerNode, 3)
        )
        .is_err());
    assert_eq!(budget.snapshot().ordinary(), Charges::ZERO);
    assert_eq!(budget.snapshot().reserved(), Charges::ZERO);

    let mut credit = budget
        .admit_and_reserve(
            Charges::one(Event::TaskKey, 1),
            Charges::one(Event::WalkerNode, 2),
        )
        .unwrap();

    assert_eq!(budget.snapshot().ordinary().count(Event::TaskKey), 1);
    budget
        .admit_fallback(&mut credit, Charges::one(Event::WalkerNode, 2))
        .unwrap();
    assert_eq!(budget.snapshot().fallback().count(Event::WalkerNode), 2);
}

#[test]
fn combined_reservation_overflow_is_rejected_before_admission() {
    let mut budget = WorkBudget::new(Limits::uniform(u64::MAX));
    let error = budget
        .admit_and_reserve(
            Charges::one(Event::BodyPass, u64::MAX),
            Charges::one(Event::BodyPass, 1),
        )
        .err()
        .unwrap();

    assert_eq!(error.reason, Reason::Overflow);
    assert_eq!(budget.snapshot().ordinary(), Charges::ZERO);
    assert_eq!(budget.snapshot().reserved(), Charges::ZERO);
}

#[test]
fn admission_precedes_work_and_batch_failure_is_atomic() {
    let mut budget = WorkBudget::new(Limits::uniform(1).with(Event::QueuePush, 0));
    let mut actual_work = 0;
    let charges = Charges::one(Event::TaskKey, 1)
        .plus(Event::QueuePush, 1)
        .unwrap();

    if budget.admit(charges).is_ok() {
        actual_work += 1;
    }

    assert_eq!(actual_work, 0);
    assert_eq!(budget.snapshot().ordinary, Charges::ZERO);
    assert!(budget.snapshot().exhausted(Event::QueuePush));
    budget.admit(Charges::one(Event::TaskKey, 1)).unwrap();

    actual_work += 1;

    assert_eq!(actual_work, 1);
}

#[test]
fn numeric_boundaries_never_wrap() {
    let mut budget = WorkBudget::new(Limits::uniform(u64::MAX));

    budget
        .admit(Charges::one(Event::WalkerNode, u64::MAX))
        .unwrap();
    assert_eq!(budget.available(Event::WalkerNode), 0);
    assert_eq!(
        budget
            .admit(Charges::one(Event::WalkerNode, 1))
            .unwrap_err()
            .reason,
        Reason::Limit
    );
    assert_eq!(budget.snapshot().consumed(Event::WalkerNode), u64::MAX);
    assert_eq!(
        Charges::one(Event::WalkerNode, u64::MAX)
            .plus(Event::WalkerNode, 1)
            .unwrap_err()
            .reason,
        Reason::Overflow
    );
}

#[test]
fn fallback_is_reserved_before_discovery_and_counted_separately() {
    let mut budget = WorkBudget::new(Limits::uniform(10));
    let mut credit = budget
        .reserve_fallback(
            Charges::one(Event::WalkerNode, 4)
                .plus(Event::BodyPass, 1)
                .unwrap(),
        )
        .unwrap();

    budget.admit(Charges::one(Event::WalkerNode, 6)).unwrap();
    assert!(budget.admit(Charges::one(Event::WalkerNode, 1)).is_err());
    budget
        .admit_fallback(
            &mut credit,
            Charges::one(Event::WalkerNode, 4)
                .plus(Event::BodyPass, 1)
                .unwrap(),
        )
        .unwrap();

    let snapshot = budget.snapshot();

    assert_eq!(snapshot.ordinary.count(Event::WalkerNode), 6);
    assert_eq!(snapshot.fallback.count(Event::WalkerNode), 4);
    assert_eq!(snapshot.reserved, Charges::ZERO);
    assert_eq!(snapshot.consumed(Event::WalkerNode), 10);
    assert_eq!(snapshot.fallback.count(Event::BodyPass), 1);
}

#[test]
fn repeat_exhaustion_is_idempotent_and_does_not_consume_work() {
    let mut budget = WorkBudget::new(Limits::uniform(0));
    let charge = Charges::one(Event::Specialization, 1);
    let first = budget.admit(charge).unwrap_err();
    let snapshot = budget.snapshot();

    for _ in 0..1000 {
        assert_eq!(budget.admit(charge), Err(first));
    }

    assert_eq!(budget.snapshot(), snapshot);
    assert_eq!(
        snapshot.exhaustion.iter().filter(|event| **event).count(),
        1
    );
}

#[test]
fn credit_failure_is_atomic_and_release_restores_only_unused_capacity() {
    let mut budget = WorkBudget::new(Limits::uniform(10));
    let mut credit = budget
        .reserve_fallback(Charges::one(Event::WalkerNode, 6))
        .unwrap();
    let snapshot = budget.snapshot();

    assert!(budget
        .admit_fallback(
            &mut credit,
            Charges::one(Event::WalkerNode, 3)
                .plus(Event::BodyPass, 1)
                .unwrap()
        )
        .is_err());
    assert_eq!(budget.snapshot().fallback, snapshot.fallback);
    assert_eq!(credit.remaining().count(Event::WalkerNode), 6);
    budget
        .admit_fallback(&mut credit, Charges::one(Event::WalkerNode, 2))
        .unwrap();
    budget.release(&mut credit).unwrap();
    assert_eq!(budget.available(Event::WalkerNode), 8);
    assert_eq!(budget.snapshot().consumed(Event::WalkerNode), 2);
    assert_eq!(
        budget.release(&mut credit).unwrap_err().reason,
        Reason::ReleasedCredit
    );
    assert_eq!(
        budget
            .admit_fallback(&mut credit, Charges::ZERO)
            .unwrap_err()
            .reason,
        Reason::ReleasedCredit
    );
}

#[test]
fn foreign_and_abandoned_credits_cannot_create_capacity() {
    let mut first = WorkBudget::new(Limits::uniform(5));
    let mut other = WorkBudget::new(Limits::uniform(5));
    let mut credit = first
        .reserve_fallback(Charges::one(Event::GraphEdge, 5))
        .unwrap();

    assert_eq!(
        other
            .admit_fallback(&mut credit, Charges::one(Event::GraphEdge, 1))
            .unwrap_err()
            .reason,
        Reason::ForeignCredit
    );
    assert_eq!(other.snapshot().reserved, Charges::ZERO);
    drop(credit);
    assert_eq!(first.available(Event::GraphEdge), 0);
    assert_eq!(first.snapshot().consumed(Event::GraphEdge), 0);
}

#[test]
fn fallback_and_ordinary_share_numeric_ceiling() {
    let mut budget = WorkBudget::new(Limits::uniform(u64::MAX));
    let mut credit = budget
        .reserve_fallback(Charges::one(Event::GraphNode, u64::MAX - 1))
        .unwrap();

    budget.admit(Charges::one(Event::GraphNode, 1)).unwrap();
    budget
        .admit_fallback(&mut credit, Charges::one(Event::GraphNode, u64::MAX - 1))
        .unwrap();
    assert_eq!(budget.snapshot().consumed(Event::GraphNode), u64::MAX);
    assert_eq!(budget.available(Event::GraphNode), 0);
}

#[test]
fn event_dimensions_and_multiple_credits_stay_independent() {
    let mut budget = WorkBudget::new(Limits::uniform(6));
    let mut first = budget
        .reserve_fallback(Charges::one(Event::BudgetPrepassNode, 2))
        .unwrap();
    let mut second = budget
        .reserve_fallback(Charges::one(Event::BudgetPrepassNode, 3))
        .unwrap();

    budget
        .admit(Charges::one(Event::EffectPrepassNode, 6))
        .unwrap();
    budget
        .admit_fallback(&mut second, Charges::one(Event::BudgetPrepassNode, 3))
        .unwrap();
    budget.release(&mut first).unwrap();
    assert_eq!(budget.available(Event::BudgetPrepassNode), 3);
    assert_eq!(budget.available(Event::EffectPrepassNode), 0);
    assert_eq!(budget.snapshot().consumed(Event::BudgetPrepassNode), 3);
}

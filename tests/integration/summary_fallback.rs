use olint::analysis::work::{Event, Snapshot, EVENTS};
use olint::analysis::Analysis;
use olint::cost::{Cost, CostComparison};
use olint::declarations::FunctionId;
use olint::summaries::{SchedulerLimits, SchedulerStats};
use olint::unknowns::UnknownReason;

use crate::support;

fn first_body_limits(analysis: &mut Analysis<'_, '_>) -> SchedulerLimits {
    let mut limits = SchedulerLimits::default();
    limits.work = limits.work.with(Event::BodyPass, 2);

    analysis.set_scheduler_limits(limits).unwrap();

    limits
}

#[test]
fn first_body_fallback_reuses_ready_closed_callee() {
    support::run_with_source(
        "/** @perf O(N^3) */\nfunction known(){} export function root(){known();}",
        |analysis, file| {
            let limits = first_body_limits(analysis);

            let known = support::function_of_name(analysis.project, file, "known");
            let expected = analysis
                .summarize(file, known)
                .total(&mut analysis.unknowns, &mut analysis.traces);
            let root = support::function_of_name(analysis.project, file, "root");
            let actual = analysis
                .summarize(file, root)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(actual.cost, expected.cost);
            assert!(actual.is_complete());
            assert_eq!(
                analysis
                    .scheduler_stats()
                    .work
                    .fallback()
                    .count(Event::BodyPass),
                1
            );
            terminal(analysis.scheduler_stats(), limits);
        },
    );
}

#[test]
fn first_body_lookup_rejects_other_envelopes_inputs_and_raw_records() {
    for (parameters, root_parameters, raw) in [
        ("", "xs:number[]", false),
        ("x=1", "", false),
        ("...xs:number[]", "", false),
        ("", "", true),
    ] {
        let source = format!(
            "/** @perf O(N^3) */\nfunction known({parameters}){{}} export function root({root_parameters}){{known();}}"
        );

        support::run_with_source(&source, |analysis, file| {
            let limits = first_body_limits(analysis);

            let known = support::function_of_name(analysis.project, file, "known");

            analysis.summarize_with(file, known, Default::default(), raw);

            let root = support::function_of_name(analysis.project, file, "root");
            let part = analysis
                .summarize(file, root)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(part.cost, Cost::ONE, "{source}, raw={raw}");
            assert!(support::unknown_reasons(analysis, part.unknowns)
                .contains(&UnknownReason::ResourceExhaustion));
            terminal(analysis.scheduler_stats(), limits);
        });
    }
}

fn terminal(stats: SchedulerStats, limits: SchedulerLimits) {
    support::assert_scheduler_terminal(stats);

    for event in EVENTS {
        assert!(
            stats.work.consumed(event) <= limits.work.limit(event),
            "over budget {event:?}: {stats:?}"
        );
    }
}

fn fallback_case(
    source: &str,
    expected: &str,
    partial: bool,
    bound_unknown: bool,
    prewarm: bool,
    whole_loop: bool,
) {
    support::run_with_source(source, |analysis, file| {
        let mut limits = SchedulerLimits::default();
        let trigger = if whole_loop {
            Event::BodyPass
        } else {
            Event::DependencyPair
        };
        limits.work = limits.work.with(trigger, u64::from(whole_loop));

        analysis.set_scheduler_limits(limits).unwrap();

        if prewarm {
            let known = support::function_of_name(analysis.project, file, "known");

            analysis.summarize(file, known);
            terminal(analysis.scheduler_stats(), limits);
        }

        let before = analysis.scheduler_stats();
        let function = support::function_of_name(analysis.project, file, "root");
        let reading = analysis.summarize(file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let expected = analysis
            .bind_function_cost(file, function, &Cost::parse(expected).unwrap())
            .unwrap();

        assert_eq!(
            part.cost.compare(&expected),
            CostComparison::Within,
            "actual {:?}, expected {:?}",
            part.cost,
            expected
        );
        assert_eq!(
            expected.compare(&part.cost),
            CostComparison::Within,
            "actual {:?}, expected {:?}",
            part.cost,
            expected
        );
        assert_eq!(!part.is_complete(), partial);

        let found = support::unknown_reasons(analysis, part.unknowns);

        assert_eq!(
            found.contains(&UnknownReason::ResourceExhaustion),
            partial,
            "{found:?}"
        );
        assert_eq!(
            found.contains(&UnknownReason::Bound),
            bound_unknown,
            "{found:?}"
        );
        assert!(
            !found.contains(&UnknownReason::Target),
            "a rejected known target lost its resource reason: {found:?}"
        );

        let after = analysis.scheduler_stats();

        assert!(
            after.work.fallback().count(Event::BodyPass)
                > before.work.fallback().count(Event::BodyPass),
            "fixture did not enter fallback"
        );
        assert!(
            after.work.exhausted(trigger),
            "fixture did not exhaust the chosen event"
        );
        terminal(after, limits);

        for event in [
            Event::TaskKey,
            Event::DependencyPair,
            Event::DependencyWake,
            Event::RuntimePair,
            Event::InvocationSite,
            Event::CallbackDescriptor,
            Event::CaptureEdge,
            Event::GraphNode,
            Event::GraphEdge,
            Event::Specialization,
        ] {
            assert_eq!(
                after.work.fallback().count(event),
                0,
                "fallback admitted new {event:?}"
            );
        }

        let records = analysis.summary_records_for(FunctionId {
            file,
            node: function.node_id(),
        });

        assert!(!records.is_empty());
        assert!(
            records.iter().all(|record| record.effects.unknown_global),
            "fallback must fence unavailable effects"
        );
        assert_eq!(analysis.summarize(file, function), reading);

        let cached = analysis.scheduler_stats();

        assert_eq!(cached.tasks, after.tasks);

        for event in [
            Event::TaskKey,
            Event::BodyPass,
            Event::Publication,
            Event::DependencyPair,
        ] {
            assert_eq!(
                cached.work.consumed(event),
                after.work.consumed(event),
                "cache hit repeated {event:?}"
            );
        }

        terminal(cached, limits);
    });
}

fn wide_observations(source: &str) -> (Snapshot, u64) {
    let mut result = None;

    support::run_with_source(source, |analysis, file| {
        let function = support::function_of_name(analysis.project, file, "root");
        let reading = analysis.summarize(file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

        assert_eq!(part.cost, Cost::ONE);
        assert!(part.is_complete());

        let stats = analysis.scheduler_stats();

        assert_eq!(stats.tasks, 1);
        assert_eq!(stats.work.fallback().count(Event::BodyPass), 0);
        terminal(stats, SchedulerLimits::default());

        let admitted = |walker_limit| {
            let mut probe = Analysis::new(analysis.project, support::SYNTACTIC);
            let mut limits = SchedulerLimits::default();
            limits.work = limits
                .work
                .with(Event::BodyPass, 1)
                .with(Event::WalkerNode, walker_limit);

            probe.set_scheduler_limits(limits).unwrap();

            let reading = probe.summarize(file, function);
            let stats = probe.scheduler_stats();

            terminal(stats, limits);

            if stats.tasks == 0 {
                return false;
            }

            assert_eq!(stats.tasks, 1);
            assert_eq!(stats.work.ordinary().count(Event::BodyPass), 0);
            assert_eq!(stats.work.fallback().count(Event::BodyPass), 1);

            let part = reading.total(&mut probe.unknowns, &mut probe.traces);

            assert_eq!(part.cost, Cost::ONE);
            assert!(part.is_complete());

            true
        };
        let mut low = 0;
        let mut high = SchedulerLimits::default().work.limit(Event::WalkerNode);

        assert!(
            admitted(high),
            "ordinary function cannot reserve its bounded fallback"
        );

        while low < high {
            let middle = low + (high - low) / 2;

            if admitted(middle) {
                high = middle;
            } else {
                low = middle + 1;
            }
        }

        assert!(low > 0);
        assert!(!admitted(low - 1));
        assert!(admitted(low));

        result = Some((stats.work, low));
    });

    result.unwrap()
}

const LOCAL_CUBIC_PREFIX: &str = r#"function deferred() {}
export function root(xs:number[]) {
for(const a of xs) for(const b of xs) for(const c of xs) void c;
deferred();
}
"#;

#[test]
fn local_cubic_prefix() {
    fallback_case(LOCAL_CUBIC_PREFIX, "O(N^3)", true, false, false, false);
}

const BOUNDED_LOOP: &str = r#"/** @perf O(N^3) */
function known() {}
function deferred() {}
export function root() {
/** @perf bounded */
for(;;) {known(); deferred(); break;}
}
"#;

#[test]
fn bounded_loop() {
    fallback_case(BOUNDED_LOOP, "O(N^3)", true, false, true, false);
}

const ASSUMED_WHOLE_LOOP: &str = r#"export function root() {
/** @perf O(N^3) */
for(;;) {}
}
"#;

#[test]
fn assumed_whole_loop() {
    fallback_case(ASSUMED_WHOLE_LOOP, "O(N^3)", false, false, false, true);
}

const COLD_ONLY: &str = r#"function deferred() {}
export function root() {
/** @perf cold */
{
/** @perf O(N^3) */
void 0;
deferred();
}
}
"#;

#[test]
fn cold_only() {
    fallback_case(COLD_ONLY, "O(N^3)", true, false, false, false);
}

const UNAVAILABLE_MULTIPLIER: &str = r#"function deferred() {}
export function root(xs:number[]) {
for(const x of xs) {
/** @perf O(N^3) */
void x;
deferred();
}
}
"#;

#[test]
fn unavailable_multiplier() {
    fallback_case(UNAVAILABLE_MULTIPLIER, "O(1)", true, true, false, false);
}

const ASSUMED_STATEMENT_BEFORE: &str = r#"function deferred() {}
export function root() {
/** @perf O(N^3) */
void 0;
deferred();
}
"#;

#[test]
fn assumed_statement_before() {
    fallback_case(
        ASSUMED_STATEMENT_BEFORE,
        "O(N^3)",
        true,
        false,
        false,
        false,
    );
}

const READY_CALLEE_BEFORE: &str = r#"/** @perf O(N^3) */
function known() {}
function deferred() {}
export function root() {
known(); deferred();
}
"#;

#[test]
fn ready_callee_before() {
    fallback_case(READY_CALLEE_BEFORE, "O(N^3)", true, false, true, false);
}

const ASSUMED_STATEMENT_AFTER: &str = r#"function deferred() {}
export function root() {
deferred();
/** @perf O(N^3) */
void 0;
}
"#;

#[test]
fn assumed_statement_after() {
    fallback_case(ASSUMED_STATEMENT_AFTER, "O(N^3)", true, false, false, false);
}

const READY_CALLEE_AFTER: &str = r#"/** @perf O(N^3) */
function known() {}
function deferred() {}
export function root() {
deferred(); known();
}
"#;

#[test]
fn ready_callee_after() {
    fallback_case(READY_CALLEE_AFTER, "O(N^3)", true, false, true, false);
}

const COLD_REJECTED_SITE: &str = r#"function deferred() {}
export function root() {
/** @perf O(N^3) */
void 0;
/** @perf cold */
deferred();
}
"#;

#[test]
fn cold_rejected_site() {
    fallback_case(COLD_REJECTED_SITE, "O(N^3)", true, false, false, false);
}

const HOT_REJECTED_SITE: &str = r#"function deferred() {}
export function root() {
/** @perf O(N^3) */
void 0;
/** @perf hot */
deferred();
}
"#;

#[test]
fn hot_rejected_site() {
    fallback_case(HOT_REJECTED_SITE, "O(1)", true, false, false, false);
}

const COLD_REJECTED_HOT_KNOWN: &str = r#"function deferred() {}
export function root() {
/** @perf hot @perf O(N^3) */
void 0;
/** @perf cold */
deferred();
}
"#;

#[test]
fn cold_rejected_hot_known() {
    fallback_case(COLD_REJECTED_HOT_KNOWN, "O(N^3)", true, false, false, false);
}

fn ordinary_wide_source(statements: usize) -> String {
    let mut source = String::from("export function root() {\n");

    for index in 0..statements {
        source.push_str(&format!("void {index};\n"));
    }

    source.push_str("}\n");

    source
}

#[test]
fn ordinary_wide_counts_and_measured_reservation_scale_linearly() {
    let (small, small_reservation) = wide_observations(&ordinary_wide_source(1000));
    let (large, large_reservation) = wide_observations(&ordinary_wide_source(2000));

    assert!(large_reservation > small_reservation);
    assert!(
        large_reservation <= 2 * small_reservation,
        "nonlinear reservation: {small_reservation}, {large_reservation}"
    );
    assert!(large.consumed(Event::WalkerNode) > small.consumed(Event::WalkerNode));

    for event in EVENTS {
        assert!(
            large.consumed(event) <= 2 * small.consumed(event),
            "nonlinear {event:?}: small={small:?}, large={large:?}"
        );
    }

    eprintln!("wide source 1000/2000: reserved WalkerNode={small_reservation}/{large_reservation}; work={small:?}/{large:?}");
}

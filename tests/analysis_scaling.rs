use std::collections::BTreeSet;

use olint::analysis::work::{Event, Limits, Snapshot};
use olint::analysis::Analysis;
use olint::cost::{Cost, Part};
use olint::declarations::FunctionId;
use olint::effects::Effects;
use olint::project::FileId;
use olint::summaries::{SchedulerLimits, SchedulerStats};
use olint::unknowns::UnknownReason;

mod support;

use support::{
    assert_scheduler_terminal as assert_terminal, function_of_name, run_with_source, summary_of,
    unknown_reasons as reasons,
};

fn chain_source(count: usize, reverse: bool) -> String {
    let mut declarations: Vec<_> = (0..count)
        .map(|index| {
            if index + 1 == count {
                format!("function f{index}() {{ return 1; }}")
            } else {
                format!("function f{index}() {{ f{}(); return 1; }}", index + 1)
            }
        })
        .collect();

    if reverse {
        declarations.reverse();
    }

    declarations.join("\n")
}

fn assert_acyclic_counts(stats: SchedulerStats, tasks: usize, pairs: u64, sites: u64, passes: u64) {
    assert_terminal(stats);
    assert_eq!(stats.tasks, tasks, "{stats:?}");

    for (event, expected) in [
        (Event::TaskKey, tasks as u64),
        (Event::Publication, tasks as u64),
        (Event::DependencyPair, pairs),
        (Event::RuntimePair, pairs),
        (Event::InvocationSite, sites),
    ] {
        assert_eq!(stats.work.consumed(event), expected, "{event:?}: {stats:?}");
    }

    assert!(stats.work.consumed(Event::BodyPass) <= passes, "{stats:?}");
    assert!(stats.maximum_body_passes <= 2, "{stats:?}");
    assert!(
        stats.work.consumed(Event::QueuePush) <= 2 * tasks as u64 + pairs,
        "{stats:?}"
    );
}

fn assert_cached_root(analysis: &mut Analysis<'_, '_>, file: FileId, name: &str, part: &Part) {
    let before = analysis.scheduler_stats();
    let again = summary_of(analysis, file, name);

    assert_eq!(&again, part);
    assert_terminal(analysis.scheduler_stats());
    assert_eq!(analysis.scheduler_stats().generation, before.generation);
    assert_eq!(analysis.scheduler_stats().work, before.work);
    assert_eq!(analysis.scheduler_stats().tasks, before.tasks);
}

fn function_id(analysis: &Analysis<'_, '_>, file: FileId, name: &str) -> FunctionId {
    FunctionId {
        file,
        node: function_of_name(analysis.project, file, name).node_id(),
    }
}

#[test]
fn direct_chains_finish_in_bounded_passes_in_both_declaration_orders() {
    for count in [128, 512] {
        let mut forward: Option<Snapshot> = None;

        for reverse in [false, true] {
            run_with_source(&chain_source(count, reverse), |analysis, file| {
                let part = summary_of(analysis, file, "f0");

                assert_eq!(part.cost, Cost::ONE);
                assert!(part.is_complete());

                let stats = analysis.scheduler_stats();

                assert_acyclic_counts(
                    stats,
                    count,
                    count as u64 - 1,
                    count as u64 - 1,
                    2 * count as u64 - 1,
                );
                assert_eq!(stats.work.consumed(Event::DependencyWake), count as u64 - 1);
                assert_cached_root(analysis, file, "f0", &part);

                for index in (0..count).rev() {
                    let name = format!("f{index}");
                    let member = summary_of(analysis, file, &name);
                    let records = analysis.summary_records_for(function_id(analysis, file, &name));

                    assert_eq!(member.cost, Cost::ONE);
                    assert!(member.is_complete());
                    assert_eq!(records.len(), 1);
                    assert_eq!(records[0].effects, Effects::default());
                }

                assert_eq!(analysis.scheduler_stats().work, stats.work);
                assert_terminal(analysis.scheduler_stats());

                if let Some(expected) = forward {
                    assert_eq!(
                        stats.work, expected,
                        "declaration order changed scheduler work"
                    );
                } else {
                    forward = Some(stats.work);
                }
            });
        }
    }
}

#[test]
fn wide_callers_discover_all_siblings_before_retry() {
    for count in [64, 256] {
        let declarations = (0..count)
            .map(|index| format!("function leaf{index}() {{ return {index}; }}"))
            .collect::<String>();
        let calls = (0..count)
            .map(|index| format!("leaf{index}();"))
            .collect::<String>();
        let source = format!("{declarations} export function root() {{ {calls} return 1; }}");

        run_with_source(&source, |analysis, file| {
            let part = summary_of(analysis, file, "root");
            let stats = analysis.scheduler_stats();

            assert_eq!(part.cost, Cost::ONE);
            assert!(part.is_complete());
            assert_acyclic_counts(
                stats,
                count + 1,
                count as u64,
                count as u64,
                count as u64 + 2,
            );
            assert_eq!(stats.work.consumed(Event::DependencyWake), count as u64);
            assert_cached_root(analysis, file, "root", &part);

            for index in 0..count {
                assert!(summary_of(analysis, file, &format!("leaf{index}")).is_complete());
            }

            assert_eq!(analysis.scheduler_stats().work, stats.work);
        });
    }
}

#[test]
fn finite_repeated_function_identity_is_not_a_recursive_task() {
    run_with_source("function invoke(cb:()=>number){return cb()} function f(){return invoke(g)} function g(){return 1} export function root(){return invoke(f)}", |analysis, file| {
        let part = complete_one(analysis,file,"root");

        assert_acyclic_counts(analysis.scheduler_stats(), 5, 4, 4, 9);
        assert_eq!(analysis.summary_records_for(function_id(analysis, file, "invoke")).len(), 2);
        assert_cached_root(analysis, file, "root", &part);
    });
}

#[test]
fn unused_self_callbacks_are_descriptors_without_body_dependencies() {
    for argument in ["root", "()=>{root();return 1}"] {
        let source = format!("function ignore(cb:()=>number){{return 1}} export function root():number{{return ignore({argument})}}");

        run_with_source(&source, |analysis, file| {
            let part = complete_one(analysis, file, "root");

            assert_acyclic_counts(analysis.scheduler_stats(), 2, 1, 1, 3);
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn growing_callback_captures_stop_at_finite_admission_limits() {
    let source = "function grow(cb:()=>void,xs:number[]){cb();grow(()=>{for(const x of xs)cb()},xs)} export function root(xs:number[]){grow(()=>{},xs)}";

    for limit in [1, 4] {
        run_with_source(source, |analysis, file| {
            analysis
                .set_scheduler_limits(SchedulerLimits {
                    specializations_per_function: limit,
                    ..SchedulerLimits::default()
                })
                .unwrap();

            let part = summary_of(analysis, file, "root");
            let why = reasons(analysis, part.unknowns);
            let stats = analysis.scheduler_stats();

            assert_unresolved_cycle(&part, &why);
            assert_terminal(stats);
            assert!(stats.tasks <= 4 * (limit + 1), "{stats:?}");
            assert!(
                analysis
                    .summary_records_for(function_id(analysis, file, "grow"))
                    .len()
                    <= limit + 1
            );
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn task_exhaustion_retains_ready_assumed_work_and_reuses_the_result() {
    for calls in ["known();middle()", "middle();known()"] {
        let source = format!("/** @perf O(N^3) */ function known(){{}} function leaf(){{}} function middle(){{leaf()}} export function root(){{{calls}}}");

        run_with_source(&source, |analysis, file| {
            limit_work(analysis, Event::TaskKey, 3);

            let known = summary_of(analysis, file, "known");

            assert!(known.is_complete());
            assert_eq!(analysis.scheduler_stats().tasks, 1);
            assert_terminal(analysis.scheduler_stats());

            let function = function_of_name(analysis.project, file, "root");
            let part = summary_of(analysis, file, "root");
            let stats = analysis.scheduler_stats();

            assert!(!part.is_complete());
            assert_class(analysis, file, function, &part, "O(N^3)", "");
            assert!(reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion));
            assert_eq!(stats.work.consumed(Event::TaskKey), 3);
            assert!(stats.work.exhausted(Event::TaskKey));
            assert!(stats.work.consumed(Event::BodyPass) > 0);
            assert_terminal(stats);
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn diamond_dependencies_deduplicate_pairs_without_merging_call_sites() {
    let declarations = [
        "function shared() { return 1; }",
        "function left() { shared(); shared(); return 1; }",
        "function right() { shared(); return 1; }",
        "export function root() { left(); right(); return 1; }",
    ];

    for reverse in [false, true] {
        let mut ordered = declarations;

        if reverse {
            ordered.reverse();
        }

        for warm_members in [None, Some(["left", "right"]), Some(["right", "left"])] {
            run_with_source(&ordered.join("\n"), |analysis, file| {
                if let Some(names) = warm_members {
                    for name in names {
                        assert!(summary_of(analysis, file, name).is_complete());
                    }
                }

                let part = summary_of(analysis, file, "root");
                let stats = analysis.scheduler_stats();

                assert_eq!(part.cost, Cost::ONE);
                assert!(part.is_complete());
                assert_acyclic_counts(stats, 4, 4, 5, 7);
                assert_cached_root(analysis, file, "root", &part);

                for name in ["shared", "right", "left"] {
                    assert!(summary_of(analysis, file, name).is_complete());
                }

                assert_eq!(analysis.scheduler_stats().work, stats.work);
            });
        }
    }
}

#[test]
fn forwarding_and_aliases_reuse_one_known_callback_specialization() {
    run_with_source(
        "function invoke(cb:()=>number){return cb()}\nfunction forward(cb:()=>number){return invoke(cb)}\nfunction pure(){return 1}\nconst alias=pure; const other=alias;\nexport function root(){forward(pure);forward(other);forward(pure);return 1}",
        |analysis, file| {
            let part = complete_one(analysis,file,"root");

            assert_acyclic_counts(analysis.scheduler_stats(), 4, 3, 5, 7);

            for name in ["forward", "invoke", "pure"] {
                let records = analysis.summary_records_for(function_id(analysis, file, name));

                assert_eq!(records.len(), 1, "{name}");
                assert_eq!(records[0].effects, Effects::default(), "{name}");
            }

            assert_cached_root(analysis, file, "root", &part);
        },
    );
}

#[test]
fn captured_callback_facts_separate_impure_work_and_reuse_pure_work() {
    let source = "declare function opaque():void;\nfunction pure(){return 1}\nfunction impure(){opaque();return 1}\nfunction outer(cb:()=>void){function inner(){cb()} inner()}\nexport function root(){outer(pure);outer(impure);outer(pure)}\nexport function pureRoot(){outer(pure)}";

    run_with_source(source, |analysis, file| {
        let part = summary_of(analysis, file, "root");

        assert_eq!(part.cost, Cost::ONE);
        assert!(!part.is_complete());
        assert_eq!(
            reasons(analysis, part.unknowns),
            BTreeSet::from([UnknownReason::Target])
        );
        assert_terminal(analysis.scheduler_stats());
        assert_cached_root(analysis, file, "root", &part);

        for name in ["outer", "inner"] {
            let records: Vec<_> = analysis
                .summary_records_for(function_id(analysis, file, name))
                .into_iter()
                .cloned()
                .collect();
            let mut outcomes = Vec::new();

            assert_eq!(
                records.len(),
                2,
                "{name} must retain exactly the two callback/capture specializations"
            );

            for record in records {
                let selected = record
                    .reading
                    .total(&mut analysis.unknowns, &mut analysis.traces);
                let why = reasons(analysis, selected.unknowns);

                assert_eq!(selected.cost, Cost::ONE);
                outcomes.push((
                    selected.is_complete(),
                    !record.effects.unknown_reachable.is_empty(),
                ));

                if selected.is_complete() {
                    assert_eq!(record.effects, Effects::default());
                } else {
                    assert_eq!(why, BTreeSet::from([UnknownReason::Target]));
                }
            }

            outcomes.sort();
            assert_eq!(outcomes, [(false, true), (true, false)], "{name}");
        }

        let before = analysis.scheduler_stats();
        let pure = summary_of(analysis, file, "pureRoot");

        assert!(pure.is_complete());
        assert_eq!(pure.cost, Cost::ONE);
        assert_eq!(analysis.scheduler_stats().tasks, before.tasks + 1);
        assert_eq!(
            analysis.scheduler_stats().work.consumed(Event::Publication),
            before.work.consumed(Event::Publication) + 1
        );
        assert_eq!(
            analysis
                .summary_records_for(function_id(analysis, file, "inner"))
                .len(),
            2
        );
        assert_cached_root(analysis, file, "pureRoot", &pure);
    });
}

#[test]
fn recurrence_members_keep_local_work_and_cached_member_results() {
    let source = "declare const xs:number[];\nfunction a(){\nfor(const item of xs)void item;\nb();\n}\nfunction b(){\nfor(const outer of xs)for(const inner of xs)void inner;\na();\n}";
    let mut first_order = None;

    for order in [["a", "b"], ["b", "a"]] {
        run_with_source(source, |analysis, file| {
            let _ = summary_of(analysis, file, order[0]);
            let before = analysis.scheduler_stats();
            let _ = summary_of(analysis, file, order[1]);

            assert_eq!(analysis.scheduler_stats().work, before.work);
            assert_terminal(analysis.scheduler_stats());

            let mut outcomes = Vec::new();

            for (name, cost, loop_text) in [
                ("a", "O(N)", "for(const item"),
                ("b", "O(N^2)", "for(const outer"),
            ] {
                let function = function_of_name(analysis.project, file, name);
                let records: Vec<_> = analysis
                    .member_local_records_for(FunctionId {
                        file,
                        node: function.node_id(),
                    })
                    .into_iter()
                    .cloned()
                    .collect();

                assert_eq!(records.len(), 1, "{name}");

                let local = records[0]
                    .reading
                    .clone()
                    .total(&mut analysis.unknowns, &mut analysis.traces);
                let loop_line = analysis
                    .project
                    .line_of(file, source.find(loop_text).unwrap() as u32);

                assert_eq!(
                    support::legacy_class_of(analysis, file, function, &local.cost),
                    Cost::parse(cost).unwrap(),
                    "{name}"
                );
                assert!(
                    support::trace_nodes(&analysis.traces, local.trace)
                        .iter()
                        .any(|factor| factor.site.line == loop_line),
                    "{name} lost its own loop origin"
                );

                let part = summary_of(analysis, file, name);
                let why = reasons(analysis, part.unknowns);

                assert!(!part.is_complete());
                assert!(why.contains(&UnknownReason::Recurrence));
                outcomes.push((part.cost, part.preference, why));
            }

            assert_eq!(analysis.scheduler_stats().work, before.work);

            if let Some(expected) = &first_order {
                assert_eq!(&outcomes, expected, "request order changed member results");
            } else {
                first_order = Some(outcomes);
            }
        });
    }
}

#[test]
fn captured_arrow_specialization_regression_finishes_incomplete() {
    let source = "function expensive(xs:number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }\nfunction cheap() {}\nfunction visit(cb:()=>void,recur:boolean,data:number[]) {\n    if(recur) visit(()=>expensive(data),false,data);\n    cb();\n}\nexport function entry(data:number[]) { visit(cheap,true,data); }\n";

    run_with_source(source, |analysis, file| {
        let limit = 4;

        analysis
            .set_scheduler_limits(SchedulerLimits {
                specializations_per_function: limit,
                ..SchedulerLimits::default()
            })
            .unwrap();

        let part = summary_of(analysis, file, "entry");
        let why = reasons(analysis, part.unknowns);
        let stats = analysis.scheduler_stats();

        assert_unresolved_cycle(&part, &why);
        assert!(stats.tasks <= 5 * (limit + 1), "{stats:?}");
        assert_terminal(stats);
        assert_cached_root(analysis, file, "entry", &part);
    });
}

#[test]
fn independent_graph_and_callback_limits_publish_stable_incomplete_results() {
    let simple = "function leaf(){return 1} export function root(){leaf()}";
    let callback = "function invoke(cb:()=>number){return cb()} function pure(){return 1} export function root(){invoke(pure)}";
    let capture =
        "function invoke(cb:()=>void){cb()} export function root(cb:()=>void){invoke(()=>cb())}";

    for (event, source) in [
        (Event::RuntimePair, simple),
        (Event::InvocationSite, simple),
        (Event::DependencyPair, simple),
        (Event::CallbackDescriptor, callback),
        (Event::CaptureEdge, capture),
    ] {
        run_with_source(source, |analysis, file| {
            limit_work(analysis, event, 0);

            let part = summary_of(analysis, file, "root");
            let stats = analysis.scheduler_stats();

            assert!(!part.is_complete(), "{event:?}");
            assert!(
                reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion),
                "{event:?}"
            );
            assert_eq!(stats.work.consumed(event), 0, "{event:?}");
            assert!(stats.work.exhausted(event), "{event:?}");
            assert_terminal(stats);
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn visit_and_prepass_limits_include_reserved_fallback_work() {
    for (event, limit) in [
        (Event::BodyPass, 4),
        (Event::WalkerNode, 128),
        (Event::BudgetPrepassNode, 128),
        (Event::EffectPrepassNode, 128),
    ] {
        let source = if event == Event::EffectPrepassNode {
            format!(
                "declare const xs:number[]; export function f0(){{for(const item of xs){{ {} }} }}",
                (0..128)
                    .map(|index| format!("void {index};"))
                    .collect::<String>()
            )
        } else {
            chain_source(128, false)
        };

        run_with_source(&source, |analysis, file| {
            limit_work(analysis, event, limit);

            let part = summary_of(analysis, file, "f0");
            let stats = analysis.scheduler_stats();

            assert!(
                stats.tasks > 0,
                "the root and its fallback must be admitted: {event:?}"
            );
            assert!(!part.is_complete(), "{event:?}");
            assert!(
                reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion),
                "{event:?}"
            );
            assert!(stats.work.consumed(event) <= limit, "{event:?}: {stats:?}");
            assert!(stats.work.exhausted(event), "{event:?}");
            assert_terminal(stats);
            assert_cached_root(analysis, file, "f0", &part);
        });
    }
}

#[test]
fn fallback_preserves_completed_loops_and_source_selection() {
    for (mark, expected, partial) in [
        ("", "O(N^3)", true),
        ("/** @perf cold */", "O(N^3)", false),
        ("/** @perf hot */", "O(1)", true),
    ] {
        let source=format!("function deferred(){{}} export function root(xs:number[]){{\nfor(const a of xs)for(const b of xs)for(const c of xs)void c;\n{mark}\ndeferred();\n}}");

        run_with_source(&source, |analysis, file| {
            limit_work(analysis, Event::DependencyPair, 0);

            let function = function_of_name(analysis.project, file, "root");
            let part = summary_of(analysis, file, "root");

            assert_class(analysis, file, function, &part, expected, "{mark}");
            assert_eq!(!part.is_complete(), partial, "{mark}");
            assert!(
                analysis
                    .scheduler_stats()
                    .work
                    .fallback()
                    .count(Event::BodyPass)
                    > 0
            );
            assert_terminal(analysis.scheduler_stats());
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn cyclic_discovery_and_retry_limits_always_reach_terminal_states() {
    let source="function invoke(cb:()=>void){cb()} function a(){b()} function b(){a();invoke(helper)} function helper(){return 1} export function root(){a()}";

    for event in [
        Event::QueuePush,
        Event::GraphNode,
        Event::GraphEdge,
        Event::DependencyWake,
        Event::BodyPass,
    ] {
        for limit in 0..12 {
            run_with_source(source, |analysis, file| {
                limit_work(analysis, event, limit);

                let part = summary_of(analysis, file, "root");

                assert!(!part.is_complete(), "{event:?} {limit}");
                assert_terminal(analysis.scheduler_stats());
                assert!(analysis.scheduler_stats().work.consumed(event) <= limit);
            });
        }
    }
}

#[test]
fn three_member_recurrence_preserves_distant_known_work() {
    let source="declare const xs:number[]; function a(){b()} function b(){c()} function c(){for(const first of xs)for(const second of xs)for(const third of xs)void third;a()}";

    for order in [["a", "b", "c"], ["c", "b", "a"]] {
        run_with_source(source, |analysis, file| {
            for name in order {
                let function = function_of_name(analysis.project, file, name);
                let part = summary_of(analysis, file, name);

                assert_class(analysis, file, function, &part, "O(N^3)", "{name}");
                assert!(reasons(analysis, part.unknowns).contains(&UnknownReason::Recurrence));
            }

            assert_terminal(analysis.scheduler_stats());
        });
    }
}

#[test]
fn recurrence_contexts_preserve_selection_and_independent_loop_assumptions() {
    for (body, expected, partial, bound) in [
        ("b();", "O(N^3)", true, false),
        (
            "/** @perf hot @perf O(1) */\nvoid 0; b();",
            "O(1)",
            false,
            false,
        ),
        ("for(const item of xs)b();", "O(N^3)", true, true),
        (
            "/** @perf bounded */\nfor(const item of xs)b();",
            "O(N^3)",
            true,
            false,
        ),
    ] {
        let source=format!("declare const xs:number[]; function a(){{\n{body}\n}} function b(){{c()}} function c(){{for(const x of xs)for(const y of xs)for(const z of xs)void z;a()}} export function root(){{a()}}");

        run_with_source(&source, |analysis, file| {
            let (part, function) = root_summary(analysis, file);

            assert_class(analysis, file, function, &part, expected, "{body}");
            assert_eq!(!part.is_complete(), partial, "{body}");
            assert_eq!(
                reasons(analysis, part.unknowns).contains(&UnknownReason::Bound),
                bound,
                "{body}"
            );
            assert_terminal(analysis.scheduler_stats());
        });
    }

    for calls in [
        "/** @perf cold */\nb(); c();",
        "c();\n/** @perf cold */\nb();",
    ] {
        let source=format!("function a(){{\n{calls}\n}} function b(){{\n/** @perf hot @perf O(N^3) */\nvoid 0;c();\n}} function c(){{b();a()}} export function root(){{a()}}");

        run_with_source(&source, |analysis, file| {
            let (part, function) = root_summary(analysis, file);

            assert_class(analysis, file, function, &part, "O(N^3)", "");
            assert!(!part.is_complete());
            assert_terminal(analysis.scheduler_stats());
        });
    }
}

#[test]
fn dense_recurrence_contexts_stop_before_their_work_limit() {
    let source = (0..4)
        .map(|index| {
            format!(
                "function f{index}(){{\n/** @perf O(N^3) */\nvoid 0;{}\n}}",
                (0..4)
                    .map(|child| format!("f{child}();"))
                    .collect::<String>()
            )
        })
        .collect::<String>();

    for limit in [0, 1, 4, 16] {
        run_with_source(&source, |analysis, file| {
            limit_work(analysis, Event::RecurrenceContext, limit);

            let part = summary_of(analysis, file, "f0");
            let function = function_of_name(analysis.project, file, "f0");

            assert_class(analysis, file, function, &part, "O(N^3)", "");
            assert!(!part.is_complete());
            assert!((0..4).any(|index| analysis
                .summary_records_for(function_id(analysis, file, &format!("f{index}")))
                .iter()
                .any(|record| reasons(analysis, record.reading.main.unknowns)
                    .contains(&UnknownReason::ResourceExhaustion))));
            assert!(analysis
                .scheduler_stats()
                .work
                .exhausted(Event::RecurrenceContext));
            assert!(
                analysis
                    .scheduler_stats()
                    .work
                    .consumed(Event::RecurrenceContext)
                    <= limit
            );
            assert_terminal(analysis.scheduler_stats());
            assert_cached_root(analysis, file, "f0", &part);
        });
    }
}

#[test]
fn fallback_preserves_authoritative_and_ready_work_in_both_orders() {
    for body in [
        "known(); deferred();",
        "deferred(); known();",
        "/** @perf bounded */\nfor(;;){known();deferred();break;}",
        "for(;;){known();deferred();}",
    ] {
        let source=format!("/** @perf O(N^3) */\nfunction known(){{}} function deferred(){{}} export function root(){{\n{body}\n}}");

        run_with_source(&source, |analysis, file| {
            limit_work(analysis, Event::DependencyPair, 0);

            let _ = summary_of(analysis, file, "known");
            let function = function_of_name(analysis.project, file, "root");
            let part = summary_of(analysis, file, "root");

            assert_class(analysis, file, function, &part, "O(N^3)", "{body}");
            assert!(reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion));
            assert_eq!(
                reasons(analysis, part.unknowns).contains(&UnknownReason::Bound),
                body.starts_with("for")
            );
            assert!(
                analysis
                    .scheduler_stats()
                    .work
                    .fallback()
                    .count(Event::BodyPass)
                    > 0
            );
            assert_terminal(analysis.scheduler_stats());
        });
    }
}

fn limit_work(analysis: &mut Analysis<'_, '_>, event: Event, limit: u64) {
    analysis
        .set_scheduler_limits(SchedulerLimits {
            work: Limits::uniform(100_000).with(event, limit),
            ..SchedulerLimits::default()
        })
        .unwrap();
}

fn complete_one(analysis: &mut Analysis<'_, '_>, file: FileId, name: &str) -> Part {
    let part = summary_of(analysis, file, name);

    assert_eq!(part.cost, Cost::ONE);
    assert!(part.is_complete());

    part
}

#[test]
fn failed_discovery_wave_reuses_source_invocations_without_capture_rescans() {
    for count in [16, 64] {
        let parameters = (0..count)
            .map(|index| format!("p{index}:number"))
            .collect::<Vec<_>>()
            .join(",");
        let source=format!("function warm(){{}}\n/** @perf O(N^3) */\nfunction known(){{}} export function root({parameters}){{{}known();}}","warm();".repeat(count));

        run_with_source(&source, |analysis, file| {
            limit_work(analysis, Event::DiscoveryWave, 0);

            let (part, function) = root_summary(analysis, file);
            let expected = analysis
                .bind_function_cost(file, function, &Cost::parse("O(N^3)").unwrap())
                .unwrap();

            assert!(
                part.cost == expected
                    || part.cost == Cost::maximum(vec![Cost::ONE, expected]).unwrap()
            );
            assert!(!reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion));

            let stats = analysis.scheduler_stats();

            assert!(stats.work.exhausted(Event::DiscoveryWave));
            assert!(stats.work.fallback().count(Event::BodyPass) > 0);
            assert_eq!(stats.work.fallback().count(Event::CaptureEdge), 0);
            assert_eq!(stats.work.fallback().count(Event::BudgetPrepassNode), 0);
            assert_terminal(stats);
            assert_cached_root(analysis, file, "root", &part);
        });
    }
}

#[test]
fn context_exhaustion_keeps_resource_at_the_selected_invocation() {
    for limit in [0, 1, 64] {
        run_with_source(
            "export function root(){\n/** @perf hot */\nvoid 0;\nroot();\n}",
            |analysis, file| {
                limit_work(analysis, Event::RecurrenceContext, limit);

                let part = complete_one(analysis, file, "root");

                assert_eq!(part.preference, olint::cost::Preference::Hot);
                assert_terminal(analysis.scheduler_stats());
            },
        );
    }
}

#[test]
fn mid_context_body_exhaustion_reuses_reserved_selected_work() {
    let source =
        "function a(){b();\n/** @perf O(N^3) */\nvoid 0;} function b(){a();void 0;void 1;void 2;}";
    let mut exhausted_context = false;

    for limit in 50..100 {
        run_with_source(source, |analysis, file| {
            limit_work(analysis, Event::WalkerNode, limit);

            let part = summary_of(analysis, file, "a");
            let stats = analysis.scheduler_stats();

            if stats.work.exhausted(Event::WalkerNode)
                && stats.work.consumed(Event::RecurrenceContext) > 0
            {
                exhausted_context = true;
                let function = function_of_name(analysis.project, file, "a");

                assert_class(analysis, file, function, &part, "O(N^3)", "");
                assert!(
                    reasons(analysis, part.unknowns).contains(&UnknownReason::ResourceExhaustion)
                );
            }

            assert_terminal(stats);
        });
    }

    assert!(exhausted_context);
}

fn assert_class<'a>(
    analysis: &mut Analysis<'_, 'a>,
    file: FileId,
    function: olint::declarations::FunctionNode<'a>,
    part: &Part,
    expected: &str,
    context: &str,
) {
    assert_eq!(
        support::legacy_class_of(analysis, file, function, &part.cost),
        Cost::parse(expected).unwrap(),
        "{context}"
    );
}

fn assert_unresolved_cycle(part: &Part, why: &BTreeSet<UnknownReason>) {
    assert!(!part.is_complete());
    assert!(
        why.contains(&UnknownReason::Recurrence)
            || why.contains(&UnknownReason::ResourceExhaustion),
        "{why:?}"
    );
}

fn root_summary<'a>(
    analysis: &mut Analysis<'_, 'a>,
    file: FileId,
) -> (Part, olint::declarations::FunctionNode<'a>) {
    let function = function_of_name(analysis.project, file, "root");

    (summary_of(analysis, file, "root"), function)
}

#[test]
fn context_exhaustion_keeps_an_independent_local_loop_prefix() {
    run_with_source("declare const xs:number[]; function a(){for(const x of xs)for(const y of xs)for(const z of xs)void z;b()} function b(){a()}",|analysis,file| {
        limit_work(analysis,Event::RecurrenceContext,0);

        let part=summary_of(analysis,file,"a");
        let function=function_of_name(analysis.project,file,"a");

        assert_class(analysis,file,function,&part,"O(N^3)","local prefix");
        assert!(reasons(analysis,part.unknowns).contains(&UnknownReason::ResourceExhaustion));
        assert_terminal(analysis.scheduler_stats());
    });
}

#[test]
fn failed_membership_union_runs_the_reserved_pass() {
    let source="function a(){a()} function b(){b()} export function root(){a();b();\n/** @perf O(N^3) */\nvoid 0;}";
    let mut preparation = 0;

    run_with_source(source, |analysis, file| {
        let _ = summary_of(analysis, file, "a");
        let _ = summary_of(analysis, file, "b");
        preparation = analysis.scheduler_stats().work.consumed(Event::GraphNode);
    });
    run_with_source(source, |analysis, file| {
        limit_work(analysis, Event::GraphNode, preparation + 1);

        let _ = summary_of(analysis, file, "a");
        let _ = summary_of(analysis, file, "b");
        let before = analysis
            .scheduler_stats()
            .work
            .fallback()
            .count(Event::BodyPass);
        let (part, function) = root_summary(analysis, file);

        assert_class(
            analysis,
            file,
            function,
            &part,
            "O(N^3)",
            "membership union",
        );

        let stats = analysis.scheduler_stats();

        assert!(stats.work.exhausted(Event::GraphNode));
        assert!(stats.work.fallback().count(Event::BodyPass) > before);
        assert_terminal(stats);
    });
}

fn compiler_sites_of(count: usize) -> (String, Vec<(u32, u32)>) {
    let mut source = String::new();
    let mut sites = Vec::new();

    for index in 0..count {
        let line = format!(
            "export function f{index}(xs: number[]) {{ return xs.map((x) => x + {index}); }}\n"
        );
        let offset = source.len() + line.find("xs.map").expect("call site");

        sites.push((offset as u32, (offset + 2) as u32));
        sites.push((offset as u32, (offset + 6) as u32));
        source.push_str(&line);
    }

    (source, sites)
}

fn compiler_counts_of(
    source: &str,
    sites: &[(u32, u32)],
) -> (Vec<Option<olint::tsc::TscAnswer>>, olint::tsc::TscCounts) {
    let directory = support::project_of(&[
        (
            "tsconfig.json",
            r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["index.ts"]}"#,
        ),
        ("index.ts", source),
    ]);
    let file = directory
        .path()
        .join("index.ts")
        .to_string_lossy()
        .into_owned();
    let queries: Vec<olint::tsc::Query> = sites
        .iter()
        .map(|(pos, end)| {
            if end - pos == 2 {
                olint::tsc::Query::Type {
                    file: file.clone(),
                    pos: *pos,
                    end: *end,
                }
            } else {
                olint::tsc::Query::Callee {
                    file: file.clone(),
                    pos: *pos,
                    end: *end,
                }
            }
        })
        .collect();
    let (reply, counts) = olint::tsc::ask_counted(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        &directory.path().join("tsconfig.json"),
        &queries,
    )
    .expect("the compiler helper answers with counts");

    (reply.answers, counts)
}

#[test]
fn doubling_compiler_queries_reuses_one_span_index() {
    let (source, sites) = compiler_sites_of(200);
    let (half_answers, half) = compiler_counts_of(&source, &sites[..sites.len() / 2]);
    let (answers, full) = compiler_counts_of(&source, &sites);

    assert_eq!(answers[..half_answers.len()], half_answers[..]);
    assert!(answers.iter().all(Option::is_some));
    assert_eq!((half.programs, half.checkers), (1, 1));
    assert_eq!((full.programs, full.checkers), (1, 1));
    assert_eq!((half.indexed_files, full.indexed_files), (1, 1));
    assert_eq!(half.indexed_nodes, full.indexed_nodes);
    assert_eq!((half.lookups, full.lookups), (200, 400));

    let (larger, larger_sites) = compiler_sites_of(400);
    let (_, doubled) = compiler_counts_of(&larger, &larger_sites);

    assert_eq!(doubled.lookups, 800);
    assert!(doubled.indexed_nodes <= 2 * full.indexed_nodes + 1);

    for counts in [half, full, doubled] {
        assert_eq!(counts.visited_nodes, counts.indexed_nodes);
    }

    assert_eq!(half.visited_nodes, full.visited_nodes);

    let misses: Vec<(u32, u32)> = sites.iter().map(|(pos, end)| (pos + 1, end + 1)).collect();
    let (missed_answers, missed) = compiler_counts_of(&source, &misses);

    assert!(missed_answers.iter().all(Option::is_none));
    assert_eq!(missed.lookups, 400);
    assert_eq!(missed.visited_nodes, full.visited_nodes);
    assert!(doubled.visited_nodes <= 2 * full.visited_nodes + 1);
}

#[test]
fn an_empty_compiler_batch_builds_no_index_or_checker() {
    let (source, _) = compiler_sites_of(4);
    let (answers, counts) = compiler_counts_of(&source, &[]);

    assert!(answers.is_empty());
    assert_eq!(counts, olint::tsc::TscCounts::default());
}

fn callee_span_visits_of(count: usize, targets: usize, rounds: usize) -> (usize, usize) {
    let mut source: String = (0..count)
        .map(|index| format!("export function f{index}(xs: number[]) {{ return xs.length; }}\n"))
        .collect();
    let spans: Vec<(u32, u32)> = source
        .lines()
        .scan(0, |offset, line| {
            let start = *offset;

            *offset += line.len() + 1;

            Some((start as u32, (start + line.len()) as u32))
        })
        .collect();

    source.push_str(&format!(
        "export function run(o: any) {{ {} }}\n",
        (0..count)
            .map(|index| format!("o.f{index}([]);"))
            .collect::<String>()
    ));

    let files = [("tsconfig.json", "{}"), ("index.ts", source.as_str())];
    let mut found = (0, 0);

    support::run_in_project(&files, |project, root| {
        let file = support::file_of(project, root, "index.ts");
        let calls: Vec<_> = project
            .file(file)
            .semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                oxc_ast::AstKind::CallExpression(call) => Some(call),
                _ => None,
            })
            .collect();
        let mut analysis = Analysis::new(project, support::SYNTACTIC);

        analysis.set_pass(olint::types::TscPass::Recording);

        for call in &calls {
            analysis.callee_targets_of(file, call);
        }

        let answers = analysis
            .needed_queries()
            .into_iter()
            .map(|query| {
                let olint::tsc::Query::Callee { file, pos, end } = query else {
                    panic!("only callee sites are open");
                };
                let name = &source[pos as usize..end as usize];
                let index: usize = name["o.f".len()..].parse().expect("callee index");

                Some(olint::tsc::TscAnswer::Callee(olint::tsc::CalleeAnswer {
                    targets: (0..targets)
                        .map(|offset| {
                            let (start, end) = spans[(index + offset) % count];

                            olint::tsc::CalleeTarget {
                                file: file.clone(),
                                start,
                                end,
                            }
                        })
                        .collect(),
                    open: false,
                }))
            })
            .collect();

        analysis
            .take_answers(olint::tsc::TscReply {
                typescript: "5.9.3".to_string(),
                from: "typescript.js".to_string(),
                answers,
            })
            .expect("answers align");
        analysis.set_pass(olint::types::TscPass::Answering);

        for _ in 0..rounds {
            for call in &calls {
                let resolved = analysis.callee_targets_of(file, call);

                assert_eq!(resolved.known.len(), targets.min(count));
                assert!(!resolved.open);
            }
        }

        found = (
            analysis.declarations.resolution_stats().span_index_visits,
            project.file(file).semantic.nodes().len(),
        );
    });

    found
}

#[test]
fn callee_target_spans_index_each_file_once() {
    let (visits, nodes) = callee_span_visits_of(64, 1, 1);

    assert_eq!(visits, nodes);

    for (targets, rounds) in [(2, 1), (1, 3), (4, 2)] {
        assert_eq!(callee_span_visits_of(64, targets, rounds), (nodes, nodes));
    }

    let (doubled, doubled_nodes) = callee_span_visits_of(128, 2, 2);

    assert_eq!(doubled, doubled_nodes);
    assert!(doubled <= 2 * nodes + 1, "{doubled} {nodes}");
}

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

fn assert_linear_growth(base: &[u64], single: &[u64], double: &[u64]) {
    for (position, ((base, single), double)) in base.iter().zip(single).zip(double).enumerate() {
        assert!(single > base, "{position}: {single} {base}");
        assert_eq!(
            double - base,
            2 * (single - base),
            "{position}: {base} {single} {double}"
        );
    }
}

fn dispatch_source(sites: usize) -> String {
    let mut lines = vec![
        "class C0 { work(xs: number[]) { for (const x of xs) void x; } run(xs: number[]) { this.work(xs); } }".to_string(),
    ];

    for index in 1..4 {
        lines.push(format!(
            "class C{index} extends C{} {{ work(xs: number[]) {{ for (const x of xs) void x; }} }}",
            index - 1
        ));
    }

    for index in 0..sites {
        lines.push(format!(
            "export function f{index}(c: C{}, xs: number[]) {{ const o = {{ m: (ys: number[]) => ys.length }}; o.m = (ys: number[]) => ys.indexOf(1); o.m(xs); c.work(xs); c.run(xs); return xs.includes(0); }}",
            index % 4
        ));
        lines.push(format!(
            "export class K{index} {{ items: number[] = []; constructor() {{ this.items = []; }} run(xs: number[]) {{ this.items.push(xs.length); }} }}"
        ));
        lines.push(format!(
            "export function g{index}(target: any, name: string, xs: number[]) {{ target[name] = () => xs.length; return xs.includes(1); }}"
        ));
    }

    lines.join("\n")
}

fn dispatch_counts_of(sites: usize) -> Vec<u64> {
    let mut counts = Vec::new();

    run_with_source(&dispatch_source(sites), |analysis, _| {
        for (file, function) in analysis.reportable() {
            analysis.summarize(file, function);
        }

        let stats = analysis.scheduler_stats();

        assert_terminal(stats);

        counts = [
            Event::DispatchStep,
            Event::TaskKey,
            Event::BodyPass,
            Event::InvocationSite,
            Event::WalkerNode,
        ]
        .iter()
        .map(|event| stats.work.consumed(*event))
        .collect();
    });

    counts
}

#[test]
fn dispatch_work_grows_linearly_with_dispatch_sites() {
    let base = dispatch_counts_of(1);
    let single = dispatch_counts_of(33);
    let double = dispatch_counts_of(65);

    assert_linear_growth(&base, &single, &double);
}

fn prototype_chain_source(length: usize) -> String {
    let mut lines = vec![
        "function cube(xs: number[]) { for (const a of xs) for (const b of xs) void b; }"
            .to_string(),
    ];

    for index in 0..length {
        lines.push(format!("function C{index}() {{}}"));
        lines.push(format!(
            "(C{index} as any).prototype.m{index} = function (xs: number[]) {{ cube(xs); }};"
        ));
        lines.push(format!("const o{index}: any = {{ k{index}: cube }};"));
    }

    for index in 1..length {
        lines.push(format!(
            "Object.setPrototypeOf((C{index} as any).prototype, (C{} as any).prototype);",
            index - 1
        ));
        lines.push(format!("Object.setPrototypeOf(o{}, o{index});", index - 1));
    }

    lines.push(format!(
        "export function deep(xs: number[]) {{ o0.k{}(xs); new (C{} as any)().m0(xs); }}",
        length - 1,
        length - 1
    ));
    lines.push(
        "export function unrelated(xs: number[]) { const ys = [1, 2]; return ys.includes(1) && xs.length; }"
            .to_string(),
    );

    lines.join("\n")
}

fn prototype_chain_counts_of(length: usize) -> (u64, BTreeSet<UnknownReason>) {
    let mut found = (0, BTreeSet::new());

    run_with_source(&prototype_chain_source(length), |analysis, file| {
        summary_of(analysis, file, "deep");

        let unrelated = summary_of(analysis, file, "unrelated");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(
            !stats.work.exhausted(Event::DispatchStep),
            "{length}: {stats:?}"
        );
        assert!(
            stats.work.consumed(Event::DispatchStep) <= 200 * length as u64,
            "{length}: {stats:?}"
        );

        found = (
            stats.work.consumed(Event::DispatchStep),
            reasons(analysis, unrelated.unknowns),
        );
    });

    found
}

#[test]
fn prototype_chains_resolve_members_in_linear_dispatch_work() {
    let counts: Vec<u64> = [8, 16, 32, 64]
        .into_iter()
        .map(|length| {
            let (count, unrelated) = prototype_chain_counts_of(length);

            assert!(
                !unrelated.contains(&UnknownReason::Target),
                "{length}: {unrelated:?}"
            );

            count
        })
        .collect();

    for pair in counts.windows(2) {
        assert!(4 * pair[1] <= 9 * pair[0], "{counts:?}");
    }
}

fn inherited_same_member_tasks_of(length: usize) -> u64 {
    let mut lines = vec![
        "function cube(xs: number[]) { for (const a of xs) for (const b of xs) void b; }"
            .to_string(),
    ];

    for index in 0..length {
        lines.push(format!("function C{index}() {{}}"));
        lines.push(format!(
            "(C{index} as any).prototype.m = function (xs: number[]) {{ cube(xs); }};"
        ));
    }

    for index in 1..length {
        lines.push(format!(
            "Object.setPrototypeOf((C{index} as any).prototype, (C{} as any).prototype);",
            index - 1
        ));
    }

    for index in 0..length {
        lines.push(format!(
            "export function f{index}(xs: number[]) {{ const c = new (C{index} as any)(); c.m(xs); }}"
        ));
    }

    let mut tasks = 0;

    run_with_source(
        &lines.join(
            "
",
        ),
        |analysis, _| {
            for (file, function) in analysis.reportable() {
                analysis.summarize(file, function);
            }

            let stats = analysis.scheduler_stats();

            assert_terminal(stats);
            assert!(
                !stats.work.exhausted(Event::DispatchStep),
                "{length}: {stats:?}"
            );

            tasks = stats.work.consumed(Event::TaskKey);
        },
    );

    tasks
}

#[test]
fn inherited_same_members_keep_linear_task_counts() {
    let counts: Vec<u64> = [8, 16, 32, 64]
        .into_iter()
        .map(inherited_same_member_tasks_of)
        .collect();

    for pair in counts.windows(2) {
        assert!(4 * pair[1] <= 9 * pair[0], "{counts:?}");
    }
}

fn size_source(count: usize) -> String {
    let mut lines = vec![
        "export function f(flag: number): number {".to_string(),
        "\tlet shared: number[] = [];".to_string(),
        "\tlet total = 0;".to_string(),
    ];

    for index in 0..count {
        lines.push(format!("\tconst a{index} = [1, 2];"));
        lines.push(format!("\tif (flag === {index}) shared = a{index};"));
        lines.push(format!("\tfor (const v of a{index}) total += v;"));
        lines.push(format!("\tfor (const k in a{index}) total += k.length;"));
        lines.push("\ttotal += shared.length;".to_string());
    }

    lines.push("\treturn total + shared.length;".to_string());
    lines.push("}".to_string());

    lines.join("\n")
}

fn size_counts_of(count: usize) -> (u64, usize, Cost) {
    let mut found = None;

    run_with_source(&size_source(count), |analysis, file| {
        let part = summary_of(analysis, file, "f");
        let stats = analysis.scheduler_stats();
        let holders = analysis
            .stats
            .lines()
            .iter()
            .find_map(|line| line.strip_suffix("  sizes: holder"))
            .map_or(0, |count| count.trim().parse::<usize>().unwrap());

        assert_terminal(stats);
        assert!(!stats.work.exhausted(Event::SizeStep), "{count}: {stats:?}");

        found = Some((stats.work.consumed(Event::SizeStep), holders, part.cost));
    });

    found.expect("size counts")
}

#[test]
fn size_stability_work_grows_linearly_with_aliased_holders() {
    let base = size_counts_of(32);
    let single = size_counts_of(64);
    let double = size_counts_of(96);

    assert_eq!(single.2, Cost::ONE);
    assert_eq!(double.2, Cost::ONE);
    assert!(single.0 > base.0, "{base:?} {single:?}");
    assert_eq!(
        double.0 - base.0,
        2 * (single.0 - base.0),
        "{base:?} {single:?} {double:?}"
    );
    assert_eq!(
        double.1 - base.1,
        2 * (single.1 - base.1),
        "{base:?} {single:?} {double:?}"
    );
}

fn pattern_source(callers: usize, alias: bool) -> String {
    let body = match alias {
        true => "const f = run; f(xs);",
        false => "run(xs);",
    };
    let mut lines = vec![format!(
        "function use({{ run }}: {{ run: (xs: number[]) => void }}, xs: number[]) {{ {body} }}"
    )];

    for index in 0..callers {
        lines.push(format!(
            "export function c{index}(xs: number[]) {{ use({{ run: (ys: number[]) => {{ for (const y of ys) void y; }} }}, xs); }}"
        ));
    }

    lines.join("\n")
}

fn pattern_counts_of(callers: usize, alias: bool) -> (Vec<u64>, Cost) {
    let mut found = None;

    run_with_source(&pattern_source(callers, alias), |analysis, file| {
        let functions = analysis.reportable();

        analysis.summarize_reportable(&functions);

        let part = summary_of(analysis, file, "c0");
        let stats = analysis.scheduler_stats();
        let events = [Event::DispatchStep, Event::TaskKey, Event::WalkerNode];

        assert_terminal(stats);
        assert!(
            events.iter().all(|event| !stats.work.exhausted(*event)),
            "{callers}: {stats:?}"
        );

        found = Some((
            events
                .iter()
                .map(|event| stats.work.consumed(*event))
                .collect(),
            part.cost,
        ));
    });

    found.expect("pattern counts")
}

#[test]
fn destructured_parameter_targets_grow_linearly_with_callers() {
    for alias in [false, true] {
        let base = pattern_counts_of(32, alias);
        let single = pattern_counts_of(64, alias);
        let double = pattern_counts_of(96, alias);

        assert!(!single.1.is_one(), "{alias}: {single:?}");

        for (position, ((base, single), double)) in
            base.0.iter().zip(&single.0).zip(&double.0).enumerate()
        {
            assert!(single > base, "{alias} {position}: {single} {base}");
            assert_eq!(
                double - base,
                2 * (single - base),
                "{alias} {position}: {base} {single} {double}"
            );
        }
    }
}

fn parameter_initialization_source(size: usize) -> String {
    let mut lines = vec![
        "function cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }".to_string(),
        "type F = (xs: number[]) => unknown;".to_string(),
        "function factory(f: F, xs: number[]) { return () => f(xs); }".to_string(),
        "function set(t: any, v: unknown) { t.includes = v; }".to_string(),
        "function d0(xs: number[], n = cube(xs)) { return n; }".to_string(),
    ];

    for index in 1..size {
        lines.push(format!(
            "function d{index}(xs: number[], n = d{}(xs)) {{ return n; }}",
            index - 1
        ));
    }

    let calls: Vec<String> = (0..size)
        .map(|index| {
            format!("d{index}(xs); d{index}(xs, undefined); d{index}(xs, {index}); factory(cube, xs)(); set(Array.prototype, () => cube(xs));")
        })
        .collect();

    lines.push(format!(
        "export function root(xs: number[]) {{ {} return [1].includes(0); }}",
        calls.join(" ")
    ));

    lines.join("\n")
}

fn parameter_initialization_counts_of(size: usize) -> (Vec<u64>, usize, Cost) {
    let mut found = None;

    run_with_source(&parameter_initialization_source(size), |analysis, file| {
        let part = summary_of(analysis, file, "root");
        let stats = analysis.scheduler_stats();
        let events = [
            Event::DispatchStep,
            Event::TaskKey,
            Event::WalkerNode,
            Event::CallbackDescriptor,
        ];

        assert_terminal(stats);
        assert!(
            events.iter().all(|event| !stats.work.exhausted(*event)),
            "{size}: {stats:?}"
        );

        found = Some((
            events
                .iter()
                .map(|event| stats.work.consumed(*event))
                .collect(),
            stats.tasks,
            part.cost,
        ));
    });

    found.expect("parameter initialization counts")
}

#[test]
fn parameter_initialization_specializations_grow_linearly() {
    let base = parameter_initialization_counts_of(8);
    let single = parameter_initialization_counts_of(16);
    let double = parameter_initialization_counts_of(24);

    assert!(!single.2.is_one(), "{single:?}");

    for (size, counts) in [(8, &base), (16, &single), (24, &double)] {
        assert_eq!(counts.1, 4 * size + 4, "{size}: {counts:?}");
    }

    for (position, ((base, single), double)) in
        base.0.iter().zip(&single.0).zip(&double.0).enumerate()
    {
        assert!(single > base, "{position}: {single} {base}");
        assert_eq!(
            double - base,
            2 * (single - base),
            "{position}: {base} {single} {double}"
        );
    }
}

fn construction_source(groups: usize) -> String {
    let mut lines = vec![
        "function scan(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }".to_string(),
    ];

    for group in 0..groups {
        lines.push(format!("class A{group}_0 {{ values = [1, 2, 3]; }}"));

        for depth in 1..4 {
            lines.push(format!(
                "class A{group}_{depth} extends A{group}_{} {{ extra = [{depth}]; }}",
                depth - 1
            ));
        }

        lines.push(format!(
            "class E{group} extends A{group}_3 {{ constructor(xs: number[]) {{ super(); scan(xs); }} }}"
        ));
        lines.push(format!(
            "export function f{group}(xs: number[]) {{ class L extends A{group}_3 {{ total = scan(xs); }} new A{group}_3(); new A{group}_2(); new E{group}(xs); for (const x of xs) new L(); return class {{ static seed = scan(xs); }}; }}"
        ));
    }

    lines.join("\n")
}

fn construction_counts_of(groups: usize) -> (Vec<u64>, Cost) {
    let mut found = None;

    run_with_source(&construction_source(groups), |analysis, file| {
        for (file, function) in analysis.reportable() {
            analysis.summarize(file, function);
        }

        let part = summary_of(analysis, file, "f0");
        let selected = function_of_name(analysis.project, file, "f0");
        let stats = analysis.scheduler_stats();
        let events = [
            Event::TaskKey,
            Event::InvocationSite,
            Event::WalkerNode,
            Event::CaptureEdge,
        ];

        assert_terminal(stats);
        assert!(
            part.is_complete(),
            "{groups}: {:?}",
            reasons(analysis, part.unknowns)
        );
        assert!(
            events.iter().all(|event| !stats.work.exhausted(*event)),
            "{groups}: {stats:?}"
        );

        found = Some((
            events
                .iter()
                .map(|event| stats.work.consumed(*event))
                .collect(),
            support::legacy_class_of(analysis, file, selected, &part.cost),
        ));
    });

    found.expect("construction counts")
}

#[test]
fn class_definition_and_construction_work_grow_linearly_with_sites_and_subclasses() {
    let base = construction_counts_of(8);
    let single = construction_counts_of(16);
    let double = construction_counts_of(24);
    let growth: Vec<(u64, u64)> = base
        .0
        .iter()
        .zip(&single.0)
        .zip(&double.0)
        .map(|((base, single), double)| (single - base, double - base))
        .collect();

    assert_eq!(single.1, Cost::parse("O(N^2)").unwrap());
    assert!(
        growth
            .iter()
            .all(|(single, double)| *single > 0 && *double == 2 * single),
        "{base:?} {single:?} {double:?}"
    );
}

fn wide_construction_walks_of(width: usize) -> u64 {
    let fields: String = (0..width)
        .map(|index| format!("f{index} = [{index}]; "))
        .collect();
    let sites: String = (0..width).map(|_| "new Derived(); ".to_string()).collect();
    let source = format!(
        "class Wide {{ {fields}}}\nclass Derived extends Wide {{}}\nexport function selected(xs: number[]) {{ class Local {{ {fields}}} {sites}for (const x of xs) {{ {} }} }}",
        sites.replace("Derived", "Local")
    );
    let mut walks = 0;

    run_with_source(&source, |analysis, file| {
        let part = summary_of(analysis, file, "selected");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(part.is_complete(), "{width}");

        walks = stats.work.consumed(Event::WalkerNode);
    });

    walks
}

#[test]
fn instance_fields_walk_once_per_class_across_construction_sites() {
    let base = wide_construction_walks_of(16);
    let single = wide_construction_walks_of(32);
    let double = wide_construction_walks_of(48);

    assert!(single > base, "{base} {single}");
    assert_eq!(
        double - base,
        2 * (single - base),
        "{base} {single} {double}"
    );
}

fn parameter_base_source(width: usize) -> String {
    let mut lines: Vec<String> = (0..width)
        .map(|index| format!("class C{index} {{ v = [{index}]; }}"))
        .collect();
    let sites: String = (0..width).map(|_| "new A(); ").collect();
    let calls: String = (0..width)
        .map(|index| format!("make(C{index}); "))
        .collect();

    lines.push(format!(
        "function make(B: any) {{ class A extends B {{}} {sites}}}"
    ));
    lines.push(format!("export function run() {{ {calls}}}"));

    lines.join("\n")
}

fn parameter_base_steps_of(width: usize) -> u64 {
    let mut steps = 0;

    run_with_source(&parameter_base_source(width), |analysis, file| {
        let part = summary_of(analysis, file, "make");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(
            part.is_complete(),
            "{width}: {:?}",
            reasons(analysis, part.unknowns)
        );
        assert!(!stats.work.exhausted(Event::DispatchStep), "{stats:?}");

        steps = stats.work.consumed(Event::DispatchStep);
    });

    steps
}

#[test]
fn parameter_superclasses_resolve_once_across_construction_sites() {
    let base = parameter_base_steps_of(16);
    let single = parameter_base_steps_of(32);
    let double = parameter_base_steps_of(48);

    assert!(single > base, "{base} {single}");
    assert_eq!(
        double - base,
        2 * (single - base),
        "{base} {single} {double}"
    );
}

fn implicit_source(sites: usize) -> String {
    let mut lines = vec![
        "function tag(parts: TemplateStringsArray, value: number) { return value; }".to_string(),
        "function install(target: any, value: unknown) { target.probe = value; }".to_string(),
        "function forward(write: (target: any, value: unknown) => void, target: any) { write(target, () => 0); }".to_string(),
    ];

    for index in 0..sites {
        lines.push(format!(
            "export function f{index}(xs: number[]) {{ const box = {{ get value() {{ return xs.length; }}, valueOf() {{ return 1; }} }}; const iterable = {{ [Symbol.iterator]() {{ let count = 0; return {{ next() {{ return {{ done: count++ > 2, value: count }}; }} }}; }} }}; const read = box.value; const coerced = +box; for (const v of iterable) void v; class Box {{ m() {{ return 1; }} v = this.m(); }} new Box(); forward(install, {{}}); return tag`${{coerced}}` === read; }}"
        ));
    }

    lines.join("\n")
}

fn implicit_counts_of(sites: usize) -> Vec<u64> {
    let mut counts = Vec::new();

    run_with_source(&implicit_source(sites), |analysis, file| {
        for (file, function) in analysis.reportable() {
            analysis.summarize(file, function);
        }

        let part = summary_of(analysis, file, "f0");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(
            part.is_complete(),
            "{sites}: {:?}",
            reasons(analysis, part.unknowns)
        );

        counts = [
            Event::DispatchStep,
            Event::InvocationEvaluation,
            Event::TaskKey,
            Event::WalkerNode,
        ]
        .iter()
        .map(|event| {
            assert!(!stats.work.exhausted(*event), "{event:?}: {stats:?}");

            stats.work.consumed(*event)
        })
        .collect();
    });

    counts
}

#[test]
fn implicit_invocations_resolve_once_per_site_in_linear_work() {
    let base = implicit_counts_of(16);
    let single = implicit_counts_of(32);
    let double = implicit_counts_of(48);

    assert_linear_growth(&base, &single, &double);
}

fn nested_iteration_source(depth: usize) -> String {
    let mut body = "step(x0);".to_string();

    for level in (0..depth).rev() {
        body = format!("for (const x{level} of items) {{ {body} }}");
    }

    format!(
        "function step(x: unknown) {{ return x; }}\nexport function selected(xs: number[]) {{ const items = {{ [Symbol.iterator]() {{ let count = 0; return {{ next() {{ return {{ done: count++ > xs.length, value: 1 }}; }}, return() {{ return {{ done: true, value: 0 }}; }} }}; }} }}; {body} }}"
    )
}

fn stat_of(analysis: &Analysis<'_, '_>, label: &str) -> u64 {
    analysis
        .stats
        .lines()
        .iter()
        .find_map(|line| {
            let (count, name) = line.trim_start().split_once("  ")?;

            (name == label).then(|| count.trim().parse().ok()).flatten()
        })
        .unwrap_or(0)
}

fn nested_iteration_counts_of(depth: usize) -> Vec<u64> {
    let mut counts = Vec::new();

    run_with_source(&nested_iteration_source(depth), |analysis, file| {
        let part = summary_of(analysis, file, "selected");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(
            part.is_complete(),
            "{depth}: {:?}",
            reasons(analysis, part.unknowns)
        );
        assert!(!stats.work.exhausted(Event::DispatchStep), "{stats:?}");

        counts = vec![
            stat_of(analysis, "iterator exits: node"),
            stat_of(analysis, "iterator exits: step"),
            stats.work.consumed(Event::DispatchStep),
        ];
    });

    counts
}

#[test]
fn nested_iteration_protocols_resolve_exits_and_targets_in_linear_work() {
    let base = nested_iteration_counts_of(8);
    let single = nested_iteration_counts_of(16);
    let double = nested_iteration_counts_of(24);

    assert_linear_growth(&base, &single, &double);
}

fn rest_copy_source(sites: usize, keys: usize) -> String {
    let properties: String = (0..keys)
        .map(|index| format!("k{index}: {index}, "))
        .collect();
    let mut lines = vec![
        "function cube(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void (a + b + c); }".to_string(),
        format!("const base = {{ {properties}run: cube, get probe(): number {{ return 1; }} }};"),
        "const fns = [cube];".to_string(),
    ];

    for index in 0..sites {
        lines.push(format!("const copy{index} = {{ ...base }};"));
    }

    let uses: String = (0..sites)
        .map(|index| {
            format!("copy{index}.run(xs); const [run{index}] = fns; run{index}(xs); const {{ k0: key{index}, ...rest{index} }} = base; void key{index}; void rest{index}; ")
        })
        .collect();

    lines.push(format!(
        "export function selected(xs: number[]) {{ {uses} }}"
    ));

    lines.join(
        "
",
    )
}

fn rest_copy_steps_of(sites: usize, keys: usize) -> u64 {
    let mut steps = 0;

    run_with_source(&rest_copy_source(sites, keys), |analysis, file| {
        let part = summary_of(analysis, file, "selected");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(!stats.work.exhausted(Event::DispatchStep), "{stats:?}");

        let selected = function_of_name(analysis.project, file, "selected");

        assert_eq!(
            support::legacy_class_of(analysis, file, selected, &part.cost),
            Cost::parse("O(N^3)").unwrap(),
            "{sites} {keys}"
        );

        steps = stats.work.consumed(Event::DispatchStep);
    });

    steps
}

#[test]
fn spread_copies_and_destructured_elements_scan_source_keys_once() {
    for (sites, keys) in [
        (8, 8),
        (16, 8),
        (24, 8),
        (8, 16),
        (8, 24),
        (16, 16),
        (24, 24),
    ] {
        let sites = sites as u64;
        let keys = keys as u64;

        assert_eq!(
            rest_copy_steps_of(sites as usize, keys as usize),
            29 * sites + 3 * sites * keys,
            "{sites} {keys}"
        );
    }
}

fn loop_phase_walks_of(loops: usize) -> u64 {
    let statements: String = (0..loops)
        .map(|index| {
            format!("for (let i{index} = 0; i{index} < scan(xs); i{index}++) total += i{index}; ")
        })
        .collect();
    let source = format!(
        "function scan(xs: number[]) {{ let found = 0; for (const x of xs) found += x; return found; }}
export function selected(xs: number[]) {{ let total = 0; {statements}return total; }}"
    );
    let mut walks = 0;

    run_with_source(&source, |analysis, file| {
        let part = summary_of(analysis, file, "selected");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);

        let selected = function_of_name(analysis.project, file, "selected");

        assert_eq!(
            support::legacy_class_of(analysis, file, selected, &part.cost),
            Cost::parse("O(N^2)").unwrap(),
            "{loops}"
        );

        walks = stats.work.consumed(Event::WalkerNode);
    });

    walks
}

#[test]
fn loop_phases_walk_their_tests_and_updates_once() {
    for loops in [16_u64, 32, 48] {
        assert_eq!(
            loop_phase_walks_of(loops as usize),
            30 * loops + 30,
            "{loops}"
        );
    }
}

fn branch_scan_source(sites: usize, escaping: bool) -> String {
    let tail = match escaping {
        true => "",
        false => "if (value < 0) continue; ",
    };
    let branches: String = (0..sites)
        .map(|index| {
            format!(
                "if (value > {index}) {{ total += scan(row); total += row.length; total += value; {tail}break; }} "
            )
        })
        .collect();

    format!(
        "function scan(xs: number[]) {{ let found = 0; for (const x of xs) found += x; return found; }}
export function selected(rows: number[][]) {{ let total = 0; for (const row of rows) {{ for (const value of row) {{ {branches}}} }} return total; }}"
    )
}

fn branch_scan_edges_of(sites: usize, escaping: bool) -> u64 {
    let mut edges = 0;

    run_with_source(&branch_scan_source(sites, escaping), |analysis, file| {
        let part = summary_of(analysis, file, "selected");
        let stats = analysis.scheduler_stats();

        assert_terminal(stats);
        assert!(!part.cost.is_one(), "{sites}");

        let lifted = support::trace_nodes(&analysis.traces, part.trace)
            .iter()
            .any(|node| node.label == "[break branch: runs once per loop]");

        assert_eq!(lifted, escaping, "{sites}");

        edges = stats.work.consumed(Event::TraversalEdge);
    });

    edges
}

#[test]
fn escaping_branches_scan_their_own_subtree_once() {
    for sites in [8_u64, 16, 24, 32] {
        assert_eq!(
            branch_scan_edges_of(sites as usize, true),
            290 * sites + 170,
            "{sites}"
        );
    }
}

#[test]
fn branches_that_cannot_leave_their_loop_stop_scanning_early() {
    for sites in [8_u64, 16, 24, 32] {
        assert_eq!(
            branch_scan_edges_of(sites as usize, false),
            329 * sites + 170,
            "{sites}"
        );
    }
}

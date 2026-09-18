use olint::analysis::Analysis;
use olint::cost::{Cost, Part, Preference};
use olint::declarations::{Binding, FunctionNode};
use olint::declared_types::Kind;
use olint::effects::Effects;
use olint::project::FileId;
use olint::summaries::{Substitutions, SummaryId, SummaryRecord};
use olint::tsc::{CalleeAnswer, Query, TscAnswer, TscReply, TypeAnswer};
use olint::types::TscPass;
use olint::unknowns::SourceSpan;
use olint::values::{ArgumentFacts, ValueId};
use oxc_ast::ast::BindingPattern;

mod support;

fn reply(answers: Vec<Option<TscAnswer>>) -> TscReply {
    TscReply {
        typescript: "5.9.3".into(),
        from: "typescript.js".into(),
        answers,
    }
}

fn query_source<'a>(source: &'a str, query: &Query) -> &'a str {
    let (pos, end) = match query {
        Query::Type { pos, end, .. } | Query::Callee { pos, end, .. } => (*pos, *end),
    };

    &source[pos as usize..end as usize]
}

fn target_answer(analysis: &Analysis<'_, '_>, file: FileId, target: FunctionNode<'_>) -> TscAnswer {
    let span = match target {
        FunctionNode::Function(inner) => inner.span,
        FunctionNode::Arrow(inner) => inner.span,
    };

    TscAnswer::Callee(CalleeAnswer {
        file: analysis
            .project
            .file(file)
            .path
            .to_string_lossy()
            .replace('\\', "/"),
        start: span.start,
        end: span.end,
    })
}

fn assert_drained(analysis: &Analysis<'_, '_>) {
    let stats = analysis.scheduler_stats();

    assert_eq!(stats.ready, stats.tasks);
    assert_eq!(stats.waiting, 0);
    assert_eq!(stats.queued, 0);
}

fn reset_generation(analysis: &mut Analysis<'_, '_>) {
    let generation = analysis.scheduler_stats().generation;

    analysis.reset_between_passes();
    assert!(analysis.scheduler_stats().generation > generation);
    assert_eq!(analysis.scheduler_stats().tasks, 0);
}

fn settle_unanswered<'a>(
    analysis: &mut Analysis<'_, 'a>,
    file: FileId,
    function: FunctionNode<'a>,
    count: usize,
) {
    analysis.take_answers(reply(vec![None; count])).unwrap();
    analysis.reset_between_passes();
    analysis.summarize(file, function);
    assert!(analysis.needed_queries().is_empty());
    assert_drained(analysis);
}

fn first_parameter(function: FunctionNode<'_>, file: FileId) -> (Binding, SourceSpan) {
    let FunctionNode::Function(inner) = function else {
        panic!("ordinary function")
    };
    let BindingPattern::BindingIdentifier(identifier) = &inner.params.items[0].pattern else {
        panic!("plain parameter")
    };

    (
        Binding::Symbol {
            file,
            symbol: identifier.symbol_id.get().unwrap(),
        },
        SourceSpan {
            file,
            start: identifier.span.start,
            end: identifier.span.end,
        },
    )
}

#[test]
fn raw_and_selected_tasks_survive_three_answer_generations_without_aliasing() {
    let source = "function target(){\n/** @perf O(N^3) */\nvoid 0;}\nfunction make():any{return 1;}\n/** @perf O(N^2) */\nexport function tagged(loose:any){loose.map((x:number)=>x);make().run();}\n";

    support::run_with_source(source, |analysis, file| {
        let target = support::function_of_name(analysis.project, file, "target");
        let tagged = support::function_of_name(analysis.project, file, "tagged");

        analysis.set_pass(TscPass::Recording);

        let selected = analysis.summarize(file, tagged);

        assert!(analysis.needed_queries().is_empty());

        let selected_tasks = analysis.scheduler_stats().tasks;
        let raw = analysis.summarize_with(file, tagged, Substitutions::new(), true);

        assert!(analysis.scheduler_stats().tasks > selected_tasks);

        let needed = analysis.needed_queries();

        assert!(needed
            .iter()
            .any(|query| matches!(query, Query::Type { .. })
                && query_source(source, query) == "loose"));
        assert!(needed
            .iter()
            .any(|query| matches!(query, Query::Callee { .. })
                && query_source(source, query) == "make().run"));

        let retained = analysis.summaries_arena.clone();
        let old_unknown = raw
            .total(&mut analysis.unknowns, &mut analysis.traces)
            .unknowns
            .map(|id| (id, analysis.unknowns.node(id).clone()));
        let answers = needed
            .iter()
            .map(|query| match query {
                Query::Type { .. } if query_source(source, query) == "loose" => {
                    Some(TscAnswer::Type(TypeAnswer {
                        kind: Kind::Array,
                        tuple: false,
                        closed: false,
                    }))
                }
                Query::Callee { .. } if query_source(source, query) == "make().run" => {
                    Some(target_answer(analysis, file, target))
                }
                _ => None,
            })
            .collect();

        analysis.take_answers(reply(answers)).unwrap();

        for _ in 0..3 {
            reset_generation(analysis);
            assert_eq!(
                &analysis.summaries_arena[..retained.len()],
                retained.as_slice()
            );

            if let Some((id, ref node)) = old_unknown {
                assert_eq!(analysis.unknowns.node(id), node);
            }

            let again = analysis.summarize(file, tagged);

            assert_eq!(again.main.cost, selected.main.cost);

            let raw_again = analysis.summarize_with(file, tagged, Substitutions::new(), true);

            assert!(analysis.needed_queries().is_empty());

            let part = raw_again.total(&mut analysis.unknowns, &mut analysis.traces);

            assert_eq!(
                support::legacy_class_of(analysis, file, tagged, &part.cost),
                Cost::parse("O(N^3)").unwrap()
            );

            let id = part.unknowns.expect("sidecar leaves dispatch open");
            let call = support::call_of(analysis.project, file, "make().run");
            let location = format!(":6 [{}..{}]", call.span.start, call.span.end);

            assert!(analysis
                .unknowns
                .lines(analysis.project, id)
                .iter()
                .any(|line| line.contains("unknown call target") && line.contains(&location)));

            assert_drained(analysis);

            let count = analysis.scheduler_stats().tasks;

            assert_eq!(analysis.summarize(file, tagged), again);
            assert_eq!(
                analysis.summarize_with(file, tagged, Substitutions::new(), true),
                raw_again
            );
            assert_eq!(analysis.scheduler_stats().tasks, count);
        }
    });
}

#[test]
fn answered_callee_enables_a_previously_unvisited_query_and_none_settles_it() {
    let source = "function target(other:any){other.map((x:number)=>x);}\nfunction make():any{return 1;}\nexport function root(){make().run();}\n";

    support::run_with_source(source, |analysis, file| {
        let root = support::function_of_name(analysis.project, file, "root");
        let target = support::function_of_name(analysis.project, file, "target");

        analysis.set_pass(TscPass::Recording);
        analysis.summarize(file, root);

        let first = analysis.needed_queries();

        assert!(!first
            .iter()
            .any(|query| query_source(source, query) == "other"));
        assert!(first
            .iter()
            .any(|query| query_source(source, query) == "make().run"));

        let answers = first
            .iter()
            .map(|query| {
                if matches!(query, Query::Callee { .. })
                    && query_source(source, query) == "make().run"
                {
                    Some(target_answer(analysis, file, target))
                } else {
                    None
                }
            })
            .collect();

        analysis.take_answers(reply(answers)).unwrap();
        analysis.reset_between_passes();
        analysis.summarize(file, root);

        let second = analysis.needed_queries();

        assert!(second
            .iter()
            .any(|query| matches!(query, Query::Type { .. })
                && query_source(source, query) == "other"));
        settle_unanswered(analysis, file, root, second.len());
    });
}

#[test]
fn malformed_reply_preserves_queries_and_valid_reply_recovers() {
    let source = "export function root(other:any){other.map((x:number)=>x);}";

    support::run_with_source(source, |analysis, file| {
        let root = support::function_of_name(analysis.project, file, "root");

        analysis.set_pass(TscPass::Recording);
        analysis.summarize(file, root);

        let needed = analysis.needed_queries();

        assert!(!needed.is_empty());

        let generation = analysis.scheduler_stats().generation;

        assert!(analysis.take_answers(reply(Vec::new())).is_err());
        assert_eq!(analysis.needed_queries(), needed);
        assert_eq!(analysis.scheduler_stats().generation, generation);
        settle_unanswered(analysis, file, root, needed.len());
    });
}

#[test]
fn equivalent_latent_effect_sets_share_keys_but_different_effects_do_not() {
    support::run_with_source(
        "function invoke(callback:()=>void){callback();}",
        |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "invoke");
            let (binding, origin) = first_parameter(function, file);
            let value = analysis.values.at(origin);
            let mut tasks = Vec::new();

            for (writes, unknown_global) in [
                (vec![ValueId(17), ValueId(19)], false),
                (vec![ValueId(19), ValueId(17), ValueId(19)], false),
                (vec![ValueId(17), ValueId(19)], true),
            ] {
                let latent = SummaryId(analysis.summaries_arena.len() as u32);

                analysis.summaries_arena.push(SummaryRecord {
                    reading: Default::default(),
                    result: value.clone(),
                    effects: Effects {
                        member_writes: writes,
                        unknown_global,
                        ..Effects::default()
                    },
                });

                let mut actual = value.clone();
                actual.latent = Some(latent);
                let facts = ArgumentFacts {
                    value: actual,
                    callback: Some(Part::unmarked(Cost::ONE, None)),
                    preference: Preference::Unmarked,
                };

                analysis.summarize_with(
                    file,
                    function,
                    Substitutions::from([(binding, facts)]),
                    false,
                );
                tasks.push(analysis.scheduler_stats().tasks);
                assert_drained(analysis);
            }

            assert_eq!(
                tasks[0], tasks[1],
                "effect set order/duplicates changed semantic cache key"
            );
            assert!(tasks[2] > tasks[1], "genuinely different effects collided");
        },
    );
}

#[test]
fn published_callback_facts_and_unknown_handles_remain_valid_after_reset() {
    let source = "declare function opaque():void;\nfunction callback(){opaque();}\nfunction invoke(cb:()=>void){cb();}";

    support::run_with_source(source, |analysis, file| {
        let callback = support::function_of_name(analysis.project, file, "callback");
        let invoke = support::function_of_name(analysis.project, file, "invoke");
        let reading = analysis.summarize(file, callback);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let unknown = part.unknowns.expect("opaque callback is partial");
        let old_node = analysis.unknowns.node(unknown).clone();
        let index = analysis
            .summaries_arena
            .iter()
            .position(|record| record.reading == reading)
            .expect("published callback");
        let id = SummaryId(index as u32);
        let old_record = analysis.summaries_arena[index].clone();
        let mut value = old_record.result.clone();
        value.latent = Some(id);
        let facts = ArgumentFacts {
            value,
            callback: Some(part),
            preference: Preference::Unmarked,
        };
        let (binding, _) = first_parameter(invoke, file);

        for _ in 0..3 {
            reset_generation(analysis);
            assert_eq!(analysis.summaries_arena[id.0 as usize], old_record);
            assert_eq!(analysis.unknowns.node(unknown), &old_node);

            let result = analysis.summarize_with(
                file,
                invoke,
                Substitutions::from([(binding, facts.clone())]),
                false,
            );
            let part = result.total(&mut analysis.unknowns, &mut analysis.traces);

            assert!(part.unknowns.is_some());
            assert!(
                analysis.scheduler_stats().tasks > 0,
                "old latent record must not resolve new generation task directly"
            );
            assert_drained(analysis);
        }
    });
}

#[test]
fn descriptor_admission_failure_keeps_resource_reason_for_a_known_callback() {
    use olint::analysis::work::Event;

    use olint::summaries::SchedulerLimits;

    support::run_with_source("function invoke(cb:()=>void){cb();} function pure(){} export function root(){invoke(pure);}", |analysis, file| {
        let mut limits = SchedulerLimits::default();
        limits.work = limits.work.with(Event::CallbackDescriptor, 0);

        analysis.set_scheduler_limits(limits).unwrap();

        let root = support::function_of_name(analysis.project, file, "root");
        let reading = analysis.summarize(file, root);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let id = part.unknowns.expect("resource exhaustion is incomplete");

        assert!(analysis.unknowns.lines(analysis.project, id).iter().any(|line| line.contains("analysis resource limit")));
        assert_drained(analysis);

        let count = analysis.scheduler_stats().tasks;

        assert_eq!(analysis.summarize(file, root), reading);
        assert_eq!(analysis.scheduler_stats().tasks, count);
    });
}

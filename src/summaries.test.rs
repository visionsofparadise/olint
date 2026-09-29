use super::*;
use crate::analysis::Options;
use crate::project::Project;
use oxc_allocator::Allocator;

#[test]
fn retained_lazy_callbacks_cannot_alias_a_new_generation() {
    let directory = tempfile::tempdir().unwrap();

    std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
    std::fs::write(
        directory.path().join("index.ts"),
        "function pure(){return 1} function capture(cb:()=>number){} capture(pure);",
    )
    .unwrap();

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &directory.path().join("tsconfig.json")).unwrap();
    let file = project
        .file_by_path(&directory.path().join("index.ts"))
        .unwrap();
    let call = project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .find_map(|node| match node.kind() {
            AstKind::CallExpression(call) => Some(call),
            _ => None,
        })
        .unwrap();
    let mut analysis = Analysis::new(
        &project,
        Options {
            minimum_exponent: 2,
            types: crate::analysis::TypeMode::Syntactic,
            record_nodes: false,
        },
    );
    let old = analysis.argument_facts_of(file, &call.arguments[0]);

    assert!(analysis
        .invoke_argument(&old, file, call.span, &[])
        .total(&mut analysis.unknowns, &mut analysis.traces)
        .is_complete());
    analysis.reset_between_passes();

    let stale = analysis.invoke_argument(&old, file, call.span, &[]);

    assert!(!stale
        .total(&mut analysis.unknowns, &mut analysis.traces)
        .is_complete());

    let fresh = analysis.argument_facts_of(file, &call.arguments[0]);

    assert_ne!(old.value.value, fresh.value.value);
    assert!(analysis
        .invoke_argument(&fresh, file, call.span, &[])
        .total(&mut analysis.unknowns, &mut analysis.traces)
        .is_complete());
    assert_eq!(analysis.invoke_argument(&old, file, call.span, &[]), stale);
}

#[test]
fn resource_fallback_keeps_observed_scheduled_and_joined_latent_work() {
    let directory = tempfile::tempdir().unwrap();

    std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
    std::fs::write(
        directory.path().join("index.ts"),
        "async function quadratic(xs:number[]){await 0; for(const a of xs)for(const b of xs)void b} function run(f:(xs:number[])=>void,xs:number[]){f(xs)} export function root(xs:number[]){run(quadratic,xs)}",
    )
    .unwrap();

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &directory.path().join("tsconfig.json")).unwrap();
    let file = project
        .file_by_path(&directory.path().join("index.ts"))
        .unwrap();
    let nodes = project.file(file).semantic.nodes();
    let function_named = |name: &str| {
        nodes
            .iter()
            .find_map(|node| match node.kind() {
                AstKind::Function(function)
                    if function.id.as_ref().is_some_and(|id| id.name == name) =>
                {
                    Some(FunctionNode::Function(function))
                }
                _ => None,
            })
            .unwrap()
    };
    let call = nodes
        .iter()
        .find_map(|node| match node.kind() {
            AstKind::CallExpression(call)
                if matches!(&call.callee, Expression::Identifier(callee) if callee.name == "run") =>
            {
                Some(call)
            }
            _ => None,
        })
        .unwrap();
    let (root, run) = (function_named("root"), function_named("run"));
    let mut analysis = Analysis::new(
        &project,
        Options {
            minimum_exponent: 2,
            types: crate::analysis::TypeMode::Syntactic,
            record_nodes: false,
        },
    );

    analysis.summarize(file, root);
    analysis.summarize(file, run);

    let task_of = |analysis: &Analysis<'_, '_>, function: FunctionNode<'_>, substituted: bool| {
        analysis
            .scheduler
            .tasks
            .iter()
            .position(|task| {
                task.key.function.node == function.node_id()
                    && task.key.substitutions.iter().any(|argument| {
                        analysis
                            .scheduler
                            .callback_values
                            .contains_key(&argument.value.value)
                    }) == substituted
            })
            .map(TaskId)
            .unwrap()
    };
    let parent = task_of(&analysis, root, false);
    let generic = task_of(&analysis, run, false);
    let target = FunctionId {
        file,
        node: run.node_id(),
    };
    let generic_key = analysis.scheduler.tasks[generic.0].key.clone();

    analysis.scheduler.work =
        WorkBudget::new(Limits::uniform(1_000_000).with(Event::InvocationObservation, 0));
    analysis.scheduler.active = Some(parent);

    analysis.observe_invocation(&generic_key, file, call.span);

    let (observed, incomplete) = analysis.scheduler.tasks[parent.0]
        .invocations
        .get(&(analysis.source_span(file, call.span), target))
        .cloned()
        .unwrap();

    assert_eq!(observed.len(), 1);
    assert!(incomplete);

    let (reading, _) = analysis.fallback_invocation(target, file, call.span, Deferral::Excluded);
    let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

    assert!(reading.completions.iter().any(|channel| channel.0
        == crate::cost::ExecutionPhase::Scheduled
        && channel.2.cost == part.cost));

    let mut reasons = Vec::new();
    let mut pending: Vec<_> = part.unknowns.into_iter().collect();

    while let Some(id) = pending.pop() {
        match analysis.unknowns.node(id) {
            crate::unknowns::UnknownNode::Origin(unknown) => reasons.push(unknown.reason),
            crate::unknowns::UnknownNode::Call { child, .. }
            | crate::unknowns::UnknownNode::Scale { child, .. } => pending.push(*child),
            crate::unknowns::UnknownNode::Join { children } => pending.extend(children),
        }
    }

    assert!(!part.cost.is_one(), "{part:?}");
    assert!(
        reasons.contains(&UnknownReason::ResourceExhaustion),
        "{reasons:?}"
    );

    analysis.scheduler.active = None;

    analysis.scheduler.work =
        WorkBudget::new(Limits::uniform(1_000_000).with(Event::LatentStep, 0));
    let deferred = |phase| Latent {
        work: Part::unmarked(Cost::N, None),
        yields: Some(Cost::ONE),
        effects: Effects::default(),
        record: None,
        storage: crate::effects::Storage::default(),
        deferred: Some(Reading::of_completion(
            phase,
            Completion::Return,
            Part::unmarked(Cost::N, None),
        )),
    };
    let joined = analysis.joined_latent_of(
        Some(deferred(crate::cost::ExecutionPhase::Immediate)),
        deferred(crate::cost::ExecutionPhase::Scheduled),
        analysis.source_span(file, call.span),
    );

    assert_eq!(joined.record, None);

    let consumed = analysis.consumed_part_of(file, call.span, &joined);

    for phase in [
        crate::cost::ExecutionPhase::Immediate,
        crate::cost::ExecutionPhase::Scheduled,
    ] {
        assert_eq!(consumed.part_of(phase, Completion::Normal).cost, Cost::N);
        assert_eq!(consumed.part_of(phase, Completion::Return), Part::none());
    }
}

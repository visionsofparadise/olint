use std::collections::HashSet;

use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::{GetSpan, SourceType};

use super::*;

#[test]
fn borrowed_contexts_reuse_the_same_owned_index() {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, "function f() {}", SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .build(&parsed.program)
        .semantic;
    let index = FlowIndex::new(&semantic);
    let first = FlowContext::from_index(&semantic, &index);
    let second = FlowContext::from_index(&semantic, &index);

    assert!(matches!(first.children, Cow::Borrowed(_)));
    assert!(std::ptr::eq(
        first.children.as_ptr(),
        index.children.as_ptr()
    ));
    assert!(std::ptr::eq(
        first.children.as_ptr(),
        second.children.as_ptr()
    ));
}

#[test]
fn erased_type_queries_have_no_executable_points() {
    let source =
        "function f(x: typeof value = runtime()): typeof other { return x as typeof erased; }";

    inspect(source, |flow, semantic| {
        for name in ["value", "other", "erased"] {
            let id = node_of(semantic, source, name);

            assert!(flow.points.iter().all(|point| point.node != id));
        }

        call(flow, semantic, source, "runtime()");
        assert!(flow
            .exits
            .iter()
            .any(|exit| exit.completion == Completion::Return));
    });
}

#[test]
fn runtime_typescript_expression_is_retained_and_enum_is_explicitly_unsupported() {
    let source = "function f(){ return runtime<typeof erased>; }";

    inspect(source, |flow, semantic| {
        let runtime = node_of(semantic, source, "runtime");
        let erased = node_of(semantic, source, "erased");

        assert!(flow.points.iter().any(|point| point.node == runtime));
        assert!(flow.points.iter().all(|point| point.node != erased));
    });

    let allocator = Allocator::default();
    let parsed = Parser::new(
        &allocator,
        "function f(){ enum E { A = runtime() } }",
        SourceType::ts(),
    )
    .parse();

    assert!(parsed.diagnostics.is_empty());

    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .build(&parsed.program)
        .semantic;
    let function = semantic
        .nodes()
        .iter()
        .find(|node| matches!(node.kind(), AstKind::Function(_)))
        .unwrap()
        .id();

    assert!(
        matches!(FlowContext::new(&semantic).unwrap().build(FileId(0),function), Err(FlowError::Unsupported(node)) if matches!(semantic.nodes().kind(node),AstKind::TSEnumDeclaration(_)))
    );
}

#[test]
fn shared_source_index_and_sequence_work_scale_by_node_count() {
    for count in [16, 64, 256] {
        let source = (0..count)
            .map(|i| format!("function f{i}() {{ value(); }}"))
            .collect::<String>();
        let allocator = Allocator::default();
        let parsed = Parser::new(&allocator, &source, SourceType::ts()).parse();
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program)
            .semantic;
        let context = FlowContext::new(&semantic).unwrap();

        assert_eq!(context.indexed_nodes, semantic.nodes().len());

        let mut visits = 0;

        for node in semantic
            .nodes()
            .iter()
            .filter(|node| matches!(node.kind(), AstKind::Function(_)))
        {
            let flow = context.build(FileId(0), node.id()).unwrap();
            visits += flow.node_visits;
        }

        assert!(visits <= semantic.nodes().len());
        assert_eq!(context.indexed_nodes, semantic.nodes().len());

        let source = format!("function f() {{ {} }}", "value();".repeat(count));

        inspect(&source, |flow, _| {
            assert!(flow.sequence_port_visits <= count * 10 + 10);
            assert!(flow.node_visits <= count * 5 + 10);
        });
    }
}

#[test]
fn implicit_iteration_and_class_validation_throw_into_catch() {
    for source in [
        "function f(){ try { for (const x of items) {} } catch { caught(); } }",
        "function f(){ try { for (const x in items) {} } catch { caught(); } }",
        "function f(){ try { class C extends 3 {} } catch { caught(); } }",
        "function f(){ try { class C { [3] = 0; } } catch { caught(); } }",
    ] {
        inspect(source, |flow, semantic| {
            let caught = call(flow, semantic, source, "caught()");
            let expected = flow
                .edges
                .iter()
                .find(|edge| {
                    if !matches!(edge.guard, Guard::Throws(_)) {
                        return false;
                    }

                    let point = &flow.points[edge.from.0];

                    point.step == Step::IterationNext
                        || point.region
                            == Region::ClassDefinition(
                                semantic
                                    .nodes()
                                    .iter()
                                    .find(|node| matches!(node.kind(), AstKind::Class(_)))
                                    .map_or(point.node, |node| node.id()),
                            )
                })
                .expect("implicit operation exception edge");

            assert!(reachable(flow, expected.to, caught, &[]));
        });
    }
}

fn inspect(source: &str, test: impl FnOnce(&FlowSummary, &Semantic<'_>)) {
    inspect_named(source, "f", test);
}

fn inspect_named(source: &str, name: &str, test: impl FnOnce(&FlowSummary, &Semantic<'_>)) {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::ts()).parse();

    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

    let result = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_class_table(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);

    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

    let function = result.semantic.nodes().iter().find(|node| matches!(node.kind(), AstKind::Function(function) if function.id.as_ref().is_some_and(|id| id.name == name))).unwrap().id();
    let summary = FlowContext::new(&result.semantic)
        .unwrap()
        .build(FileId(0), function)
        .unwrap();

    for point in &summary.points {
        assert_eq!(point.cfg, result.semantic.nodes().cfg_id(point.node));
    }

    test(&summary, &result.semantic);
}

fn node_of(semantic: &Semantic<'_>, source: &str, text: &str) -> NodeId {
    semantic
        .nodes()
        .iter()
        .find(|node| {
            let span = node.kind().span();

            &source[span.start as usize..span.end as usize] == text
        })
        .unwrap_or_else(|| panic!("missing {text}"))
        .id()
}

fn calls(
    summary: &FlowSummary,
    semantic: &Semantic<'_>,
    source: &str,
    text: &str,
) -> Vec<FlowPointId> {
    summary
        .points
        .iter()
        .enumerate()
        .filter(|(_, point)| {
            let kind = semantic.nodes().kind(point.node);
            let span = kind.span();

            point.step == Step::Evaluate
                && matches!(kind, AstKind::CallExpression(_))
                && &source[span.start as usize..span.end as usize] == text
        })
        .map(|(id, _)| FlowPointId(id))
        .collect()
}

fn call(summary: &FlowSummary, semantic: &Semantic<'_>, source: &str, text: &str) -> FlowPointId {
    let found = calls(summary, semantic, source, text);

    assert_eq!(found.len(), 1, "{text}");

    found[0]
}

fn reachable(
    summary: &FlowSummary,
    from: FlowPointId,
    to: FlowPointId,
    avoid: &[FlowPointId],
) -> bool {
    let mut pending = vec![from];
    let mut seen = HashSet::new();

    while let Some(point) = pending.pop() {
        if avoid.contains(&point) || !seen.insert(point) {
            continue;
        }

        if point == to {
            return true;
        }

        pending.extend(
            summary
                .edges
                .iter()
                .filter(|edge| edge.from == point && !matches!(edge.guard, Guard::Throws(_)))
                .map(|edge| edge.to),
        );
    }

    false
}

#[test]
fn for_phases_order_initialization_test_body_and_update() {
    let source = "function f(){ for(init(); test(); update()) body(); after(); }";

    inspect(source, |flow, semantic| {
        let [init, test, update, body, after] =
            ["init()", "test()", "update()", "body()", "after()"]
                .map(|text| call(flow, semantic, source, text));

        assert!(reachable(flow, init, test, &[]));
        assert!(reachable(flow, test, body, &[]));
        assert!(reachable(flow, body, update, &[]));
        assert!(reachable(flow, update, test, &[]));
        assert!(!reachable(flow, body, test, &[update]));
        assert!(!reachable(flow, test, init, &[]));
        assert!(reachable(flow, test, after, &[body]));
    });
}

#[test]
fn for_continue_runs_update_and_break_skips_it() {
    let source = "function f(){ for(; test(); update()) { if(skip()) continue; break; } after(); }";

    inspect(source, |flow, semantic| {
        let update = call(flow, semantic, source, "update()");
        let after = call(flow, semantic, source, "after()");
        let continued = node_of(semantic, source, "continue;");
        let broken = node_of(semantic, source, "break;");
        let point = |node| {
            FlowPointId(
                flow.points
                    .iter()
                    .position(|p| p.node == node && p.step == Step::Entry)
                    .unwrap(),
            )
        };

        assert!(reachable(flow, point(continued), update, &[]));
        assert!(!reachable(flow, point(continued), after, &[update]));
        assert!(reachable(flow, point(broken), after, &[update]));
    });
}

#[test]
fn while_test_has_zero_trip_path() {
    let source = "function f(){ while(test()) body(); after(); }";

    inspect(source, |flow, semantic| {
        let body = call(flow, semantic, source, "body()");
        let test = call(flow, semantic, source, "test()");
        let after = call(flow, semantic, source, "after()");

        assert!(reachable(flow, flow.entry, after, &[body]));
        assert!(reachable(flow, body, test, &[]));
        assert!(!reachable(flow, flow.entry, body, &[test]));
    });
}

#[test]
fn do_while_enters_body_first() {
    let source = "function f(){ do { body(); continue; } while(test()); after(); }";

    inspect(source, |flow, semantic| {
        let body = call(flow, semantic, source, "body()");
        let test = call(flow, semantic, source, "test()");
        let after = call(flow, semantic, source, "after()");

        assert!(!reachable(flow, flow.entry, after, &[body]));
        assert!(reachable(flow, flow.entry, body, &[test]));
        assert!(reachable(flow, body, test, &[]));
    });
}

#[test]
fn for_of_evaluates_iterable_once_and_assignment_each_iteration() {
    let source =
        "function f(){ for(const {x = fallback()} of iterable()) { body(); continue; } after(); }";

    inspect(source, |flow, semantic| {
        let iterable = call(flow, semantic, source, "iterable()");
        let fallback = call(flow, semantic, source, "fallback()");
        let body = call(flow, semantic, source, "body()");
        let next = FlowPointId(
            flow.points
                .iter()
                .position(|p| p.step == Step::IterationNext)
                .unwrap(),
        );

        assert!(reachable(flow, iterable, next, &[]));
        assert!(!reachable(flow, next, iterable, &[]));
        assert!(reachable(flow, body, next, &[]));
        assert!(reachable(flow, next, fallback, &[]));
        assert!(reachable(flow, fallback, body, &[]));
    });
}

#[test]
fn logical_and_records_truth_polarity() {
    let source = "function f(){ left() && right(); after(); }";

    inspect(source, |flow, semantic| {
        let left = node_of(semantic, source, "left()");
        let right = call(flow, semantic, source, "right()");
        let after = call(flow, semantic, source, "after()");

        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.guard == Guard::Truthy(left)
                && reachable(flow, edge.to, right, &[after])));
        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.guard == Guard::Falsy(left)
                && reachable(flow, edge.to, after, &[right])));
    });
}

#[test]
fn logical_or_and_nullish_use_different_guards() {
    for (operator, nullish) in [("||", false), ("??", true)] {
        let source = format!("function f(){{ left() {operator} right(); }}");

        inspect(&source, |flow, semantic| {
            let left = node_of(semantic, &source, "left()");

            assert!(flow.edges.iter().any(|edge| edge.guard
                == if nullish {
                    Guard::Nullish(left)
                } else {
                    Guard::Falsy(left)
                }));
            assert!(flow.edges.iter().any(|edge| edge.guard
                == if nullish {
                    Guard::NonNullish(left)
                } else {
                    Guard::Truthy(left)
                }));
        });
    }
}

#[test]
fn parameter_defaults_are_conditional_and_nested_functions_are_opaque() {
    let source =
        "function f(x = fallback()){ function nested(y = hidden()){ nestedBody(); } body(); }";

    inspect(source, |flow, semantic| {
        let fallback = call(flow, semantic, source, "fallback()");
        let body = call(flow, semantic, source, "body()");

        assert!(flow
            .edges
            .iter()
            .any(|edge| matches!(edge.guard, Guard::Undefined(_))));
        assert!(reachable(flow, flow.entry, body, &[fallback]));
        assert!(reachable(flow, fallback, body, &[]));
        assert!(calls(flow, semantic, source, "hidden()").is_empty());
        assert!(calls(flow, semantic, source, "nestedBody()").is_empty());
    });
    inspect_named(source, "nested", |flow, semantic| {
        assert_eq!(calls(flow, semantic, source, "hidden()").len(), 1);
    });
}

#[test]
fn destructuring_and_argument_defaults_have_distinct_guards() {
    let source = "function f({x = fallback()} = objectDefault()){ body(); }";

    inspect(source, |flow, semantic| {
        let object = call(flow, semantic, source, "objectDefault()");
        let fallback = call(flow, semantic, source, "fallback()");
        let body = call(flow, semantic, source, "body()");
        let guards: HashSet<_> = flow
            .edges
            .iter()
            .filter_map(|edge| {
                if let Guard::Undefined(node) = edge.guard {
                    Some(node)
                } else {
                    None
                }
            })
            .collect();

        assert_eq!(guards.len(), 2);
        assert!(reachable(flow, object, fallback, &[]));
        assert!(reachable(flow, flow.entry, fallback, &[object]));
        assert!(reachable(flow, flow.entry, body, &[object, fallback]));
    });
}

#[test]
fn class_definition_keys_static_work_and_instance_work_are_separate() {
    let source = "function f(){ class C extends base() { static x = stat(); [key()] = instance(); static { block(); } method(x = hidden()) { methodBody(); } } after(); }";

    inspect(source, |flow, semantic| {
        let [base, key, instance, stat, block, after] = [
            "base()",
            "key()",
            "instance()",
            "stat()",
            "block()",
            "after()",
        ]
        .map(|text| call(flow, semantic, source, text));

        assert_eq!(semantic.classes().len(), 1);
        assert!(matches!(
            flow.points[instance.0].region,
            Region::Construction(_)
        ));
        assert!(matches!(
            flow.points[stat.0].region,
            Region::ClassDefinition(_)
        ));
        assert!(!reachable(flow, flow.entry, instance, &[]));
        assert!(reachable(
            flow,
            flow.construction_entries[0].1,
            instance,
            &[]
        ));
        assert!(reachable(flow, base, key, &[]));
        assert!(reachable(flow, key, stat, &[]));
        assert!(!reachable(flow, flow.entry, stat, &[key]));
        assert!(reachable(flow, stat, block, &[]));
        assert!(reachable(flow, block, after, &[]));
        assert!(calls(flow, semantic, source, "hidden()").is_empty());
    });
}

#[test]
fn labelled_continue_targets_outer_update_and_break_outer_exit() {
    let source = "function f(){ outer: for(;outerTest();outerUpdate()){ while(innerTest()){ continue outer; } break outer; } after(); }";

    inspect(source, |flow, semantic| {
        let update = call(flow, semantic, source, "outerUpdate()");
        let after = call(flow, semantic, source, "after()");
        let continued = node_of(semantic, source, "continue outer;");
        let broken = node_of(semantic, source, "break outer;");
        let point = |node| {
            FlowPointId(
                flow.points
                    .iter()
                    .position(|p| p.node == node && p.step == Step::Entry)
                    .unwrap(),
            )
        };

        assert!(reachable(flow, point(continued), update, &[]));
        assert!(!reachable(flow, point(continued), after, &[update]));
        assert!(reachable(flow, point(broken), after, &[update]));
        assert!(!flow.exits.iter().any(|exit| matches!(
            exit.completion,
            Completion::Break(_) | Completion::Continue(_)
        )));
    });
}

#[test]
fn labelled_nonloop_break_is_resolved() {
    let source = "function f(){ label: { if(p) break label; body(); } after(); }";

    inspect(source, |flow, semantic| {
        let body = call(flow, semantic, source, "body()");
        let after = call(flow, semantic, source, "after()");

        assert!(reachable(flow, flow.entry, after, &[body]));
        assert!(!flow
            .exits
            .iter()
            .any(|exit| matches!(exit.completion, Completion::Break(_))));
    });
}

#[test]
fn catch_return_runs_finally_without_false_normal_continuation() {
    let source = "function f(){ try { throw failure(); } catch(e){ caught(); return done(); } finally { cleanup(); } after(); }";

    inspect(source, |flow, semantic| {
        let after = call(flow, semantic, source, "after()");

        assert!(!reachable(flow, flow.entry, after, &[]));
        assert!(!flow
            .exits
            .iter()
            .any(|exit| exit.completion == Completion::Normal));
        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.action == CompletionAction::EnterFinally(Completion::Return)));
        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.action == CompletionAction::Resume(Completion::Return)));
        assert!(!calls(flow, semantic, source, "cleanup()").is_empty());
    });
}

#[test]
fn finally_return_replaces_prior_return_without_erasing_expression_work() {
    let source = "function f(){ try { return first(); } finally { return second(); } after(); }";

    inspect(source, |flow, semantic| {
        let first = call(flow, semantic, source, "first()");
        let seconds = calls(flow, semantic, source, "second()");

        assert!(seconds
            .iter()
            .any(|second| reachable(flow, first, *second, &[])));
        assert!(flow.edges.iter().any(|edge| edge.action
            == CompletionAction::Replace {
                pending: Completion::Return,
                replacement: Completion::Return
            }));
        assert!(!reachable(
            flow,
            flow.entry,
            call(flow, semantic, source, "after()"),
            &[]
        ));
    });
}

#[test]
fn finally_continue_replaces_pending_return_and_reenters_test() {
    let source = "function f(){ while(test()){ try { return first(); } finally { continue; } } }";

    inspect(source, |flow, semantic| {
        let first = call(flow, semantic, source, "first()");
        let test = call(flow, semantic, source, "test()");

        assert!(reachable(flow, first, test, &[]));
        assert!(flow.edges.iter().any(|edge| matches!(
            edge.action,
            CompletionAction::Replace {
                pending: Completion::Return,
                replacement: Completion::Continue(_)
            }
        )));
        assert!(!flow
            .exits
            .iter()
            .any(|exit| exit.completion == Completion::Return));
    });
}

#[test]
fn nested_finalizers_resume_labelled_break_in_inside_out_order() {
    let source = "function f(){ outer: while(test()){ try { try { break outer; } finally { innerCleanup(); } } finally { outerCleanup(); } } after(); }";

    inspect(source, |flow, semantic| {
        let inner = call(flow, semantic, source, "innerCleanup()");
        let outer = calls(flow, semantic, source, "outerCleanup()");

        assert!(outer
            .iter()
            .any(|outer| reachable(flow, inner, *outer, &[])));
        assert!(flow
            .edges
            .iter()
            .any(|edge| matches!(edge.action, CompletionAction::Resume(Completion::Break(_)))));
        assert!(reachable(
            flow,
            inner,
            call(flow, semantic, source, "after()"),
            &[]
        ));
    });
}

#[test]
fn implicit_throw_and_normal_call_completion_remain_alternatives() {
    let source = "function f(){ try { maybeThrow(); } catch(e){ recover(); } after(); }";

    inspect(source, |flow, semantic| {
        let call = node_of(semantic, source, "maybeThrow()");
        let recover = calls(flow, semantic, source, "recover()")[0];

        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.guard == Guard::Throws(call)));
        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.guard == Guard::ReturnsNormally(call)));

        let after = calls(flow, semantic, source, "after()")[0];

        assert!(reachable(flow, flow.entry, after, &[recover]));
        assert!(reachable(flow, recover, after, &[]));
    });
}

#[test]
fn limits_and_unsupported_syntax_are_explicit() {
    let source = "function f(){ switch(value){ default: break; } }";
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .build(&parsed.program)
        .semantic;
    let function = semantic
        .nodes()
        .iter()
        .find(|node| matches!(node.kind(), AstKind::Function(_)))
        .unwrap()
        .id();

    assert!(matches!(
        FlowContext::new(&semantic)
            .unwrap()
            .build(FileId(0), function),
        Err(FlowError::Unsupported(_))
    ));
    assert!(matches!(
        FlowContext::new(&semantic)
            .unwrap()
            .build_with_limit(FileId(0), function, 1),
        Err(FlowError::ResourceLimit)
    ));

    let without_cfg = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;

    assert!(matches!(
        FlowContext::new(&without_cfg),
        Err(FlowError::MissingCfg)
    ));
}

#[test]
fn property_access_keeps_implicit_exception_path_to_catch() {
    let source = "function f(object: any){ try { object.value; } catch(e){ recover(); } }";

    inspect(source, |flow, semantic| {
        let property = node_of(semantic, source, "object.value");
        let recover = call(flow, semantic, source, "recover()");

        assert!(flow
            .edges
            .iter()
            .any(|edge| edge.guard == Guard::Throws(property)
                && reachable(flow, edge.to, recover, &[])));
    });
}

#[test]
fn multiple_labels_resolve_continue_to_same_iteration() {
    let source = "function f(){ outer: inner: while(test()){ continue outer; } }";

    inspect(source, |flow, _| {
        assert!(flow.edges.iter().any(|edge| matches!(
            edge.action,
            CompletionAction::Produce(Completion::Continue(_))
        )));
        assert!(!flow
            .exits
            .iter()
            .any(|exit| matches!(exit.completion, Completion::Continue(_))));
    });
}

#[test]
fn pinned_frontend_exposes_parse_and_semantic_diagnostics() {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, "function {", SourceType::ts()).parse();

    assert!(!parsed.diagnostics.is_empty());

    let parsed = Parser::new(&allocator, "let x; let x;", SourceType::ts()).parse();
    let result = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);

    assert!(!result.diagnostics.is_empty());
}

use olint::cost::{Cost, Domain, Part, Preference, Reading};
use olint::project::{FileId, Site};
use olint::trace::{
    render, ArenaLimits, RenderBudget, TraceArena, TraceId, TraceLayout, TraceNode, Truncation,
    TRUNCATION_MARKER,
};
use olint::unknowns::{SourceSpan, UnknownReason, Unknowns};
use std::fmt::{self, Write};

use crate::support;

#[test]
fn oversized_source_names_fail_before_trace_label_allocation() {
    let name = "long".repeat(2048);
    let source = format!("/** @perf O(N) */ function {name}(){{}} function root(){{{name}();}}");

    support::run_with_source(&source, |analysis, file| {
        let root = support::function_of_name(analysis.project, file, "root");
        let part = analysis
            .summarize(file, root)
            .total(&mut analysis.unknowns, &mut analysis.traces);

        assert!(!part.is_complete());
        assert!(support::unknown_reasons(analysis, part.unknowns)
            .contains(&UnknownReason::ResourceExhaustion));
        assert!(analysis.traces.stats().label_bytes < 4096);
    });
}

#[test]
fn oversized_dimension_labels_stop_at_the_output_sink() {
    let label = "λ".repeat(100_000);
    let cost = Cost::dimension(17, Domain::Size);
    let mut traces = TraceArena::default();
    let root = leaf(&mut traces, cost.clone(), 1);
    let rendered = render(
        &traces,
        root,
        0,
        RenderBudget {
            visits: 10,
            depth: 10,
            bytes: 96,
        },
        &|_, out| out.write_str("index.ts:1"),
        &|cost, full, out| cost.write_with(out, full, &|_, out| out.write_str(&label)),
    )
    .unwrap();

    assert_eq!(rendered.truncated, Some(Truncation::Bytes));
    assert_eq!(rendered.text, TRUNCATION_MARKER);
    support::run_with_source("void 0;", |analysis, _| {
        let root = analysis.unknowns.origin(span(0), UnknownReason::Target);
        let scaled = analysis
            .unknowns
            .scale(Some(root), Some(cost.clone()))
            .unwrap();
        let rendered = analysis.unknowns.render_with(
            analysis.project,
            scaled,
            &|_, out| out.write_str(&label),
            RenderBudget {
                visits: 10,
                depth: 10,
                bytes: 128,
            },
        );

        assert!(rendered.truncated);
        assert_eq!(rendered.text, TRUNCATION_MARKER);
    });
}

#[test]
fn unresolved_statement_keeps_trace_resource_origin() {
    let source="function kernel(n:number){\n/** @perf O(n^2+N^3) */\nvoid 0;} function root(n:number){kernel(n-n);}";

    support::run_with_source(source, |analysis, file| {
        let root = support::function_of_name(analysis.project, file, "root");
        let part = limited_trace(analysis, file, root);
        let reasons = support::unknown_reasons(analysis, part.unknowns);

        assert!(reasons.contains(&UnknownReason::SizeRelation));
        assert!(reasons.contains(&UnknownReason::ResourceExhaustion));

        let mut pending: Vec<_> = part.unknowns.into_iter().collect();
        let mut found = false;

        while let Some(id) = pending.pop() {
            use olint::unknowns::UnknownNode;

            match analysis.unknowns.node(id) {
                UnknownNode::Origin(unknown) => {
                    found |= unknown.reason == UnknownReason::ResourceExhaustion
                        && unknown.origin.start == source.find("void 0").unwrap() as u32
                }
                UnknownNode::Call { child, .. } | UnknownNode::Scale { child, .. } => {
                    pending.push(*child)
                }
                UnknownNode::Join { children } => pending.extend(children.iter().copied()),
            }
        }

        assert!(
            found,
            "selected provenance lost the statement resource origin"
        );
    });
}

#[test]
fn semantic_key_rejection_cannot_publish_a_fabricated_specialization() {
    support::run_with_source("function root(cb:()=>void){cb();}", |analysis, file| {
        use olint::analysis::work::Event;

        use olint::declarations::{Binding, FunctionNode};

        use olint::summaries::{SchedulerLimits, Substitutions};

        use olint::values::ArgumentFacts;

        let function = support::function_of_name(analysis.project, file, "root");
        let FunctionNode::Function(inner) = function else {
            panic!("function declaration");
        };
        let oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) =
            &inner.params.items[0].pattern
        else {
            panic!("plain parameter");
        };
        let source = SourceSpan {
            file,
            start: identifier.span.start,
            end: identifier.span.end,
        };
        let mut callback = Part::unmarked(Cost::N, None);
        callback.unknowns = Some(analysis.unknowns.origin(source, UnknownReason::Target));
        let facts = ArgumentFacts {
            value: analysis.values.at(source),
            callback: Some(callback),
            preference: Preference::Unmarked,
            definedness: olint::values::Definedness::Unknown,
        };
        let inputs = Substitutions::from([(
            Binding::Symbol {
                file,
                symbol: identifier.symbol_id.get().unwrap(),
            },
            facts,
        )]);
        let mut limits = SchedulerLimits::default();
        limits.work = limits.work.with(Event::SemanticIdentity, 0);

        analysis.set_scheduler_limits(limits).unwrap();

        let reading = analysis.summarize_with(file, function, inputs.clone(), false);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

        assert!(support::unknown_reasons(analysis, part.unknowns)
            .contains(&UnknownReason::ResourceExhaustion));
        assert_eq!(analysis.scheduler_stats().tasks, 0);
        analysis
            .set_scheduler_limits(SchedulerLimits::default())
            .unwrap();

        let reading = analysis.summarize_with(file, function, inputs, false);

        assert!(reading
            .total(&mut analysis.unknowns, &mut analysis.traces)
            .trace
            .is_some());
        assert_eq!(analysis.scheduler_stats().ready, 1);
    });
}

#[test]
fn unknown_rendering_preserves_paths_and_bounds_diamond_expansion() {
    support::run_with_source(&" ".repeat(256), |analysis, _| {
        let origin = Some(analysis.unknowns.origin(span(0), UnknownReason::Target));
        let direct = analysis.unknowns.called(origin, span(1));
        let scaled = analysis.unknowns.scale(origin, Some(Cost::N));
        let looped = analysis.unknowns.called(scaled, span(2));
        let root = analysis.unknowns.join(direct, looped).unwrap();
        let rendered = analysis.unknowns.render_with(
            analysis.project,
            root,
            &|id, out| write!(out, "size_{id}"),
            RenderBudget::default(),
        );

        assert!(!rendered.truncated);
        assert_eq!(rendered.text.lines().count(), 2);
        assert!(rendered.text.contains("multiplicity O(1) via"));
        assert!(rendered.text.contains("multiplicity O(N) via"));

        let mut root = Some(root);

        for index in 0..30 {
            let left = analysis.unknowns.called(root, span(10 + index * 2));
            let right = analysis.unknowns.called(root, span(11 + index * 2));
            root = analysis.unknowns.join(left, right);
        }

        assert!(analysis.unknowns.len() <= 96);

        let budget = RenderBudget {
            visits: 100,
            depth: 128,
            bytes: 4096,
        };
        let rendered = analysis.unknowns.render_with(
            analysis.project,
            root.unwrap(),
            &|id, out| write!(out, "size_{id}"),
            budget,
        );

        assert!(rendered.truncated);
        assert!(rendered.text.ends_with(TRUNCATION_MARKER));
        assert!(rendered.stats.visits <= 100);
        assert!(rendered.stats.path_frames <= 100);
        assert!(rendered.stats.bytes <= 4096);
    });
}

#[test]
fn trace_capacity_failure_preserves_known_selected_cost() {
    support::run_with_source(
        "export function root(){\n/** @perf O(N^3) */\nvoid 0;}",
        |analysis, file| {
            let root = support::function_of_name(analysis.project, file, "root");
            let part = limited_trace(analysis, file, root);
            let expected = analysis
                .bind_function_cost(file, root, &Cost::parse("O(N^3)").unwrap())
                .unwrap();

            assert_eq!(part.cost, expected);
            assert!(!part.is_complete());
            assert!(support::unknown_reasons(analysis, part.unknowns)
                .contains(&UnknownReason::ResourceExhaustion));
            assert_eq!(analysis.traces.stats().nodes, 0);
        },
    );
}

#[test]
fn source_chains_retain_linear_explanations_and_reset_preserves_handles() {
    for count in [128, 512] {
        for reverse in [false, true] {
            for partial in [false, true] {
                let mut functions = Vec::new();

                for index in 0..count - 1 {
                    functions.push(format!("function f{index}(){{f{}();}}", index + 1));
                }

                functions.push(format!(
                    "function f{}(){{\n/** @perf O(N) */\nvoid 0; {} }}",
                    count - 1,
                    if partial { "opaque();" } else { "" }
                ));

                if reverse {
                    functions.reverse();
                }

                let source = format!("declare function opaque():void;\n{}", functions.join("\n"));

                support::run_with_source(&source, |analysis, file| {
                    let function = support::function_of_name(analysis.project, file, "f0");
                    let reading = analysis.summarize(file, function);
                    let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

                    assert_eq!(!part.is_complete(), partial);

                    let stats = analysis.traces.stats();

                    assert!(stats.nodes <= 3 * count, "{stats:?}");
                    assert!(stats.edges <= 4 * count, "{stats:?}");
                    assert!(stats.shallow_key_edges <= 12 * count, "{stats:?}");
                    assert!(analysis.unknowns.len() <= 12 * count);
                    assert!(analysis.unknowns.edge_count() <= 16 * count);

                    let warm = analysis.summarize(file, function);

                    assert_eq!(warm, reading);
                    assert_eq!(analysis.traces.stats(), stats);

                    let root = part.trace.unwrap();

                    analysis.reset_between_passes();
                    assert!(analysis.traces.node(root).is_ok());
                    assert_eq!(
                        reading
                            .total(&mut analysis.unknowns, &mut analysis.traces)
                            .cost,
                        part.cost
                    );
                });
            }
        }
    }
}

fn span(start: u32) -> SourceSpan {
    SourceSpan {
        file: FileId(0),
        start,
        end: start + 1,
    }
}

fn leaf(arena: &mut TraceArena, cost: Cost, start: u32) -> TraceId {
    arena
        .insert(
            TraceNode {
                label: "for-of".into(),
                site: Site {
                    file: FileId(0),
                    line: 1,
                },
                cost,
                children: vec![],
            },
            Some(span(start)),
            TraceLayout::Factor { inner_children: 0 },
        )
        .unwrap()
}

fn cost_text(cost: &Cost, full: bool, out: &mut dyn Write) -> fmt::Result {
    let text = cost.text();

    out.write_str(if full {
        &text
    } else {
        text.strip_prefix("O(")
            .and_then(|text| text.strip_suffix(')'))
            .unwrap_or(&text)
    })
}

#[test]
fn actual_parts_keep_scalar_selection_independent_of_trace_descendants() {
    let mut traces = TraceArena::default();
    let mut unknowns = Unknowns::default();
    let cubic = Cost::parse("O(N^3)").unwrap();
    let expensive = Part::unmarked(cubic.clone(), Some(leaf(&mut traces, cubic.clone(), 10)));
    let mut opaque = Part::unmarked(Cost::ONE, None).preferred(Preference::Hot);
    opaque.unknowns = Some(unknowns.origin(span(11), UnknownReason::Target));

    traces.reset_node_reads();

    let selected = expensive
        .clone()
        .max(opaque.clone(), &mut unknowns, &mut traces);

    assert_eq!(selected.cost, Cost::ONE);
    assert_eq!(selected.preference, Preference::Hot);
    assert!(!selected.is_complete());
    assert_eq!(selected.trace, None);

    let excluded = opaque.preferred(Preference::Cold).max(
        expensive.clone().preferred(Preference::Hot),
        &mut unknowns,
        &mut traces,
    );

    assert_eq!(excluded.cost, cubic);
    assert!(excluded.is_complete());
    assert_eq!(excluded.trace, expensive.trace);

    let reading = Reading::of_part(excluded.clone());
    let copies = vec![reading; 1000];

    for reading in &copies {
        let total = reading.total(&mut unknowns, &mut traces);

        assert_eq!(total.cost, excluded.cost);
        assert_eq!(total.trace, excluded.trace);
    }

    assert_eq!(traces.stats().node_reads, 0);

    let before = traces.stats();
    let n = Cost::dimension(100, Domain::Size);
    let m = Cost::dimension(101, Domain::Size);
    let left = Part::unmarked(n, expensive.trace);
    let right = Part::unmarked(m, expensive.trace);
    let result = left.max(right, &mut unknowns, &mut traces);

    assert!(result.trace.is_some());
    assert_eq!(traces.stats().node_reads, 0);
    assert!(traces.stats().nodes <= before.nodes + 1);
    assert!(traces.stats().shallow_key_edges <= before.shallow_key_edges + 2);
}

#[test]
fn actual_source_same_line_calls_share_callee_but_not_call_span() {
    let source = "function leaf(xs:number[]){for(const x of xs)void x;} export function root(xs:number[]){leaf(xs);leaf(xs);}";

    support::run_with_source(source, |analysis, file| {
        let root = support::function_of_name(analysis.project, file, "root");

        analysis.summarize(file, root);

        let expected: Vec<_> = source
            .match_indices("leaf(xs)")
            .map(|(start, text)| (start as u32, (start + text.len()) as u32))
            .collect();
        let mut calls = Vec::new();

        for index in 0..analysis.traces.stats().nodes {
            let id = TraceId(index as u32);
            let node = analysis.traces.node(id).unwrap();

            if node.label == "call leaf()" && !node.children.is_empty() {
                let origin = analysis.traces.origin(id).unwrap().unwrap();

                calls.push((id, origin, node.children[0]));
            }
        }

        for (start, end) in expected {
            assert!(calls.iter().any(|(_, origin, _)| origin.file == file
                && origin.start == start
                && origin.end == end));
        }

        assert!(calls
            .iter()
            .any(|(left, left_site, child)| calls.iter().any(
                |(right, right_site, right_child)| left != right
                    && left_site != right_site
                    && child == right_child
            )));
        support::assert_scheduler_terminal(analysis.scheduler_stats());
        analysis.traces.reset_node_reads();

        let before = analysis.traces.stats();
        let result = analysis.summarize(file, root);

        assert!(result
            .total(&mut analysis.unknowns, &mut analysis.traces)
            .trace
            .is_some());

        let after = analysis.traces.stats();

        assert_eq!(after.nodes, before.nodes);
        assert_eq!(after.edges, before.edges);
        assert_eq!(after.insertion_attempts, before.insertion_attempts);
        assert_eq!(after.node_reads, 0);
    });
}

#[test]
fn actual_deep_trace_parts_render_and_drop_on_a_small_rust_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut traces = TraceArena::new(ArenaLimits::default());
            let mut root = leaf(&mut traces, Cost::ONE, 0);

            for index in 1..=50_000 {
                root = traces
                    .insert(
                        TraceNode {
                            label: "call shared()".into(),
                            site: Site {
                                file: FileId(0),
                                line: 1,
                            },
                            cost: Cost::ONE,
                            children: vec![root],
                        },
                        Some(span(index)),
                        TraceLayout::Factor { inner_children: 1 },
                    )
                    .unwrap();
            }

            assert_eq!(traces.stats().nodes, 50_001);
            assert_eq!(traces.stats().edges, 50_000);
            assert_eq!(traces.stats().shallow_key_edges, 50_000);

            let part = Part::unmarked(Cost::ONE, Some(root));
            let retained = vec![Reading::of_part(part.clone()); 1000];
            let rendered = render(
                &traces,
                root,
                0,
                RenderBudget {
                    visits: 7,
                    depth: 16,
                    bytes: 1024,
                },
                &|site, out| write!(out, "index.ts:{}", site.line),
                &cost_text,
            )
            .unwrap();

            assert_eq!(rendered.truncated, Some(Truncation::Visits));
            assert_eq!(rendered.stats.visits, 7);
            assert!(rendered.stats.peak_frames <= 8);
            assert!(rendered.text.len() <= 1024);
            assert!(rendered.text.ends_with(TRUNCATION_MARKER));
            assert!(part.is_complete());
            drop(retained);
            drop(part);
            drop(traces);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn limited_trace<'a>(
    analysis: &mut olint::analysis::Analysis<'_, 'a>,
    file: FileId,
    root: olint::declarations::FunctionNode<'a>,
) -> Part {
    analysis.traces = TraceArena::new(ArenaLimits {
        nodes: 0,
        ..ArenaLimits::default()
    });

    analysis
        .summarize(file, root)
        .total(&mut analysis.unknowns, &mut analysis.traces)
}

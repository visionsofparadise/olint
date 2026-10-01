use super::*;

fn source(start: u32) -> SourceSpan {
    SourceSpan {
        file: crate::project::FileId(0),
        start,
        end: start + 1,
    }
}

fn factor(
    arena: &mut TraceArena,
    label: &str,
    degree: u32,
    line: u32,
    start: u32,
    children: Vec<TraceId>,
    inner_children: u8,
) -> TraceId {
    arena
        .insert(
            TraceNode {
                label: label.into(),
                site: Site {
                    file: crate::project::FileId(0),
                    line,
                },
                cost: if degree == 0 {
                    Cost::ONE
                } else {
                    Cost::power(Cost::N, Cost::constant(u64::from(degree))).unwrap()
                },
                children,
                derivation: None,
            },
            Some(source(start)),
            TraceLayout::Factor { inner_children },
        )
        .unwrap()
}

fn group(arena: &mut TraceArena, children: Vec<TraceId>) -> TraceId {
    arena
        .insert(
            TraceNode {
                label: String::new(),
                site: Site {
                    file: crate::project::FileId(0),
                    line: 1,
                },
                cost: Cost::ONE,
                children,
                derivation: None,
            },
            None,
            TraceLayout::Group,
        )
        .unwrap()
}

fn shown(arena: &TraceArena, root: TraceId, depth: usize, budget: RenderBudget) -> Rendered {
    render(
        arena,
        root,
        depth,
        budget,
        &|site, out| write!(out, "file{}.ts:{}", site.file.0, site.line),
        &|cost, full, out| {
            let text = cost.text();

            out.write_str(if full {
                &text
            } else {
                &text[2..text.len() - 1]
            })
        },
    )
    .unwrap()
}

#[test]
fn repeated_calls_share_callees_and_keep_same_line_site_identity() {
    let mut arena = TraceArena::default();
    let callee = factor(&mut arena, "scan()", 1, 9, 90, vec![], 0);
    let first = factor(&mut arena, "call scan()", 1, 1, 1, vec![callee], 1);
    let again = factor(&mut arena, "call scan()", 1, 1, 1, vec![callee], 1);
    let second = factor(&mut arena, "call scan()", 1, 1, 10, vec![callee], 1);

    assert_eq!(first, again);
    assert_ne!(first, second);
    assert_eq!(arena.origin(first).unwrap(), Some(source(1)));
    assert_eq!(arena.origin(second).unwrap(), Some(source(10)));
    assert_eq!(arena.stats().nodes, 3);
    assert_eq!(arena.stats().edges, 2);
    assert_eq!(arena.stats().intern_hits, 1);
    assert_eq!(arena.stats().node_reads, 0);

    let root = group(&mut arena, vec![first, second]);
    let output = shown(&arena, root, 1, RenderBudget::default());

    assert_eq!(output.text.matches("calls scan()").count(), 2);
    assert_eq!(output.text.matches("does scan()").count(), 2);
    assert_eq!(output.stats.visits, 5);
    assert_eq!(output.stats.edges, 4);
    assert_eq!(output.stats.lines, 4);
    assert_eq!(output.truncated, None);
}

#[test]
fn factor_layout_preserves_inner_and_continuation_indentation() {
    let mut arena = TraceArena::default();
    let inner_leaf = factor(&mut arena, "scan()", 1, 3, 30, vec![], 0);
    let inner_loop = factor(&mut arena, "for-of cells", 1, 2, 20, vec![inner_leaf], 0);
    let suffix = factor(&mut arena, "done()", 0, 4, 40, vec![], 0);
    let call = factor(
        &mut arena,
        "call helper()",
        2,
        1,
        10,
        vec![inner_loop, suffix],
        1,
    );
    let output = shown(&arena, call, 1, RenderBudget::default());
    let lines: Vec<_> = output.text.lines().collect();

    assert_eq!(
        lines,
        [
            format!("    calls {:48} file0.ts:1  = O(N^2)", "helper()"),
            format!("    in loop {:48} file0.ts:2  x N", "for-of cells"),
            format!("        does {:44} file0.ts:3  x N", "scan()"),
            format!("    does {:48} file0.ts:4", "done()"),
        ]
    );
}

#[test]
fn labels_utf16_padding_and_preference_handles_survive_sharing() {
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct ScalarReading {
        cost: Cost,
        trace: Option<TraceId>,
        preference: u8,
        partial: bool,
    }

    let mut arena = TraceArena::default();
    let leaf = factor(&mut arena, "💚()", 1, 3, 30, vec![], 0);
    let hot = factor(&mut arena, "@perf hot", 1, 1, 10, vec![leaf], 1);
    let cold = factor(&mut arena, "@perf cold", 1, 2, 20, vec![leaf], 1);
    let reading = ScalarReading {
        cost: Cost::N,
        trace: Some(hot),
        preference: 3,
        partial: true,
    };
    let ignored = ScalarReading {
        cost: Cost::ONE,
        trace: None,
        preference: 0,
        partial: false,
    };
    let before = arena.stats();

    assert_eq!(reading.clone(), reading);
    assert_eq!(ignored.clone().trace, None);
    assert_eq!(
        reading.cost.compare_legacy(&Cost::parse("O(N^2)").unwrap()),
        crate::cost::CostComparison::Within
    );
    assert_eq!(arena.stats(), before);
    assert_eq!(arena.stats().node_reads, 0);

    let hot_output = shown(&arena, reading.trace.unwrap(), 1, RenderBudget::default());
    let cold_output = shown(&arena, cold, 1, RenderBudget::default());

    assert!(hot_output.text.starts_with("    reads as @perf hot"));
    assert!(cold_output.text.starts_with("    reads as @perf cold"));

    let leaf_line = hot_output.text.lines().nth(1).unwrap();

    assert_eq!(
        leaf_line,
        format!("    does 💚(){} file0.ts:3  x N", " ".repeat(44))
    );
    assert_eq!(reading.preference, 3);
    assert!(reading.partial);
}

#[test]
fn ten_thousand_deep_call_nodes_render_and_drop_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut arena = TraceArena::default();
            let mut root = factor(&mut arena, "leaf()", 0, 1, 0, vec![], 0);

            for index in 1..=10_000 {
                root = factor(
                    &mut arena,
                    "call next()",
                    0,
                    index + 1,
                    index,
                    vec![root],
                    1,
                );
            }

            assert_eq!(arena.stats().nodes, 10_001);
            assert_eq!(arena.stats().edges, 10_000);
            assert_eq!(arena.stats().shallow_key_edges, 10_000);
            assert_eq!(arena.stats().node_reads, 0);

            let result = shown(
                &arena,
                root,
                1,
                RenderBudget {
                    visits: 10_001,
                    depth: 2,
                    bytes: 2 * 1024 * 1024,
                },
            );

            assert_eq!(result.stats.visits, 10_001);
            assert_eq!(result.stats.peak_frames, 10_001);
            assert_eq!(result.stats.lines, 10_001);
            assert_eq!(result.truncated, None);
            drop(result);
            drop(arena);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn growing_depth_stops_before_quadratic_indentation_output() {
    let mut arena = TraceArena::default();
    let mut root = factor(&mut arena, "work()", 0, 1, 0, vec![], 0);

    for index in 1..=10_000 {
        root = factor(
            &mut arena,
            "for-of rows",
            1,
            index + 1,
            index,
            vec![root],
            0,
        );
    }

    let output = shown(
        &arena,
        root,
        1,
        RenderBudget {
            visits: 20_000,
            depth: 8,
            bytes: 4096,
        },
    );

    assert_eq!(output.truncated, Some(Truncation::Depth));
    assert_eq!(output.stats.visits, 8);
    assert!(output.stats.peak_frames <= 9);
    assert!(output.text.ends_with(TRUNCATION_MARKER));
    assert!(output.stats.bytes <= 4096);
}

#[test]
fn shared_diamond_expansion_has_a_deterministic_presentation_bound() {
    let mut arena = TraceArena::default();
    let mut root = factor(&mut arena, "work()", 0, 1, 0, vec![], 0);

    for _ in 0..30 {
        root = group(&mut arena, vec![root, root]);
    }

    assert_eq!(arena.stats().nodes, 31);
    assert_eq!(arena.stats().edges, 60);

    let budget = RenderBudget {
        visits: 100,
        depth: 1,
        bytes: 32_000,
    };
    let first = shown(&arena, root, 1, budget);
    let second = shown(&arena, root, 1, budget);

    assert_eq!(first.truncated, Some(Truncation::Visits));
    assert_eq!(first.stats.visits, 100);
    assert!(first.stats.peak_frames <= 31);
    assert_eq!(first.stats, second.stats);
    assert_eq!(first.text, second.text);
    assert!(first.text.ends_with(TRUNCATION_MARKER));
}

#[test]
fn byte_budget_removes_partial_lines_and_preserves_the_omission_marker() {
    let mut arena = TraceArena::default();
    let root = factor(&mut arena, &"x".repeat(4000), 1, 1, 0, vec![], 0);
    let output = shown(
        &arena,
        root,
        1,
        RenderBudget {
            visits: 2,
            depth: usize::MAX,
            bytes: 100,
        },
    );

    assert_eq!(output.truncated, Some(Truncation::Bytes));
    assert_eq!(output.text, TRUNCATION_MARKER);
    assert_eq!(output.stats.lines, 0);

    let visits = shown(
        &arena,
        root,
        1,
        RenderBudget {
            visits: 0,
            depth: 0,
            bytes: TRUNCATION_MARKER.len(),
        },
    );

    assert_eq!(visits.stats.visits, 0);
    assert_eq!(visits.text, TRUNCATION_MARKER);

    let depth = shown(
        &arena,
        root,
        usize::MAX,
        RenderBudget {
            visits: 1,
            depth: usize::MAX,
            bytes: 100,
        },
    );

    assert_eq!(depth.truncated, Some(Truncation::Depth));
}

#[test]
fn invalid_edges_sites_layouts_and_capacity_are_explicit() {
    let mut arena = TraceArena::new(ArenaLimits {
        nodes: 1,
        ..ArenaLimits::default()
    });
    let node = TraceNode {
        label: "work()".into(),
        site: Site {
            file: crate::project::FileId(0),
            line: 1,
        },
        cost: Cost::ONE,
        children: vec![],
        derivation: None,
    };
    let layout = TraceLayout::Factor { inner_children: 0 };

    assert_eq!(
        arena.insert(
            TraceNode {
                children: vec![TraceId(0)],
                ..node.clone()
            },
            Some(source(0)),
            layout
        ),
        Err(TraceError::InvalidId)
    );
    assert_eq!(
        arena.insert(
            TraceNode {
                label: "call work()".into(),
                ..node.clone()
            },
            None,
            layout
        ),
        Err(TraceError::InvalidOrigin)
    );
    assert_eq!(
        arena.insert(
            node.clone(),
            Some(SourceSpan {
                file: crate::project::FileId(1),
                start: 0,
                end: 1
            }),
            layout
        ),
        Err(TraceError::InvalidOrigin)
    );
    assert_eq!(
        arena.insert(
            node.clone(),
            Some(source(0)),
            TraceLayout::Factor { inner_children: 1 }
        ),
        Err(TraceError::InvalidLayout)
    );

    let root = arena.insert(node.clone(), Some(source(0)), layout).unwrap();

    assert_eq!(
        arena.insert(node.clone(), Some(source(0)), layout),
        Ok(root)
    );
    assert_eq!(
        arena.insert(node, Some(source(1)), layout),
        Err(TraceError::Capacity)
    );
    assert_eq!(arena.stats().nodes, 1);
    assert_eq!(arena.node(TraceId(1)), Err(TraceError::InvalidId));
    assert!(matches!(
        render(
            &arena,
            root,
            1,
            RenderBudget {
                bytes: 0,
                ..RenderBudget::default()
            },
            &|_, _| Ok(()),
            &|_, _, _| Ok(())
        ),
        Err(RenderError::BudgetTooSmall)
    ));
}

#[test]
fn retained_nodes_and_edges_scale_with_wrappers_in_both_orders() {
    for count in [1000, 2000] {
        let mut arena = TraceArena::default();
        let leaf = factor(&mut arena, "work()", 1, 1, 0, vec![], 0);
        let callers: Vec<_> = (1..=count)
            .map(|index| factor(&mut arena, "call shared()", 1, index, index, vec![leaf], 1))
            .collect();
        let before = arena.stats();

        for index in (1..=count).rev() {
            let same = factor(&mut arena, "call shared()", 1, index, index, vec![leaf], 1);

            assert_eq!(same, callers[(index - 1) as usize]);
        }

        let after = arena.stats();

        assert_eq!(after.nodes, count as usize + 1);
        assert_eq!(after.edges, count as usize);
        assert_eq!(after.nodes, before.nodes);
        assert_eq!(after.intern_hits, count as usize);
        assert_eq!(after.shallow_key_edges, count as usize * 2);
        assert_eq!(after.node_reads, 0);
    }
}

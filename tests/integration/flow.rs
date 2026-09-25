use olint::flow::{
    class_phases_of, completion_of, interceptions_of, loop_phases_of, Completion, FlowError,
    Interception, Region, Resumption,
};
use olint::project::{DiagnosticPhase, Project, ProjectError};
use olint::unknowns::UnknownReason;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;

use crate::support;

use support::{file_of, first_node_of, project_of, run_in_project};

fn first_function_of(project: &Project<'_>, file: olint::project::FileId) -> NodeId {
    first_node_of(project, file, |kind| match kind {
        AstKind::Function(function) => Some(function.node_id()),
        _ => None,
    })
}

fn run_in_file(source: &str, body: impl for<'a> FnOnce(&olint::project::SourceFile<'a>, &str)) {
    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |project, root| body(project.file(file_of(project, root, "index.ts")), source),
    );
}

#[test]
fn project_flow_reuses_source_index_and_retains_semantic_anchors() {
    let source = (0..128)
        .map(|index| format!("export function f{index}(x = input()) {{ return x; }}"))
        .collect::<String>();

    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", &source)],
        |project, root| {
            let file = project.file(file_of(project, root, "index.ts"));
            let context = file.flow_context().unwrap();

            assert_eq!(context.indexed_nodes, file.semantic.nodes().len());

            let mut visits = 0;

            for node in file
                .semantic
                .nodes()
                .iter()
                .filter(|node| matches!(node.kind(), AstKind::Function(_)))
            {
                let first = file.flow(node.id()).unwrap();
                let second = context.build(file.id, node.id()).unwrap();

                assert_eq!(first.file, file.id);
                assert_eq!(first.function, node.id());
                assert_eq!(first.points.len(), second.points.len());
                assert_eq!(first.edges.len(), second.edges.len());

                visits += first.node_visits;

                for point in &first.points {
                    assert_eq!(point.cfg, file.semantic.nodes().cfg_id(point.node));
                    assert_eq!(point.region, Region::Invocation(node.id()));
                }

                assert!(first
                    .exits
                    .iter()
                    .any(|exit| exit.completion == Completion::Return));
            }

            assert!(visits <= context.indexed_nodes);
        },
    );
}

#[test]
fn unsupported_and_resource_failures_retain_their_source() {
    let source = "export function f(){ switch (value) { default: break; } }";

    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |project, root| {
            let file = project.file(file_of(project, root, "index.ts"));
            let function = file
                .semantic
                .nodes()
                .iter()
                .find(|node| matches!(node.kind(), AstKind::Function(_)))
                .unwrap()
                .id();
            let unsupported = file.flow(function).unwrap_err();

            assert_eq!(unsupported.file, file.id);
            assert_eq!(
                unsupported.unknown_reason(),
                UnknownReason::UnsupportedSyntax
            );
            assert!(matches!(unsupported.error, FlowError::Unsupported(_)));
            assert!(unsupported.span.source_text(source).starts_with("switch"));

            let resource = file.flow_with_limit(function, 0).unwrap_err();

            assert_eq!(resource.unknown_reason(), UnknownReason::ResourceExhaustion);
            assert_eq!(resource.error, FlowError::ResourceLimit);
            assert!(resource.span.source_text(source).starts_with("function"));
            assert!(matches!(
                file.flow(NodeId::new(file.semantic.nodes().len() + 1))
                    .unwrap_err()
                    .error,
                FlowError::InvalidTarget(_)
            ));
        },
    );
}

#[test]
fn project_retains_recoverable_parser_and_semantic_diagnostics() {
    for (source, phase) in [
        ("export function f(){ const x; }", DiagnosticPhase::Parse),
        (
            "export function f(){ let x; let x; }",
            DiagnosticPhase::Semantic,
        ),
    ] {
        run_in_project(
            &[("tsconfig.json", "{}"), ("index.ts", source)],
            |project, root| {
                let file = project.file(file_of(project, root, "index.ts"));

                assert!(file
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.phase == phase
                        && !diagnostic.message.is_empty()
                        && !diagnostic.spans.is_empty()));
                assert!(
                    matches!(file.flow_context(), Err(error) if error.error == FlowError::InvalidSource)
                );
            },
        );
    }
}

#[test]
fn unrecoverable_syntax_keeps_the_project_parse_error() {
    let directory = project_of(&[("tsconfig.json", "{}"), ("index.ts", "function {")]);
    let allocator = Allocator::default();

    assert!(
        matches!(Project::load(&allocator, &directory.path().join("tsconfig.json")), Err(ProjectError::Parse { message, .. }) if !message.is_empty())
    );
}

#[test]
fn class_phases_separate_accessor_initializers_and_skip_index_signatures() {
    let source = "export function f(){ const C = class extends base() { [key: string]: unknown; static accessor shared = stat(); accessor [name()] = instance(); declare hidden: number; static { block(); } run() { method(); } }; after(); }";

    run_in_project(
        &[("tsconfig.json", "{}"), ("index.ts", source)],
        |project, root| {
            let file = project.file(file_of(project, root, "index.ts"));
            let nodes = file.semantic.nodes();
            let call = |text: &str| {
                nodes
                    .iter()
                    .find(|node| {
                        matches!(node.kind(), AstKind::CallExpression(call) if call.span.source_text(source) == text)
                    })
                    .unwrap()
                    .id()
            };
            let function = first_function_of(project, file.id);
            let class = nodes
                .iter()
                .find_map(|node| match node.kind() {
                    AstKind::Class(class) => Some(class),
                    _ => None,
                })
                .unwrap();
            let phases = class_phases_of(class);
            let flow = file.flow(function).unwrap();
            let region = |text: &str| {
                let node = call(text);

                flow.points
                    .iter()
                    .find(|point| point.node == node)
                    .map(|point| point.region)
            };

            assert_eq!(phases.heritage, Some(call("base()")));
            assert_eq!(phases.keys.len(), 1);
            assert_eq!(phases.statics.len(), 2);
            assert_eq!(
                phases
                    .instances
                    .iter()
                    .map(|(_, value)| *value)
                    .collect::<Vec<_>>(),
                vec![call("instance()")]
            );
            assert!(phases
                .instances
                .iter()
                .all(|(element, _)| matches!(nodes.kind(*element), AstKind::AccessorProperty(_))));
            assert_eq!(phases.decorated, None);

            for text in ["base()", "name()", "stat()", "block()"] {
                assert!(
                    matches!(region(text), Some(Region::ClassDefinition(_))),
                    "{text}"
                );
            }

            assert!(matches!(
                region("instance()"),
                Some(Region::Construction(_))
            ));
            assert_eq!(region("method()"), None);
            assert!(matches!(region("after()"), Some(Region::Invocation(_))));
            assert_eq!(flow.construction_entries.len(), 1);
        },
    );
}

#[test]
fn decorated_elements_and_parameters_report_their_decorator_as_unsupported() {
    for (source, decorated) in [
        (
            "export function f(){ class C { @mark run() {} } }",
            "@mark run",
        ),
        (
            "export function f(){ class C { constructor(@mark v: number) {} } }",
            "@mark v",
        ),
        (
            "export function f(){ class C { run(@mark v: number) {} } }",
            "@mark v",
        ),
    ] {
        run_in_project(
            &[("tsconfig.json", "{}"), ("index.ts", source)],
            |project, root| {
                let file = project.file(file_of(project, root, "index.ts"));
                let failure = file.flow(first_function_of(project, file.id)).unwrap_err();

                assert!(matches!(failure.error, FlowError::Unsupported(_)));
                assert!(failure.span.source_text(source).starts_with(decorated));
            },
        );
    }
}

#[test]
fn loop_phases_separate_once_only_initialization_from_repeated_tests() {
    let source = "export function f(xs: number[], o: Record<string, number>) {\n\tfor (let i = 0; i < xs.length; i++) void i;\n\twhile (xs.length > 0) break;\n\tdo {\n\t\tvoid 0;\n\t} while (xs.length > 0);\n\tfor (const value of xs) void value;\n\tfor (const key in o) void key;\n}";

    run_in_file(source, |file, source| {
        let nodes = file.semantic.nodes();
        let phases_of = |prefix: &str| {
            nodes
                .iter()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        AstKind::ForStatement(_)
                            | AstKind::WhileStatement(_)
                            | AstKind::DoWhileStatement(_)
                            | AstKind::ForOfStatement(_)
                            | AstKind::ForInStatement(_)
                    )
                })
                .find(|node| node.kind().span().source_text(source).starts_with(prefix))
                .and_then(|node| loop_phases_of(node.kind()))
                .unwrap_or_else(|| panic!("{prefix} is an iteration statement"))
        };
        let text =
            |node: Option<NodeId>| node.map(|node| nodes.kind(node).span().source_text(source));

        let counted = phases_of("for (let i");

        assert_eq!(text(counted.initialize), Some("let i = 0"));
        assert_eq!(text(counted.test), Some("i < xs.length"));
        assert_eq!(text(counted.update), Some("i++"));
        assert_eq!(text(counted.iterable), None);
        assert_eq!(text(counted.binding), None);
        assert_eq!(text(Some(counted.body)), Some("void i;"));
        assert!(!counted.tested_after);
        assert!(!counted.iterates());
        assert!(counted.repeats(counted.test.unwrap()));
        assert!(counted.repeats(counted.update.unwrap()));
        assert!(!counted.repeats(counted.initialize.unwrap()));
        assert!(!counted.repeats(counted.body));

        let tested = phases_of("while (xs.length");

        assert_eq!(text(tested.initialize), None);
        assert_eq!(text(tested.test), Some("xs.length > 0"));
        assert!(!tested.tested_after);
        assert!(tested.repeats(tested.test.unwrap()));

        let tested_after = phases_of("do {");

        assert_eq!(text(tested_after.test), Some("xs.length > 0"));
        assert!(tested_after.tested_after);
        assert!(tested_after.repeats(tested_after.test.unwrap()));

        let iterated = phases_of("for (const value");

        assert_eq!(text(iterated.iterable), Some("xs"));
        assert_eq!(text(iterated.binding), Some("const value"));
        assert_eq!(text(iterated.test), None);
        assert!(iterated.iterates());
        assert!(iterated.repeats(iterated.binding.unwrap()));
        assert!(!iterated.repeats(iterated.iterable.unwrap()));

        let enumerated = phases_of("for (const key");

        assert_eq!(text(enumerated.iterable), Some("o"));
        assert_eq!(text(enumerated.binding), Some("const key"));
        assert!(enumerated.iterates());
        assert!(!enumerated.repeats(enumerated.iterable.unwrap()));
    });
}

fn node_of(file: &olint::project::SourceFile<'_>, source: &str, text: &str) -> NodeId {
    file.semantic
        .nodes()
        .iter()
        .find(|node| node.kind().span().source_text(source) == text)
        .unwrap_or_else(|| panic!("{text} is a node"))
        .id()
}

fn nodes_matching(
    file: &olint::project::SourceFile<'_>,
    predicate: fn(&AstKind<'_>) -> bool,
) -> Vec<NodeId> {
    file.semantic
        .nodes()
        .iter()
        .filter(|node| predicate(&node.kind()))
        .map(|node| node.id())
        .collect()
}

#[test]
fn break_and_continue_completions_resolve_their_labelled_and_switch_targets() {
    let source = "export function f(rows: number[][], flag: boolean) {\n\touter: for (const row of rows) {\n\t\tfor (const value of row) {\n\t\t\tif (flag) break outer;\n\t\t\tif (value > 0) continue outer;\n\t\t\tif (value < 0) continue;\n\t\t\tif (flag) {\n\t\t\t\tcontinue;\n\t\t\t} else {\n\t\t\t\treturn value;\n\t\t\t}\n\t\t}\n\t\tswitch (row.length) {\n\t\t\tcase 1:\n\t\t\t\tif (flag) break;\n\t\t\t\tthrow new Error('no');\n\t\t}\n\t}\n\treturn -1;\n}";

    run_in_file(source, |file, source| {
        let labelled = nodes_matching(file, |kind| matches!(kind, AstKind::LabeledStatement(_)))[0];
        let switched = nodes_matching(file, |kind| matches!(kind, AstKind::SwitchStatement(_)))[0];
        let loops = nodes_matching(file, |kind| matches!(kind, AstKind::ForOfStatement(_)));
        let completion = |text: &str| completion_of(&file.semantic, node_of(file, source, text));

        assert_eq!(loops.len(), 2);
        assert_eq!(
            completion("break outer;"),
            Some(Completion::Break(labelled))
        );
        assert_eq!(
            completion("continue outer;"),
            Some(Completion::Continue(loops[0]))
        );
        assert_eq!(
            completion("continue;"),
            Some(Completion::Continue(loops[1]))
        );
        assert_eq!(completion("break;"), Some(Completion::Break(switched)));
        assert_eq!(completion("return value;"), Some(Completion::Return));
        assert_eq!(
            completion("throw new Error('no');"),
            Some(Completion::Throw)
        );
        assert_eq!(
            completion(
                "if (flag) {\n\t\t\t\tcontinue;\n\t\t\t} else {\n\t\t\t\treturn value;\n\t\t\t}"
            ),
            Some(Completion::Continue(loops[1]))
        );
        assert_eq!(completion("return -1;"), Some(Completion::Return));
        assert_eq!(completion("rows"), None);
    });
}

#[test]
fn catch_and_finally_interceptions_resolve_their_resumption_targets() {
    let source = "export function f(rows: number[][]) {
	for (const row of rows) {
		try {
			try {
				return row.length;
			} finally {
				continue;
			}
		} catch (error) {
			throw error;
		} finally {
			row.pop();
		}
	}
	return -1;
}";

    run_in_file(source, |file, source| {
        let tries = nodes_matching(file, |kind| matches!(kind, AstKind::TryStatement(_)));
        let handler = nodes_matching(file, |kind| matches!(kind, AstKind::CatchClause(_)))[0];
        let finalizer = |text: &str| Resumption::Finalizer(node_of(file, source, text));
        let overriding = Interception {
            statement: tries[1],
            resumption: finalizer(
                "{
				continue;
			}",
            ),
        };
        let catching = Interception {
            statement: tries[0],
            resumption: Resumption::Handler(handler),
        };
        let cleaning = Interception {
            statement: tries[0],
            resumption: finalizer(
                "{
			row.pop();
		}",
            ),
        };
        let interceptions =
            |text: &str| interceptions_of(&file.semantic, node_of(file, source, text));

        assert_eq!(tries.len(), 2);
        assert_eq!(
            interceptions("return row.length;"),
            vec![overriding, catching, cleaning]
        );
        assert_eq!(interceptions("continue;"), vec![catching, cleaning]);
        assert_eq!(interceptions("throw error;"), vec![cleaning]);
        assert!(interceptions("row.pop();").is_empty());
    });
}

#[test]
fn nested_function_boundaries_stop_interception_and_control_resolution() {
    let source = "export function f(rows: number[][]) {\n\ttry {\n\t\tconst inner = () => {\n\t\t\tthrow new Error('inner');\n\t\t};\n\t\tinner();\n\t} catch (error) {\n\t\treturn 0;\n\t}\n\treturn rows.length;\n}";

    run_in_file(source, |file, source| {
        let thrown = node_of(file, source, "throw new Error('inner');");

        assert!(interceptions_of(&file.semantic, thrown).is_empty());
    });
}

#[test]
fn built_flow_resolves_the_same_control_targets_as_the_shared_resolver() {
    let source = "export function f(rows: number[][]) {\n\touter: inner: for (const row of rows) {\n\t\tfor (const value of row) {\n\t\t\tif (value > 0) continue outer;\n\t\t\tif (value < 0) break inner;\n\t\t}\n\t}\n\treturn rows.length;\n}";

    run_in_file(source, |file, source| {
        let labels = nodes_matching(file, |kind| matches!(kind, AstKind::LabeledStatement(_)));
        let iteration = nodes_matching(file, |kind| matches!(kind, AstKind::ForOfStatement(_)))[0];
        let function = nodes_matching(file, |kind| matches!(kind, AstKind::Function(_)))[0];
        let summary = file.flow(function).unwrap();

        assert_eq!(labels.len(), 2);
        assert_eq!(
            completion_of(&file.semantic, node_of(file, source, "continue outer;")),
            Some(Completion::Continue(iteration))
        );
        assert_eq!(
            completion_of(&file.semantic, node_of(file, source, "break inner;")),
            Some(Completion::Break(labels[1]))
        );
        assert!(summary.exits.iter().all(|exit| !matches!(
            exit.completion,
            Completion::Break(_) | Completion::Continue(_)
        )));
        assert!(summary
            .exits
            .iter()
            .any(|exit| exit.completion == Completion::Return));
    });
}

use olint::flow::{class_phases_of, Completion, FlowError, Region};
use olint::project::{DiagnosticPhase, Project, ProjectError};
use olint::unknowns::UnknownReason;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_semantic::NodeId;

mod support;

use support::{file_of, first_node_of, project_of, run_in_project};

fn first_function_of(project: &Project<'_>, file: olint::project::FileId) -> NodeId {
    first_node_of(project, file, |kind| match kind {
        AstKind::Function(function) => Some(function.node_id()),
        _ => None,
    })
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

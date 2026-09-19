use std::path::Path;

use olint::analysis::Analysis;
use olint::cost::Cost;
use olint::declarations::FunctionNode;
use olint::project::Project;
use olint::syntax::is_iteration_kind;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;

mod support;

use support::{run_with_source, SYNTACTIC};

fn loop_reasons_of(
    analysis: &mut Analysis<'_, '_>,
    file: olint::project::FileId,
) -> Vec<(String, String)> {
    let project = analysis.project;
    let nodes = project.file(file).semantic.nodes();
    let loops: Vec<_> = nodes
        .iter()
        .map(|node| node.kind())
        .filter(is_iteration_kind)
        .collect();
    let mut reasons = Vec::new();

    for kind in loops {
        let function = nodes
            .ancestors(kind.node_id())
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Function(function) => Some(FunctionNode::Function(function)),
                AstKind::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
                _ => None,
            })
            .expect("every fixture loop sits in a function");
        let bound = analysis.bound_of(file, kind);
        let reason = match bound.why {
            Some(why) => why.to_string(),
            None if bound.factor == Cost::LOG => "log".to_string(),
            None => "N".to_string(),
        };

        reasons.push((analysis.name_of(file, function), reason));
    }

    reasons
}

#[test]
fn every_bound_reason_fires_on_the_model_fixture() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/model");
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &root.join("tsconfig.json")).expect("fixture loads");
    let mut analysis = Analysis::new(&project, SYNTACTIC);
    let mut reasons = Vec::new();

    for name in ["src/bounds.ts", "src/branches.ts"] {
        let file = project
            .file_by_path(&root.join(name))
            .expect("fixture file loads");

        reasons.extend(loop_reasons_of(&mut analysis, file));
    }

    for (function, reason) in [
        ("constantBoundLoop", "constant bound"),
        ("constantOffsetFromStart", "constant offset from start"),
        ("geometricStepLoop", "geometric step"),
        ("whileHalvingShift", "halving"),
        ("whileHalvingMidpoint", "halving"),
        ("forOfTuple", "N"),
        ("forInClosed", "N"),
        ("forInRecord", "N"),
        ("singleIterationLoop", "single iteration"),
        ("boundedLoopStatement", "@perf bounded"),
    ] {
        assert!(
            reasons
                .iter()
                .any(|(found, why)| found == function && why == reason),
            "{function} reads {reason}: {reasons:?}"
        );
    }
}

#[test]
fn fresh_collections_keep_constant_and_closed_bounds() {
    run_with_source(
        "export function f() {
	const values = [1, 2];
	const table = { a: 1 };
	for (const value of values) void value;
	for (const key in table) void key;
}",
        |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![
                    ("f".to_string(), "constant collection".to_string()),
                    ("f".to_string(), "closed object type".to_string()),
                ]
            );
        },
    );
}

#[test]
fn a_while_counter_stepped_linearly_is_linear() {
    run_with_source(
        "export function f(n: number) {\n\twhile (n > 1) {\n\t\tn = n - 1;\n\t}\n}",
        |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![("f".to_string(), "N".to_string())]
            );
        },
    );
}

#[test]
fn unary_reads_preserve_bounds_while_updates_invalidate_them() {
    for (expression, expected) in [
        ("+n", "halving"),
        ("-n", "halving"),
        ("!n", "halving"),
        ("~n", "halving"),
        ("++n", "N"),
        ("--n", "N"),
        ("n++", "N"),
        ("n--", "N"),
    ] {
        let source = format!(
            "export function f(n: number) {{ while (n > 1) {{ consume({expression}); n >>= 1; }} }}"
        );

        run_with_source(&source, |analysis, file| {
            assert_eq!(
                loop_reasons_of(analysis, file),
                vec![("f".to_string(), expected.to_string())],
                "{expression}"
            );
        });
    }
}

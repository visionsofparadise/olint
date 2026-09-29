use std::path::{Path, PathBuf};

use olint::analysis::{Analysis, Options};
use olint::config::read_config;
use olint::project::Project;
use olint::public::public_functions;
use olint::report::report_rows_of;
use olint::snapshot::{snapshot_rows, NodeKey, NodeRow, NodeState};
use oxc_allocator::Allocator;
use oxc_span::GetSpan;

use crate::support;

use support::SYNTACTIC;

const RECORDING: Options = Options {
    record_nodes: true,
    ..SYNTACTIC
};

fn model_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/model")
}

fn model_rows_with(options: Options, config: Option<&Path>) -> Vec<NodeRow> {
    let root = model_root();
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &root.join("tsconfig.json")).expect("fixture loads");
    let mut analysis = Analysis::new(&project, options);

    if let Some(config) = config {
        let config = read_config(&project, Some(config)).expect("config reads");

        public_functions(&mut analysis, &config).expect("public functions resolve");
    }

    snapshot_rows(&mut analysis)
}

fn serialized(rows: &[NodeRow]) -> String {
    serde_json::to_string(rows).expect("rows serialize")
}

#[test]
fn model_rows_are_byte_identical_across_runs() {
    let first = model_rows_with(RECORDING, None);
    let second = model_rows_with(RECORDING, None);

    assert!(first.windows(2).all(|pair| pair[0].key < pair[1].key));
    assert!(first.iter().any(|row| row.state == NodeState::Partial));
    assert!(first.iter().any(|row| row.asserted));
    assert!(first
        .iter()
        .any(|row| !row.contributions.is_empty() && row.state == NodeState::Partial));
    assert_eq!(serialized(&first), serialized(&second));
}

#[test]
fn model_rows_ignore_the_unknown_policy_and_minimum() {
    let directory = tempfile::tempdir().expect("temporary directory");
    let base: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(model_root().join("olint.config.json")).expect("config"),
    )
    .expect("config parses");
    let mut expected = None;

    for policy in ["ignore", "warn", "error"] {
        let mut config = base.clone();

        config["unknown"] = serde_json::Value::from(policy);

        let path = directory.path().join(format!("{policy}.json"));

        std::fs::write(&path, config.to_string()).expect("config writes");

        for minimum_exponent in [0, 2, 100] {
            let rows = serialized(&model_rows_with(
                Options {
                    minimum_exponent,
                    ..RECORDING
                },
                Some(&path),
            ));

            match &expected {
                Some(expected) => assert_eq!(&rows, expected, "{policy} --min {minimum_exponent}"),
                None => expected = Some(rows),
            }
        }
    }
}

#[test]
fn model_rows_name_implementation_defined_unknowns() {
    let rows = model_rows_with(RECORDING, None);
    let sort = rows
        .iter()
        .flat_map(|row| &row.unknowns)
        .find(|(key, reason)| {
            key.path == "src/methods.ts"
                && key.kind == "CallExpression"
                && reason == "implementation-defined work"
        });

    assert!(sort.is_some());
}

#[test]
fn model_function_rows_match_their_report_rows() {
    let root = model_root();
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &root.join("tsconfig.json")).expect("fixture loads");
    let mut analysis = Analysis::new(&project, RECORDING);
    let rows = snapshot_rows(&mut analysis);
    let functions = analysis.reportable();
    let reported = report_rows_of(&mut analysis, &functions);

    assert!(rows.len() > functions.len());

    for ((file, function), report) in functions.iter().zip(&reported) {
        let kind = project
            .file(*file)
            .semantic
            .nodes()
            .kind(function.node_id());
        let key = NodeKey {
            path: project.file(*file).relative.clone(),
            start: kind.span().start,
            end: kind.span().end,
            kind: format!("{:?}", kind.ty()),
        };
        let row = rows
            .iter()
            .find(|row| row.key == key)
            .unwrap_or_else(|| panic!("{key:?} has a row"));
        let text = report.cost.text_with(&|id| analysis.values.label(id));

        assert_eq!(
            row.state != NodeState::Known,
            report.unknowns.is_some(),
            "{key:?}"
        );
        assert_eq!(
            (row.bound.clone(), row.floor.clone()),
            match row.state {
                NodeState::Known => (Some(text), None),
                NodeState::Partial => (None, Some(text)),
                NodeState::Unknown => (None, None),
            },
            "{key:?}"
        );
    }
}

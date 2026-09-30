use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use olint::analysis::{Analysis, Options};
use olint::config::{read_config, unknown_policy_of};
use olint::cost::Cost;
use olint::project::Project;
use olint::public::public_functions;
use olint::report::{lint_lines, report_lines, report_rows_of, Finding};
use olint::snapshot::{snapshot_rows, Labels, NodeKey, NodeRow, NodeState};
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

/// Loads the model fixture and runs `run` on a fresh analysis with `options`.
fn on_model<T>(options: Options, run: impl FnOnce(&Project<'_>, &mut Analysis<'_, '_>) -> T) -> T {
    let allocator = Allocator::default();
    let project =
        Project::load(&allocator, &model_root().join("tsconfig.json")).expect("fixture loads");
    let mut analysis = Analysis::new(&project, options);

    run(&project, &mut analysis)
}

fn model_rows() -> Vec<NodeRow> {
    on_model(RECORDING, |_, analysis| snapshot_rows(analysis))
}

fn serialized(rows: &[NodeRow]) -> String {
    serde_json::to_string(rows).expect("rows serialize")
}

#[test]
fn model_rows_are_byte_identical_across_runs() {
    let first = model_rows();
    let second = model_rows();

    assert!(first.windows(2).all(|pair| pair[0].key < pair[1].key));
    assert!(first.iter().any(|row| row.state == NodeState::Partial));
    assert!(first.iter().any(|row| row.asserted));
    assert!(first
        .iter()
        .any(|row| !row.contributions.is_empty() && row.state == NodeState::Partial));
    assert_eq!(serialized(&first), serialized(&second));
}

/// Runs the lint or the report diagnostics under one unknown policy and `--min`, as `olint` does, then snapshots:
/// the policy reaches rows only through that path, so the rows must equal the plain snapshot's (§3.5).
fn rows_after_diagnostics(policy: &str, minimum_exponent: u32, report: bool) -> (String, usize) {
    let options = Options {
        minimum_exponent,
        ..RECORDING
    };

    on_model(options, |project, analysis| {
        let mut config =
            read_config(project, Some(&model_root().join("olint.config.json"))).expect("config");

        config.unknown =
            unknown_policy_of(Some(&serde_json::Value::from(policy))).expect("policy parses");

        let public = public_functions(analysis, &config).expect("public functions resolve");
        let lines = match report {
            true => {
                let functions = analysis.reportable();
                let rows = report_rows_of(analysis, &functions);

                report_lines(
                    &analysis.values,
                    &analysis.traces,
                    project,
                    &rows,
                    minimum_exponent,
                )
            }
            false => {
                let mut checked = Vec::new();

                for public in public.functions {
                    let part = analysis
                        .summarize(public.file, public.function)
                        .total(&mut analysis.unknowns, &mut analysis.traces);

                    checked.push(Finding {
                        name: analysis.name_of(public.file, public.function),
                        site: analysis.function_site_of(public.file, public.function),
                        public,
                        part,
                    });
                }

                // Every finding renders as over its limit, so the lint path formats each one.
                let over: Vec<&Finding> = checked.iter().collect();

                lint_lines(
                    &analysis.values,
                    &analysis.traces,
                    project,
                    &config,
                    &checked,
                    &over,
                )
            }
        };

        (serialized(&snapshot_rows(analysis)), lines.len())
    })
}

#[test]
fn model_rows_ignore_the_policy_minimum_and_diagnostics_path() {
    let plain = serialized(&model_rows());

    for policy in ["ignore", "warn", "error"] {
        for minimum_exponent in [0, 2, 100] {
            for report in [false, true] {
                let (rows, lines) = rows_after_diagnostics(policy, minimum_exponent, report);

                assert!(
                    lines > 0,
                    "{policy} --min {minimum_exponent} report {report}"
                );
                assert_eq!(
                    rows, plain,
                    "{policy} --min {minimum_exponent} report {report}"
                );
            }
        }
    }
}

#[test]
fn model_rows_name_implementation_defined_unknowns() {
    let rows = model_rows();
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
    on_model(RECORDING, check_function_rows);
}

fn check_function_rows(project: &Project<'_>, analysis: &mut Analysis<'_, '_>) {
    let rows = snapshot_rows(analysis);
    let functions = analysis.reportable();
    let reported = report_rows_of(analysis, &functions);
    let labels = Labels::of(analysis);

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
        let text = labels.text(&report.cost);

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

fn source_rows(source: &str) -> Vec<NodeRow> {
    let directory = tempfile::tempdir().expect("temporary directory");

    std::fs::create_dir_all(directory.path().join("src")).expect("src");
    std::fs::write(
        directory.path().join("tsconfig.json"),
        r#"{ "compilerOptions": { "target": "ES2022", "module": "ESNext", "strict": true, "noEmit": true }, "include": ["src/**/*.ts"] }"#,
    )
    .expect("tsconfig");
    std::fs::write(directory.path().join("src/index.ts"), source).expect("source");

    let allocator = Allocator::default();
    let project =
        Project::load(&allocator, &directory.path().join("tsconfig.json")).expect("project loads");
    let mut analysis = Analysis::new(&project, RECORDING);

    snapshot_rows(&mut analysis)
}

/// The rows inside the function whose text starts at `start`, with spans made relative to it.
fn rows_from(rows: &[NodeRow], start: u32, end: u32) -> Vec<String> {
    rows.iter()
        .filter(|row| row.key.start >= start && row.key.end <= end)
        .map(|row| {
            format!(
                "{} {}-{} {:?} {:?} {:?} {}",
                row.key.kind,
                row.key.start - start,
                row.key.end - start,
                row.state,
                row.bound,
                row.floor,
                row.contributions.len()
            )
        })
        .collect()
}

#[test]
fn node_recording_is_independent_of_declaration_order() {
    const MAIN: &str = "export function main() {\n\treturn helper();\n}\n";

    const HELPER: &str = "export function helper() {\n\tlet total = 0;\n\tfor (let index = 0; index < 64; index++) {\n\t\ttotal += index;\n\t}\n\treturn total;\n}\n";

    let mut found = Vec::new();

    for (source, offset) in [
        (format!("{MAIN}{HELPER}"), MAIN.len()),
        (format!("{HELPER}{MAIN}"), 0),
    ] {
        let rows = source_rows(&source);
        let start = offset as u32;

        found.push(rows_from(&rows, start, start + HELPER.len() as u32));
    }

    assert!(
        found[0].len() > 1,
        "helper records more than its function row: {:?}",
        found[0]
    );
    assert_eq!(found[0], found[1]);
}

#[test]
fn labels_name_each_dimension_uniquely() {
    let rows = source_rows(
        "export function first(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) total += x;\n\treturn total;\n}\nexport function second(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) total += x;\n\treturn total;\n}\n",
    );
    let bounds: BTreeSet<&str> = rows
        .iter()
        .filter(|row| row.key.kind == "Function")
        .filter_map(|row| row.bound.as_deref())
        .collect();

    // Two parameters named `xs` are two dimensions, so the bounds differ in text and each parses back.
    assert_eq!(bounds.len(), 2, "{bounds:?}");

    for bound in &bounds {
        assert!(bound.contains('$'), "{bound}");
        assert!(Cost::parse(bound).is_ok(), "{bound} parses back");
    }
}

/// §1 Floor: an unresolved loop's repeated work is no proven contribution, so it leaves the floors and contributions
/// of the loop and the function, while a loop's initializer runs once and stays a proven contribution.
#[test]
fn unresolved_loops_leave_their_repeated_work_out_of_floors_and_contributions() {
    const UNBOUNDED: &str = "export function unbounded(xs: number[]): number { let c = 0; let k = 1; while (k !== xs.length) { for (const a of xs) for (const b of xs) c += a * b; k = (k * 3) % 7; } return c; }\n";

    const INITIALIZED: &str = "function scan(xs: number[]) { let total = 0; for (const x of xs) total += x; return total; }\nexport function initialized(xs: number[]) { for (let i = scan(xs); i !== 7; i = (i * 3) % 7) { for (const a of xs) for (const b of xs) void (a + b); } }\n";

    let rows = source_rows(&format!("{UNBOUNDED}{INITIALIZED}"));
    let row_of = |kind: &str, start: usize| {
        rows.iter()
            .find(|row| row.key.kind == kind && row.key.start == start as u32)
            .unwrap_or_else(|| panic!("{kind} at {start} has a row"))
    };

    for kind in ["Function", "WhileStatement"] {
        let start = match kind {
            "Function" => UNBOUNDED.find("function").unwrap(),
            _ => UNBOUNDED.find("while").unwrap(),
        };
        let row = row_of(kind, start);

        assert_ne!(row.state, NodeState::Known, "{row:?}");
        assert!(
            row.floor
                .iter()
                .chain(row.contributions.iter().map(|(_, bound)| bound))
                .all(|cost| Cost::parse(cost) == Ok(Cost::ONE)),
            "{row:?}"
        );
        assert!(!row.unknowns.is_empty(), "{row:?}");
    }

    let offset = UNBOUNDED.len();
    let row = row_of(
        "ForStatement",
        offset + INITIALIZED.find("for (let i").unwrap(),
    );

    assert_eq!(row.state, NodeState::Partial, "{row:?}");
    assert!(
        row.floor
            .as_deref()
            .is_some_and(|floor| floor.contains("xs$")),
        "{row:?}"
    );
    assert_eq!(
        row.contributions
            .iter()
            .map(|(key, _)| key.kind.as_str())
            .collect::<Vec<_>>(),
        ["VariableDeclaration"],
        "{row:?}"
    );
}

use std::path::Path;

use olint::analysis::{Analysis, Options, TypeMode};
use olint::oracle::{ask, OracleError};
use olint::project::Project;
use olint::report::{chain_lines, order_by_cost_descending, report_row, report_rows_of};
use oxc_allocator::Allocator;

const ORACLE: Options = Options {
    strings_linear: true,
    callbacks: true,
    minimum_exponent: 2,
    types: TypeMode::Oracle,
};

struct Row {
    block: String,
    n: u32,
    log: u32,
}

fn rows_of(fixture: &str) -> Vec<Row> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tsconfig = root
        .join("tests/fixtures")
        .join(fixture)
        .join("tsconfig.json");
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).expect("fixture loads");
    let mut analysis = Analysis::new(&project, ORACLE);
    let functions = analysis.reportable();

    analysis
        .gather_answers(&functions, |queries| {
            ask(root, &project.tsconfig_path, queries)
        })
        .unwrap_or_else(|error| match error {
            OracleError::NodeUnavailable(error) => panic!("node is unavailable: {error}"),
            OracleError::TypescriptUnavailable(message) => {
                panic!("typescript is unavailable: {message}")
            }
            error => panic!("the oracle failed: {error:?}"),
        });

    let mut rows: Vec<(olint::cost::Cost, Row)> = report_rows_of(&mut analysis, &functions)
        .into_iter()
        .map(|report| {
            let mut lines = vec![report_row(
                &project,
                report.cost,
                &report.name,
                report.mark.as_deref(),
                report.site,
            )];

            chain_lines(&project, &report.chain, 1, &mut lines);

            (
                report.cost,
                Row {
                    block: lines.join(
                        "
",
                    ),
                    n: report.cost.n,
                    log: report.cost.log,
                },
            )
        })
        .collect();

    rows.sort_by(|(left, _), (right, _)| order_by_cost_descending(*left, *right));

    rows.into_iter().map(|(_, row)| row).collect()
}

fn golden_blocks_of(fixture: &str, golden: &str) -> Vec<String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(fixture)
        .join(golden);
    let text = std::fs::read_to_string(path)
        .expect("golden exists")
        .replace("\r\n", "\n");

    text.split("\n\n")
        .skip(2)
        .map(|block| block.trim_matches('\n').to_string())
        .filter(|block| !block.is_empty())
        .collect()
}

fn differences_of(fixture: &str, rows: &[Row], golden: &str, minimum: u32) -> Vec<String> {
    let expected = golden_blocks_of(fixture, golden);
    let found: Vec<String> = rows
        .iter()
        .filter(|row| row.n >= minimum || (row.n >= 1 && row.log >= 1))
        .map(|row| row.block.clone())
        .collect();
    let mut unmatched = found.clone();
    let mut differences = Vec::new();

    for block in &expected {
        match unmatched.iter().position(|candidate| candidate == block) {
            Some(index) => {
                unmatched.remove(index);
            }
            None => differences.push(format!("{fixture} {golden} reference:\n{block}")),
        }
    }

    for block in unmatched {
        differences.push(format!("{fixture} {golden} olint:\n{block}"));
    }

    differences
}

#[test]
fn every_fixture_function_matches_the_goldens() {
    let mut differences = Vec::new();

    for fixture in ["model", "tags"] {
        let rows = rows_of(fixture);

        differences.extend(differences_of(fixture, &rows, "expected-report.txt", 2));
        differences.extend(differences_of(
            fixture,
            &rows,
            "expected-report-min0.txt",
            0,
        ));
    }

    assert!(
        differences.is_empty(),
        "{} differing blocks:\n\n{}",
        differences.len(),
        differences.join("\n\n")
    );
}

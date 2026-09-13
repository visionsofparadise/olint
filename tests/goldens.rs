use std::path::Path;

use olint::analysis::{Analysis, Options, TypeMode};
use olint::annotations::{cost_tag_of, PerfTag};
use olint::oracle::{ask, OracleError};
use olint::project::Project;
use olint::report::{chain_lines, report_row};
use olint::summaries::Substitutions;
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

    let mut rows: Vec<(olint::cost::Part, Row)> = Vec::new();

    for (file, function) in functions {
        let tags = analysis.function_tags(file, function);
        let mark = if tags.contains(&PerfTag::Cold) {
            Some("cold".to_string())
        } else {
            cost_tag_of(&tags).map(|(_, text)| text)
        };
        let part = match mark {
            Some(_) => analysis.summarize_with(file, function, Substitutions::new(), true),
            None => analysis.summarize(file, function),
        }
        .total();
        let name = analysis.name_of(file, function);
        let site = analysis.function_site_of(file, function);
        let mut lines = vec![report_row(
            &project,
            part.cost,
            &name,
            mark.as_deref(),
            site,
        )];

        chain_lines(&project, &part.chain, 1, &mut lines);

        let row = Row {
            block: lines.join("\n"),
            n: part.cost.n,
            log: part.cost.log,
        };

        rows.push((part, row));
    }

    rows.sort_by(|(left, _), (right, _)| {
        if left.cost.exceeds(right.cost) {
            std::cmp::Ordering::Less
        } else if right.cost.exceeds(left.cost) {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    });

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

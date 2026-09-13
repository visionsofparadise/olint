use super::{lines_of_chain, lines_of_report, lint_header_of, ReportRow};
use crate::config::{Config, Limit};
use crate::cost::{Cost, Factor};
use crate::project::{FileId, Site};

fn factor_of(label: &str, line: u32, cost: Cost, inner: Vec<Factor>) -> Factor {
    Factor {
        label: label.to_string(),
        site: Site {
            file: FileId(0),
            line,
        },
        cost,
        inner,
    }
}

#[test]
fn chains_pad_labels_and_nest_inner_calls() {
    let chain = vec![
        factor_of("for-of", 137, Cost::N, Vec::new()),
        factor_of(
            "call costFn()",
            137,
            Cost::N,
            vec![factor_of("@perf O(N)", 129, Cost::N, Vec::new())],
        ),
    ];
    let mut out = Vec::new();

    lines_of_chain(&chain, 1, &mut out, &|site| {
        format!("src/tags.ts:{}", site.line)
    });

    assert_eq!(
        out,
        vec![
            "    in loop for-of                                           src/tags.ts:137  x N",
            "        calls costFn()                                     src/tags.ts:137  = O(N)",
            "        reads as @perf O(N)                                   src/tags.ts:129  = O(N)",
        ]
    );
}

fn row_of(cost: Cost, name: &str, file: u32, line: u32) -> ReportRow {
    ReportRow {
        cost,
        name: name.to_string(),
        mark: None,
        site: Site {
            file: FileId(file),
            line,
        },
        chain: Vec::new(),
    }
}

#[test]
fn report_histogram_orders_by_count_and_keeps_first_seen_ties() {
    let rows = vec![
        row_of(Cost::N, "linear", 0, 1),
        row_of(Cost::ONE, "first", 0, 2),
        row_of(Cost::N_LOG_N, "sorting", 1, 3),
        row_of(Cost::ONE, "second", 1, 4),
        row_of(Cost { n: 2, log: 0 }, "square", 1, 5),
    ];
    let lines = lines_of_report("tsconfig.json", &rows, 2, &|site| {
        format!("src/{}.ts:{}", site.file.0, site.line)
    });

    assert_eq!(
        lines,
        vec![
            "# tsconfig.json  (5 functions in 2 files)",
            "",
            "O(1)                2",
            "O(N)                1",
            "O(N log N)          1",
            "O(N^2)              1",
            "",
            "O(N^2)         square  src/1.ts:5",
            "",
            "O(N log N)     sorting  src/1.ts:3",
            "",
        ]
    );
}

#[test]
fn report_minimum_zero_flags_every_row() {
    let rows = vec![
        row_of(Cost::ONE, "first", 0, 2),
        row_of(Cost::N, "linear", 0, 1),
    ];
    let lines = lines_of_report("tsconfig.json", &rows, 0, &|site| {
        format!("src/a.ts:{}", site.line)
    });

    assert_eq!(
        &lines[5..],
        &[
            "O(N)           linear  src/a.ts:1",
            "",
            "O(1)           first  src/a.ts:2",
            ""
        ]
    );
}

fn config_of(entries: &[&str]) -> Config {
    let max = Limit {
        cost: Cost { n: 2, log: 0 },
        text: "O(N^2)".to_string(),
    };

    Config {
        max: max.clone(),
        entrypoints: entries
            .iter()
            .map(|entry| (std::path::PathBuf::from(entry), max.clone()))
            .collect(),
        ignore: Vec::new(),
        source: "olint.config.json".to_string(),
    }
}

#[test]
fn lint_header_counts_entrypoints() {
    let entries = vec!["src/index.ts".to_string()];

    assert_eq!(
        lint_header_of("tsconfig.json", &config_of(&["src/index.ts"]), &entries, 3),
        "# tsconfig.json  olint.config.json: max O(N^2), 1 entrypoint (src/index.ts), 3 public functions"
    );

    let entries = vec!["src/index.ts".to_string(), "src/cli.ts".to_string()];

    assert_eq!(
        lint_header_of(
            "tsconfig.json",
            &config_of(&["src/index.ts", "src/cli.ts"]),
            &entries,
            0
        ),
        "# tsconfig.json  olint.config.json: max O(N^2), 2 entrypoints (src/index.ts, src/cli.ts), 0 public functions"
    );
}

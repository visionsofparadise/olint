use super::{lines_of_chain, lines_of_report, lint_header_of, verdict_of, ReportRow, Verdict};
use crate::config::{Config, Limit};
use crate::cost::{Cost, Part, State};
use crate::project::{FileId, Site};
use crate::trace::TraceArena;
use crate::unknowns::{SourceSpan, UnknownId};
use crate::values::Values;

#[test]
fn chains_pad_labels_and_nest_inner_calls() {
    let mut traces = TraceArena::default();
    let tag = traces
        .factor(
            "@perf O(N)".into(),
            Site {
                file: FileId(0),
                line: 129,
            },
            SourceSpan {
                file: FileId(0),
                start: 129,
                end: 130,
            },
            Cost::N,
            None,
            None,
        )
        .unwrap();
    let call = traces
        .factor(
            "call costFn()".into(),
            Site {
                file: FileId(0),
                line: 137,
            },
            SourceSpan {
                file: FileId(0),
                start: 137,
                end: 138,
            },
            Cost::N,
            Some(tag),
            None,
        )
        .unwrap();
    let root = traces
        .factor(
            "for-of".into(),
            Site {
                file: FileId(0),
                line: 137,
            },
            SourceSpan {
                file: FileId(0),
                start: 136,
                end: 139,
            },
            Cost::N,
            None,
            Some(call),
        )
        .unwrap();
    let mut out = Vec::new();

    lines_of_chain(
        &Values::default(),
        &traces,
        Some(root),
        1,
        &mut out,
        &|site, out| write!(out, "src/tags.ts:{}", site.line),
    );
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
        entry: false,
        envelope: Some(
            Cost::N
                .bind(
                    &|_| None,
                    &[Cost::dimension(u64::MAX, crate::cost::Domain::Size)],
                )
                .unwrap(),
        ),
        unknowns: None,
        state: State::Known,
        asserted: false,
        cost,
        latent: None,
        name: name.to_string(),
        mark: None,
        site: Site {
            file: FileId(file),
            line,
        },
        trace: None,
        derivation: None,
    }
}

#[test]
fn report_histogram_orders_by_count_and_keeps_first_seen_ties() {
    let rows = vec![
        row_of(Cost::N, "linear", 0, 1),
        row_of(Cost::ONE, "first", 0, 2),
        row_of(Cost::N_LOG_N, "sorting", 1, 3),
        row_of(Cost::ONE, "second", 1, 4),
        row_of(Cost::parse("O(N^2)").unwrap(), "square", 1, 5),
    ];
    let lines = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &rows,
        2,
        &|site, out| write!(out, "src/{}.ts:{}", site.file.0, site.line),
        &|_| Vec::new(),
    );

    assert_eq!(
        lines,
        vec![
            "# tsconfig.json  (5 functions in 2 files: 5 known, 0 partial, 0 unknown)",
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
    let lines = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &rows,
        0,
        &|site, out| write!(out, "src/a.ts:{}", site.line),
        &|_| Vec::new(),
    );

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
        cost: Cost::parse("O(N^2)").unwrap(),
        text: "O(N^2)".to_string(),
    };

    Config {
        explicit_entrypoints: true,
        unknown: crate::config::UnknownPolicy::Warn,
        max: max.clone(),
        entrypoints: entries
            .iter()
            .map(|entry| (std::path::PathBuf::from(entry), vec![max.clone()]))
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

#[test]
fn incomparable_report_rows_have_a_total_order_independent_of_input_order() {
    let a = row_of(Cost::dimension(1, crate::cost::Domain::Size), "alpha", 0, 1);
    let b = row_of(Cost::dimension(2, crate::cost::Domain::Size), "beta", 0, 2);
    let rows = vec![a, b];
    let render = |rows: &[ReportRow]| {
        lines_of_report(
            &Values::default(),
            &TraceArena::default(),
            "tsconfig.json",
            rows,
            0,
            &|site, out| write!(out, "index.ts:{}", site.line),
            &|_| Vec::new(),
        )
        .into_iter()
        .filter(|line| line.contains("alpha") || line.contains("beta"))
        .collect::<Vec<_>>()
    };
    let expected = render(&rows);
    let reversed = rows.into_iter().rev().collect::<Vec<_>>();

    assert_eq!(expected, render(&reversed));
}

#[test]
fn high_minimum_keeps_only_the_qualified_logarithmic_exception() {
    let rows = vec![
        row_of(Cost::parse("O(N^3)").unwrap(), "pure_cubic", 0, 1),
        row_of(Cost::N_LOG_N, "legacy_sorting", 0, 2),
        row_of(Cost::parse("O(N^3 * log(N)^2)").unwrap(), "polylog", 0, 3),
        row_of(
            Cost::parse("O(N^3 + log(N))").unwrap(),
            "additive_log",
            0,
            4,
        ),
        row_of(Cost::parse("O(N^3 / log(N))").unwrap(), "inverse_log", 0, 5),
    ];
    let lines = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &rows,
        99,
        &|_, out| out.write_str("index.ts:1"),
        &|_| Vec::new(),
    );
    let text = lines.join("\n");

    assert!(text.contains("legacy_sorting"));
    assert!(text.contains("polylog"));
    assert!(!text.contains("pure_cubic"));
    assert!(!text.contains("additive_log"));
    assert!(!text.contains("inverse_log"));

    let zero = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &rows,
        0,
        &|_, out| out.write_str("index.ts:1"),
        &|_| Vec::new(),
    )
    .join("\n");

    assert!(zero.contains("pure_cubic"));

    let three = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &rows,
        3,
        &|_, out| out.write_str("index.ts:1"),
        &|_| Vec::new(),
    )
    .join("\n");

    assert!(three.contains("pure_cubic"));
}

/// §4.7: each row shows its bound, its floor marked partial or its Unknown state, an asserted mark where its cost
/// depends on a directive, and the source origin of every unknown contribution.
#[test]
fn rows_render_each_state_with_its_marks_and_origins() {
    let mut partial = row_of(Cost::N, "partial", 0, 1);
    let mut unknown = row_of(Cost::ONE, "unknown", 0, 2);
    let mut asserted = row_of(Cost::parse("O(N^2)").unwrap(), "asserted", 0, 3);

    partial.state = State::Partial;
    partial.unknowns = Some(UnknownId(1));
    unknown.state = State::Unknown;
    unknown.unknowns = Some(UnknownId(2));
    asserted.asserted = true;

    let lines = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &[partial, unknown, asserted],
        0,
        &|site, out| write!(out, "src/a.ts:{}", site.line),
        &|root| vec![format!("unknown call target at src/a.ts:{}", root.0)],
    );

    assert_eq!(
        lines,
        vec![
            "# tsconfig.json  (3 functions in 1 files: 1 known, 1 partial, 1 unknown)",
            "",
            "O(N) [partial]      1",
            "unknown             1",
            "O(N^2)              1",
            "",
            "O(N^2)         asserted [asserted]  src/a.ts:3",
            "",
            "O(N)           partial  src/a.ts:1 [partial]",
            "    unknown origin: call target at src/a.ts:1",
            "",
            "unknown        unknown  src/a.ts:2",
            "    unknown origin: call target at src/a.ts:2",
            "",
        ]
    );
}

/// §4.3: an Unknown entry has no floor, so its verdict is Inconclusive whatever cost it carries, while a Partial
/// entry's floor above the limit still Exceeds it.
#[test]
fn an_unknown_entry_is_inconclusive() {
    let linear = Cost::dimension(1, crate::cost::Domain::Size);
    let unknown = Part {
        cost: linear.clone(),
        unknowns: Some(UnknownId(1)),
        ..Part::none()
    };
    let partial = Part::unmarked(linear, None);
    let partial = Part {
        unknowns: Some(UnknownId(1)),
        ..partial
    };

    assert_eq!(unknown.state(), State::Unknown);
    assert_eq!(verdict_of(&unknown, &Cost::ONE), Verdict::Inconclusive);
    assert_eq!(partial.state(), State::Partial);
    assert_eq!(verdict_of(&partial, &Cost::ONE), Verdict::Exceeds);
}

/// §4.7: every entry shows its bound, floor or Unknown state with its origins whatever `--min` is, including an
/// entry whose envelope does not bind; `--min` filters only the other rows.
#[test]
fn entries_render_whatever_the_minimum() {
    let mut partial = row_of(Cost::ONE, "partial_entry", 0, 1);
    let mut unknown = row_of(Cost::ONE, "unknown_entry", 0, 2);
    let helper = row_of(Cost::ONE, "helper", 0, 3);

    partial.entry = true;
    partial.state = State::Partial;
    partial.unknowns = Some(UnknownId(1));
    unknown.entry = true;
    unknown.state = State::Unknown;
    unknown.unknowns = Some(UnknownId(2));
    unknown.envelope = None;

    let lines = lines_of_report(
        &Values::default(),
        &TraceArena::default(),
        "tsconfig.json",
        &[partial, unknown, helper],
        3,
        &|site, out| write!(out, "src/a.ts:{}", site.line),
        &|root| vec![format!("unknown call target at src/a.ts:{}", root.0)],
    );
    let text = lines.join("\n");

    assert!(text.contains(
        "O(1)           partial_entry  src/a.ts:1 [partial]\n    unknown origin: call target at src/a.ts:1"
    ));
    assert!(text.contains(
        "unknown        unknown_entry  src/a.ts:2\n    unknown origin: call target at src/a.ts:2"
    ));
    assert!(!text.contains("helper  src/a.ts:3"));
}

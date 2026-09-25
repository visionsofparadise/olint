use std::process::Command;

use olint::cost::{Cost, ExecutionPhase};
use olint::unknowns::{UnknownNode, UnknownReason};

use crate::support;
use support::{function_of_name, project_of, run_with_source};

fn summary_of(
    analysis: &mut olint::analysis::Analysis<'_, '_>,
    file: olint::project::FileId,
    name: &str,
) -> olint::cost::Part {
    let function = function_of_name(analysis.project, file, name);
    let mut part = support::summary_of(analysis, file, name);
    part.cost = support::legacy_class_of(analysis, file, function, &part.cost);

    part
}

fn cli(source: &str, policy: Option<&str>, report: bool) -> std::process::Output {
    let mut config = serde_json::json!({ "entrypoints": ["index.ts"], "max": "O(N^2)" });

    if let Some(policy) = policy {
        config["unknown"] = serde_json::json!(policy);
    }

    let directory = project_of(&[
        ("tsconfig.json", "{}"),
        ("index.ts", source),
        ("olint.config.json", &config.to_string()),
    ]);
    let mut command = Command::new(env!("CARGO_BIN_EXE_olint"));

    command
        .args(["--types", "syntactic"])
        .current_dir(directory.path());

    if report {
        command.args(["--report", "--min", "99"]);
    }

    command.output().expect("olint runs")
}

#[test]
fn policies_preserve_partial_results_and_change_only_diagnostics_and_lint_failure() {
    let source = "export function f(callback: () => void) { callback(); }";
    let default = cli(source, None, false);
    let ignored = cli(source, Some("ignore"), false);
    let warned = cli(source, Some("warn"), false);
    let failed = cli(source, Some("error"), false);

    assert_eq!(default.stdout, warned.stdout);
    assert_eq!(ignored.stdout, warned.stdout);
    assert_eq!(warned.stdout, failed.stdout);
    assert!(String::from_utf8_lossy(&warned.stdout).contains("1 partial results"));
    assert!(!String::from_utf8_lossy(&ignored.stderr).contains("unknown call"));
    assert!(String::from_utf8_lossy(&warned.stderr).contains("olint: warning: unknown call target"));
    assert!(String::from_utf8_lossy(&failed.stderr).contains("olint: error: unknown call target"));
    assert_eq!(ignored.status.code(), Some(0));
    assert_eq!(warned.status.code(), Some(0));
    assert_eq!(failed.status.code(), Some(1));
}

#[test]
fn filtered_report_preserves_unknown_diagnostics_and_partial_histogram() {
    for policy in ["ignore", "warn", "error"] {
        let output = cli(
            "export function f(callback: () => void) { callback(); }",
            Some(policy),
            true,
        );

        assert_eq!(
            output.status.code(),
            Some(0),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("O(1) [partial]"));
        assert_eq!(
            String::from_utf8_lossy(&output.stderr).contains("unknown call target"),
            policy != "ignore"
        );
    }
}

#[test]
fn known_over_limit_fails_every_policy_even_with_unresolved_work() {
    let source = "/** @perf O(N^3) */ function expensive() {} export function f(callback: () => void) { callback(); expensive(); }";

    for policy in ["ignore", "warn", "error"] {
        let output = cli(source, Some(policy), false);

        assert_eq!(output.status.code(), Some(1));

        let stdout = String::from_utf8_lossy(&output.stdout);

        assert!(stdout.contains("[partial] > O(N^2)"));
        assert!(stdout.contains("@perf O(N^3)"));
    }
}

#[test]
fn cheap_unknown_sibling_survives_known_cost_maximum() {
    run_with_source("/** @perf O(N^2) */ function expensive() {} export function f(callback: () => void) { callback(); expensive(); }", |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert_eq!(part.cost, Cost::parse("O(N^2)").unwrap());
        assert!(part.unknowns.is_some());
    });
}

#[test]
fn known_callback_specialization_resolves_generic_unknown_without_leaking_it() {
    run_with_source("function invoke(callback: () => void) { callback(); } export function f() { invoke(() => 1); }", |analysis, file| {
        let invoke = function_of_name(analysis.project, file, "invoke");

        assert!(analysis.summarize(file, invoke).total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_some());

        let f = function_of_name(analysis.project, file, "f");
        let first = analysis.summarize(file, f);
        let second = analysis.summarize(file, f);

        assert_eq!(first, second);
        assert!(first
            .completions
            .iter()
            .all(|channel| channel.0 == ExecutionPhase::Immediate));
        assert!(first.total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_none());
        assert!(analysis.summaries_arena.iter().any(|record| record.effects == olint::effects::Effects::default()));
    });

    let result = cli("function invoke(callback: () => void) { callback(); } export function f() { invoke(() => 1); }", Some("error"), false);

    assert_eq!(result.status.code(), Some(0));
    assert!(!String::from_utf8_lossy(&result.stderr).contains("unknown"));
}

#[test]
fn unknown_callback_keeps_known_native_invocation_count() {
    run_with_source("export function f(xs: number[], callback: (x: number) => number) { return xs.map(callback); }", |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert_eq!(part.cost, Cost::N);

        let lines = unknown_lines(analysis, part);

        assert!(lines.iter().any(|line| line.contains("multiplicity O(N)")));
    });
}

#[test]
fn repeated_calls_share_unknown_origin_and_keep_distinct_call_edges() {
    run_with_source("declare function opaque(): void; function helper() { opaque(); } export function f() { helper(); helper(); }", |analysis, file| {
        let part = summary_of(analysis, file, "f");
        let lines = unknown_lines(analysis, part);

        assert_eq!(lines.len(), 2);
        assert_ne!(lines[0], lines[1]);

        let origins = (0..analysis.unknowns.len()).filter(|id| matches!(analysis.unknowns.node(olint::unknowns::UnknownId(*id as u32)), UnknownNode::Origin(unknown) if unknown.reason == UnknownReason::Target)).count();

        assert_eq!(origins, 1);
    });
}

#[test]
fn unused_callbacks_are_complete_and_distinct_invocation_spans_are_retained() {
    run_with_source("export function unused(callback: () => void) { return 1; } export function used(callback: () => void) { callback(); callback(); }", |analysis, file| {
        let unused = function_of_name(analysis.project, file, "unused");

        assert!(analysis.summarize(file, unused).total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_none());

        let used = function_of_name(analysis.project, file, "used");
        let part = analysis.summarize(file, used).total(&mut analysis.unknowns, &mut analysis.traces);
        let lines = unknown_lines(analysis, part);

        assert_eq!(lines.len(), 2);
    });
}

#[test]
fn unknown_effects_remove_dependent_iteration_proofs() {
    for annotation in ["", "/** @perf cold */", "/** @perf ignore */"] {
        let source = format!("export function f(callback: (reset: () => void) => void) {{ for (let i = 0; i < 10; i++) {{\n{annotation}\ncallback(() => {{ i = 0; }}); }} }}");

        run_with_source(&source, |analysis, file| {
            let part = summary_of(analysis, file, "f");
            let lines = unknown_lines(analysis, part);

            assert!(lines
                .iter()
                .any(|line| line.contains("iteration bound")
                    && line.contains("multiplicity unknown")));
        });
    }

    run_with_source(
        "export function f(n: number) { for (let i = 0; i < n; i++) {} }",
        |analysis, file| {
            let part = summary_of(analysis, file, "f");

            assert_eq!(part.cost, Cost::N);
            assert!(part.unknowns.is_none());
        },
    );
    run_with_source("export function f(callback: (reset: () => void) => void) {\n/** @perf bounded */\nfor (let i = 0; i < 10; i++) { callback(() => { i = 0; }); } }", |analysis, file| {
        let part = summary_of(analysis, file, "f");
        let lines = unknown_lines(analysis, part);

        assert!(!lines.iter().any(|line| line.contains("iteration bound")));
        assert!(lines.iter().any(|line| line.contains("multiplicity O(1)")));
    });
}

#[test]
fn selected_cost_preferences_control_unknown_diagnostics() {
    for (annotation, code) in [("ignore", 0), ("cold", 1)] {
        let source = format!("/** @perf O(N) */ function known() {{}}\nexport function f(callback: () => void) {{\n/** @perf {annotation} */\ncallback();\nknown();\n}}");
        let output = cli(&source, Some("error"), false);

        assert_eq!(
            output.status.code(),
            Some(code),
            "{annotation}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stderr).contains("unknown call target"),
            code == 1,
            "{annotation}"
        );
    }

    let hot = cli(
        "export function f(callback: () => void) {\n/** @perf hot */\ncallback();\nreturn 1;\n}",
        Some("error"),
        false,
    );

    assert_eq!(hot.status.code(), Some(1));
}

#[test]
fn equal_cost_callbacks_retain_different_effect_facts() {
    run_with_source("declare function opaque(): void; function invoke(callback: () => void) { callback(); } export function pure() { invoke(() => 1); } export function impure() { invoke(() => opaque()); }", |analysis, file| {
        let pure = function_of_name(analysis.project, file, "pure");
        let impure = function_of_name(analysis.project, file, "impure");

        assert!(analysis.summarize(file, pure).total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_none());
        assert!(analysis.summarize(file, impure).total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_some());
        assert!(analysis.summarize(file, pure).total(&mut analysis.unknowns, &mut analysis.traces).unknowns.is_none());
    });
}

#[test]
fn cached_ignored_callee_effects_invalidate_enclosing_loops() {
    run_with_source("let counter = 0;\n/** @perf ignore */\nfunction reset() { counter = 0; } export function f() { for (counter = 0; counter < 10; counter++) { reset(); reset(); } }", |analysis, file| {
        let reset = function_of_name(analysis.project, file, "reset");

        analysis.summarize(file, reset);
        analysis.summarize(file, reset);

        let part = summary_of(analysis, file, "f");
        let lines = unknown_lines(analysis, part);

        assert!(lines.iter().any(|line| line.contains("iteration bound")));
        assert!(analysis.summaries_arena.iter().any(|record| record.effects.unknown_global));
    });
}

#[test]
fn unsupported_methods_preserve_evaluated_argument_costs() {
    for parameter in ["receiver: number", "receiver: unknown"] {
        let source = format!("/** @perf O(N^2) */ function expensive() {{ return 1; }} export function f({parameter}) {{ receiver.toFixed(expensive()); }}");

        run_with_source(&source, |analysis, file| {
            let part = summary_of(analysis, file, "f");

            assert_eq!(part.cost, Cost::parse("O(N^2)").unwrap());

            let lines = unknown_lines(analysis, part);

            assert!(lines
                .iter()
                .any(|line| line.contains("unknown operation model")));
        });
    }

    run_with_source(
        "export function f(xs: number[]) { return xs.slice(); }",
        |analysis, file| {
            let part = summary_of(analysis, file, "f");

            assert_eq!(part.cost, Cost::N);
            assert!(part.unknowns.is_none());
        },
    );
}

#[test]
fn known_native_cost_does_not_prove_empty_effects() {
    for annotation in ["", "/** @perf cold */"] {
        let source = format!("function mutate(xs: number[]) {{ xs.splice(0, 0, 1); }} export function f(xs: number[]) {{ for (let i = 0; i < xs.length; i++) {{\n{annotation}\nmutate(xs); }} }}");

        run_with_source(&source, |analysis, file| {
            let mutation = summary_of(analysis, file, "mutate");

            assert_eq!(mutation.cost, Cost::N);
            assert!(mutation.unknowns.is_none());
            assert!(analysis
                .summaries_arena
                .iter()
                .any(|record| !record.effects.unknown_reachable.is_empty()));

            let part = summary_of(analysis, file, "f");

            assert_ne!(part.cost, Cost::parse("O(N^2)").unwrap());

            let lines = unknown_lines(analysis, part);

            assert!(lines.iter().any(|line| line.contains("iteration bound")));
        });
    }
}

fn unknown_lines(
    analysis: &olint::analysis::Analysis<'_, '_>,
    part: olint::cost::Part,
) -> Vec<String> {
    analysis
        .unknowns
        .lines(analysis.project, part.unknowns.expect("partial reading"))
}

#[test]
fn cached_summary_preserves_phase_latent_and_comparison_facts() {
    run_with_source("export function f() { return 1; }", |analysis, file| {
        let function = function_of_name(analysis.project, file, "f");

        analysis.summarize(file, function);

        let unknown = analysis.unknowns.origin(
            olint::unknowns::SourceSpan {
                file,
                start: 0,
                end: 1,
            },
            UnknownReason::Comparison,
        );
        let phased = vec![
            (
                ExecutionPhase::Immediate,
                olint::flow::Completion::Normal,
                olint::cost::Part {
                    unknowns: Some(unknown),
                    ..olint::cost::Part::unmarked(Cost::ONE, None)
                },
            ),
            (
                ExecutionPhase::Scheduled,
                olint::flow::Completion::Normal,
                olint::cost::Part::unmarked(Cost::N, None),
            ),
            (
                ExecutionPhase::Lazy,
                olint::flow::Completion::Throw,
                olint::cost::Part::unmarked(Cost::LOG, None),
            ),
        ];
        let record = &mut analysis.summaries_arena[0];
        record.reading.completions = phased.clone();
        record.result.latent = Some(olint::summaries::SummaryId(0));
        let nodes = analysis.unknowns.len();
        let cached = analysis.summarize(file, function);

        assert_eq!(cached.completions, phased);
        assert_eq!(cached.main().unknowns, Some(unknown));
        assert_eq!(analysis.unknowns.len(), nodes);
        assert_eq!(analysis.summaries_arena.len(), 1);
        assert_eq!(
            analysis.summaries_arena[0].result.latent,
            Some(olint::summaries::SummaryId(0))
        );
        assert!(unknown_lines(analysis, cached.main())
            .iter()
            .any(|line| line.contains("comparison")));
    });
}

#[test]
fn unresolved_loop_bound_does_not_promote_cold_known_work() {
    run_with_source("/** @perf ignore */\nfunction ignored() { return 0; }\n/** @perf cold */\nfunction cold(xs: number[][]) { for (const row of xs) for (const x of row) for (const y of row) void y; return 0; }\nexport function f(xs: number[][]) { let sum = 0; for (const row of xs) sum += ignored() + cold([row]); return sum; }", |analysis, file| {
        let part = summary_of(analysis, file, "f");

        assert_eq!(part.cost, Cost::ONE);
        assert!(unknown_lines(analysis, part).iter().any(|line| line.contains("iteration bound")));
    });
}

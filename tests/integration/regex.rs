use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use olint::cost::Cost;
use olint::regex::{
    ask, RegexAnswer, RegexError, RegexLimits, RegexRequest, HELPER_NAME, QUALIFIED_MODEL,
};
use olint::unknowns::UnknownReason;
use tempfile::TempDir;

use crate::support;

use support::{
    classified_result_of, legacy_result_of, prepared_result_of, repository_helper_of, LegacyResult,
};

const FAKE_PACKAGE: &str = r#"const fs = require("node:fs");
const path = require("node:path");
fs.writeFileSync(path.join(__dirname, "loaded.txt"), "loaded");
const answer = (source, flags, complexity) => ({ source, flags, status: "safe", checker: "automaton", complexity });
exports.checkSync = (source, flags, parameters) => {
	fs.appendFileSync(
		path.join(__dirname, "calls.jsonl"),
		JSON.stringify({
			source,
			flags,
			parameters,
			backend: process.env.RECHECK_BACKEND ?? null,
			syncBackend: process.env.RECHECK_SYNC_BACKEND ?? null,
			nodeOptions: process.env.NODE_OPTIONS ?? null,
			nodePath: process.env.NODE_PATH ?? null,
			bin: process.env.RECHECK_BIN ?? null,
			arguments: process.execArgv,
		}) + "\n",
	);
	BEHAVIOUR
	return answer(source, flags, { type: "linear", summary: "linear", isFuzz: false });
};
"#;

const MARKER_PACKAGE: &str = r#"require("node:fs").writeFileSync(require("node:path").join(__dirname, "..", "..", "executed.txt"), "recheck");
exports.checkSync = () => { throw new Error("analysed project recheck"); };
"#;

const CLOCKED_PACKAGE: &str = r#"let now = 0;
const step = () => (now += 3600000);
Date.now = step;
performance.now = step;
module.exports = require(RECHECK);
"#;

fn selected_of(body: &str) -> LegacyResult {
    classified_result_of(&format!("export function selected{body}"), "selected")
}

fn assert_classified(cases: &[(&str, &str, bool)]) {
    for (body, expected, complete) in cases {
        let (cost, found, reasons) = selected_of(body);

        assert_eq!(cost, Cost::parse(expected).unwrap(), "{body}: {reasons:?}");
        assert_eq!(found, *complete, "{body}: {reasons:?}");
    }
}

fn copy_directory(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();

    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());

        match entry.file_type().unwrap().is_dir() {
            true => copy_directory(&entry.path(), &target),
            false => {
                std::fs::copy(entry.path(), target).unwrap();
            }
        }
    }
}

enum Dependency<'d> {
    Pinned,
    Missing,
    Clocked,
    Fake {
        version: &'d str,
        behaviour: &'d str,
    },
}

fn package_of(helper: Option<&str>, dependency: Dependency<'_>) -> TempDir {
    let directory = tempfile::tempdir().unwrap();
    let executable = Path::new(env!("CARGO_BIN_EXE_olint"));

    std::fs::copy(
        executable,
        directory.path().join(executable.file_name().unwrap()),
    )
    .unwrap();

    if let Some(helper) = helper {
        std::fs::write(directory.path().join(HELPER_NAME), helper).unwrap();
    }

    let modules = directory.path().join("node_modules");

    match dependency {
        Dependency::Pinned => {
            let installed = Path::new(env!("CARGO_MANIFEST_DIR")).join("node_modules");

            for name in ["recheck", "synckit", "@pkgr", "tslib"] {
                copy_directory(&installed.join(name), &modules.join(name));
            }
        }
        Dependency::Missing => {}
        Dependency::Clocked => {
            let package = modules.join("recheck");
            let installed = Path::new(env!("CARGO_MANIFEST_DIR")).join("node_modules/recheck");

            std::fs::create_dir_all(&package).unwrap();
            std::fs::write(
                package.join("package.json"),
                r#"{"name":"recheck","version":"4.5.0","main":"index.js"}"#,
            )
            .unwrap();
            std::fs::write(
                package.join("index.js"),
                CLOCKED_PACKAGE.replace(
                    "RECHECK",
                    &serde_json::to_string(&installed.to_string_lossy()).unwrap(),
                ),
            )
            .unwrap();
        }
        Dependency::Fake { version, behaviour } => {
            let package = modules.join("recheck");

            std::fs::create_dir_all(&package).unwrap();
            std::fs::write(
                package.join("package.json"),
                format!(r#"{{"name":"recheck","version":"{version}","main":"index.js"}}"#),
            )
            .unwrap();
            std::fs::write(
                package.join("index.js"),
                FAKE_PACKAGE.replace("BEHAVIOUR", behaviour),
            )
            .unwrap();
        }
    }

    directory
}

fn helper_script_of() -> String {
    std::fs::read_to_string(repository_helper_of()).unwrap()
}

fn fake_package_of(behaviour: &str) -> TempDir {
    package_of(
        Some(&helper_script_of()),
        Dependency::Fake {
            version: "4.5.0",
            behaviour,
        },
    )
}

fn packaged_helper_of(package: &TempDir) -> PathBuf {
    package.path().join(HELPER_NAME)
}

fn packaged_executable_of(package: &TempDir) -> PathBuf {
    package
        .path()
        .join(Path::new(env!("CARGO_BIN_EXE_olint")).file_name().unwrap())
}

fn calls_of(package: &TempDir) -> Vec<serde_json::Value> {
    std::fs::read_to_string(package.path().join("node_modules/recheck/calls.jsonl"))
        .unwrap_or_default()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

fn requests_of(patterns: &[(&str, &str)]) -> Vec<RegexRequest> {
    patterns
        .iter()
        .map(|(source, flags)| RegexRequest::qualified(source, flags))
        .collect()
}

fn project_of(policy: &str, source: &str) -> TempDir {
    support::project_of(&[
        ("tsconfig.json", r#"{"files":["index.ts"]}"#),
        ("index.ts", source),
        (
            "olint.config.json",
            &serde_json::json!({"entrypoints":["index.ts"],"max":"O(N^3)","unknown":policy})
                .to_string(),
        ),
    ])
}

#[derive(Debug)]
struct Run {
    exit: Option<i32>,
    stdout: String,
    stderr: String,
}

fn run_of(package: &TempDir, project: &TempDir, report: bool, environment: &[(&str, &str)]) -> Run {
    let mut command = Command::new(packaged_executable_of(package));

    command
        .args(["--types", "syntactic"])
        .current_dir(project.path());

    if report {
        command.args(["--report", "--min", "0"]);
    }

    for (name, value) in environment {
        command.env(name, value);
    }

    let output = command.output().unwrap();

    Run {
        exit: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

fn fake_answers_of(
    behaviour: &str,
    requests: &[RegexRequest],
    limits: &RegexLimits,
) -> (TempDir, Result<Vec<RegexAnswer>, RegexError>) {
    let package = fake_package_of(behaviour);
    let answers = ask(&packaged_helper_of(&package), requests, limits);

    (package, answers)
}

fn kinds_of(answers: &[RegexAnswer]) -> Vec<&'static str> {
    answers
        .iter()
        .map(|answer| match answer {
            RegexAnswer::Bound { .. } => "bound",
            RegexAnswer::Unknown { .. } => "unknown",
            RegexAnswer::Exhausted { .. } => "exhausted",
        })
        .collect()
}

const POLYNOMIAL: &str = "export function selected(s: string) { return /^a*a*$/.test(s); }";

#[test]
fn supported_classes_map_only_to_justified_bounds() {
    assert_classified(&[
        ("(s: string) { return /^a*a*$/.test(s); }", "O(N^2)", true),
        ("(s: string) { return /^a*a*$/.exec(s); }", "O(N^2)", true),
        ("(s: string) { return /^a*$/.test(s); }", "O(N)", true),
        ("(s: string) { return s.match(/^a*a*$/); }", "O(N^2)", true),
        (
            "(s: string) { return s.match(\"^a*a*$\"); }",
            "O(N^2)",
            true,
        ),
        ("(s: string) { return s.search(/a*a*$/); }", "O(N^3)", true),
        (
            "(s: string) { return s.replace(/^a*a*$/, \"b\"); }",
            "O(N^2)",
            true,
        ),
        ("() { return /^a*a*$/.test(\"aaaa\"); }", "O(1)", true),
        ("() { return /^(?=a)a+$/.test(\"aaaa\"); }", "O(1)", true),
    ]);
}

#[test]
fn unsupported_and_unbounded_classes_keep_known_work_partial() {
    for body in [
        "(s: string) { return /^(?=a)a+$/.test(s); }",
        "(s: string) { return /(?<=a)b+/.test(s); }",
        "(s: string) { return /^(a+)\\1$/.test(s); }",
        "(s: string) { return /[a&&b]+/v.test(s); }",
        "(s: string) { return /^xyz$/.test(s); }",
        "(s: string) { return /xyz/.test(s); }",
        "(s: string) { return /^(a+)+$/.test(s); }",
        "(s: string) { return /(a*)*b/.test(s); }",
    ] {
        let (cost, complete, reasons) = selected_of(body);

        assert_eq!(cost, Cost::parse("O(N)").unwrap(), "{body}: {reasons:?}");
        assert!(!complete, "{body}");
        assert!(
            reasons.contains(&UnknownReason::UnsupportedModel),
            "{body}: {reasons:?}"
        );
    }
}

#[test]
fn repeated_matching_charges_every_match_or_its_proven_modifier() {
    assert_classified(&[
        (
            "(s: string) { return s.replaceAll(/\\s+/g, \" \"); }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return [...s.matchAll(/a+/g)]; }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return s.matchAll(\"a*a*$\"); }",
            "O(N^4)",
            true,
        ),
        (
            "(s: string) { return s.replace(/x*y/g, \"\"); }",
            "O(N^3)",
            true,
        ),
        ("(s: string) { return s.split(/x*y/); }", "O(N^3)", true),
        (
            "(s: string) { return s.replace(/a*b|a/g, \"\"); }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return s.replace(/(?<run>x*)y/g, \"\"); }",
            "O(N^3)",
            true,
        ),
        (
            "(s: string) { return s.replace(/x*y/gy, \"\"); }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return s.replace(/x*y/y, \"\"); }",
            "O(N)",
            true,
        ),
        ("(s: string) { return s.match(/x*y/); }", "O(N^2)", true),
        (
            "(s: string) { return s.replace(/^a*a*$/g, \"b\"); }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return s.replaceAll(/^a*a*$/gy, \"b\"); }",
            "O(N^2)",
            true,
        ),
        ("(s: string) { return /^a*a*$/g.test(s); }", "O(N^2)", true),
        ("(s: string) { return /x*y/gy.exec(s); }", "O(N)", true),
        ("(s: string) { return s.search(/x*y/g); }", "O(N^2)", true),
    ]);
}

#[test]
fn context_dependent_repetition_keeps_one_search_partial() {
    assert_classified(&[
        (
            "(s: string) { return s.replace(/^a*a*$/gm, \"b\"); }",
            "O(N^2)",
            false,
        ),
        (
            "(s: string) { return s.replace(/x*y|^z/g, \"\"); }",
            "O(N^2)",
            false,
        ),
        (
            "(s: string) { return s.replace(/^z|x*y/g, \"\"); }",
            "O(N^2)",
            false,
        ),
        (
            "(s: string) { return s.replace(/\\bx*y/g, \"\"); }",
            "O(N)",
            false,
        ),
        (
            "(s: string) { return s.replace(/[\\b^]x*y/g, \"\"); }",
            "O(N^2)",
            true,
        ),
        (
            "(s: string) { return s.replace(/a/g, \"b\"); }",
            "O(N)",
            false,
        ),
        ("(s: string) { return s.split(/,/); }", "O(N)", false),
    ]);
}

#[test]
fn modifiers_are_read_from_the_pattern_structure() {
    use olint::regex::{is_context_free, is_matched_once};

    for (source, flags, once, free) in [
        ("^a*", "g", true, false),
        ("^a*", "gm", false, false),
        ("^a|b", "g", false, false),
        ("^(a|b)", "g", true, false),
        ("^[|]a", "g", true, false),
        ("^\\|a", "g", true, false),
        ("^[[|]]", "gv", true, false),
        ("a^", "g", false, false),
        ("x*y", "g", false, true),
        ("[\\b]x", "g", false, true),
        ("\\bx", "g", false, false),
        ("\\Bx", "g", false, false),
        ("[^x]y", "g", false, true),
        ("\\^x", "g", false, true),
        ("(?<=a)x", "g", false, false),
        ("(?<!a)x", "g", false, false),
        ("(?<run>a)x", "g", false, true),
        ("(?=a)x", "g", false, true),
    ] {
        assert_eq!(is_matched_once(source, flags), once, "{source} {flags}");
        assert_eq!(is_context_free(source, flags), free, "{source} {flags}");
    }
}

#[test]
fn dynamic_patterns_stay_unknown_even_for_constant_subjects() {
    assert_classified(&[
        ("(re: RegExp) { return re.test(\"abc\"); }", "O(1)", false),
        (
            "(s: string, re: RegExp) { return s.replace(re, \"b\"); }",
            "O(N)",
            false,
        ),
        (
            "(s: string, pattern: string) { return s.match(pattern); }",
            "O(N)",
            false,
        ),
        (
            "(s: string) { return s.match(new RegExp(\"^a*$\")); }",
            "O(N)",
            false,
        ),
        (
            "(s: string) { return s.replace(\"x\", \"y\"); }",
            "O(N)",
            true,
        ),
        ("(s: string) { return s.split(\",\"); }", "O(N)", true),
        ("(s: string) { return s.includes(\"x\"); }", "O(N)", true),
        (
            "(s: string, pattern: any) { return s.includes(pattern); }",
            "O(N)",
            true,
        ),
    ]);
}

#[test]
fn requests_follow_the_compiled_flags() {
    support::run_with_source(
        "export function selected(s: string) { return [s.match(\"a+\"), s.matchAll(\"b+\"), s.search(\"c+\"), s.replace(\"d+\", \"\"), /e+/y.test(s)]; }",
        |analysis, _| {
            assert_eq!(
                analysis.regex_requests_of(),
                requests_of(&[("a+", ""), ("b+", "g"), ("c+", ""), ("e+", "y")])
            );
        },
    );
}

#[test]
fn unrequested_classifications_stay_unknown() {
    let (cost, complete, reasons) = legacy_result_of(POLYNOMIAL, "selected");

    assert_eq!(cost, Cost::parse("O(N)").unwrap());
    assert!(!complete);
    assert!(
        reasons.contains(&UnknownReason::UnsupportedModel),
        "{reasons:?}"
    );
}

#[test]
fn analysis_exhaustion_yields_unknown() {
    let limits = RegexLimits {
        source_bytes: 4,
        ..RegexLimits::default()
    };
    let answers = ask(
        &repository_helper_of(),
        &requests_of(&[("^(a+)+$", ""), ("^a*a*$", "")]),
        &limits,
    )
    .unwrap();

    assert!(
        answers
            .iter()
            .all(|answer| matches!(answer, RegexAnswer::Exhausted { .. })),
        "{answers:?}"
    );

    for source in [
        POLYNOMIAL,
        "export function selected(s: string) { return s.replace(/x*y|^z/g, \"\"); }",
    ] {
        let (cost, complete, reasons) = prepared_result_of(source, "selected", |analysis| {
            analysis
                .gather_regex_answers(|requests| ask(&repository_helper_of(), requests, &limits))
                .unwrap();
        });

        assert_eq!(cost, Cost::parse("O(N)").unwrap(), "{source}");
        assert!(!complete, "{source}");
        assert_eq!(
            reasons,
            [UnknownReason::ResourceExhaustion].into_iter().collect(),
            "{source}"
        );
    }
}

#[test]
fn request_budgets_withhold_patterns_from_the_helper() {
    let limits = RegexLimits {
        source_bytes: 8,
        requests: 2,
        ..RegexLimits::default()
    };
    let mut requests = requests_of(&[("a", ""), ("aaaaaaaaa", ""), ("bbbbbbbb", ""), ("c", "")]);

    requests.push(RegexRequest {
        source: "d".to_string(),
        flags: String::new(),
        model: "engine exact".to_string(),
    });

    let (package, answers) = fake_answers_of("", &requests, &limits);
    let sent: Vec<_> = calls_of(&package)
        .iter()
        .map(|call| call["source"].as_str().unwrap().to_string())
        .collect();

    assert_eq!(
        kinds_of(&answers.unwrap()),
        ["bound", "exhausted", "bound", "exhausted", "unknown"]
    );
    assert_eq!(sent, ["a", "bbbbbbbb"]);
}

#[test]
fn oversized_replies_are_tool_errors() {
    let per_line = RegexLimits {
        source_bytes: 8,
        ..RegexLimits::default()
    };
    let (_, result) = fake_answers_of(
        "return answer(source + \" \".repeat(2000), flags, { type: \"linear\", isFuzz: false });",
        &requests_of(&[("a", "")]),
        &per_line,
    );

    assert!(
        matches!(&result, Err(RegexError::Malformed(message)) if message.starts_with("reply exceeds")),
        "{result:?}"
    );

    let total = RegexLimits {
        reply_bytes: 200,
        ..RegexLimits::default()
    };
    let (_, result) = fake_answers_of("", &requests_of(&[("a", ""), ("b", "")]), &total);

    assert!(
        matches!(&result, Err(RegexError::Malformed(message)) if message.starts_with("reply exceeds")),
        "{result:?}"
    );

    let (_, result) = fake_answers_of("", &requests_of(&[("a", "")]), &total);

    assert_eq!(kinds_of(&result.unwrap()), ["bound"]);
}

#[test]
fn helpers_request_only_automaton_analysis_without_recall() {
    let package = fake_package_of("");
    let project = project_of("warn", POLYNOMIAL);
    let lint = run_of(
        &package,
        &project,
        false,
        &[
            ("NODE_OPTIONS", "--no-warnings"),
            ("NODE_PATH", "nowhere"),
            ("RECHECK_BACKEND", "java"),
            ("RECHECK_SYNC_BACKEND", "worker"),
            ("RECHECK_BIN", "nowhere"),
        ],
    );
    let calls = calls_of(&package);

    assert_eq!(lint.exit, Some(0), "{lint:?}");
    assert_eq!(calls.len(), 1, "{lint:?}");
    assert_eq!(
        calls[0]["parameters"],
        serde_json::json!({"checker":"automaton","timeout":null,"recallTimeout":-1,"maxRecallStringSize":128})
    );
    assert_eq!(
        (
            &calls[0]["backend"],
            &calls[0]["syncBackend"],
            &calls[0]["bin"]
        ),
        (
            &serde_json::json!("pure"),
            &serde_json::json!("pure"),
            &serde_json::Value::Null
        )
    );
    assert_eq!(
        (&calls[0]["nodeOptions"], &calls[0]["nodePath"]),
        (&serde_json::Value::Null, &serde_json::Value::Null)
    );
    assert_eq!(
        calls[0]["arguments"],
        serde_json::json!(["--max-old-space-size=512"])
    );
}

#[test]
fn forbidden_executions_are_tool_errors() {
    for (behaviour, attempt) in [
        (
            "new RegExp(source, flags).exec(\"aaaa\");",
            "matching /^a+$/",
        ),
        (
            "require(\"node:child_process\").spawnSync(\"node\", [\"--version\"]);",
            "child_process.spawnSync",
        ),
        (
            "new (require(\"node:worker_threads\").Worker)(\"\");",
            "worker_threads.Worker",
        ),
    ] {
        let (_, result) = fake_answers_of(
            behaviour,
            &requests_of(&[("^a+$", "")]),
            &RegexLimits::default(),
        );

        assert!(
            matches!(&result, Err(RegexError::Malformed(message)) if message.contains(attempt)),
            "{behaviour}: {result:?}"
        );
    }
}

#[test]
fn malformed_replies_are_tool_errors() {
    for behaviour in [
        "return { ...answer(source, flags, { type: \"linear\", isFuzz: false }), checker: \"fuzz\" };",
        "return answer(source, flags, { type: \"linear\", isFuzz: true });",
        "return answer(source + \"b\", flags, { type: \"linear\", isFuzz: false });",
        "return { ...answer(source, flags, { type: \"linear\", isFuzz: false }), status: \"maybe\" };",
        "return { ...answer(source, flags, { type: \"linear\", isFuzz: false }), error: { kind: \"timeout\" } };",
        "return { source, flags, status: \"unknown\", checker: \"automaton\", error: { kind: \"surprise\" } };",
        "return { source, flags, status: \"unknown\", checker: \"automaton\", error: { kind: \"timeout\" } };",
        "return { source, flags, status: \"unknown\", checker: \"automaton\", error: { kind: \"cancel\" } };",
        "return { source, flags, status: \"unknown\", error: { kind: \"x\".repeat(100000) } };",
        "return answer(source, flags, { type: \"cubic\", isFuzz: false });",
        "return answer(source, flags, { type: \"linear\", degree: 1, isFuzz: false });",
    ] {
        let (_, result) =
            fake_answers_of(behaviour, &requests_of(&[("a", "")]), &RegexLimits::default());

        assert!(
            matches!(result, Err(RegexError::Malformed(_))),
            "{behaviour}: {result:?}"
        );
    }
}

#[test]
fn only_qualified_classes_supply_bounds() {
    for (behaviour, expected) in [
        (
            "return answer(source, flags, { type: \"constant\", isFuzz: false });",
            Some(Cost::ONE),
        ),
        ("", Some(Cost::N)),
        (
            "return { ...answer(source, flags, { type: \"polynomial\", degree: 3, isFuzz: false }), status: \"vulnerable\" };",
            Some(Cost::power(Cost::N, Cost::constant(3)).unwrap()),
        ),
        (
            "return answer(source, flags, { type: \"polynomial\", degree: 2.5, isFuzz: false });",
            None,
        ),
        (
            "return answer(source, flags, { type: \"polynomial\", degree: 0, isFuzz: false });",
            None,
        ),
        (
            "return answer(source, flags, { type: \"polynomial\", degree: 17, isFuzz: false });",
            None,
        ),
        (
            "return answer(source, flags, { type: \"polynomial\", isFuzz: false });",
            None,
        ),
        (
            "return answer(source, flags, { type: \"safe\", isFuzz: false });",
            None,
        ),
        (
            "return answer(source, flags, { type: \"exponential\", isFuzz: false });",
            None,
        ),
        (
            "return { source, flags, status: \"unknown\", checker: \"automaton\", error: { kind: \"unsupported\" } };",
            None,
        ),
        (
            "return { source, flags, status: \"unknown\", error: { kind: \"invalid\" } };",
            None,
        ),
    ] {
        let (_, answers) =
            fake_answers_of(behaviour, &requests_of(&[("a", "")]), &RegexLimits::default());
        let answer = answers.unwrap().remove(0);

        match expected {
            Some(cost) => assert_eq!(
                answer,
                RegexAnswer::Bound {
                    cost,
                    model: QUALIFIED_MODEL.to_string(),
                },
                "{behaviour}"
            ),
            None => assert_eq!(kinds_of(&[answer]), ["unknown"], "{behaviour}"),
        }
    }
}

#[test]
fn the_deadline_terminates_a_stuck_helper() {
    let limits = RegexLimits {
        deadline: Duration::from_secs(3),
        ..RegexLimits::default()
    };
    let (_, answers) = fake_answers_of(
        "if (source === \"stuck\") for (;;) {}",
        &requests_of(&[("fast", ""), ("stuck", ""), ("never", "")]),
        &limits,
    );

    assert_eq!(answers, Err(RegexError::Deadline(Duration::from_secs(3))));
}

#[test]
fn answers_are_identical_under_a_stubbed_clock() {
    let requests = requests_of(&[
        ("^a*a*$", ""),
        ("^(a+)+$", ""),
        ("\\s+", "g"),
        ("^(?=a)a+$", ""),
    ]);
    let limits = RegexLimits::default();
    let answers = ask(&repository_helper_of(), &requests, &limits).unwrap();
    let clocked = package_of(Some(&helper_script_of()), Dependency::Clocked);
    let stubbed = ask(&packaged_helper_of(&clocked), &requests, &limits).unwrap();

    assert_eq!(kinds_of(&answers), ["bound", "unknown", "bound", "unknown"]);
    assert_eq!(stubbed, answers);
}

#[test]
fn the_heap_cap_stops_runaway_analysis() {
    let limits = RegexLimits {
        heap_megabytes: 32,
        ..RegexLimits::default()
    };
    let (_, answers) = fake_answers_of(
        "if (source === \"grow\") { const held = []; for (;;) held.push(new Array(100000).fill(source)); }",
        &requests_of(&[("fast", ""), ("grow", "")]),
        &limits,
    );

    assert_eq!(kinds_of(&answers.unwrap()), ["bound", "exhausted"]);
}

struct Unavailable {
    name: &'static str,
    package: TempDir,
    environment: Vec<(&'static str, String)>,
    reason: &'static str,
}

#[test]
fn availability_failures_keep_known_work_under_every_unknown_policy() {
    let helper = helper_script_of();
    let empty = tempfile::tempdir().unwrap();
    let changed = format!("{helper}\n");
    let cases = [
        Unavailable {
            name: "missing node",
            package: package_of(Some(&helper), Dependency::Pinned),
            environment: vec![("PATH", empty.path().to_string_lossy().into_owned())],
            reason: "node did not start",
        },
        Unavailable {
            name: "missing helper",
            package: package_of(None, Dependency::Pinned),
            environment: Vec::new(),
            reason: "cannot be read",
        },
        Unavailable {
            name: "changed helper",
            package: package_of(Some(&changed), Dependency::Pinned),
            environment: Vec::new(),
            reason: "does not match this olint build",
        },
        Unavailable {
            name: "missing package",
            package: package_of(Some(&helper), Dependency::Missing),
            environment: Vec::new(),
            reason: "is not installed beside",
        },
        Unavailable {
            name: "version mismatch",
            package: package_of(
                Some(&helper),
                Dependency::Fake {
                    version: "4.4.0",
                    behaviour: "",
                },
            ),
            environment: Vec::new(),
            reason: "recheck 4.4.0",
        },
    ];

    for case in &cases {
        let name = case.name;
        let environment: Vec<(&str, &str)> = case
            .environment
            .iter()
            .map(|(variable, value)| (*variable, value.as_str()))
            .collect();

        for policy in ["ignore", "warn", "error"] {
            let project = project_of(policy, POLYNOMIAL);
            let lint = run_of(&case.package, &project, false, &environment);

            assert_eq!(
                lint.exit,
                Some(i32::from(policy == "error")),
                "{name} {policy}: {lint:?}"
            );
            assert!(
                lint.stderr
                    .contains("olint: regex classification unavailable (")
                    && lint.stderr.contains(case.reason),
                "{name} {policy}: {lint:?}"
            );
            assert_eq!(
                lint.stderr.contains("unknown operation model"),
                policy != "ignore",
                "{name} {policy}: {lint:?}"
            );
            assert!(
                lint.stdout.contains("1 partial result"),
                "{name} {policy}: {lint:?}"
            );

            let report = run_of(&case.package, &project, true, &environment);

            assert_eq!(report.exit, Some(0), "{name} {policy}: {report:?}");
            assert!(
                report
                    .stdout
                    .lines()
                    .any(|line| line.starts_with("O(s) ") && line.ends_with("[partial]")),
                "{name} {policy}: {report:?}"
            );
        }

        assert!(
            !case
                .package
                .path()
                .join("node_modules/recheck/loaded.txt")
                .exists(),
            "{name}"
        );
    }

    let package = package_of(Some(&helper), Dependency::Pinned);

    for policy in ["ignore", "warn", "error"] {
        let project = project_of(policy, POLYNOMIAL);
        let report = run_of(&package, &project, true, &[]);

        assert_eq!(report.exit, Some(0), "{policy}: {report:?}");
        assert!(
            !report.stderr.contains("unavailable"),
            "{policy}: {report:?}"
        );
        assert!(
            report.stdout.lines().any(|line| line.starts_with("O(s^2) ")
                && line.contains("selected")
                && !line.contains("[partial]")),
            "{policy}: {report:?}"
        );
    }
}

#[test]
fn malformed_helper_replies_exit_two() {
    let package = fake_package_of(
        "return { ...answer(source, flags, { type: \"linear\", isFuzz: false }), checker: \"fuzz\" };",
    );
    let project = project_of("warn", POLYNOMIAL);
    let lint = run_of(&package, &project, false, &[]);

    assert_eq!(lint.exit, Some(2), "{lint:?}");
    assert!(
        lint.stderr
            .contains("olint: regex helper replied malformed: fuzz answer"),
        "{lint:?}"
    );
}

#[test]
fn analysed_projects_cannot_supply_or_override_the_adapter() {
    let package = package_of(Some(&helper_script_of()), Dependency::Pinned);
    let project = support::project_of(&[
        ("tsconfig.json", r#"{"files":["index.ts"]}"#),
        (
            "index.ts",
            "import { poison } from \"./poison\";\nexport function selected(s: string) { poison(); return /^a*a*$/.test(s); }",
        ),
        (
            "poison.ts",
            "require(\"node:fs\").writeFileSync(\"executed.txt\", \"module\");\nexport function poison() {}",
        ),
        (
            "node_modules/recheck/package.json",
            r#"{"name":"recheck","version":"4.4.0","main":"index.js"}"#,
        ),
        ("node_modules/recheck/index.js", MARKER_PACKAGE),
        (
            "preload.cjs",
            "require(\"node:fs\").writeFileSync(require(\"node:path\").join(__dirname, \"executed.txt\"), \"preload\");",
        ),
        (
            "olint.config.json",
            r#"{"entrypoints":["index.ts"],"max":"O(N^3)","unknown":"error"}"#,
        ),
    ]);
    let modules = project
        .path()
        .join("node_modules")
        .to_string_lossy()
        .into_owned();
    let preload = format!("--require={}", project.path().join("preload.cjs").display());
    let report = run_of(
        &package,
        &project,
        true,
        &[
            ("NODE_PATH", modules.as_str()),
            ("NODE_OPTIONS", preload.as_str()),
            ("RECHECK_BACKEND", "java"),
            ("RECHECK_SYNC_BACKEND", "worker"),
        ],
    );

    assert_eq!(report.exit, Some(0), "{report:?}");
    assert!(!report.stderr.contains("unavailable"), "{report:?}");
    assert!(
        report
            .stdout
            .lines()
            .any(|line| line.starts_with("O(s^2) ") && !line.contains("[partial]")),
        "{report:?}"
    );
    assert!(!project.path().join("executed.txt").exists());

    let bare = package_of(Some(&helper_script_of()), Dependency::Missing);
    let substitute = support::project_of(&[
        ("tsconfig.json", r#"{"files":["index.ts"]}"#),
        ("index.ts", POLYNOMIAL),
        (
            "node_modules/recheck/package.json",
            r#"{"name":"recheck","version":"4.5.0","main":"index.js"}"#,
        ),
        ("node_modules/recheck/index.js", MARKER_PACKAGE),
    ]);
    let modules = substitute
        .path()
        .join("node_modules")
        .to_string_lossy()
        .into_owned();
    let report = run_of(&bare, &substitute, true, &[("NODE_PATH", modules.as_str())]);

    assert!(
        report
            .stderr
            .contains("olint: regex classification unavailable (recheck 4.5.0 is not installed"),
        "{report:?}"
    );
    assert!(!substitute.path().join("executed.txt").exists());
}

#[test]
fn the_packaged_helper_resolves_its_own_dependency_from_another_cwd() {
    let package = package_of(Some(&helper_script_of()), Dependency::Pinned);
    let project = support::project_of(&[
        (
            "node_modules/recheck/package.json",
            r#"{"name":"recheck","version":"4.4.0","main":"index.js"}"#,
        ),
        ("node_modules/recheck/index.js", MARKER_PACKAGE),
    ]);
    let mut child = Command::new("node")
        .arg(packaged_helper_of(&package))
        .current_dir(project.path())
        .env_remove("NODE_PATH")
        .env_remove("NODE_OPTIONS")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    child
        .stdin
        .take()
        .unwrap()
        .write_all(br#"{"version":2,"requests":[{"source":"^a*a*$","flags":""}]}"#)
        .unwrap();

    let output = child.wait_with_output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<serde_json::Value> = stdout
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();

    assert_eq!(output.status.code(), Some(0), "{stdout}");
    assert_eq!(lines[0], serde_json::json!({"version":2,"recheck":"4.5.0"}));
    assert_eq!(lines[1]["complexity"]["type"], "polynomial");
    assert_eq!(lines[1]["complexity"]["degree"], 2);
    assert!(!project.path().join("executed.txt").exists());
}

#[test]
fn selected_regex_requests_follow_calls_and_recompute_answers() {
    let source = "function dependency(value: string){return /^a+$/.test(value)} function unreachable(value:string){return /^b+$/.test(value)} export function selected(value:string){return dependency(value)}";

    support::run_with_source(source, |analysis, file| {
        let selected = support::function_of_name(analysis.project, file, "selected");
        let mut batches = Vec::new();

        analysis
            .gather_selected_regex_answers(&[(file, selected)], |requests| {
                batches.push(requests.to_vec());

                Ok(vec![
                    RegexAnswer::Bound {
                        cost: Cost::N,
                        model: QUALIFIED_MODEL.into()
                    };
                    requests.len()
                ])
            })
            .unwrap();

        assert_eq!(batches, vec![requests_of(&[("^a+$", "")])]);

        let part = support::summary_of(analysis, file, "selected");

        assert!(part.is_complete(), "{part:?}");
        assert_eq!(
            support::legacy_class_of(analysis, file, selected, &part.cost),
            Cost::N
        );

        let functions = analysis.reportable();
        let mut reported = Vec::new();

        analysis
            .gather_selected_regex_answers(&functions, |requests| {
                reported.extend_from_slice(requests);

                Ok(vec![
                    RegexAnswer::Bound {
                        cost: Cost::N,
                        model: QUALIFIED_MODEL.into()
                    };
                    requests.len()
                ])
            })
            .unwrap();
        assert_eq!(reported, requests_of(&[("^b+$", "")]));
    });
}

#[test]
fn empty_selected_regex_scope_does_not_invoke_the_helper() {
    support::run_with_source(
        "export function unused(value:string){return /^a+$/.test(value)}",
        |analysis, _| {
            analysis
                .gather_selected_regex_answers(&[], |_| panic!("empty regex scope reached helper"))
                .unwrap();
            assert_eq!(analysis.scheduler_stats().tasks, 0);
        },
    );
}

#[test]
fn selected_regex_gathering_keeps_ignored_dependency_calls() {
    support::run_in_project(&[
        ("tsconfig.json", "{}"),
        ("olint.config.json", r#"{"entrypoints":["index.ts"],"ignore":["helper.ts"]}"#),
        ("index.ts", "import {match} from './helper'; export function selected(value:string){return match(value)}"),
        ("helper.ts", "export function match(value:string){return /^a+$/.test(value)} export function unused(value:string){return /^b+$/.test(value)}"),
    ], |project, _| {
        let config = olint::config::read_config(project, None).unwrap();
        let mut analysis = olint::analysis::Analysis::new(project, support::SYNTACTIC);
        let functions = olint::public::public_roots(&mut analysis, &config).unwrap();
        let mut asked = Vec::new();

        analysis.gather_selected_regex_answers(&functions, |requests| {
            asked.extend_from_slice(requests);

            Ok(requests.iter().map(|_| RegexAnswer::Unknown {reason: "test unknown".into()}).collect())
        }).unwrap();
        assert_eq!(asked, requests_of(&[("^a+$", "")]));
    });
}

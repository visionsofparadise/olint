use std::path::Path;
use std::process::Command;

#[test]
fn public_value_surfaces_retain_known_functions_and_partial_coverage() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("fixtures/public-surfaces.json")).unwrap(),
    );
}

#[test]
fn public_coverage_policy_survives_filtering_without_a_numeric_surcharge() {
    for policy in ["ignore", "warn", "error"] {
        for mixed in ["none", "constant", "cubic"] {
            let directory = tempfile::tempdir().unwrap();

            std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
            std::fs::write(
                directory.path().join("olint.config.json"),
                serde_json::json!({"entrypoints":["index.ts"],"unknown":policy,"max":"O(1)"})
                    .to_string(),
            )
            .unwrap();

            let known = match mixed {
                "constant" => "export function known() { void 0; }",
                "cubic" => "export function known(xs:number[]) {for(const a of xs)for(const b of xs)for(const c of xs)void c;}",
                _ => "",
            };

            std::fs::write(
                directory.path().join("index.ts"),
                format!("declare const unavailable:()=>void; export {{unavailable}}; {known}"),
            )
            .unwrap();

            for report in [false, true] {
                let mut command = Command::new(env!("CARGO_BIN_EXE_olint"));

                command.args(["--types", "syntactic", "--min", "100"]);

                if report {
                    command.arg("--report");
                }

                let (exit, stdout, stderr) = captured(command.current_dir(directory.path()));

                assert_eq!(
                    exit,
                    Some(i32::from(
                        !report && (policy == "error" || mixed == "cubic")
                    )),
                    "{policy} {mixed} {report}: {stdout} {stderr}"
                );
                assert!(stdout.contains("public coverage [partial]"), "{stdout}");
                assert_eq!(
                    stderr.contains("olint: warning:") || stderr.contains("olint: error:"),
                    policy != "ignore",
                    "{stderr}"
                );
                assert!(!stdout.contains("exceeds"), "{stdout}");
            }
        }
    }
}

#[test]
fn explicit_source_paths_override_heuristics_in_both_modes() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("fixtures/source-paths.json")).unwrap(),
    );
}

#[test]
fn package_entry_mappings_select_costly_apis_and_diagnose_unknown_mappings() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("fixtures/package-entries.json")).unwrap(),
    );
}

#[test]
fn explicit_selection_matrix_rejects_invalid_coverage_and_preserves_empty_controls() {
    assert_selection_cases(&serde_json::from_str(include_str!("fixtures/selection.json")).unwrap());
}

fn assert_selection_cases(cases: &serde_json::Value) {
    for case in cases.as_array().unwrap() {
        let directory = tempfile::tempdir().unwrap();

        for (name, value) in case["files"].as_object().unwrap() {
            let path = directory.path().join(name);

            std::fs::create_dir_all(path.parent().unwrap()).unwrap();

            let text = value
                .as_str()
                .map(str::to_string)
                .unwrap_or_else(|| value.to_string());

            std::fs::write(path, text).unwrap();
        }

        for mode in ["lint", "report"] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_olint"));

            command.args(["--types", "syntactic"]);

            for argument in case["args"].as_array().unwrap() {
                command.arg(argument.as_str().unwrap());
            }

            if mode == "report" {
                command.args(["--report", "--min", "0"]);
            }

            let (exit, stdout, stderr) = captured(command.current_dir(directory.path()));
            let combined = format!("{stdout}\n{stderr}");
            let name = case["name"].as_str().unwrap();

            assert_eq!(
                exit,
                Some(case["expected_exits"][mode].as_i64().unwrap() as i32),
                "{name} {mode}: {combined}"
            );

            if case["kind"] == "invalid-selection" {
                assert!(!stderr.trim().is_empty(), "{name}");
            }

            for (field, present) in [("expected_contains", true), ("expected_absent", false)] {
                for expected in case[field][mode].as_array().into_iter().flatten() {
                    assert_eq!(
                        combined.contains(expected.as_str().unwrap()),
                        present,
                        "{name} {mode}: {combined}"
                    );
                }
            }
        }
    }
}

fn golden_of(fixture: &Path, name: &str) -> String {
    std::fs::read_to_string(fixture.join(name))
        .unwrap_or_else(|error| panic!("{} {name}: {error}", fixture.display()))
        .replace("\r\n", "\n")
}

fn differences_of(
    fixture: &Path,
    arguments: &[&str],
    golden: &str,
    exit: Option<i32>,
) -> Vec<String> {
    let output = Command::new(env!("CARGO_BIN_EXE_olint"))
        .args(["--tsconfig", "tsconfig.json"])
        .args(arguments)
        .current_dir(fixture)
        .output()
        .expect("olint runs");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let label = format!("{} {}", fixture.display(), arguments.join(" "));
    let failure = stderr
        .lines()
        .find(|line| line.starts_with("olint:"))
        .unwrap_or_default();
    let mut differences = Vec::new();

    if stdout != golden_of(fixture, golden) {
        differences.push(format!(
            "{label}: stdout differs from {golden} {failure}\n{stdout}"
        ));
    }

    if output.status.code() != exit {
        differences.push(format!(
            "{label}: exit {:?}, expected {exit:?} {failure}",
            output.status.code()
        ));
    }

    differences
}

#[test]
fn fixtures_print_their_golden_output() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut directories: Vec<_> = std::fs::read_dir(&fixtures)
        .expect("fixtures directory")
        .map(|entry| entry.expect("fixture entry").path())
        .filter(|path| path.is_dir())
        .collect();
    let mut differences = Vec::new();

    directories.sort();

    assert!(!directories.is_empty(), "no fixtures found");

    for fixture in &directories {
        let exit = golden_of(fixture, "expected-lint.exit").trim().parse().ok();

        differences.extend(differences_of(
            fixture,
            &["--types=tsc"],
            "expected-lint.txt",
            exit,
        ));
        differences.extend(differences_of(
            fixture,
            &["--types=tsc", "--report"],
            "expected-report.txt",
            Some(0),
        ));
        differences.extend(differences_of(
            fixture,
            &["--types=tsc", "--report", "--min=0"],
            "expected-report-min0.txt",
            Some(0),
        ));
    }

    assert!(differences.is_empty(), "{}", differences.join("\n\n"));
}

mod support;

#[test]
fn minimum_filter_preserves_logarithmic_exception_and_unknown_policy() {
    for (expression, minimum, visible) in [
        ("N^3", "99", false),
        ("N^3", "3", true),
        ("N^3", "0", true),
        ("N log N", "99", true),
        ("N^3 * log(N)^2", "99", true),
        ("N^2 * log(N)^2 / (N * log(N))", "99", true),
        ("N * log(N) / log(N)", "99", false),
        ("N^3 / log(N)", "99", false),
    ] {
        for unknown in [false, true] {
            let body = if unknown { "callback();" } else { "" };
            let source = format!(
                "export function selected(n: number, callback: () => void) {{\n/** @perf O({expression}) */\nvoid 0;\n{body}\n}}"
            );
            let mut previous = None;

            for policy in ["ignore", "warn", "error"] {
                let config = serde_json::json!({
                    "entrypoints": ["index.ts"], "max": "O(1)", "unknown": policy
                });
                let directory = support::project_of(&[
                    ("tsconfig.json", "{\"files\":[\"index.ts\"]}"),
                    ("index.ts", &source),
                    ("olint.config.json", &config.to_string()),
                ]);
                let report = Command::new(env!("CARGO_BIN_EXE_olint"))
                    .args(["--types", "syntactic", "--report", "--min", minimum])
                    .current_dir(directory.path())
                    .output()
                    .expect("olint runs");
                let stdout = String::from_utf8_lossy(&report.stdout);
                let stderr = String::from_utf8_lossy(&report.stderr);

                assert_eq!(report.status.code(), Some(0), "{stderr}");
                assert_eq!(
                    stdout
                        .lines()
                        .any(|line| line.contains(" selected  index.ts:")),
                    visible,
                    "{expression} {minimum}: {stdout}"
                );

                if visible {
                    let row = stdout
                        .lines()
                        .find(|line| line.contains(" selected  index.ts:"))
                        .unwrap();

                    assert_eq!(row.contains("[partial]"), unknown, "{row}");
                }

                assert_eq!(stdout.contains("[partial]"), unknown, "{stdout}");
                assert_eq!(
                    stderr.contains("unknown call target"),
                    unknown && policy != "ignore",
                    "{stderr}"
                );

                if unknown && policy != "ignore" {
                    let severity = if policy == "error" {
                        "error"
                    } else {
                        "warning"
                    };

                    assert!(
                        stderr.contains(&format!("olint: {severity}: unknown call target")),
                        "{stderr}"
                    );
                }

                if let Some(previous) = previous.replace(report.stdout.clone()) {
                    assert_eq!(previous, report.stdout);
                }

                let lint = Command::new(env!("CARGO_BIN_EXE_olint"))
                    .args(["--types", "syntactic", "--min", minimum])
                    .current_dir(directory.path())
                    .output()
                    .expect("olint runs");

                assert_eq!(lint.status.code(), Some(1));
                assert!(String::from_utf8_lossy(&lint.stdout).contains("1 over limit"));
            }
        }
    }
}

fn captured(command: &mut Command) -> (Option<i32>, String, String) {
    let output = command.output().unwrap();

    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

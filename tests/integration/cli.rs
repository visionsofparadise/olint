use std::path::Path;
use std::process::Command;

#[test]
fn public_value_surfaces_retain_known_functions_and_partial_coverage() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("../fixtures/public-surfaces.json")).unwrap(),
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
        &serde_json::from_str(include_str!("../fixtures/source-paths.json")).unwrap(),
    );
}

#[test]
fn package_entry_mappings_select_costly_apis_and_diagnose_unknown_mappings() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("../fixtures/package-entries.json")).unwrap(),
    );
}

#[test]
fn explicit_selection_matrix_rejects_invalid_coverage_and_preserves_empty_controls() {
    assert_selection_cases(
        &serde_json::from_str(include_str!("../fixtures/selection.json")).unwrap(),
    );
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

use crate::support;

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

#[test]
fn an_absent_channel_neither_cancels_a_cold_cost_nor_hides_an_open_target() {
    let helpers = "export function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) for (const y of xs) total += x + y;\n\treturn total;\n}\n// @perf cold\nexport function coldQuadratic(xs: number[]) {\n\treturn quadratic(xs);\n}\nexport class Engine {\n\t// @perf cold\n\trebuild(xs: number[]) {\n\t\treturn quadratic(xs);\n\t}\n}\n";

    for (body, cost, partial, over_limit) in [
        (
            "export function selected(xs: number[]) {\n\tfor (const x of xs) {\n\t\treturn coldQuadratic(xs);\n\t}\n}\n",
            "O(xs^2)",
            false,
            true,
        ),
        (
            "export function selected(xs: number[], flag: boolean, f: (xs: number[]) => number) {\n\tconst g = flag ? coldQuadratic : f;\n\n\treturn g(xs);\n}\n",
            "O(1)",
            true,
            false,
        ),
        (
            "export function selected(xs: number[]) {\n\treturn new Engine().rebuild(xs);\n}\n",
            "O(xs^2)",
            true,
            true,
        ),
    ] {
        let source =
            format!("import {{ coldQuadratic, Engine }} from \"./helpers\";\n\nvoid Engine;\n\n{body}");
        let directory = support::project_of(&[
            (
                "tsconfig.json",
                "{\"compilerOptions\":{\"strict\":true},\"files\":[\"index.ts\"]}",
            ),
            ("helpers.ts", helpers),
            ("index.ts", &source),
            (
                "olint.config.json",
                "{\"entrypoints\":[\"index.ts\"],\"max\":\"O(N)\"}",
            ),
        ]);
        let (row, stderr) = reported_row_of(directory.path(), "selected");

        assert!(row.starts_with(cost), "{row}");
        assert_eq!(row.contains("[partial]"), partial, "{row}");
        assert_eq!(stderr.contains("unknown call target"), partial, "{stderr}");

        lint_diagnostics_of(directory.path(), over_limit);
    }
}

fn reported_row_of(directory: &Path, name: &str) -> (String, String) {
    let (code, stdout, stderr) = captured(
        Command::new(env!("CARGO_BIN_EXE_olint"))
            .args(["--types", "syntactic", "--report", "--min", "0"])
            .current_dir(directory),
    );

    assert_eq!(code, Some(0), "{stderr}");

    let row = stdout
        .lines()
        .find(|line| line.contains(&format!(" {name}  index.ts:")))
        .unwrap_or_else(|| panic!("{stdout}"));

    (row.to_owned(), stderr)
}

fn lint_diagnostics_of(directory: &Path, over_limit: bool) -> String {
    let (code, stdout, stderr) = captured(
        Command::new(env!("CARGO_BIN_EXE_olint"))
            .args(["--types", "syntactic"])
            .current_dir(directory),
    );

    assert_eq!(code, Some(i32::from(over_limit)), "{stdout}{stderr}");
    assert!(
        stdout.contains(if over_limit {
            "1 over limit"
        } else {
            "0 over limit"
        }),
        "{stdout}"
    );

    stderr
}

#[test]
fn an_absorbed_escape_beside_its_own_loop_stays_comparable_against_the_limit() {
    let source = "function quadratic(xs: number[]): number {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\treturn total;\n}\n\nexport function continueOuter(xs: number[]): number {\n\tlet total = 0;\n\touter: for (const a of xs) {\n\t\tfor (const b of xs) {\n\t\t\tif (b > 0) {\n\t\t\t\ttotal += quadratic(xs);\n\t\t\t\tcontinue outer;\n\t\t\t}\n\t\t}\n\t}\n\treturn total;\n}\n";
    let directory = support::project_of(&[
        (
            "tsconfig.json",
            "{\"compilerOptions\":{\"strict\":true},\"files\":[\"index.ts\"]}",
        ),
        ("index.ts", source),
        (
            "olint.config.json",
            "{\"entrypoints\":[\"index.ts\"],\"max\":\"O(N^2)\"}",
        ),
    ]);
    let stderr = lint_diagnostics_of(directory.path(), true);

    assert!(!stderr.contains("unknown comparison"), "{stderr}");

    let (row, _) = reported_row_of(directory.path(), "continueOuter");

    assert!(row.starts_with("O((xs * xs^2))"), "{row}");
}

#[test]
fn reports_show_scheduled_and_lazy_work_without_charging_unconsumed_generators() {
    let source = "function quadratic(xs: number[]): number {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\treturn total;\n}\n\nexport function* rows(xs: number[]) {\n\tfor (const a of xs) for (const b of xs) yield a + b;\n}\n\nexport function consume(xs: number[]): number {\n\tlet total = 0;\n\tfor (const row of rows(xs)) total += quadratic(xs);\n\treturn total;\n}\n\nexport function first(xs: number[]) {\n\treturn rows(xs).next();\n}\n\nexport function later(xs: number[], ready: Promise<number>) {\n\treturn ready.then(() => quadratic(xs));\n}\n";
    let directory = support::project_of(&[
        (
            "tsconfig.json",
            "{\"compilerOptions\":{\"strict\":true},\"files\":[\"index.ts\"]}",
        ),
        ("index.ts", source),
        (
            "olint.config.json",
            "{\"entrypoints\":[\"index.ts\"],\"max\":\"O(N^3)\"}",
        ),
    ]);
    let (code, stdout, stderr) = captured(
        Command::new(env!("CARGO_BIN_EXE_olint"))
            .args(["--types", "syntactic", "--report", "--min", "0"])
            .current_dir(directory.path()),
    );

    assert_eq!(code, Some(0), "{stderr}");

    let lines: Vec<&str> = stdout.lines().collect();
    let generator = lines
        .iter()
        .position(|line| line.contains(" rows  index.ts:"))
        .unwrap_or_else(|| panic!("{stdout}"));

    assert!(lines[generator].starts_with("O(1) "), "{stdout}");
    assert_eq!(
        lines[generator + 1].trim(),
        "lazy O(xs^2) when consumed",
        "{stdout}"
    );
    assert!(stdout.contains("calls rows(xs) [lazy]"), "{stdout}");
    assert!(
        stdout.contains("in loop for-of [iterator visits]"),
        "{stdout}"
    );
    assert!(
        stdout.contains("calls ready.then() callback [scheduled]"),
        "{stdout}"
    );

    let (row, _) = reported_row_of(directory.path(), "consume");

    assert!(!row.contains("[partial]"), "{row}");

    let (code, stdout, stderr) = captured(
        Command::new(env!("CARGO_BIN_EXE_olint"))
            .args(["--types", "syntactic"])
            .current_dir(directory.path()),
    );

    assert_eq!(code, Some(1), "{stdout}{stderr}");
    assert!(stdout.contains("  consume  index.ts:"), "{stdout}");
    assert!(!stdout.contains("  rows  index.ts:"), "{stdout}");
    assert!(stdout.contains("1 over limit"), "{stdout}");
}

type PackageCase<'c> = (&'c str, String, &'c str, Vec<(&'c str, &'c str)>);

#[test]
fn lint_walks_package_implementations_statically_and_keeps_boundaries_visible() {
    let cube = "let t = 0; for (const a of xs) for (const b of xs) for (const c of xs) t += a * b * c; return t;";
    let linear = "let t = 0; for (const a of xs) t += a; return t;";
    let consumer = "import { run } from \"pkg\";\nexport function selected(xs: number[]) {\n\treturn run(xs);\n}\n";
    let declaration = "export declare function run(xs: number[]): number;\n";
    let module_of = |module: &str| {
        format!(
            r#"{{"compilerOptions":{{"strict":true,"module":"{module}"}},"files":["index.ts"]}}"#
        )
    };
    let esm = format!("export function run(xs) {{ {cube} }}\n");
    let commonjs = format!("exports.run = function (xs) {{ {linear} }};\n");
    let dynamic = format!(
        "exports.run = function (xs, name) {{ {} return require(\"./\" + name).fast(xs) + t; }};\n",
        cube.replace("return t;", "")
    );
    let native_types = format!("export function run(xs: number[]) {{ {linear} }}\n");
    let conditions = r#"{"name":"pkg","types":"./index.d.ts","exports":{".":{"types":"./index.d.ts","import":"./esm.mjs","require":"./cjs.cjs"}}}"#;
    let limit = r#"{"entrypoints":["index.ts"],"max":"O(N^2)"}"#;
    let ignored = r#"{"entrypoints":["index.ts"],"max":"O(N^2)","ignore":["node_modules/pkg/**"]}"#;
    let module_manifest = (
        "node_modules/pkg/package.json",
        r#"{"name":"pkg","type":"module","main":"index.js","types":"index.d.ts"}"#,
    );
    let declared = ("node_modules/pkg/index.d.ts", declaration);
    let conditional = vec![
        ("node_modules/pkg/package.json", conditions),
        declared,
        ("node_modules/pkg/esm.mjs", esm.as_str()),
        ("node_modules/pkg/cjs.cjs", commonjs.as_str()),
    ];
    let cases: [PackageCase<'_>; 6] = [
        (
            "declaration beside an expensive module",
            module_of("esnext"),
            limit,
            vec![
                module_manifest,
                declared,
                ("node_modules/pkg/index.js", "import { writeFileSync } from \"node:fs\";\nwriteFileSync(\"executed.txt\", \"module\");\nexport { run } from \"./esm.mjs\";\n"),
                ("node_modules/pkg/esm.mjs", &esm),
            ],
        ),
        (
            "import condition",
            module_of("esnext"),
            limit,
            conditional.clone(),
        ),
        (
            "require condition",
            module_of("commonjs"),
            limit,
            conditional,
        ),
        (
            "ignored package",
            module_of("esnext"),
            ignored,
            vec![module_manifest, declared, ("node_modules/pkg/index.js", &esm)],
        ),
        (
            "native runtime entry",
            module_of("esnext"),
            limit,
            vec![
                ("node_modules/pkg/package.json", r#"{"name":"pkg","main":"build/addon.node","types":"src/index.ts"}"#),
                ("node_modules/pkg/src/index.ts", &native_types),
                ("node_modules/pkg/build/addon.node", "binary"),
            ],
        ),
        (
            "computed require inside a walked body",
            module_of("esnext"),
            limit,
            vec![
                ("node_modules/pkg/package.json", r#"{"name":"pkg","main":"index.js","types":"index.d.ts"}"#),
                declared,
                ("node_modules/pkg/index.js", &dynamic),
            ],
        ),
    ];

    let expectations = [
        ("O((xs * xs^2))", false, true),
        ("O((xs * xs^2))", false, true),
        ("O(xs)", false, false),
        ("O((xs * xs^2))", false, true),
        ("O(1)", true, false),
        ("O((xs * xs^2))", true, true),
    ];

    for ((label, tsconfig, config, package), (cost, partial, over_limit)) in
        cases.into_iter().zip(expectations)
    {
        let mut files = vec![
            ("tsconfig.json", tsconfig.as_str()),
            ("index.ts", consumer),
            ("olint.config.json", config),
        ];

        files.extend(package);

        let directory = support::project_of(&files);
        let (row, stderr) = reported_row_of(directory.path(), "selected");

        assert!(row.starts_with(&format!("{cost} ")), "{label}: {row}");
        assert_eq!(row.contains("[partial]"), partial, "{label}: {row}");
        assert_eq!(
            stderr.contains("unknown call target"),
            partial,
            "{label}: {stderr}"
        );

        lint_diagnostics_of(directory.path(), over_limit);

        let (_, report, _) = captured(
            Command::new(env!("CARGO_BIN_EXE_olint"))
                .args(["--types", "syntactic", "--report", "--min", "0"])
                .current_dir(directory.path()),
        );
        let (_, lint, _) = captured(
            Command::new(env!("CARGO_BIN_EXE_olint"))
                .args(["--types", "syntactic"])
                .current_dir(directory.path()),
        );

        assert!(
            report
                .lines()
                .filter(|line| line.starts_with("O("))
                .all(|line| !line.contains("node_modules/")),
            "{label}: {report}"
        );
        assert!(lint.contains("1 public functions"), "{label}: {lint}");
        assert!(!directory.path().join("executed.txt").exists(), "{label}");
        assert!(
            !directory
                .path()
                .join("node_modules/pkg/executed.txt")
                .exists(),
            "{label}"
        );
    }
}

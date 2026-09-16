use std::path::Path;
use std::process::Command;

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

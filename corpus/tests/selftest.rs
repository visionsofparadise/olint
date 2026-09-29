//! Runs selftest checks 3 (a snapshot diffs empty against itself) and 4 (planted weakening and tightening report as a
//! lowering and a raise) on the `model` fixture alone, so they run without the package corpus.

use std::path::Path;
use std::process::Command;

#[test]
fn model_fixture_passes_the_self_diff_and_planted_changes() {
    let work = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache/selftest-test");
    let output = Command::new(env!("CARGO_BIN_EXE_olint-corpus"))
        .args(["selftest", "--member", "fixtures/model", "--check", "3,4"])
        .arg("--work")
        .arg(&work)
        .output()
        .expect("olint-corpus starts");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "selftest failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("check 3 passed"), "{stdout}");
    assert!(stdout.contains("check 4 passed"), "{stdout}");
}

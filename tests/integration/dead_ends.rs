//! Pins the evidence programs of recorded dead ends.
//!
//! Each dead end is one olint commit `test(olint): record dead end <slug>` carrying a `Dead-end: <slug>` trailer. Its body states the attempt, the acceptance failure or reason for abandonment, the evidence, and what a successor must change. An attempt with no evidence program is an empty commit (`--allow-empty`).
//!
//! The evidence program lands under `tests/fixtures/dead-ends/<slug>/` (§5.10) and this test pins it. A fixture holds `src/`, `tsconfig.json` and `expected.json`, a list of node row subsets: each is a JSON object with a `key` (`path`, `start`, `end`, `kind`) and any subset of the other row fields, checked against the row with that key. The ranked fields (`state`, `bound`, `floor`, `contributions`, `unknowns`) must rank at or above the expectation in the knownness order (`corpus/src/ranking.rs`, the corpus diff's order), with each ranked field left out taken from the row, so a later raise keeps the fixture passing; every other field must be equal.
//!
//! An attempt resembling a dead end carries `Resembles: <sha>; <what differs>` (§5.11).
//!
//! Agents find dead ends with `git log --grep='^Dead-end:' --format='%h %s'` and `ls tests/fixtures/dead-ends`.

use std::path::{Path, PathBuf};

use olint::analysis::{Analysis, Options};
use olint::project::Project;
use olint::snapshot::{snapshot_rows, NodeRow};
use oxc_allocator::Allocator;
use serde_json::Value;

use crate::support;

#[path = "../../corpus/src/ranking.rs"]
mod ranking;

use ranking::Ranking;

use support::SYNTACTIC;

const RECORDING: Options = Options {
    record_nodes: true,
    ..SYNTACTIC
};

fn dead_ends_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/dead-ends")
}

/// Row fields compared by the knownness order rather than by equality.
const RANKED: [&str; 5] = ["state", "bound", "floor", "contributions", "unknowns"];

fn mismatch(rows: &[Value], expected: &Value) -> Result<(), String> {
    let expected = expected
        .as_object()
        .ok_or_else(|| format!("expectation {expected} is not an object"))?;
    let key = expected
        .get("key")
        .ok_or_else(|| format!("expectation {expected:?} has no key"))?;
    let row = rows
        .iter()
        .find(|row| row.get("key") == Some(key))
        .ok_or_else(|| format!("no row with key {key}"))?;
    let mut wanted = row.clone();

    for (field, value) in expected {
        if RANKED.contains(&field.as_str()) {
            wanted[field] = value.clone();
        } else if row.get(field) != Some(value) {
            return Err(format!(
                "row {key} field {field}: expected {value}, found {}",
                row.get(field).unwrap_or(&Value::Null)
            ));
        }
    }

    let parse = |value: &Value| {
        serde_json::from_value::<NodeRow>(value.clone())
            .map_err(|error| format!("row {key}: {value} is not a node row: {error}"))
    };

    match Ranking::new().ranks_at_or_above(&parse(row)?, &parse(&wanted)?) {
        true => Ok(()),
        false => Err(format!(
            "row {key} ranks below its expectation: expected at or above {wanted}, found {row}"
        )),
    }
}

fn fixture_failures(fixture: &Path) -> Vec<String> {
    let name = fixture.file_name().unwrap().to_string_lossy().into_owned();
    let expected: Vec<Value> = serde_json::from_str(
        &std::fs::read_to_string(fixture.join("expected.json"))
            .unwrap_or_else(|error| panic!("{name}: expected.json reads: {error}")),
    )
    .unwrap_or_else(|error| panic!("{name}: expected.json parses as a list: {error}"));
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &fixture.join("tsconfig.json"))
        .unwrap_or_else(|_| panic!("{name}: fixture loads"));
    let mut analysis = Analysis::new(&project, RECORDING);
    let rows: Vec<Value> = snapshot_rows(&mut analysis)
        .iter()
        .map(|row| serde_json::to_value(row).expect("row serializes"))
        .collect();

    expected
        .iter()
        .filter_map(|expected| mismatch(&rows, expected).err())
        .map(|failure| format!("{name}: {failure}"))
        .collect()
}

#[test]
fn dead_end_fixtures_hold() {
    let mut failures = Vec::new();

    for entry in std::fs::read_dir(dead_ends_root()).expect("dead-ends directory reads") {
        let path = entry.expect("entry reads").path();

        if path.is_dir() {
            failures.extend(fixture_failures(&path));
        }
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn subset_matcher_ranks_named_fields() {
    let row = serde_json::json!({
        "key": {"path": "a.ts", "start": 0, "end": 5, "kind": "Function"},
        "state": "Known",
        "bound": "O(n)",
        "floor": null,
        "contributions": [],
        "asserted": false,
        "unknowns": [],
        "rules": [],
        "certificate": null,
    });
    let key = row["key"].clone();
    let rows = [row];

    assert!(mismatch(&rows, &serde_json::json!({"key": key})).is_ok());
    assert!(mismatch(&rows, &serde_json::json!({"key": key, "bound": "O(n)"})).is_ok());
    assert!(mismatch(
        &rows,
        &serde_json::json!({"key": key, "bound": "O((n * n))"})
    )
    .is_ok());
    assert!(mismatch(
        &rows,
        &serde_json::json!({"key": key, "state": "Unknown", "bound": null})
    )
    .is_ok());
    assert!(
        mismatch(&rows, &serde_json::json!({"key": key, "bound": "O(1)"}))
            .unwrap_err()
            .contains("ranks below")
    );
    assert!(
        mismatch(&rows, &serde_json::json!({"key": key, "asserted": true}))
            .unwrap_err()
            .contains("field asserted")
    );
    assert!(
        mismatch(&rows, &serde_json::json!({"key": {"path": "b.ts"}}))
            .unwrap_err()
            .contains("no row")
    );
}

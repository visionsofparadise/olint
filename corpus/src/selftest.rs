//! `selftest` runs the harness's integrity checks:
//!
//! 1. Re-derives `corpus/.cache/packages.json` from the cached registry answers, or from fresh registry answers under
//!    `--refresh true`, and requires it byte-identical, then verifies each selected package's tarball against its
//!    recorded integrity and its extracted files against the tarball.
//! 2. Snapshots the working tree twice and requires byte identity.
//! 3. Diffs a snapshot against itself and requires an empty result.
//! 4. Plants a weakening (every loop factor forced unresolved in `bounds.rs`), a widening (every proven loop factor
//!    forced to the envelope `N`, which a Partial loop shows only in its floor) and a tightening
//!    (`Array.prototype.includes` forced constant) as in-cache edits of a tree copy, and requires the first two to
//!    report only lowerings, the widening including a Partial-to-Partial lowering, and the third only raises.
//! 5. Requires identical rows under the `ignore`, `warn` and `error` unknown policies.
//!
//! Every snapshot runs on a copy of the working tree under the work directory, never on the real `src/`, and
//! `--member` prefixes narrow the members each snapshot covers.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde::Deserialize;

use crate::diff::compare;
use crate::snapshot::{snapshot, SnapshotArgs};

pub const CHECKS: [u8; 5] = [1, 2, 3, 4, 5];

const POLICIES: [&str; 3] = ["ignore", "warn", "error"];

pub struct SelftestArgs {
    pub only: Vec<String>,
    pub checks: BTreeSet<u8>,
    pub jobs: usize,
    pub timeout: Duration,
    pub work: Option<PathBuf>,
    /// Check 1 re-derives from fresh registry answers (`select.mjs --refresh`) instead of the cached ones.
    pub refresh: bool,
}

/// A planted edit: `find` must occur exactly once in `file`, and becomes `replace`.
struct Plant {
    name: &'static str,
    file: &'static str,
    find: &'static str,
    replace: &'static str,
}

const WEAKEN: Plant = Plant {
    name: "weaken",
    file: "src/bounds.rs",
    find: "        let verdict = self.inner_bound_of(file, loop_kind);\n",
    replace: "        let _ = self.inner_bound_of(file, loop_kind);\n        let verdict = unresolved_bound_of();\n",
};

const WIDEN: Plant = Plant {
    name: "widen",
    file: "src/bounds.rs",
    find: "        let verdict = self.inner_bound_of(file, loop_kind);\n",
    replace: "        let verdict = match self.inner_bound_of(file, loop_kind) {\n            Verdict::Proven { rule, condition, .. } => Verdict::Proven {\n                factor: crate::cost::Cost::dimension(u64::MAX, crate::cost::Domain::Size),\n                rule,\n                condition,\n            },\n            verdict => verdict,\n        };\n",
};

const TIGHTEN: Plant = Plant {
    name: "tighten",
    file: "src/walker.rs",
    find: "        let bounded = self.is_constant_sized(file, receiver) || shared;\n",
    replace: "        let bounded = self.is_constant_sized(file, receiver)\n            || shared\n            || (kind == Kind::Array && method == \"includes\");\n",
};

struct Context {
    repo: PathBuf,
    cache: PathBuf,
    work: PathBuf,
    /// Prefix of every tree directory, so concurrent work directories never share a build key.
    label: String,
    args: SelftestArgs,
}

impl Context {
    fn snapshot(&self, tree: &Path, name: &str, unknown: Option<&str>) -> Result<PathBuf, String> {
        let out = self.work.join("snap").join(name);

        if out.exists() {
            std::fs::remove_dir_all(&out).map_err(io_error("remove", &out))?;
        }

        snapshot(SnapshotArgs {
            src: tree.to_string_lossy().into_owned(),
            out: Some(out.clone()),
            jobs: self.args.jobs,
            timeout: self.args.timeout,
            only: self.args.only.clone(),
            unknown: unknown.map(str::to_string),
        })?;

        Ok(out)
    }

    fn tree(&self, name: &str) -> PathBuf {
        self.work
            .join("trees")
            .join(format!("{}-{name}", self.label))
    }
}

fn io_error<'p>(
    action: &'static str,
    path: &'p Path,
) -> impl FnOnce(std::io::Error) -> String + 'p {
    move |error| format!("cannot {action} {}: {error}", path.display())
}

fn git_lines(repo: &Path, arguments: &[&str]) -> Result<Vec<String>, String> {
    let output = Command::new("git")
        .args(arguments)
        .current_dir(repo)
        .output()
        .map_err(|error| format!("git did not start: {error}"))?;

    if !output.status.success() {
        return Err(format!(
            "git {} failed: {}",
            arguments.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }

    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect())
}

/// Removes `to` when it exists.
fn cleared(to: &Path) -> Result<(), String> {
    if to.exists() {
        std::fs::remove_dir_all(to).map_err(io_error("remove", to))?;
    }

    Ok(())
}

/// Copies the working tree's tracked files, plus untracked unignored files under `src/`, `tests/` and `corpus/`,
/// into `to`.
fn copy_working_tree(repo: &Path, to: &Path) -> Result<(), String> {
    cleared(to)?;

    let mut files: BTreeSet<String> = git_lines(repo, &["ls-files", "--cached"])?
        .into_iter()
        .collect();

    files.extend(git_lines(
        repo,
        &[
            "ls-files",
            "--others",
            "--exclude-standard",
            "--",
            "src",
            "tests",
            "corpus",
        ],
    )?);

    for file in files {
        let from = repo.join(&file);

        // A tracked file deleted in the working tree is left out, as the working tree has it.
        if !from.is_file() {
            continue;
        }

        let target = to.join(&file);

        std::fs::create_dir_all(target.parent().expect("a file has a parent"))
            .map_err(io_error("create", &target))?;
        std::fs::copy(&from, &target).map_err(io_error("copy", &from))?;
    }

    Ok(())
}

/// Copies the materialized head tree to `to`, so each plant differs from the head by its edit alone.
fn copy_tree(from: &Path, to: &Path) -> Result<(), String> {
    cleared(to)?;

    let mut pending = vec![(from.to_path_buf(), to.to_path_buf())];

    while let Some((source, target)) = pending.pop() {
        std::fs::create_dir_all(&target).map_err(io_error("create", &target))?;

        for entry in std::fs::read_dir(&source).map_err(io_error("list", &source))? {
            let entry = entry.map_err(io_error("list", &source))?;
            let path = entry.path();

            match path.is_dir() {
                true => pending.push((path, target.join(entry.file_name()))),
                false => {
                    std::fs::copy(&path, target.join(entry.file_name()))
                        .map_err(io_error("copy", &path))?;
                }
            }
        }
    }

    Ok(())
}

fn plant(tree: &Path, plant: &Plant) -> Result<(), String> {
    let path = tree.join(plant.file);
    let text = std::fs::read_to_string(&path).map_err(io_error("read", &path))?;
    let found = text.matches(plant.find).count();

    if found != 1 {
        return Err(format!(
            "the {} plant expects its anchor once in {}, found {found}: {:?}",
            plant.name, plant.file, plant.find
        ));
    }

    std::fs::write(&path, text.replacen(plant.find, plant.replace, 1))
        .map_err(io_error("write", &path))
}

/// Lists every file under `directory` except its `logs/`, keyed by relative path.
fn files_of(directory: &Path) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let mut found = BTreeMap::new();
    let mut pending = vec![directory.to_path_buf()];

    while let Some(current) = pending.pop() {
        for entry in std::fs::read_dir(&current).map_err(io_error("list", &current))? {
            let entry = entry.map_err(io_error("list", &current))?;
            let path = entry.path();
            let relative = path
                .strip_prefix(directory)
                .expect("entries sit under the directory")
                .to_string_lossy()
                .replace('\\', "/");

            if relative == "logs" {
                continue;
            }

            match path.is_dir() {
                true => pending.push(path),
                false => {
                    found.insert(
                        relative,
                        std::fs::read(&path).map_err(io_error("read", &path))?,
                    );
                }
            }
        }
    }

    Ok(found)
}

fn differences(
    left: &BTreeMap<String, Vec<u8>>,
    right: &BTreeMap<String, Vec<u8>>,
    skip: impl Fn(&str) -> bool,
) -> Vec<String> {
    let names: BTreeSet<&String> = left.keys().chain(right.keys()).collect();

    names
        .into_iter()
        .filter(|name| !skip(name))
        .filter(|name| left.get(*name) != right.get(*name))
        .map(
            |name| match (left.contains_key(name), right.contains_key(name)) {
                (true, true) => format!("{name} differs"),
                (true, false) => format!("{name} is missing from the second"),
                _ => format!("{name} is missing from the first"),
            },
        )
        .collect()
}

fn summary(problems: &[String]) -> String {
    let shown: Vec<&str> = problems.iter().take(10).map(String::as_str).collect();
    let rest = match problems.len() > shown.len() {
        true => format!("; and {} more", problems.len() - shown.len()),
        false => String::new(),
    };

    format!("{}{rest}", shown.join("; "))
}

#[derive(Deserialize)]
struct Package {
    name: String,
    version: String,
    integrity: String,
    tarball: String,
}

/// Verifies each package's tarball against its integrity through pacote, then compares every regular file the
/// tarball holds with the extracted copy, skipping the generated root `tsconfig.json` and `olint.config.json`.
const VERIFY: &str = r#"
import fs from "node:fs";
import path from "node:path";
import { gunzipSync } from "node:zlib";
import pacote from "pacote";

const GENERATED = new Set(["tsconfig.json", "olint.config.json"]);
const packages = JSON.parse(fs.readFileSync(0, "utf8"));
const problems = [];
const text = (block, start, end) => {
	const slice = block.subarray(start, end);
	const zero = slice.indexOf(0);
	return slice.subarray(0, zero === -1 ? slice.length : zero).toString("utf8");
};
const entries = (gzipped) => {
	const archive = gunzipSync(gzipped);
	const found = [];
	let pending;
	for (let offset = 0; offset + 512 <= archive.length; ) {
		const header = archive.subarray(offset, offset + 512);
		if (header.every((byte) => byte === 0)) break;
		const size = parseInt(text(header, 124, 136).trim() || "0", 8);
		const type = String.fromCharCode(header[156] || 48);
		const body = archive.subarray(offset + 512, offset + 512 + size);
		const prefix = text(header, 257, 262) === "ustar" ? text(header, 345, 500) : "";
		const name = pending ?? (prefix ? `${prefix}/${text(header, 0, 100)}` : text(header, 0, 100));
		pending = undefined;
		if (type === "L") pending = text(body, 0, body.length);
		else if (type === "x") pending = /(?:^|\n)\d+ path=([^\n]*)\n/.exec(body.toString("utf8"))?.[1];
		else if (type === "0" || type === "7") found.push([name, body]);
		offset += 512 + Math.ceil(size / 512) * 512;
	}
	return found;
};
let next = 0;
const worker = async () => {
	while (next < packages.length) {
		const { spec, integrity, tarball, dir } = packages[next++];
		try {
			const gzipped = await pacote.tarball(spec, { integrity, resolved: tarball });
			const seen = new Set();
			for (const [name, body] of entries(gzipped)) {
				const relative = name.split("/").slice(1).join("/");
				if (!relative || GENERATED.has(relative) || seen.has(relative)) continue;
				seen.add(relative);
				const file = path.join(dir, relative);
				if (!fs.existsSync(file)) problems.push(`${spec}: ${relative} is not extracted`);
				else if (!fs.readFileSync(file).equals(body)) problems.push(`${spec}: ${relative} differs from its tarball`);
			}
		} catch (error) {
			problems.push(`${spec}: ${error.code ?? ""} ${error.message}`);
		}
	}
};
await Promise.all(Array.from({ length: 16 }, worker));
process.stdout.write(JSON.stringify(problems));
"#;

fn check_packages(context: &Context) -> Result<String, String> {
    let packages_path = context.cache.join("packages.json");
    let bands_path = context.cache.join("bands.json");
    let original = std::fs::read(&packages_path).map_err(io_error("read", &packages_path))?;
    let bands = std::fs::read(&bands_path).ok();
    let mut select = Command::new("node");

    select.arg("corpus/select.mjs");

    if context.args.refresh {
        select.arg("--refresh");
    }

    let status = select
        .current_dir(&context.repo)
        .stdin(Stdio::null())
        .status()
        .map_err(|error| format!("node did not start: {error}"))?;
    let derived = std::fs::read(&packages_path).unwrap_or_default();

    if !status.success() || derived != original {
        std::fs::write(&packages_path, &original).map_err(io_error("restore", &packages_path))?;

        if let Some(bands) = bands {
            std::fs::write(&bands_path, bands).map_err(io_error("restore", &bands_path))?;
        }

        return Err(match status.success() {
            true => "the re-derived packages.json differs from the cached one, which is restored"
                .to_string(),
            false => format!("corpus/select.mjs exited {status}"),
        });
    }

    let packages: Vec<Package> = serde_json::from_slice(&original)
        .map_err(|error| format!("{} is malformed: {error}", packages_path.display()))?;
    let fetched_path = context.cache.join("fetched.json");
    let fetched: BTreeMap<String, String> = std::fs::read(&fetched_path)
        .ok()
        .and_then(|bytes| serde_json::from_slice(&bytes).ok())
        .unwrap_or_default();
    let selected: Vec<(String, &Package)> = packages
        .iter()
        .map(|package| (format!("{}@{}", package.name, package.version), package))
        .filter(|(spec, _)| {
            let id = format!("packages/{spec}");

            context.args.only.is_empty()
                || context
                    .args
                    .only
                    .iter()
                    .any(|prefix| id.starts_with(prefix))
        })
        .collect();
    let mut problems: Vec<String> = selected
        .iter()
        .filter(|(spec, package)| fetched.get(spec) != Some(&package.integrity))
        .map(|(spec, _)| format!("{spec}: fetched.json records another integrity or none"))
        .collect();

    if !selected.is_empty() {
        let request: Vec<serde_json::Value> = selected
            .iter()
            .map(|(spec, package)| {
                serde_json::json!({
                    "spec": spec,
                    "integrity": package.integrity,
                    "tarball": package.tarball,
                    "dir": context.cache.join("packages").join(spec),
                })
            })
            .collect();
        let mut child = Command::new("node")
            .args(["--input-type=module", "--eval", VERIFY])
            .current_dir(&context.repo)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|error| format!("node did not start: {error}"))?;

        child
            .stdin
            .take()
            .expect("stdin is piped")
            .write_all(&serde_json::to_vec(&request).expect("request serializes"))
            .map_err(|error| format!("cannot write to node: {error}"))?;

        let output = child
            .wait_with_output()
            .map_err(|error| format!("node failed: {error}"))?;

        if !output.status.success() {
            return Err(format!("the integrity verifier exited {}", output.status));
        }

        let reported: Vec<String> = serde_json::from_slice(&output.stdout)
            .map_err(|error| format!("the integrity verifier answered malformed JSON: {error}"))?;

        problems.extend(reported);
    }

    match problems.is_empty() {
        true => Ok(format!(
            "packages.json re-derives byte-identical ({} packages); {} selected packages match their integrity",
            packages.len(),
            selected.len()
        )),
        false => Err(format!(
            "{} integrity problems: {}",
            problems.len(),
            summary(&problems)
        )),
    }
}

fn check_identity(first: &Path, second: &Path) -> Result<String, String> {
    let left = files_of(first)?;
    let right = files_of(second)?;
    let problems = differences(&left, &right, |_| false);

    match problems.is_empty() {
        true => Ok(format!(
            "{} files byte-identical across two snapshots",
            left.len()
        )),
        false => Err(summary(&problems)),
    }
}

fn check_self_diff(snapshot: &Path) -> Result<String, String> {
    let report = compare(snapshot, snapshot, &[])?;

    match report.is_empty() && report.passed() {
        true => Ok(format!(
            "{} runs, {} unchanged nodes, empty diff",
            report.members.len(),
            report.totals().unchanged
        )),
        false => Err(format!("self diff is not empty:\n{}", report.render())),
    }
}

fn check_plants(context: &Context, head_tree: &Path, base: &Path) -> Result<String, String> {
    let mut outcomes = Vec::new();

    for (planted, lowering) in [(&WEAKEN, true), (&WIDEN, true), (&TIGHTEN, false)] {
        let tree = context.tree(planted.name);

        copy_tree(head_tree, &tree)?;
        plant(&tree, planted)?;

        let snapshot = context.snapshot(&tree, planted.name, None)?;
        let report = compare(base, &snapshot, &[])?;
        let totals = report.totals();
        let expected = match lowering {
            true => totals.lowers > 0 && totals.raises == 0,
            false => totals.raises > 0 && totals.lowers == 0,
        };

        if !expected {
            return Err(format!(
                "the {} plant should report only {}, got {} raises and {} lowers:\n{}",
                planted.name,
                if lowering { "lowerings" } else { "raises" },
                totals.raises,
                totals.lowers,
                report.render()
            ));
        }

        if lowering && report.passed() {
            return Err(format!(
                "the {} plant's undeclared lowerings did not reject the diff",
                planted.name
            ));
        }

        let floors = report
            .unmatched
            .iter()
            .filter(|lowering| {
                lowering.from.starts_with("Partial") && lowering.to.starts_with("Partial")
            })
            .count();

        if planted.name == WIDEN.name && floors == 0 {
            return Err(format!(
                "the widen plant should lower a Partial loop through its floor, got no Partial-to-Partial lowering:\n{}",
                report.render()
            ));
        }

        outcomes.push(format!(
            "{}: {} raises, {} lowers",
            planted.name, totals.raises, totals.lowers
        ));
    }

    Ok(outcomes.join("; "))
}

fn check_policies(context: &Context, tree: &Path) -> Result<String, String> {
    let mut snapshots = Vec::new();

    for policy in POLICIES {
        let out = context.snapshot(tree, &format!("unknown-{policy}"), Some(policy))?;

        snapshots.push((policy, files_of(&out)?));
    }

    let (first, rows) = &snapshots[0];
    let mut problems = Vec::new();

    for (policy, other) in &snapshots[1..] {
        problems.extend(
            differences(rows, other, |name| !name.ends_with(".jsonl.gz"))
                .into_iter()
                .map(|problem| format!("{first} vs {policy}: {problem}")),
        );
    }

    let errors: Vec<String> = snapshots
        .iter()
        .map(|(_, files)| member_errors(files))
        .collect::<Result<_, _>>()?;

    if errors.windows(2).any(|pair| pair[0] != pair[1]) {
        problems.push("member errors differ across policies".to_string());
    }

    match problems.is_empty() {
        true => Ok(format!(
            "{} row files and their certificates identical under ignore, warn and error",
            rows.keys()
                .filter(|name| name.ends_with(".jsonl.gz") && !name.contains("certificates/"))
                .count()
        )),
        false => Err(summary(&problems)),
    }
}

fn member_errors(files: &BTreeMap<String, Vec<u8>>) -> Result<String, String> {
    let counts: serde_json::Value = files
        .get("counts.json")
        .map(|bytes| serde_json::from_slice(bytes))
        .transpose()
        .map_err(|error| format!("counts.json is malformed: {error}"))?
        .unwrap_or_default();
    let mut errors = Vec::new();

    if let Some(passes) = counts["passes"].as_object() {
        for (pass, members) in passes {
            for (member, status) in members.as_object().into_iter().flatten() {
                if let Some(error) = status["error"].as_str() {
                    errors.push(format!("{pass} {member}: {error}"));
                }
            }
        }
    }

    Ok(errors.join("\n"))
}

fn timed(
    check: u8,
    run: impl FnOnce() -> Result<String, String>,
) -> (u8, Result<String, String>, Duration) {
    let begun = Instant::now();
    let result = run();

    eprintln!(
        "selftest check {check}: {} in {:.1}s",
        match &result {
            Ok(_) => "passed",
            Err(_) => "failed",
        },
        begun.elapsed().as_secs_f64()
    );

    (check, result, begun.elapsed())
}

pub fn selftest(args: SelftestArgs) -> Result<(), String> {
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo = corpus
        .parent()
        .expect("the corpus package sits in the olint tree")
        .to_path_buf();
    let cache = corpus.join(".cache");
    let work = match &args.work {
        Some(work) => std::path::absolute(work).map_err(io_error("resolve", work))?,
        None => cache.join("selftest"),
    };
    let label = work
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| "selftest".to_string());

    std::fs::create_dir_all(&work).map_err(io_error("create", &work))?;

    let context = Context {
        repo,
        cache,
        work,
        label,
        args,
    };
    let checks = &context.args.checks;
    let started = Instant::now();
    let mut results: Vec<(u8, Result<String, String>, Duration)> = Vec::new();

    if checks.contains(&1) {
        results.push(timed(1, || check_packages(&context)));
    }

    if checks.iter().any(|check| *check >= 2) {
        let head_tree = context.tree("head");
        let begun = Instant::now();
        let base = copy_working_tree(&context.repo, &head_tree)
            .and_then(|()| context.snapshot(&head_tree, "head", None));

        eprintln!(
            "selftest head snapshot in {:.1}s",
            begun.elapsed().as_secs_f64()
        );

        match base {
            Err(error) => {
                for check in checks.iter().filter(|check| **check >= 2) {
                    results.push((
                        *check,
                        Err(format!("the head snapshot failed: {error}")),
                        Duration::ZERO,
                    ));
                }
            }
            Ok(base) => {
                if checks.contains(&2) {
                    results.push(timed(2, || {
                        // Peak bytes include the output path the member holds, so the rerun's directory name
                        // has the length of "head".
                        let again = context.snapshot(&head_tree, "twin", None)?;

                        check_identity(&base, &again)
                    }));
                }

                if checks.contains(&3) {
                    results.push(timed(3, || check_self_diff(&base)));
                }

                if checks.contains(&4) {
                    results.push(timed(4, || check_plants(&context, &head_tree, &base)));
                }

                if checks.contains(&5) {
                    results.push(timed(5, || check_policies(&context, &head_tree)));
                }
            }
        }
    }

    let mut failed = 0;

    for (check, result, elapsed) in &results {
        match result {
            Ok(message) => println!(
                "check {check} passed in {:.1}s: {message}",
                elapsed.as_secs_f64()
            ),
            Err(message) => {
                failed += 1;

                println!(
                    "check {check} FAILED in {:.1}s: {message}",
                    elapsed.as_secs_f64()
                );
            }
        }
    }

    println!(
        "selftest: {} of {} checks passed in {:.1}s",
        results.len() - failed,
        results.len(),
        started.elapsed().as_secs_f64()
    );

    match failed {
        0 => Ok(()),
        _ => Err(format!("{failed} selftest checks failed")),
    }
}

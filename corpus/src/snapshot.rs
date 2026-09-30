//! `snapshot` materializes an olint tree, builds this harness inside it, and runs one `snapshot-member`
//! subprocess per corpus member and pass, writing gzip JSON Lines of `NodeRow` plus `counts.json`.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use flate2::write::GzEncoder;
use flate2::Compression;
use olint::analysis::work::EVENTS;
use olint::analysis::{Analysis, Options, TypeMode};
use olint::config::{read_config, unknown_policy_of};
use olint::project::Project;
use olint::public::public_functions;
use olint::regex::{RegexError, RegexLimits};
use olint::snapshot::{snapshot_rows, SCHEMA};
use olint::summaries::SchedulerLimits;
use olint::tsc::{ask_counted, TscError};
use oxc_allocator::Allocator;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

use crate::alloc;
use crate::members::{members, Member};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pass {
    Syntactic,
    Tsc,
}

pub const PASSES: [Pass; 2] = [Pass::Syntactic, Pass::Tsc];

impl Pass {
    pub fn name(self) -> &'static str {
        match self {
            Pass::Syntactic => "syntactic",
            Pass::Tsc => "tsc",
        }
    }

    pub fn of(name: &str) -> Option<Pass> {
        PASSES.into_iter().find(|pass| pass.name() == name)
    }

    fn mode(self) -> TypeMode {
        match self {
            Pass::Syntactic => TypeMode::Syntactic,
            Pass::Tsc => TypeMode::Tsc,
        }
    }

    /// The pass's directory inside a snapshot: syntactic rows at the root, tsc rows under `tsc/`.
    pub fn directory(self, out: &Path) -> PathBuf {
        match self {
            Pass::Syntactic => out.to_path_buf(),
            Pass::Tsc => out.join("tsc"),
        }
    }
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub struct TscTotals {
    pub typescript: String,
    pub rounds: usize,
    pub sites: usize,
    pub programs: u64,
    pub checkers: u64,
    pub indexed_files: u64,
    pub indexed_nodes: u64,
    pub lookups: u64,
    pub visited_nodes: u64,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq)]
pub struct MemberCounts {
    /// The hard failure that left the member without rows: the project did not load, the analysis or its process
    /// failed, or the member timed out.
    pub error: Option<String>,
    /// Errors the analysis reported while still writing rows; `diff` compares those rows and lists the errors.
    #[serde(default)]
    pub errors: Vec<String>,
    pub rows: usize,
    /// Consumed work per scheduler `Event`, in `EVENTS` order.
    pub events: Map<String, Value>,
    pub exhausted: Vec<String>,
    /// Events whose consumed work reached olint's default scheduler limit, which caps them whether or not the
    /// scheduler flagged the event exhausted.
    #[serde(default)]
    pub at_limit: Vec<String>,
    pub tasks: usize,
    pub maximum_body_passes: u64,
    /// |G|: the syntax nodes of every file the project loaded, counted as `oxc_semantic` AST nodes, the node universe
    /// `NodeKey` spans and kinds are drawn from.
    pub nodes: Option<u64>,
    /// Peak live bytes the counting allocator saw from project load through `snapshot_rows`.
    pub peak_bytes: Option<u64>,
    /// Memory of the tsc and regex sidecar processes, which the counting allocator cannot see. Always `null` until
    /// Phase 6 action 6.3 attributes delegated checker work and memory per query; `peak_bytes` covers olint's own
    /// process only.
    pub sidecar_bytes: Option<u64>,
    pub tsc: Option<TscTotals>,
    pub warnings: Vec<String>,
}

#[derive(Serialize)]
struct Counts<'c> {
    schema: u32,
    source: &'c str,
    passes: BTreeMap<&'static str, BTreeMap<String, MemberCounts>>,
}

pub struct SnapshotArgs {
    pub src: String,
    pub out: Option<PathBuf>,
    pub jobs: usize,
    pub timeout: Duration,
    pub only: Vec<String>,
    /// Applies the member's `olint.config.json` with this unknown policy before snapshotting, for selftest check 5.
    pub unknown: Option<String>,
}

pub struct MemberArgs {
    pub root: PathBuf,
    pub pass: Pass,
    pub rows: PathBuf,
    pub counts: PathBuf,
    pub tree: PathBuf,
    pub unknown: Option<String>,
}

pub struct Source {
    pub tree: PathBuf,
    pub key: String,
    locked: bool,
}

pub fn head_corpus() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

pub fn absolute(path: &Path) -> Result<PathBuf, String> {
    std::path::absolute(path).map_err(|error| format!("cannot resolve {}: {error}", path.display()))
}

fn io_error<'p>(
    action: &'static str,
    path: &'p Path,
) -> impl FnOnce(std::io::Error) -> String + 'p {
    move |error| format!("cannot {action} {}: {error}", path.display())
}

fn status_of(command: &mut Command, label: &str) -> Result<(), String> {
    let status = command
        .status()
        .map_err(|error| format!("{label} did not start: {error}"))?;

    match status.success() {
        true => Ok(()),
        false => Err(format!("{label} exited {status}")),
    }
}

pub fn materialize(src: &str, repo: &Path, cache: &Path) -> Result<Source, String> {
    let directory = Path::new(src);

    if directory.is_dir() {
        let tree = absolute(directory)?;
        let key = format!(
            "tree-{}",
            tree.file_name().unwrap_or_default().to_string_lossy()
        );

        return Ok(Source {
            tree,
            key,
            locked: true,
        });
    }

    let output = Command::new("git")
        .args([
            "rev-parse",
            "--verify",
            "--quiet",
            &format!("{src}^{{commit}}"),
        ])
        .current_dir(repo)
        .output()
        .map_err(|error| format!("git did not start: {error}"))?;

    if !output.status.success() {
        return Err(format!("--src {src} is neither a directory nor a commit"));
    }

    let sha = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let tree = cache.join("src").join(&sha);
    let ready = cache.join("src").join(format!("{sha}.ready"));

    if !ready.is_file() {
        if tree.exists() {
            std::fs::remove_dir_all(&tree).map_err(io_error("remove", &tree))?;
        }

        std::fs::create_dir_all(&tree).map_err(io_error("create", &tree))?;
        extract_archive(repo, &sha, &tree)?;
        std::fs::write(&ready, &sha).map_err(io_error("write", &ready))?;
    }

    copy_corpus(&head_corpus(), &tree.join("corpus"))?;

    Ok(Source {
        tree,
        key: sha,
        locked: false,
    })
}

fn extract_archive(repo: &Path, sha: &str, tree: &Path) -> Result<(), String> {
    let mut archive = Command::new("git")
        .args(["archive", sha])
        .current_dir(repo)
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| format!("git archive did not start: {error}"))?;
    let stdout = archive.stdout.take().expect("stdout is piped");
    let extracted = status_of(
        Command::new("tar")
            .arg("-x")
            .current_dir(tree)
            .stdin(stdout),
        "tar",
    );
    let archived = archive
        .wait()
        .map_err(|error| format!("git archive failed: {error}"))?;

    extracted?;

    match archived.success() {
        true => Ok(()),
        false => Err(format!("git archive {sha} exited {archived}")),
    }
}

/// Copies the head's `corpus/` over the materialized tree's, leaving out the cache and build output.
fn copy_corpus(from: &Path, to: &Path) -> Result<(), String> {
    if to.exists() {
        std::fs::remove_dir_all(to).map_err(io_error("remove", to))?;
    }

    copy_directory(from, to, &[".cache", "target"])
}

fn copy_directory(from: &Path, to: &Path, skipped: &[&str]) -> Result<(), String> {
    std::fs::create_dir_all(to).map_err(io_error("create", to))?;

    for entry in std::fs::read_dir(from).map_err(io_error("list", from))? {
        let entry = entry.map_err(io_error("list", from))?;
        let name = entry.file_name();

        if skipped.iter().any(|skip| name == *skip) {
            continue;
        }

        let target = to.join(&name);

        match entry.path().is_dir() {
            true => copy_directory(&entry.path(), &target, &[])?,
            false => {
                std::fs::copy(entry.path(), &target).map_err(io_error("copy", &entry.path()))?;
            }
        }
    }

    Ok(())
}

/// Builds `olint-corpus` inside the tree against the shared target directory, then copies the binary out so a later
/// build for another tree cannot replace it mid-run.
pub fn build(source: &Source, cache: &Path) -> Result<PathBuf, String> {
    let target = cache.join("target");
    let mut command = Command::new("cargo");

    command
        .args(["build", "--release", "--manifest-path"])
        .arg(source.tree.join("corpus/Cargo.toml"))
        .arg("--target-dir")
        .arg(&target)
        .current_dir(&source.tree)
        .env_remove("RUSTUP_TOOLCHAIN");

    if source.locked {
        command.arg("--locked");
    }

    status_of(&mut command, "cargo build")?;

    let name = format!("olint-corpus{}", std::env::consts::EXE_SUFFIX);
    let directory = cache.join("bin").join(&source.key);
    let binary = directory.join(&name);

    std::fs::create_dir_all(&directory).map_err(io_error("create", &directory))?;
    std::fs::copy(target.join("release").join(&name), &binary)
        .map_err(io_error("copy", &binary))?;

    Ok(binary)
}

/// The corpus cache and the olint tree `src` names, materialized with the head's harness and built.
pub struct Built {
    pub cache: PathBuf,
    pub source: Source,
    pub binary: PathBuf,
}

pub fn built(src: &str) -> Result<Built, String> {
    let corpus = head_corpus();
    let repo = corpus
        .parent()
        .expect("the corpus package sits in the olint tree");
    let cache = corpus.join(".cache");
    let source = materialize(src, repo, &cache)?;
    let binary = build(&source, &cache)?;

    Ok(Built {
        cache,
        source,
        binary,
    })
}

/// Runs `work` on every task with its index from `jobs` threads, each taking the next unclaimed task.
pub fn in_parallel<T: Sync>(tasks: &[T], jobs: usize, work: impl Fn(usize, &T) + Sync) {
    let next = AtomicUsize::new(0);

    std::thread::scope(|scope| {
        for _ in 0..jobs.max(1) {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let Some(task) = tasks.get(index) else {
                    break;
                };

                work(index, task);
            });
        }
    });
}

pub fn snapshot(args: SnapshotArgs) -> Result<(), String> {
    let Built {
        cache,
        source,
        binary,
    } = built(&args.src)?;
    let out = match args.out {
        Some(out) => absolute(&out)?,
        None => cache.join("snap").join(&source.key),
    };
    let selected: Vec<Member> = members(&source.tree, &cache, &args.only)?;
    let tasks: Vec<(Pass, &Member)> = selected
        .iter()
        .flat_map(|member| PASSES.map(|pass| (pass, member)))
        .collect();
    let results = Mutex::new(BTreeMap::new());
    let started = Instant::now();

    eprintln!(
        "snapshot {} of {} members into {}",
        tasks.len(),
        selected.len(),
        out.display()
    );

    in_parallel(&tasks, args.jobs, |index, (pass, member)| {
        let begun = Instant::now();
        let counts = run_member(
            &binary,
            &source.tree,
            &out,
            *pass,
            member,
            args.timeout,
            args.unknown.as_deref(),
        );

        eprintln!(
            "[{}/{}] {} {}: {} rows{} in {:.1}s",
            index + 1,
            tasks.len(),
            pass.name(),
            member.id,
            counts.rows,
            counts
                .error
                .as_ref()
                .map(|error| format!(", error: {error}"))
                .unwrap_or_default(),
            begun.elapsed().as_secs_f64()
        );
        results
            .lock()
            .expect("results lock")
            .insert((*pass, member.id.clone()), counts);
    });

    let mut passes: BTreeMap<&'static str, BTreeMap<String, MemberCounts>> = BTreeMap::new();

    for ((pass, id), counts) in results.into_inner().expect("results lock") {
        passes.entry(pass.name()).or_default().insert(id, counts);
    }

    let failed = passes
        .values()
        .flat_map(BTreeMap::values)
        .filter(|counts| counts.error.is_some())
        .count();
    let counts = Counts {
        schema: SCHEMA,
        source: &source.key,
        passes,
    };
    let path = out.join("counts.json");
    let text = serde_json::to_string_pretty(&counts).expect("counts serialize");

    std::fs::write(&path, text + "\n").map_err(io_error("write", &path))?;
    eprintln!(
        "snapshot finished {} runs, {failed} failed, in {:.1}s",
        tasks.len(),
        started.elapsed().as_secs_f64()
    );

    Ok(())
}

fn failed(error: String) -> MemberCounts {
    MemberCounts {
        error: Some(error),
        ..MemberCounts::default()
    }
}

pub fn run_member(
    binary: &Path,
    tree: &Path,
    out: &Path,
    pass: Pass,
    member: &Member,
    timeout: Duration,
    unknown: Option<&str>,
) -> MemberCounts {
    let rows = pass.directory(out).join(format!("{}.jsonl.gz", member.id));
    let log = out
        .join("logs")
        .join(pass.name())
        .join(format!("{}.log", member.id));
    let counts = log.with_extension("counts.json");

    for path in [&rows, &log] {
        let parent = path.parent().expect("member files have a parent");

        if let Err(error) = std::fs::create_dir_all(parent) {
            return failed(format!("cannot create {}: {error}", parent.display()));
        }
    }

    let _ = std::fs::remove_file(&rows);
    let _ = std::fs::remove_file(&counts);

    let stderr = match File::create(&log) {
        Ok(file) => file,
        Err(error) => return failed(format!("cannot create {}: {error}", log.display())),
    };
    let mut command = Command::new(binary);

    command.arg("snapshot-member");

    if let Some(unknown) = unknown {
        command.args(["--unknown", unknown]);
    }

    let spawned = command
        .arg("--root")
        .arg(&member.root)
        .args(["--pass", pass.name()])
        .arg("--rows")
        .arg(&rows)
        .arg("--counts")
        .arg(&counts)
        .arg("--tree")
        .arg(tree)
        .current_dir(tree)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr)
        .spawn();
    let mut child = match spawned {
        Ok(child) => child,
        Err(error) => return failed(format!("member process did not start: {error}")),
    };
    let deadline = Instant::now() + timeout;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();

                return failed(format!("timed out after {}s", timeout.as_secs()));
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(50)),
            Err(error) => return failed(format!("member process wait failed: {error}")),
        }
    };

    if !status.success() {
        let text = std::fs::read_to_string(&log).unwrap_or_default();
        let tail: Vec<&str> = text.lines().rev().take(3).collect();

        return failed(format!(
            "member process exited {status}: {}",
            tail.into_iter().rev().collect::<Vec<_>>().join(" / ")
        ));
    }

    let text = match std::fs::read_to_string(&counts) {
        Ok(text) => text,
        Err(error) => return failed(format!("cannot read {}: {error}", counts.display())),
    };
    let _ = std::fs::remove_file(&counts);

    serde_json::from_str(&text)
        .unwrap_or_else(|error| failed(format!("member counts are malformed: {error}")))
}

/// Regex classification limits for snapshots: answers are deterministic since action 4.5, and the process `deadline`,
/// a hard failure, is effectively unlimited so machine load cannot fail a member; the deterministic caps (source
/// bytes, request count, reply bytes, sidecar heap) keep their defaults.
fn snapshot_regex_limits() -> RegexLimits {
    RegexLimits {
        deadline: Duration::from_secs(7 * 24 * 60 * 60),
        ..RegexLimits::default()
    }
}

fn pinned_typescript(tree: &Path) -> Result<String, String> {
    let path = tree.join("package.json");
    let text = std::fs::read_to_string(&path).map_err(io_error("read", &path))?;
    let manifest: Value = serde_json::from_str(&text)
        .map_err(|error| format!("{} is malformed: {error}", path.display()))?;

    manifest["devDependencies"]["typescript"]
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| format!("{} pins no typescript", path.display()))
}

/// Analyses one member in one pass and writes its rows and counts; an analysis failure is recorded in the counts.
pub fn snapshot_member(args: MemberArgs) -> Result<(), String> {
    let counts = match analyse_member(&args) {
        Ok(counts) => counts,
        Err(error) => failed(error),
    };
    let text = serde_json::to_string(&counts).expect("counts serialize");

    std::fs::write(&args.counts, text).map_err(io_error("write", &args.counts))
}

fn analyse_member(args: &MemberArgs) -> Result<MemberCounts, String> {
    alloc::reset_peak();

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &args.root.join("tsconfig.json"))
        .map_err(|error| format!("project does not load: {error:?}"))?;
    let nodes = project
        .files
        .iter()
        .map(|file| file.semantic.nodes().len() as u64)
        .sum();
    let options = Options {
        minimum_exponent: 2,
        types: args.pass.mode(),
        record_nodes: true,
    };
    let mut analysis = Analysis::new(&project, options);

    if let Some(policy) = &args.unknown {
        let mut config = read_config(&project, None)
            .map_err(|error| format!("config does not read: {error:?}"))?;

        config.unknown = unknown_policy_of(Some(&Value::from(policy.as_str())))
            .map_err(|error| format!("unknown policy {policy}: {error:?}"))?;

        public_functions(&mut analysis, &config)
            .map_err(|error| format!("public functions do not resolve: {error:?}"))?;
    }

    let helper = args.tree.join("src/regex_sidecar.mjs");
    let pinned = match args.pass {
        Pass::Tsc => Some(pinned_typescript(&args.tree)?),
        Pass::Syntactic => None,
    };
    let mut tsc: Option<TscTotals> = None;
    let mut warnings = Vec::new();
    let regex_limits = snapshot_regex_limits();

    loop {
        let functions = match args.pass {
            Pass::Syntactic => analysis.reportable(),
            Pass::Tsc => {
                let totals = tsc.get_or_insert_with(TscTotals::default);
                let (rounds, functions) = analysis
                    .gather_discovered_answers(
                        |analysis| Ok::<_, TscError>(analysis.reportable()),
                        |queries| {
                            let (reply, counts) =
                                ask_counted(&project.root, &project.tsconfig_path, queries)?;

                            totals.typescript.clone_from(&reply.typescript);

                            totals.programs += counts.programs;
                            totals.checkers += counts.checkers;
                            totals.indexed_files += counts.indexed_files;
                            totals.indexed_nodes += counts.indexed_nodes;
                            totals.lookups += counts.lookups;
                            totals.visited_nodes += counts.visited_nodes;

                            Ok(reply)
                        },
                    )
                    .map_err(|error| format!("tsc failed: {error:?}"))?;

                totals.rounds += rounds.rounds;
                totals.sites += rounds.sites;

                functions
            }
        };
        let classified = analysis.regex_answers.len();
        let unavailable = analysis
            .gather_selected_regex_answers(&functions, |requests| {
                olint::regex::ask(&helper, requests, &regex_limits)
            })
            .map_err(|error: RegexError| format!("regex classification failed: {error:?}"))?;

        if let Some(reason) = unavailable {
            warnings.push(format!("regex classification unavailable: {reason}"));
        }

        if analysis.regex_answers.len() == classified {
            break;
        }
    }

    if let (Some(pinned), Some(totals)) = (&pinned, &tsc) {
        if !totals.typescript.is_empty() && &totals.typescript != pinned {
            return Err(format!(
                "typescript {} answered where the tree pins {pinned}",
                totals.typescript
            ));
        }
    }

    let rows = snapshot_rows(&mut analysis);
    let peak_bytes = alloc::peak();

    write_rows(&args.rows, &rows)?;

    let stats = analysis.scheduler_stats();
    let events = EVENTS
        .iter()
        .map(|event| {
            (
                format!("{event:?}"),
                Value::from(stats.work.consumed(*event)),
            )
        })
        .collect();
    let exhausted = EVENTS
        .iter()
        .filter(|event| stats.work.exhausted(**event))
        .map(|event| format!("{event:?}"))
        .collect();

    let limits = SchedulerLimits::default().work;
    let at_limit = EVENTS
        .iter()
        .filter(|event| stats.work.consumed(**event) >= limits.limit(**event))
        .map(|event| format!("{event:?}"))
        .collect();

    warnings.extend(analysis.warnings.iter().cloned());

    Ok(MemberCounts {
        error: None,
        errors: analysis.errors.iter().cloned().collect(),
        rows: rows.len(),
        events,
        exhausted,
        at_limit,
        tasks: stats.tasks,
        maximum_body_passes: stats.maximum_body_passes,
        nodes: Some(nodes),
        peak_bytes: Some(peak_bytes),
        sidecar_bytes: None,
        tsc,
        warnings,
    })
}

fn write_rows(path: &Path, rows: &[olint::snapshot::NodeRow]) -> Result<(), String> {
    let partial = path.with_extension("partial");
    let file = File::create(&partial).map_err(io_error("create", &partial))?;
    let mut encoder = GzEncoder::new(BufWriter::new(file), Compression::default());

    for row in rows {
        serde_json::to_writer(&mut encoder, row).expect("rows serialize");
        encoder
            .write_all(b"\n")
            .map_err(io_error("write", &partial))?;
    }

    encoder
        .finish()
        .and_then(|mut writer| writer.flush())
        .map_err(io_error("write", &partial))?;

    std::fs::rename(&partial, path).map_err(io_error("rename", &partial))
}

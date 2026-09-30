//! `diff` ranks every node of a head snapshot against its base snapshot by the spec's knownness order, and accepts the
//! change only when every lowering matches a `Lowers:` trailer of the commits between them and every trailer matches
//! at least one lowering.
//!
//! Ranking, per key present in both snapshots of a member and pass, is `crate::ranking::Ranking`: Known above Partial
//! above Unknown; Known against Known by bound tightness; Partial against Partial by unknown-origin subset,
//! contribution tightness and floor tightness; Unknown against Unknown by unknown-origin subset. An `Inconclusive`
//! comparison fails "at least as tight", so the node lowers. Asserted rows never count as raises (§5.6).
//!
//! The corpus programs are pinned, so beyond rank:
//!
//! - A key present in the base and absent from the head fails; an added key is reported and allowed, since it adds
//!   coverage.
//! - The one exemption is a function whose own walk a resource limit cut short on either side: its row carries an
//!   `analysis resource limit` unknown whose origin lies in that function and in no function nested inside it (a
//!   refused root, or a WalkerNode or TraversalEdge refusal within it). Its row is ranked as usual, so its lowering
//!   still needs a trailer (§5.1), and keys of its descendants present on both sides are ranked as usual, but a
//!   descendant key present on one side only is skipped and counted per member. olint records a row for each node its
//!   walker visits, and the walker's per-kind handlers choose which children it visits, so the key set of a walk that
//!   a limit stopped cannot be rebuilt without that walk. The harness therefore owns this exemption, and applies it
//!   only to descendants of such a function.
//! - A member present in the base and absent from the head fails.
//! - A member that fails hard (no rows) in the head fails unless it also failed hard in the base, in which case it is
//!   skipped and listed under "failed on both sides". A member whose analysis reported errors but wrote rows is
//!   compared, with its errors listed.
//! - `rule=<name>` selectors match the rows' `rules`, which Phase 5 fills; until then only `rule=*` is valid, and a
//!   trailer naming a rule fails while neither snapshot carries rules.
//! - A `disproof` trailer's evidence must be an existing commit or a path in the head tree.
//! - §5.3 compares `corpus/.cache/scale/<sha>.json` of both sides; a missing scale file fails unless `--no-scale` is
//!   passed, and acceptance requires the comparison, so `--no-scale` is for iteration only.
//!
//! Git parses only the final paragraph of a commit message as trailers, so a `Lowers:` line in an earlier paragraph is
//! invisible to `%(trailers)`. `diff` scans each full message for such lines and warns.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::Command;

use flate2::read::GzDecoder;
use olint::snapshot::{NodeKey, NodeRow, NodeState, SCHEMA};
use serde::Deserialize;

use crate::ranking::Ranking;
use crate::scale::{raised_orders, read_scale};
use crate::snapshot::{Pass, PASSES};

/// Unmatched lowerings printed before the rest are summarized as a count.
const PRINTED_LOWERINGS: usize = 200;
/// The node kinds of the rows olint emits for reportable functions and constructions.
const FUNCTION_KINDS: [&str; 3] = ["Function", "ArrowFunctionExpression", "Class"];
/// `UnknownReason::ResourceExhaustion`'s text.
const RESOURCE_LIMIT: &str = "analysis resource limit";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Category {
    Disproof,
    Uncertified,
    Scaling,
}

/// One `Lowers:` trailer: `member=<glob> path=<glob> kind=<AstKind|*> rule=<rule|*>; <category>; <evidence>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trailer {
    pub text: String,
    pub member: String,
    pub path: String,
    pub kind: String,
    pub rule: String,
    pub category: Category,
    pub evidence: String,
}

impl Trailer {
    pub fn parse(text: &str) -> Result<Trailer, String> {
        let text = text.trim();
        let parts: Vec<&str> = text.splitn(3, "; ").collect();
        let [selector, category, evidence] = parts[..] else {
            return Err(format!(
                "Lowers: {text} needs three parts separated by \"; \""
            ));
        };
        let mut fields: BTreeMap<&str, &str> = BTreeMap::new();

        for token in selector.split_whitespace() {
            let Some((name, value)) = token.split_once('=') else {
                return Err(format!(
                    "Lowers: {text} has a selector token {token} without ="
                ));
            };

            if !["member", "path", "kind", "rule"].contains(&name) {
                return Err(format!("Lowers: {text} has an unknown selector {name}"));
            }

            if value.is_empty() || fields.insert(name, value).is_some() {
                return Err(format!(
                    "Lowers: {text} gives selector {name} twice or empty"
                ));
            }
        }

        let field = |name: &str| {
            fields
                .get(name)
                .map(|value| value.to_string())
                .ok_or_else(|| format!("Lowers: {text} lacks {name}="))
        };
        let category = match category.trim() {
            "disproof" => Category::Disproof,
            "uncertified" => Category::Uncertified,
            "scaling" => Category::Scaling,
            other => {
                return Err(format!(
                    "Lowers: {text} has category {other}, not disproof, uncertified or scaling"
                ))
            }
        };

        if evidence.trim().is_empty() {
            return Err(format!("Lowers: {text} names no evidence"));
        }

        Ok(Trailer {
            text: text.to_string(),
            member: field("member")?,
            path: field("path")?,
            kind: field("kind")?,
            rule: field("rule")?,
            category,
            evidence: evidence.trim().to_string(),
        })
    }

    fn matches(&self, lowering: &Lowering) -> bool {
        glob(&self.member, &lowering.member)
            && glob(&self.path, &lowering.key.path)
            && (self.kind == "*" || self.kind == lowering.key.kind)
            && (self.rule == "*" || lowering.rules.contains(&self.rule))
    }
}

/// Matches `text` against a glob where `*` is any run of characters, `/` included, and `?` is any one character.
pub fn glob(pattern: &str, text: &str) -> bool {
    let pattern: Vec<char> = pattern.chars().collect();
    let text: Vec<char> = text.chars().collect();
    let (mut p, mut t) = (0, 0);
    let mut resume: Option<(usize, usize)> = None;

    while t < text.len() {
        match pattern.get(p) {
            Some('*') => {
                resume = Some((p, t));
                p += 1;
            }
            Some(&character) if character == '?' || character == text[t] => {
                p += 1;
                t += 1;
            }
            _ => match resume {
                Some((star, from)) => {
                    p = star + 1;
                    t = from + 1;
                    resume = Some((star, from + 1));
                }
                None => return false,
            },
        }
    }

    pattern[p..].iter().all(|character| *character == '*')
}

#[derive(Clone, Debug)]
pub struct Lowering {
    pub pass: Pass,
    pub member: String,
    pub key: NodeKey,
    pub rules: BTreeSet<String>,
    pub from: String,
    pub to: String,
}

impl Lowering {
    fn describe(&self) -> String {
        format!(
            "{}{} {}:{}-{} {}: {} -> {}",
            prefix(self.pass),
            self.member,
            self.key.path,
            self.key.start,
            self.key.end,
            self.key.kind,
            self.from,
            self.to
        )
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Totals {
    pub unchanged: usize,
    pub raises: usize,
    /// Raises §5.6 excludes, being asserted in the base or the head.
    pub asserted: usize,
    pub lowers: usize,
    pub added: usize,
    pub removed: usize,
    /// Descendant keys of a resource-limited function present on one side only, left out of `added` and `removed`.
    pub skipped: usize,
}

impl Totals {
    fn changed(&self) -> bool {
        self.raises + self.asserted + self.lowers + self.added + self.removed + self.skipped > 0
    }

    fn add(&mut self, other: &Totals) {
        self.unchanged += other.unchanged;
        self.raises += other.raises;
        self.asserted += other.asserted;
        self.lowers += other.lowers;
        self.added += other.added;
        self.removed += other.removed;
        self.skipped += other.skipped;
    }
}

#[derive(Debug, Default)]
pub struct Report {
    /// Totals per `(pass, member)`.
    pub members: BTreeMap<(Pass, String), Totals>,
    pub lowerings: usize,
    pub unmatched: Vec<Lowering>,
    pub unmatched_count: usize,
    pub trailers: Vec<(Trailer, usize)>,
    /// Removed keys printed before the rest are summarized as a count.
    pub removed: Vec<String>,
    /// Members that fail the diff: absent from the head, or failing hard in the head without failing in the base.
    pub failed: Vec<String>,
    /// Members that failed hard on both sides, skipped from the comparison.
    pub both_failed: Vec<String>,
    /// Members compared whose analysis reported errors while writing rows.
    pub errors: Vec<String>,
    /// Informational notes: members added or failing only in the base, and skipped comparisons.
    pub notes: Vec<String>,
    /// Warnings that do not fail the diff by themselves, such as `Lowers:` lines outside the final trailer block.
    pub warnings: Vec<String>,
    /// Failed checks beyond rank: trailer validity, scaling order (§5.3) and ceilings (§5.2).
    pub problems: Vec<String>,
}

impl Report {
    pub fn totals(&self) -> Totals {
        let mut totals = Totals::default();

        for member in self.members.values() {
            totals.add(member);
        }

        totals
    }

    /// True when nothing changed: no raise, lowering, added or removed key, failure or problem.
    pub fn is_empty(&self) -> bool {
        !self.totals().changed()
            && self.failed.is_empty()
            && self.problems.is_empty()
            && self.trailers.is_empty()
    }

    pub fn passed(&self) -> bool {
        self.unmatched_count == 0
            && self.totals().removed == 0
            && self.trailers.iter().all(|(_, hits)| *hits > 0)
            && self.failed.is_empty()
            && self.problems.is_empty()
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        let totals = self.totals();

        let _ = writeln!(
            out,
            "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}",
            "member", "raises", "asserted", "lowers", "added", "removed", "skipped"
        );

        for ((pass, member), counts) in &self.members {
            if counts.changed() {
                let _ = writeln!(
                    out,
                    "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}",
                    format!("{}{member}", prefix(*pass)),
                    counts.raises,
                    counts.asserted,
                    counts.lowers,
                    counts.added,
                    counts.removed,
                    counts.skipped
                );
            }
        }

        let _ = writeln!(
            out,
            "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8} {:>8}",
            format!(
                "total ({} runs, {} unchanged)",
                self.members.len(),
                totals.unchanged
            ),
            totals.raises,
            totals.asserted,
            totals.lowers,
            totals.added,
            totals.removed,
            totals.skipped
        );

        for member in &self.failed {
            let _ = writeln!(out, "failed: {member}");
        }

        if !self.both_failed.is_empty() {
            let _ = writeln!(
                out,
                "FAILED ON BOTH SIDES, skipped from the comparison ({}):",
                self.both_failed.len()
            );

            for member in &self.both_failed {
                let _ = writeln!(out, "  {member}");
            }
        }

        for member in &self.errors {
            let _ = writeln!(out, "analysis errors, rows compared: {member}");
        }

        for note in &self.notes {
            let _ = writeln!(out, "note: {note}");
        }

        for warning in &self.warnings {
            let _ = writeln!(out, "warning: {warning}");
        }

        let removed = self.totals().removed;

        if removed > 0 {
            let _ = writeln!(
                out,
                "{removed} keys removed; the corpus programs are pinned, so a removed key fails:"
            );

            for key in &self.removed {
                let _ = writeln!(out, "  {key}");
            }

            if removed > self.removed.len() {
                let _ = writeln!(out, "  ... and {} more", removed - self.removed.len());
            }
        }

        for problem in &self.problems {
            let _ = writeln!(out, "problem: {problem}");
        }

        if self.unmatched_count > 0 {
            let _ = writeln!(
                out,
                "{} of {} lowerings match no Lowers: trailer:",
                self.unmatched_count, self.lowerings
            );

            for lowering in &self.unmatched {
                let _ = writeln!(out, "  {}", lowering.describe());
            }

            if self.unmatched_count > self.unmatched.len() {
                let _ = writeln!(
                    out,
                    "  ... and {} more",
                    self.unmatched_count - self.unmatched.len()
                );
            }
        }

        for (trailer, hits) in &self.trailers {
            match hits {
                0 => {
                    let _ = writeln!(out, "trailer matches no lowering: Lowers: {}", trailer.text);
                }
                _ => {
                    let _ = writeln!(
                        out,
                        "trailer matches {hits} lowerings: Lowers: {}",
                        trailer.text
                    );
                }
            }
        }

        let _ = writeln!(
            out,
            "{}",
            match self.passed() {
                true => "diff: accepted",
                false => "diff: rejected",
            }
        );

        out
    }
}

/// The function rows of one member's two snapshots, and those whose own walk a resource limit cut short on either
/// side.
struct Functions {
    spans: BTreeMap<String, Vec<(u32, u32)>>,
    limited: BTreeSet<(String, u32, u32)>,
}

impl Functions {
    fn of(old: &BTreeMap<NodeKey, NodeRow>, new: &BTreeMap<NodeKey, NodeRow>) -> Functions {
        let rows = || {
            old.values()
                .chain(new.values())
                .filter(|row| FUNCTION_KINDS.contains(&row.key.kind.as_str()))
        };
        let mut spans: BTreeMap<String, Vec<(u32, u32)>> = BTreeMap::new();

        for row in rows() {
            spans
                .entry(row.key.path.clone())
                .or_default()
                .push((row.key.start, row.key.end));
        }

        for list in spans.values_mut() {
            list.sort_unstable();
            list.dedup();
        }

        let mut functions = Functions {
            spans,
            limited: BTreeSet::new(),
        };
        let limited: Vec<(String, u32, u32)> = rows()
            .filter(|row| {
                row.unknowns.iter().any(|(origin, reason)| {
                    reason == RESOURCE_LIMIT
                        && origin.path == row.key.path
                        && functions.enclosing(&origin.path, origin.start, origin.end)
                            == Some((row.key.start, row.key.end))
                })
            })
            .map(|row| (row.key.path.clone(), row.key.start, row.key.end))
            .collect();

        functions.limited.extend(limited);

        functions
    }

    /// The smallest function span of `path` that contains `start..end`, the span itself included.
    fn enclosing(&self, path: &str, start: u32, end: u32) -> Option<(u32, u32)> {
        self.spans
            .get(path)?
            .iter()
            .filter(|(from, to)| *from <= start && end <= *to)
            .min_by_key(|(from, to)| to - from)
            .copied()
    }

    /// Whether `key` is a descendant of a function whose own walk a resource limit cut short, so its presence on one
    /// side only is skipped. A function row itself is never exempt.
    fn exempts(&self, key: &NodeKey) -> bool {
        !FUNCTION_KINDS.contains(&key.kind.as_str())
            && self
                .enclosing(&key.path, key.start, key.end)
                .is_some_and(|(start, end)| self.limited.contains(&(key.path.clone(), start, end)))
    }
}

fn prefix(pass: Pass) -> &'static str {
    match pass {
        Pass::Syntactic => "",
        Pass::Tsc => "tsc/",
    }
}

fn state_text(row: &NodeRow) -> String {
    match row.state {
        NodeState::Known => format!("Known {}", row.bound.as_deref().unwrap_or("?")),
        NodeState::Partial => format!(
            "Partial floor {} ({} unknown, {} proven)",
            row.floor.as_deref().unwrap_or("?"),
            row.unknowns.len(),
            row.contributions.len()
        ),
        NodeState::Unknown => format!("Unknown ({} unknown)", row.unknowns.len()),
    }
}

#[derive(Deserialize)]
struct CountsFile {
    schema: u32,
    passes: BTreeMap<String, BTreeMap<String, MemberStatus>>,
}

#[derive(Clone, Deserialize)]
struct MemberStatus {
    error: Option<String>,
    #[serde(default)]
    errors: Vec<String>,
}

/// A snapshot directory's members per pass, each with its hard failure and analysis errors.
struct Snapshot {
    directory: PathBuf,
    members: BTreeMap<(Pass, String), MemberStatus>,
}

impl Snapshot {
    fn open(directory: &Path) -> Result<Snapshot, String> {
        let path = directory.join("counts.json");
        let text = std::fs::read_to_string(&path).map_err(|error| {
            format!(
                "cannot read {}: {error}; run olint-corpus snapshot first",
                path.display()
            )
        })?;
        let counts: CountsFile = serde_json::from_str(&text)
            .map_err(|error| format!("{} is malformed: {error}", path.display()))?;

        if counts.schema != SCHEMA {
            return Err(format!(
                "{} has row schema {} where this harness reads {SCHEMA}, and no adapter exists for that pair",
                path.display(),
                counts.schema
            ));
        }

        let mut members = BTreeMap::new();

        for (name, runs) in counts.passes {
            let pass = Pass::of(&name)
                .ok_or_else(|| format!("{} names unknown pass {name}", path.display()))?;

            for (member, status) in runs {
                members.insert((pass, member), status);
            }
        }

        Ok(Snapshot {
            directory: directory.to_path_buf(),
            members,
        })
    }

    fn rows(&self, pass: Pass, member: &str) -> Result<BTreeMap<NodeKey, NodeRow>, String> {
        let path = pass
            .directory(&self.directory)
            .join(format!("{member}.jsonl.gz"));

        read_rows(&path)
    }
}

pub fn read_rows(path: &Path) -> Result<BTreeMap<NodeKey, NodeRow>, String> {
    let file = std::fs::File::open(path)
        .map_err(|error| format!("cannot open {}: {error}", path.display()))?;
    let mut rows = BTreeMap::new();

    for line in BufReader::new(GzDecoder::new(file)).lines() {
        let line = line.map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        let row: NodeRow = serde_json::from_str(&line)
            .map_err(|error| format!("{} has a malformed row: {error}", path.display()))?;

        rows.insert(row.key.clone(), row);
    }

    Ok(rows)
}

/// Compares the head snapshot directory against the base one, matching lowerings against `trailers`.
pub fn compare(base: &Path, head: &Path, trailers: &[Trailer]) -> Result<Report, String> {
    let base = Snapshot::open(base)?;
    let head = Snapshot::open(head)?;
    let ranking = Ranking::new();
    let mut report = Report {
        trailers: trailers
            .iter()
            .map(|trailer| (trailer.clone(), 0))
            .collect(),
        ..Report::default()
    };
    let runs: BTreeSet<(Pass, String)> = base
        .members
        .keys()
        .chain(head.members.keys())
        .cloned()
        .collect();
    let mut ruled = false;

    for (pass, member) in runs {
        let label = format!("{}{member}", prefix(pass));
        let before = base.members.get(&(pass, member.clone()));
        let after = head.members.get(&(pass, member.clone()));
        let empty = BTreeMap::new;

        if let Some(status) =
            after.filter(|status| status.error.is_none() && !status.errors.is_empty())
        {
            report
                .errors
                .push(format!("{label}: {}", status.errors.join("; ")));
        }

        let (old, new) = match (
            before.map(|status| status.error.as_deref()),
            after.map(|status| status.error.as_deref()),
        ) {
            (Some(None), Some(None)) => (base.rows(pass, &member)?, head.rows(pass, &member)?),
            (Some(_), None) => {
                report.failed.push(format!(
                    "{label} is absent from the head; the corpus is pinned"
                ));

                continue;
            }
            (None, Some(None)) => {
                report.notes.push(format!(
                    "{label} is new in the head; its keys count as added"
                ));

                (empty(), head.rows(pass, &member)?)
            }
            (Some(None), Some(Some(error))) => {
                report
                    .failed
                    .push(format!("{label} fails in the head: {error}"));

                continue;
            }
            (None, Some(Some(error))) => {
                report.failed.push(format!(
                    "{label} is new in the head and fails there: {error}"
                ));

                continue;
            }
            (Some(Some(error)), Some(None)) => {
                report.notes.push(format!(
                    "{label} failed in the base and analyses in the head, so its keys count as added: {error}"
                ));

                (empty(), head.rows(pass, &member)?)
            }
            (Some(Some(was)), Some(Some(now))) => {
                report
                    .both_failed
                    .push(format!("{label}: base {was}; head {now}"));

                continue;
            }
            (None, None) => continue,
        };
        let mut totals = Totals::default();
        let functions = Functions::of(&old, &new);

        ruled |= old
            .values()
            .chain(new.values())
            .any(|row| !row.rules.is_empty());

        for (key, prior) in &old {
            let Some(current) = new.get(key) else {
                if functions.exempts(key) {
                    totals.skipped += 1;

                    continue;
                }

                totals.removed += 1;

                if report.removed.len() < PRINTED_LOWERINGS {
                    report.removed.push(format!(
                        "{label} {}:{}-{} {}: {}",
                        key.path,
                        key.start,
                        key.end,
                        key.kind,
                        state_text(prior)
                    ));
                }

                continue;
            };
            let up = ranking.ranks_at_or_above(current, prior);
            let down = ranking.ranks_at_or_above(prior, current);

            match (up, down) {
                (true, true) => totals.unchanged += 1,
                (true, false) if current.asserted || prior.asserted => totals.asserted += 1,
                (true, false) => totals.raises += 1,
                (false, _) => {
                    totals.lowers += 1;
                    report.lowerings += 1;

                    let lowering = Lowering {
                        pass,
                        member: member.clone(),
                        key: key.clone(),
                        rules: prior.rules.iter().chain(&current.rules).cloned().collect(),
                        from: state_text(prior),
                        to: state_text(current),
                    };
                    let mut matched = false;

                    for (trailer, hits) in report.trailers.iter_mut() {
                        if trailer.matches(&lowering) {
                            *hits += 1;
                            matched = true;
                        }
                    }

                    if !matched {
                        report.unmatched_count += 1;

                        if report.unmatched.len() < PRINTED_LOWERINGS {
                            report.unmatched.push(lowering);
                        }
                    }
                }
            }
        }

        for key in new.keys().filter(|key| !old.contains_key(*key)) {
            match functions.exempts(key) {
                true => totals.skipped += 1,
                false => totals.added += 1,
            }
        }

        report.members.insert((pass, member), totals);
    }

    if !ruled {
        for trailer in trailers.iter().filter(|trailer| trailer.rule != "*") {
            report.problems.push(format!(
                "Lowers: {} names rule={}, but neither snapshot carries rules; rows gain rules in Phase 5, and until then only rule=* is valid",
                trailer.text, trailer.rule
            ));
        }
    }

    Ok(report)
}

/// §5.3: a raised growth order on a scaling family fails. The comparison needs both `corpus/.cache/scale/<sha>.json`
/// files; a missing one fails, unless `skip` (`--no-scale`) turns it into a note. Acceptance requires the comparison.
fn scaling_problems(
    cache: &Path,
    base: &str,
    head: &str,
    skip: bool,
) -> Result<(Vec<String>, Option<String>), String> {
    let base = cache.join("scale").join(format!("{base}.json"));
    let head = cache.join("scale").join(format!("{head}.json"));

    if skip {
        return Ok((
            Vec::new(),
            Some(
                "--no-scale skipped the §5.3 scaling comparison; acceptance requires it"
                    .to_string(),
            ),
        ));
    }

    let missing: Vec<String> = [&base, &head]
        .into_iter()
        .filter(|path| !path.is_file())
        .map(|path| path.display().to_string())
        .collect();

    if !missing.is_empty() {
        return Ok((
            vec![format!(
                "no scaling comparison: {} missing; run `olint-corpus scale --src <sha>` for both sides, or pass --no-scale while iterating",
                missing.join(" and ")
            )],
            None,
        ));
    }

    Ok((
        raised_orders(&read_scale(&base)?, &read_scale(&head)?),
        None,
    ))
}

/// §5.2 hook: a Known bound below a ceiling of its node fails. Action 7.3 adds `proofs/Olint/Ceilings/` and fills
/// this comparison; until then the check passes when the head tree carries no ceilings.
fn ceiling_problems(repo: &Path, head: &str) -> Result<Vec<String>, String> {
    let listed = git(
        repo,
        &[
            "ls-tree",
            "-r",
            "--name-only",
            head,
            "--",
            "proofs/Olint/Ceilings",
        ],
    )?;

    Ok(match listed.trim().is_empty() {
        true => Vec::new(),
        false => vec![format!(
            "{head} carries ceilings under proofs/Olint/Ceilings, but the ceiling check (action 7.3) is not implemented"
        )],
    })
}

fn git(repo: &Path, arguments: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .args(arguments)
        .current_dir(repo)
        .output()
        .map_err(|error| format!("git did not start: {error}"))?;

    match output.status.success() {
        true => Ok(String::from_utf8_lossy(&output.stdout).into_owned()),
        false => Err(format!(
            "git {} failed: {}",
            arguments.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        )),
    }
}

fn commit(repo: &Path, name: &str) -> Result<String, String> {
    git(
        repo,
        &[
            "rev-parse",
            "--verify",
            "--quiet",
            &format!("{name}^{{commit}}"),
        ],
    )
    .map(|sha| sha.trim().to_string())
    .map_err(|_| format!("{name} is not a commit"))
}

/// Reads and parses the `Lowers:` trailers of every commit in `base..head`.
pub fn trailers(repo: &Path, base: &str, head: &str) -> Result<Vec<Trailer>, String> {
    let text = git(
        repo,
        &[
            "log",
            "--format=%(trailers:key=Lowers,valueonly,unfold)",
            &format!("{base}..{head}"),
        ],
    )?;

    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(Trailer::parse)
        .collect()
}

/// The number of `Lowers:` lines anywhere in `message`, trailer or not.
fn lowers_lines(message: &str) -> usize {
    message
        .lines()
        .filter(|line| line.trim_start().starts_with("Lowers:"))
        .count()
}

/// Warns for every commit in `base..head` whose full message holds more `Lowers:` lines than git parses as trailers.
/// Git reads trailers from the final paragraph only, so a `Lowers:` line above a blank line, or in a final paragraph
/// git does not read as a trailer block, never reaches `diff`.
fn misplaced_trailers(repo: &Path, base: &str, head: &str) -> Result<Vec<String>, String> {
    let range = format!("{base}..{head}");
    let messages = git(repo, &["log", "--format=%H%x00%B%x01", &range])?;
    let parsed = git(
        repo,
        &[
            "log",
            "--format=%H%x00%(trailers:key=Lowers,valueonly,unfold)%x01",
            &range,
        ],
    )?;
    let counts = |text: &str, count: &dyn Fn(&str) -> usize| -> BTreeMap<String, usize> {
        text.split('\u{1}')
            .filter_map(|entry| entry.trim_start().split_once('\0'))
            .map(|(sha, body)| (sha.to_string(), count(body)))
            .collect()
    };
    let written = counts(&messages, &lowers_lines);
    let read = counts(&parsed, &|body| {
        body.lines().filter(|line| !line.trim().is_empty()).count()
    });

    Ok(written
        .into_iter()
        .filter(|(sha, count)| *count > read.get(sha).copied().unwrap_or(0))
        .map(|(sha, count)| {
            format!(
                "commit {sha} has {count} Lowers: lines but git parses {} as trailers; git reads trailers from the final paragraph only, so move every Lowers: line into the one final trailer block with no blank line inside it",
                read.get(&sha).copied().unwrap_or(0)
            )
        })
        .collect())
}

/// A `disproof` trailer's evidence must be an existing commit or a path in the head tree.
fn evidence_problems(repo: &Path, head: &str, trailers: &[Trailer]) -> Vec<String> {
    trailers
        .iter()
        .filter(|trailer| trailer.category == Category::Disproof)
        .filter(|trailer| {
            commit(repo, &trailer.evidence).is_err()
                && git(repo, &["ls-tree", "--name-only", head, "--", &trailer.evidence])
                    .map_or(true, |listed| listed.trim().is_empty())
        })
        .map(|trailer| {
            format!(
                "Lowers: {} cites disproof evidence {}, which is neither a commit nor a path in {head}",
                trailer.text, trailer.evidence
            )
        })
        .collect()
}

/// `olint-corpus diff <base> <head> [--no-scale]`: prints the summary and fails unless the change is accepted.
pub fn diff(base: &str, head: &str, no_scale: bool) -> Result<(), String> {
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo = corpus
        .parent()
        .expect("the corpus package sits in the olint tree");
    let cache = corpus.join(".cache");
    let base = commit(repo, base)?;
    let head = commit(repo, head)?;
    let trailers = trailers(repo, &base, &head)?;
    let mut report = compare(
        &cache.join("snap").join(&base),
        &cache.join("snap").join(&head),
        &trailers,
    )?;

    let (scaling, note) = scaling_problems(&cache, &base, &head, no_scale)?;

    report.problems.extend(scaling);
    report.notes.extend(note);
    report.problems.extend(ceiling_problems(repo, &head)?);
    report
        .problems
        .extend(evidence_problems(repo, &head, &trailers));
    report
        .warnings
        .extend(misplaced_trailers(repo, &base, &head)?);

    for pass in PASSES {
        if !report.members.keys().any(|(run, _)| *run == pass) {
            report
                .notes
                .push(format!("no {} rows on either side", pass.name()));
        }
    }

    print!("{}", report.render());

    match (report.passed(), report.warnings.is_empty()) {
        (true, _) => Ok(()),
        (false, true) => Err(format!("diff {base}..{head} is rejected")),
        (false, false) => Err(format!(
            "diff {base}..{head} is rejected; a commit in range has Lowers: lines outside its final trailer block, which git never parses as trailers"
        )),
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write as _;

    use flate2::write::GzEncoder;
    use flate2::Compression;

    use super::*;

    fn row(state: NodeState, bound: Option<&str>) -> NodeRow {
        NodeRow {
            key: key("a.ts", 0, "CallExpression"),
            state,
            bound: (state == NodeState::Known).then(|| bound.unwrap_or("O(1)").to_string()),
            floor: (state == NodeState::Partial).then(|| bound.unwrap_or("O(1)").to_string()),
            contributions: Vec::new(),
            asserted: false,
            unknowns: Vec::new(),
            rules: Vec::new(),
            certificate: None,
        }
    }

    fn key(path: &str, start: u32, kind: &str) -> NodeKey {
        NodeKey {
            path: path.to_string(),
            start,
            end: start + 1,
            kind: kind.to_string(),
        }
    }

    #[test]
    fn globs_match_runs_and_single_characters() {
        assert!(glob("*", "packages/@scope/pkg@1.0.0"));
        assert!(glob("packages/*", "packages/@scope/pkg@1.0.0"));
        assert!(glob("src/*.ts", "src/deep/file.ts"));
        assert!(glob("a?c", "abc"));
        assert!(!glob("a?c", "ac"));
        assert!(!glob("fixtures/*", "packages/x"));
        assert!(glob("*model", "fixtures/model"));
        assert!(glob("**x*", "abxcd"));
    }

    #[test]
    fn trailers_parse_the_plan_format() {
        let trailer = Trailer::parse(
            "member=* path=* kind=CallExpression rule=array-method; uncertified; §2.4 sort comparisons are implementation-defined",
        )
        .expect("parses");

        assert_eq!(trailer.kind, "CallExpression");
        assert_eq!(trailer.rule, "array-method");
        assert_eq!(trailer.category, Category::Uncertified);
        assert!(Trailer::parse("member=* path=* kind=*; uncertified; x").is_err());
        assert!(Trailer::parse("member=* path=* kind=* rule=*; unsure; x").is_err());
        assert!(Trailer::parse("member=* path=* kind=* rule=*; scaling").is_err());
    }

    #[test]
    fn knownness_order_ranks_states_and_bounds() {
        let ranking = Ranking::new();
        let known = |bound| row(NodeState::Known, Some(bound));

        assert!(ranking.ranks_at_or_above(&known("O(1)"), &known("O(xs)")));
        assert!(!ranking.ranks_at_or_above(&known("O(xs)"), &known("O(1)")));
        assert!(ranking.ranks_at_or_above(&known("O(xs)"), &known("O((xs * N))")));
        assert!(ranking.ranks_at_or_above(&known("O(xs)"), &known("O(xs)")));
        assert!(!ranking.ranks_at_or_above(&known("O(xs)"), &known("O(ys)")));
        assert!(!ranking.ranks_at_or_above(&known("O(unknown)"), &known("O(1)")));
        assert!(ranking.ranks_at_or_above(&known("O(N)"), &row(NodeState::Partial, None)));
        assert!(ranking.ranks_at_or_above(
            &row(NodeState::Partial, None),
            &row(NodeState::Unknown, None)
        ));
        assert!(!ranking.ranks_at_or_above(&row(NodeState::Unknown, None), &known("O(N^2)")));
        assert!(ranking.ranks_at_or_above(
            &row(NodeState::Unknown, None),
            &row(NodeState::Unknown, None)
        ));
    }

    fn partial(unknowns: &[u32], contributions: &[(u32, &str)], floor: &str) -> NodeRow {
        NodeRow {
            unknowns: unknowns
                .iter()
                .map(|start| (key("a.ts", *start, "CallExpression"), "reason".to_string()))
                .collect(),
            contributions: contributions
                .iter()
                .map(|(start, bound)| (key("a.ts", *start, "Expression"), bound.to_string()))
                .collect(),
            ..row(NodeState::Partial, Some(floor))
        }
    }

    #[test]
    fn partial_ranks_by_unknown_subset_and_contribution_tightness() {
        let ranking = Ranking::new();

        assert!(ranking.ranks_at_or_above(
            &partial(&[1], &[(5, "O(1)")], "O(1)"),
            &partial(&[1, 2], &[(5, "O(xs)")], "O(xs)")
        ));
        assert!(
            !ranking.ranks_at_or_above(&partial(&[1, 3], &[], "O(1)"), &partial(&[1], &[], "O(1)"))
        );
        assert!(!ranking.ranks_at_or_above(
            &partial(&[1], &[], "O(1)"),
            &partial(&[1], &[(5, "O(1)")], "O(1)")
        ));
        assert!(!ranking.ranks_at_or_above(
            &partial(&[1], &[(5, "O(xs)")], "O(xs)"),
            &partial(&[1], &[(5, "O(1)")], "O(1)")
        ));
    }

    #[test]
    fn partial_floors_rank_where_contributions_are_silent() {
        let ranking = Ranking::new();

        // `for (i < xs.length) { opaque(); }` with the loop multiplicity weakened from xs to xs * N: no contribution
        // lists the multiplicity, so only the floor shows the lowering.
        assert!(!ranking.ranks_at_or_above(
            &partial(&[1], &[], "O((xs * N))"),
            &partial(&[1], &[], "O(xs)")
        ));
        assert!(ranking.ranks_at_or_above(
            &partial(&[1], &[], "O(xs)"),
            &partial(&[1], &[], "O((xs * N))")
        ));
        assert!(
            !ranking.ranks_at_or_above(&partial(&[1], &[], "O(ys)"), &partial(&[1], &[], "O(xs)"))
        );
        // A newly proven contribution may raise the floor up to its own bound.
        assert!(ranking.ranks_at_or_above(
            &partial(&[1], &[(5, "O(ys)")], "O(max(xs, ys))"),
            &partial(&[1, 5], &[], "O(xs)")
        ));
        assert!(!ranking.ranks_at_or_above(
            &partial(&[1], &[(5, "O(ys)")], "O((xs * ys))"),
            &partial(&[1, 5], &[], "O(xs)")
        ));
    }

    #[test]
    fn unknown_ranks_by_unknown_origin_subset() {
        let ranking = Ranking::new();
        let unknown = |origins: &[u32]| NodeRow {
            unknowns: origins
                .iter()
                .map(|start| (key("a.ts", *start, "CallExpression"), "reason".to_string()))
                .collect(),
            ..row(NodeState::Unknown, None)
        };

        assert!(ranking.ranks_at_or_above(&unknown(&[1]), &unknown(&[1, 2])));
        assert!(!ranking.ranks_at_or_above(&unknown(&[1, 3]), &unknown(&[1, 2])));
        assert!(!ranking.ranks_at_or_above(&unknown(&[1, 2]), &unknown(&[1])));
    }

    #[test]
    fn trailers_match_member_path_kind_and_rule() {
        let trailer = Trailer::parse(
            "member=fixtures/* path=src/*.ts kind=ForStatement rule=*; disproof; abc123",
        )
        .expect("parses");
        let lowering = Lowering {
            pass: Pass::Syntactic,
            member: "fixtures/model".to_string(),
            key: key("src/bounds.ts", 3, "ForStatement"),
            rules: BTreeSet::new(),
            from: String::new(),
            to: String::new(),
        };

        assert!(trailer.matches(&lowering));
        assert!(!trailer.matches(&Lowering {
            key: key("src/bounds.ts", 3, "WhileStatement"),
            ..lowering.clone()
        }));

        let ruled = Trailer::parse("member=* path=* kind=* rule=loop-bound; uncertified; x")
            .expect("parses");

        assert!(!ruled.matches(&lowering));
        assert!(ruled.matches(&Lowering {
            rules: BTreeSet::from(["loop-bound".to_string()]),
            ..lowering
        }));
    }

    /// A member of a synthetic snapshot: its rows, or its hard failure, and its analysis errors.
    enum Run<'r> {
        Rows(&'r [NodeRow], &'r [&'r str]),
        Failed(&'r str),
    }

    fn write_snapshot(directory: &Path, members: &[(&str, Run<'_>)]) {
        let mut runs = serde_json::Map::new();

        for (member, run) in members {
            let status = match run {
                Run::Rows(rows, errors) => {
                    let path = directory.join(format!("{member}.jsonl.gz"));

                    std::fs::create_dir_all(path.parent().expect("parent")).expect("directory");

                    let mut encoder = GzEncoder::new(
                        std::fs::File::create(&path).expect("rows file"),
                        Compression::default(),
                    );

                    for row in *rows {
                        serde_json::to_writer(&mut encoder, row).expect("row");
                        encoder.write_all(b"\n").expect("newline");
                    }

                    encoder.finish().expect("gzip");

                    serde_json::json!({ "error": null, "errors": errors })
                }
                Run::Failed(error) => serde_json::json!({ "error": error }),
            };

            runs.insert(member.to_string(), status);
        }

        std::fs::create_dir_all(directory).expect("snapshot directory");
        std::fs::write(
            directory.join("counts.json"),
            serde_json::json!({ "schema": SCHEMA, "passes": { "syntactic": runs } }).to_string(),
        )
        .expect("counts");
    }

    fn compared(
        name: &str,
        base: &[(&str, Run<'_>)],
        head: &[(&str, Run<'_>)],
        trailers: &[Trailer],
    ) -> Report {
        let root =
            std::env::temp_dir().join(format!("olint-corpus-diff-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);

        write_snapshot(&root.join("base"), base);
        write_snapshot(&root.join("head"), head);

        let report = compare(&root.join("base"), &root.join("head"), trailers).expect("compares");

        std::fs::remove_dir_all(&root).expect("cleanup");

        report
    }

    fn keyed(start: u32, bound: &str) -> NodeRow {
        NodeRow {
            key: key("a.ts", start, "CallExpression"),
            ..row(NodeState::Known, Some(bound))
        }
    }

    #[test]
    fn removed_keys_fail_and_added_keys_pass() {
        let both = [keyed(0, "O(1)"), keyed(2, "O(1)")];
        let one = [keyed(0, "O(1)")];

        let removed = compared(
            "removed",
            &[("m", Run::Rows(&both, &[]))],
            &[("m", Run::Rows(&one, &[]))],
            &[],
        );

        assert_eq!(removed.totals().removed, 1);
        assert!(!removed.passed());
        assert!(removed.render().contains("keys removed"));

        let added = compared(
            "added",
            &[("m", Run::Rows(&one, &[]))],
            &[("m", Run::Rows(&both, &[]))],
            &[],
        );

        assert_eq!(added.totals().added, 1);
        assert!(added.passed());
    }

    #[test]
    fn member_presence_and_failures_decide_the_diff() {
        let rows = [keyed(0, "O(1)")];

        let absent = compared(
            "absent",
            &[
                ("m", Run::Rows(&rows, &[])),
                ("gone", Run::Rows(&rows, &[])),
            ],
            &[("m", Run::Rows(&rows, &[]))],
            &[],
        );

        assert!(!absent.passed());
        assert!(absent.failed[0].contains("gone is absent from the head"));

        let both = compared(
            "both",
            &[("m", Run::Failed("load"))],
            &[("m", Run::Failed("load"))],
            &[],
        );

        assert!(both.passed());
        assert_eq!(both.both_failed.len(), 1);
        assert!(both.render().contains("FAILED ON BOTH SIDES"));

        let head = compared(
            "head",
            &[("m", Run::Rows(&rows, &[]))],
            &[("m", Run::Failed("load"))],
            &[],
        );

        assert!(!head.passed());

        let warned = compared(
            "warned",
            &[("m", Run::Rows(&rows, &["invalid @perf"]))],
            &[("m", Run::Rows(&[keyed(0, "O(xs)")], &["invalid @perf"]))],
            &[],
        );

        assert_eq!(warned.totals().lowers, 1);
        assert_eq!(warned.errors.len(), 1);
        assert!(!warned.passed());
    }

    /// A function row over `start..end` of `a.ts`, Known, or Unknown with one unknown of `reason` whose origin spans
    /// `origin`.
    fn function(start: u32, end: u32, unknown: Option<(&str, (u32, u32))>) -> NodeRow {
        let span = NodeKey {
            end,
            ..key("a.ts", start, "Function")
        };

        match unknown {
            None => NodeRow {
                key: span,
                ..row(NodeState::Known, Some("O(1)"))
            },
            Some((reason, (from, to))) => NodeRow {
                key: span,
                unknowns: vec![(
                    NodeKey {
                        end: to,
                        ..key("a.ts", from, "CallExpression")
                    },
                    reason.to_string(),
                )],
                ..row(NodeState::Unknown, None)
            },
        }
    }

    fn lowered_function_diff(name: &str, head: NodeRow, trailers: &[Trailer]) -> Report {
        let base = [function(0, 100, None), keyed(10, "O(1)"), keyed(20, "O(1)")];
        let head = [head, keyed(10, "O(1)")];

        compared(
            name,
            &[("m", Run::Rows(&base, &[]))],
            &[("m", Run::Rows(&head, &[]))],
            trailers,
        )
    }

    #[test]
    fn removed_descendants_of_a_resource_limited_function_are_skipped() {
        let any = Trailer::parse("member=m path=a.ts kind=Function rule=*; uncertified; x")
            .expect("parses");

        for origin in [(0, 100), (20, 21)] {
            let report = lowered_function_diff(
                "limited",
                function(0, 100, Some((RESOURCE_LIMIT, origin))),
                std::slice::from_ref(&any),
            );
            let totals = report.totals();

            assert_eq!((totals.removed, totals.skipped, totals.lowers), (0, 1, 1));
            assert_eq!(totals.unchanged, 1);
            assert!(report.passed(), "{}", report.render());
            assert!(report.render().contains("skipped"));
        }
    }

    #[test]
    fn removed_descendants_of_a_normal_function_still_fail() {
        let any = Trailer::parse("member=m path=a.ts kind=Function rule=*; uncertified; x")
            .expect("parses");

        // Another reason, and a resource limit whose origin lies in a callee outside the function, leave the walk
        // complete.
        for head in [
            function(0, 100, Some(("unsupported model", (0, 100)))),
            function(0, 100, Some((RESOURCE_LIMIT, (200, 300)))),
        ] {
            let report = lowered_function_diff("normal", head, std::slice::from_ref(&any));
            let totals = report.totals();

            assert_eq!((totals.removed, totals.skipped), (1, 0));
            assert!(!report.passed());
        }

        let report = lowered_function_diff("known", function(0, 100, None), &[]);

        assert_eq!(report.totals().removed, 1);
        assert!(!report.passed());
    }

    #[test]
    fn a_resource_limited_function_row_still_needs_a_trailer() {
        let report = lowered_function_diff(
            "untrailed",
            function(0, 100, Some((RESOURCE_LIMIT, (0, 100)))),
            &[],
        );

        assert_eq!(report.totals().skipped, 1);
        assert_eq!(report.unmatched_count, 1);
        assert_eq!(report.unmatched[0].key.kind, "Function");
        assert!(!report.passed());
    }

    #[test]
    fn named_rules_fail_while_no_row_carries_rules() {
        let rows = [keyed(0, "O(1)")];
        let lowered = [keyed(0, "O(xs)")];
        let ruled = Trailer::parse("member=* path=* kind=* rule=loop-bound; uncertified; x")
            .expect("parses");
        let any = Trailer::parse("member=* path=* kind=* rule=*; uncertified; x").expect("parses");
        let report = compared(
            "rules",
            &[("m", Run::Rows(&rows, &[]))],
            &[("m", Run::Rows(&lowered, &[]))],
            &[ruled, any],
        );

        assert!(!report.passed());
        assert!(report.problems[0].contains("only rule=* is valid"));
    }

    #[test]
    fn lowers_lines_count_every_paragraph() {
        assert_eq!(
            lowers_lines("feat: x\n\nLowers: a\n\nbody\n\nLowers: b\nPlan: p\n"),
            2
        );
        assert_eq!(lowers_lines("feat: x\n\nbody mentions Lowers: inline\n"), 0);
    }
}

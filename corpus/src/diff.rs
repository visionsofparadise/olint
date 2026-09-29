//! `diff` ranks every node of a head snapshot against its base snapshot by the spec's knownness order, and accepts the
//! change only when every lowering matches a `Lowers:` trailer of the commits between them and every trailer matches
//! at least one lowering.
//!
//! Ranking, per key present in both snapshots of a member and pass:
//!
//! - Known ranks above Partial, and Partial above Unknown.
//! - Known against Known ranks at or above when the new bound is at least as tight, by `Cost::compare`.
//! - Partial against Partial ranks at or above when the new unknown origins are a subset of the prior ones and every
//!   prior proven contribution has a new contribution at the same constituent that is at least as tight.
//! - Unknown against Unknown ranks equal.
//!
//! A comparison `Cost::compare` leaves `Inconclusive` fails "at least as tight", so the prior state then fails to rank
//! at or above and the node lowers. Identical cost text is equal without a comparison. Asserted rows never count as
//! raises (§5.6). Added and removed keys are reported apart from rank changes.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::Command;

use flate2::read::GzDecoder;
use olint::cost::{Cost, CostComparison, Domain};
use olint::snapshot::{NodeKey, NodeRow, NodeState, SCHEMA};
use serde::Deserialize;

use crate::scale::{raised_orders, read_scale};
use crate::snapshot::{Pass, PASSES};

/// Unmatched lowerings printed before the rest are summarized as a count.
const PRINTED_LOWERINGS: usize = 200;

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
}

impl Totals {
    fn changed(&self) -> bool {
        self.raises + self.asserted + self.lowers + self.added + self.removed > 0
    }

    fn add(&mut self, other: &Totals) {
        self.unchanged += other.unchanged;
        self.raises += other.raises;
        self.asserted += other.asserted;
        self.lowers += other.lowers;
        self.added += other.added;
        self.removed += other.removed;
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
    /// Members that analysed in the base and failed in the head.
    pub failed: Vec<String>,
    /// Members that failed on both sides, or only in the base.
    pub notes: Vec<String>,
    /// Failed checks beyond rank: scaling order (§5.3) and ceilings (§5.2).
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
            && self.trailers.iter().all(|(_, hits)| *hits > 0)
            && self.failed.is_empty()
            && self.problems.is_empty()
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        let totals = self.totals();

        let _ = writeln!(
            out,
            "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8}",
            "member", "raises", "asserted", "lowers", "added", "removed"
        );

        for ((pass, member), counts) in &self.members {
            if counts.changed() {
                let _ = writeln!(
                    out,
                    "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8}",
                    format!("{}{member}", prefix(*pass)),
                    counts.raises,
                    counts.asserted,
                    counts.lowers,
                    counts.added,
                    counts.removed
                );
            }
        }

        let _ = writeln!(
            out,
            "{:<48} {:>8} {:>8} {:>8} {:>8} {:>8}",
            format!(
                "total ({} runs, {} unchanged)",
                self.members.len(),
                totals.unchanged
            ),
            totals.raises,
            totals.asserted,
            totals.lowers,
            totals.added,
            totals.removed
        );

        for member in &self.failed {
            let _ = writeln!(out, "failed in head: {member}");
        }

        for note in &self.notes {
            let _ = writeln!(out, "note: {note}");
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

fn prefix(pass: Pass) -> &'static str {
    match pass {
        Pass::Syntactic => "",
        Pass::Tsc => "tsc/",
    }
}

/// Parses canonical cost text back into a comparable `Cost`: each label becomes one size dimension, shared across
/// every comparison of a run so both sides of a comparison name the same dimension, and `N` becomes the envelope.
struct Costs {
    names: RefCell<HashMap<String, u64>>,
    parsed: RefCell<HashMap<String, Option<Cost>>>,
}

impl Costs {
    fn new() -> Costs {
        Costs {
            names: RefCell::new(HashMap::new()),
            parsed: RefCell::new(HashMap::new()),
        }
    }

    fn parse(&self, text: &str) -> Option<Cost> {
        if let Some(cost) = self.parsed.borrow().get(text) {
            return cost.clone();
        }

        let cost = match text {
            "O(unknown)" => None,
            _ => Cost::parse(text).ok().and_then(|cost| {
                let resolve = |name: &str| {
                    let mut names = self.names.borrow_mut();
                    let next = names.len() as u64;
                    let id = *names.entry(name.to_string()).or_insert(next);

                    Some(Cost::dimension(id, Domain::Size))
                };

                cost.bind(&resolve, &[Cost::dimension(u64::MAX, Domain::Size)])
                    .ok()
            }),
        };

        self.parsed
            .borrow_mut()
            .insert(text.to_string(), cost.clone());

        cost
    }

    /// Whether cost `new` is at least as tight as cost `old`.
    fn at_least_as_tight(&self, new: Option<&str>, old: Option<&str>) -> bool {
        match (new, old) {
            (Some(new), Some(old)) if new == old => true,
            (Some(new), Some(old)) => match (self.parse(new), self.parse(old)) {
                (Some(new), Some(old)) => new.compare(&old) == CostComparison::Within,
                _ => false,
            },
            (None, None) => true,
            _ => false,
        }
    }

    /// Whether `new` ranks at or above `old` in the knownness order.
    fn ranks_at_or_above(&self, new: &NodeRow, old: &NodeRow) -> bool {
        match (new.state, old.state) {
            (NodeState::Known, NodeState::Known) => {
                self.at_least_as_tight(new.bound.as_deref(), old.bound.as_deref())
            }
            (NodeState::Known, _) | (NodeState::Partial, NodeState::Unknown) => true,
            (NodeState::Partial, NodeState::Partial) => {
                let prior: BTreeSet<&NodeKey> = old.unknowns.iter().map(|(key, _)| key).collect();
                let proven: BTreeMap<&NodeKey, &str> = new
                    .contributions
                    .iter()
                    .map(|(key, bound)| (key, bound.as_str()))
                    .collect();

                new.unknowns.iter().all(|(key, _)| prior.contains(key))
                    && old.contributions.iter().all(|(key, bound)| {
                        proven.get(key).is_some_and(|new| {
                            self.at_least_as_tight(Some(new), Some(bound.as_str()))
                        })
                    })
            }
            (NodeState::Unknown, NodeState::Unknown) => true,
            _ => false,
        }
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

#[derive(Deserialize)]
struct MemberStatus {
    error: Option<String>,
}

/// A snapshot directory's members per pass, each with its error when it failed to analyse.
struct Snapshot {
    directory: PathBuf,
    members: BTreeMap<(Pass, String), Option<String>>,
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
                members.insert((pass, member), status.error);
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
    let costs = Costs::new();
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

    for (pass, member) in runs {
        let label = format!("{}{member}", prefix(pass));
        let before = base.members.get(&(pass, member.clone()));
        let after = head.members.get(&(pass, member.clone()));
        let empty = BTreeMap::new;
        let (old, new) = match (before, after) {
            (Some(None), Some(None)) => (base.rows(pass, &member)?, head.rows(pass, &member)?),
            (Some(None), None) => (base.rows(pass, &member)?, empty()),
            (None, Some(None)) => (empty(), head.rows(pass, &member)?),
            (Some(None), Some(Some(error))) => {
                report.failed.push(format!("{label}: {error}"));

                continue;
            }
            (Some(Some(error)), Some(None)) | (Some(Some(error)), None) => {
                report
                    .notes
                    .push(format!("{label} failed in the base: {error}"));

                match after {
                    Some(None) => (empty(), head.rows(pass, &member)?),
                    _ => continue,
                }
            }
            (_, Some(Some(error))) => {
                report.notes.push(format!(
                    "{label} fails in the head, absent or failing in the base: {error}"
                ));

                continue;
            }
            (None, None) => continue,
        };
        let mut totals = Totals::default();

        for (key, prior) in &old {
            let Some(current) = new.get(key) else {
                totals.removed += 1;

                continue;
            };
            let up = costs.ranks_at_or_above(current, prior);
            let down = costs.ranks_at_or_above(prior, current);

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

        totals.added = new.keys().filter(|key| !old.contains_key(*key)).count();

        report.members.insert((pass, member), totals);
    }

    Ok(report)
}

/// §5.3: a raised growth order on a scaling family fails. The comparison runs when both `corpus/.cache/scale/<sha>.json`
/// files exist, and passes with a note otherwise.
fn scaling_problems(
    cache: &Path,
    base: &str,
    head: &str,
) -> Result<(Vec<String>, Option<String>), String> {
    let base = cache.join("scale").join(format!("{base}.json"));
    let head = cache.join("scale").join(format!("{head}.json"));

    if !(base.is_file() && head.is_file()) {
        return Ok((
            Vec::new(),
            Some(format!(
                "no scaling comparison: run `scale` for both sides ({} and {})",
                base.display(),
                head.display()
            )),
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

/// `olint-corpus diff <base> <head>`: prints the summary and fails unless the change is accepted.
pub fn diff(base: &str, head: &str) -> Result<(), String> {
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

    let (scaling, note) = scaling_problems(&cache, &base, &head)?;

    report.problems.extend(scaling);
    report.notes.extend(note);
    report.problems.extend(ceiling_problems(repo, &head)?);

    for pass in PASSES {
        if !report.members.keys().any(|(run, _)| *run == pass) {
            report
                .notes
                .push(format!("no {} rows on either side", pass.name()));
        }
    }

    print!("{}", report.render());

    match report.passed() {
        true => Ok(()),
        false => Err(format!("diff {base}..{head} is rejected")),
    }
}

#[cfg(test)]
mod tests {
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
        let costs = Costs::new();
        let known = |bound| row(NodeState::Known, Some(bound));

        assert!(costs.ranks_at_or_above(&known("O(1)"), &known("O(xs)")));
        assert!(!costs.ranks_at_or_above(&known("O(xs)"), &known("O(1)")));
        assert!(costs.ranks_at_or_above(&known("O(xs)"), &known("O((xs * N))")));
        assert!(costs.ranks_at_or_above(&known("O(xs)"), &known("O(xs)")));
        assert!(!costs.ranks_at_or_above(&known("O(xs)"), &known("O(ys)")));
        assert!(!costs.ranks_at_or_above(&known("O(unknown)"), &known("O(1)")));
        assert!(costs.ranks_at_or_above(&known("O(N)"), &row(NodeState::Partial, None)));
        assert!(costs.ranks_at_or_above(
            &row(NodeState::Partial, None),
            &row(NodeState::Unknown, None)
        ));
        assert!(!costs.ranks_at_or_above(&row(NodeState::Unknown, None), &known("O(N^2)")));
        assert!(costs.ranks_at_or_above(
            &row(NodeState::Unknown, None),
            &row(NodeState::Unknown, None)
        ));
    }

    #[test]
    fn partial_ranks_by_unknown_subset_and_contribution_tightness() {
        let costs = Costs::new();
        let partial = |unknowns: &[u32], contributions: &[(u32, &str)]| NodeRow {
            unknowns: unknowns
                .iter()
                .map(|start| (key("a.ts", *start, "CallExpression"), "reason".to_string()))
                .collect(),
            contributions: contributions
                .iter()
                .map(|(start, bound)| (key("a.ts", *start, "Expression"), bound.to_string()))
                .collect(),
            ..row(NodeState::Partial, None)
        };

        assert!(costs.ranks_at_or_above(
            &partial(&[1], &[(5, "O(1)")]),
            &partial(&[1, 2], &[(5, "O(xs)")])
        ));
        assert!(!costs.ranks_at_or_above(&partial(&[1, 3], &[]), &partial(&[1], &[])));
        assert!(!costs.ranks_at_or_above(&partial(&[1], &[]), &partial(&[1], &[(5, "O(1)")])));
        assert!(!costs.ranks_at_or_above(
            &partial(&[1], &[(5, "O(xs)")]),
            &partial(&[1], &[(5, "O(1)")])
        ));
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
}

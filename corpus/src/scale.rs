//! `scale` measures how olint's work and memory grow on the scaling families (spec §7.5).
//!
//! It materializes and builds `--src` as `snapshot` does, generates each family at n = 2^k for k in
//! `--min-k..=--max-k`, and snapshots every size and pass in its own `snapshot-member` subprocess. Each run records
//! |G| (`MemberCounts::nodes`), the 26 scheduler `Event` counts, the scheduler task and body-pass counts, peak live
//! bytes from the counting allocator and, in the tsc pass, the checker's `TscCounts`. A size that fails or times out
//! ends that family and pass: larger sizes are skipped, and the fit uses the sizes below it.
//!
//! # Fitting
//!
//! Each metric y is fitted against x = |G| over the successful sizes, using counts only, never wall-clock time. The
//! fit assigns the lowest-order class of 1, log n, n, n log n, n², n³ or "above n³" that the sequence reads as:
//!
//! 1. **Constant.** When max y − min y is at most `CONSTANT_TOLERANCE` of max |y|, the order is 1.
//! 2. **Growth ratio.** With the first, middle and last sizes i₀ < iₘ < i_K, the observed ratio of finite differences is
//!    ρ = (y_K − y_m) / (y_m − y₀). Differences cancel any additive constant exactly, and the upper span weighs the
//!    largest sizes, where lower-order terms matter least. For each candidate g the same ratio ρ_g is computed exactly
//!    from g at the measured |G| values, and the order is the candidate whose ρ_g is nearest ρ in log distance, the
//!    lower candidate winning a tie. "Above n³" stands for n⁴.
//! 3. **Edges.** When y does not rise over the upper span (y_K ≤ y_m) the order is 1. When it rises only there, step 2
//!    runs on the last three sizes, and failing that the single last ratio y_K / y_{K−1} is matched against every
//!    candidate's, 1 included. A sequence that is zero until its last size, or has fewer than `MINIMUM_POINTS` sizes,
//!    has no fit.
//!
//! The fit is exact arithmetic on the recorded integers followed by fixed comparisons, so it is deterministic. A class
//! off the candidate list reads as its nearest candidate (log² n as log n, n log² n as n log n).
//!
//! The result is `corpus/.cache/scale/<sha>.json`, which `diff` compares under §5.3.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::families::{self, Family, FAMILIES};
use crate::members::Member;
use crate::snapshot::{
    absolute, build, head_corpus, materialize, run_member, MemberCounts, Pass, PASSES,
};

pub const SCHEMA: u32 = 1;
/// The largest spread of y, as a fraction of max |y|, that still reads as constant.
pub const CONSTANT_TOLERANCE: f64 = 0.005;
/// The fewest successful sizes a fit uses.
pub const MINIMUM_POINTS: usize = 4;
/// Metrics recorded for reference but outside §5.3: the program size and the result row count.
pub const UNCOMPARED: [&str; 2] = ["nodes", "rows"];

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Order {
    #[serde(rename = "1")]
    Constant,
    #[serde(rename = "log n")]
    Log,
    #[serde(rename = "n")]
    Linear,
    #[serde(rename = "n log n")]
    Linearithmic,
    #[serde(rename = "n^2")]
    Quadratic,
    #[serde(rename = "n^3")]
    Cubic,
    #[serde(rename = ">n^3")]
    AboveCubic,
}

impl Order {
    pub fn text(self) -> &'static str {
        match self {
            Order::Constant => "1",
            Order::Log => "log n",
            Order::Linear => "n",
            Order::Linearithmic => "n log n",
            Order::Quadratic => "n^2",
            Order::Cubic => "n^3",
            Order::AboveCubic => ">n^3",
        }
    }

    fn at(self, x: f64) -> f64 {
        match self {
            Order::Constant => 1.0,
            Order::Log => x.ln(),
            Order::Linear => x,
            Order::Linearithmic => x * x.ln(),
            Order::Quadratic => x * x,
            Order::Cubic => x * x * x,
            Order::AboveCubic => x * x * x * x,
        }
    }
}

const GROWING: [Order; 6] = [
    Order::Log,
    Order::Linear,
    Order::Linearithmic,
    Order::Quadratic,
    Order::Cubic,
    Order::AboveCubic,
];

fn nearest(observed: f64, candidates: &[Order], statistic: impl Fn(Order) -> f64) -> Order {
    let target = observed.ln();
    let mut best = candidates[0];
    let mut distance = f64::INFINITY;

    for &candidate in candidates {
        let away = (statistic(candidate).ln() - target).abs();

        if away < distance {
            best = candidate;
            distance = away;
        }
    }

    best
}

/// ρ over the indices `(low, middle, high)`, or `None` when the lower span does not rise.
fn difference_ratio(values: &[f64], (low, middle, high): (usize, usize, usize)) -> Option<f64> {
    let lower = values[middle] - values[low];
    let upper = values[high] - values[middle];

    (lower > 0.0).then_some(upper / lower)
}

/// Fits the growth order of `ys` against `xs` (strictly increasing program sizes) per the module's method.
pub fn fit(xs: &[f64], ys: &[f64]) -> Option<Order> {
    let count = xs.len();

    if count != ys.len()
        || count < MINIMUM_POINTS
        || xs.windows(2).any(|pair| pair[0] >= pair[1])
        || xs[0] <= 1.0
    {
        return None;
    }

    let largest = ys.iter().fold(0.0f64, |most, y| most.max(y.abs()));
    let (low, high) = ys
        .iter()
        .fold((f64::INFINITY, f64::NEG_INFINITY), |(low, high), &y| {
            (low.min(y), high.max(y))
        });

    if high - low <= CONSTANT_TOLERANCE * largest {
        return Some(Order::Constant);
    }

    let last = count - 1;
    let middle = last / 2;

    if ys[last] <= ys[middle] {
        return Some(Order::Constant);
    }

    for indices in [(0, middle, last), (last - 2, last - 1, last)] {
        if let Some(observed) = difference_ratio(ys, indices) {
            let statistic = |order: Order| {
                let gs: Vec<f64> = xs.iter().map(|&x| order.at(x)).collect();

                difference_ratio(&gs, indices).expect("every growing candidate rises")
            };

            return Some(nearest(observed, &GROWING, statistic));
        }
    }

    if ys[last - 1] <= 0.0 {
        return None;
    }

    let observed = ys[last] / ys[last - 1];
    let mut candidates = vec![Order::Constant];

    candidates.extend(GROWING);

    Some(nearest(observed, &candidates, |order| {
        order.at(xs[last]) / order.at(xs[last - 1])
    }))
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct Size {
    pub k: u32,
    pub n: usize,
    pub nodes: u64,
    /// The scheduler events this run flagged exhausted or drove to their work limit; their counts, and every count
    /// downstream of them, read the limit instead of olint's unbounded work from this size on.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub exhausted: Vec<String>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct Metric {
    /// One value per successful size, in size order.
    pub values: Vec<u64>,
    pub order: Option<Order>,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq)]
pub struct PassScale {
    /// The largest k that succeeded, when any did.
    pub max_k: Option<u32>,
    /// The first size that failed, and why.
    pub failure: Option<String>,
    /// The smallest k at which a scheduler work limit was exhausted.
    pub exhausted_k: Option<u32>,
    pub sizes: Vec<Size>,
    pub metrics: BTreeMap<String, Metric>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct FamilyScale {
    pub shape: String,
    pub passes: BTreeMap<String, PassScale>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct ScaleFile {
    pub schema: u32,
    pub source: String,
    pub min_k: u32,
    pub max_k: u32,
    pub families: BTreeMap<String, FamilyScale>,
}

pub struct ScaleArgs {
    pub src: String,
    pub family: Option<String>,
    pub min_k: u32,
    pub max_k: u32,
    pub out: Option<PathBuf>,
    pub jobs: usize,
    pub timeout: Duration,
}

/// Every recorded metric of one run, by name.
fn metrics_of(counts: &MemberCounts) -> BTreeMap<String, u64> {
    let mut metrics = BTreeMap::new();

    for (event, value) in &counts.events {
        metrics.insert(event.clone(), value.as_u64().unwrap_or_default());
    }

    metrics.insert("nodes".to_string(), counts.nodes.unwrap_or_default());
    metrics.insert("rows".to_string(), counts.rows as u64);
    metrics.insert("tasks".to_string(), counts.tasks as u64);
    metrics.insert(
        "maximum_body_passes".to_string(),
        counts.maximum_body_passes,
    );
    metrics.insert(
        "peak_bytes".to_string(),
        counts.peak_bytes.unwrap_or_default(),
    );

    if let Some(tsc) = &counts.tsc {
        for (name, value) in [
            ("rounds", tsc.rounds as u64),
            ("sites", tsc.sites as u64),
            ("programs", tsc.programs),
            ("checkers", tsc.checkers),
            ("indexed_files", tsc.indexed_files),
            ("indexed_nodes", tsc.indexed_nodes),
            ("lookups", tsc.lookups),
            ("visited_nodes", tsc.visited_nodes),
        ] {
            metrics.insert(format!("tsc.{name}"), value);
        }
    }

    metrics
}

/// The events a run flagged exhausted or drove to their scheduler limit, sorted and unique.
fn limited(counts: &MemberCounts) -> Vec<String> {
    let mut events: Vec<String> = counts
        .exhausted
        .iter()
        .chain(&counts.at_limit)
        .cloned()
        .collect();

    events.sort();
    events.dedup();

    events
}

/// Builds one family and pass's record from its runs in size order, stopping at the first failure.
pub fn pass_scale(runs: &[(u32, Result<MemberCounts, String>)]) -> PassScale {
    let mut scale = PassScale::default();
    let mut series: BTreeMap<String, Vec<u64>> = BTreeMap::new();

    for (k, run) in runs {
        let counts = match run {
            Ok(counts) if counts.error.is_none() => counts,
            Ok(counts) => {
                scale.failure = Some(format!(
                    "k={k}: {}",
                    counts.error.clone().unwrap_or_default()
                ));

                break;
            }
            Err(error) => {
                scale.failure = Some(format!("k={k}: {error}"));

                break;
            }
        };

        scale.max_k = Some(*k);

        scale.sizes.push(Size {
            k: *k,
            n: families::size_of(*k),
            nodes: counts.nodes.unwrap_or_default(),
            exhausted: limited(counts),
        });

        if !limited(counts).is_empty() && scale.exhausted_k.is_none() {
            scale.exhausted_k = Some(*k);
        }

        for (name, value) in metrics_of(counts) {
            series.entry(name).or_default().push(value);
        }
    }

    let xs: Vec<f64> = scale.sizes.iter().map(|size| size.nodes as f64).collect();

    for (name, values) in series {
        let ys: Vec<f64> = values.iter().map(|&value| value as f64).collect();
        let order = match values.len() == xs.len() {
            true => fit(&xs, &ys),
            false => None,
        };

        scale.metrics.insert(name, Metric { values, order });
    }

    scale
}

fn selected(family: Option<&str>) -> Result<Vec<&'static Family>, String> {
    match family {
        None => Ok(FAMILIES.iter().collect()),
        Some(name) => families::family(name)
            .map(|family| vec![family])
            .ok_or_else(|| {
                let names: Vec<&str> = FAMILIES.iter().map(|family| family.name).collect();

                format!("unknown family {name}; families are {}", names.join(", "))
            }),
    }
}

struct Task {
    family: &'static Family,
    k: u32,
    pass: Pass,
    root: PathBuf,
}

type Outcome = Result<MemberCounts, String>;

pub fn scale(args: ScaleArgs) -> Result<(), String> {
    if args.min_k > args.max_k || args.max_k > 24 {
        return Err(format!(
            "--min-k {} and --max-k {} must satisfy min <= max <= 24",
            args.min_k, args.max_k
        ));
    }

    let chosen = selected(args.family.as_deref())?;
    let corpus = head_corpus();
    let repo = corpus
        .parent()
        .expect("the corpus package sits in the olint tree");
    let cache = corpus.join(".cache");
    let source = materialize(&args.src, repo, &cache)?;
    let binary = build(&source, &cache)?;
    let out = match args.out {
        Some(out) => absolute(&out)?,
        None => cache.join("scale").join(format!("{}.json", source.key)),
    };
    let runs = out.with_extension("");
    let mut tasks = Vec::new();

    // Sizes run smallest first, so a failed size can cancel the larger ones of its family and pass.
    for k in args.min_k..=args.max_k {
        for &family in &chosen {
            let root = families::ensure(&cache, family, families::size_of(k))?;

            for pass in PASSES {
                tasks.push(Task {
                    family,
                    k,
                    pass,
                    root: root.clone(),
                });
            }
        }
    }

    let next = AtomicUsize::new(0);
    let results: Mutex<BTreeMap<(&'static str, Pass, u32), Outcome>> = Mutex::new(BTreeMap::new());
    let timings: Mutex<BTreeMap<(&'static str, Pass, u32), f64>> = Mutex::new(BTreeMap::new());
    let started = Instant::now();

    eprintln!(
        "scale {} runs of {} families into {}",
        tasks.len(),
        chosen.len(),
        out.display()
    );

    std::thread::scope(|scope| {
        for _ in 0..args.jobs.max(1) {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, Ordering::Relaxed);
                let Some(task) = tasks.get(index) else {
                    break;
                };
                let earlier_failed = results.lock().expect("results lock").iter().any(
                    |((family, pass, k), outcome)| {
                        *family == task.family.name
                            && *pass == task.pass
                            && *k < task.k
                            && outcome
                                .as_ref()
                                .map_or(true, |counts| counts.error.is_some())
                    },
                );

                if earlier_failed {
                    continue;
                }

                let begun = Instant::now();
                let member = Member {
                    id: format!("{}/{}", task.family.name, families::size_of(task.k)),
                    root: task.root.clone(),
                };
                let counts = run_member(
                    &binary,
                    &source.tree,
                    &runs,
                    task.pass,
                    &member,
                    args.timeout,
                    None,
                );
                let seconds = begun.elapsed().as_secs_f64();
                let outcome = match &counts.error {
                    Some(error) if counts.nodes.is_none() => Err(error.clone()),
                    _ => Ok(counts),
                };

                eprintln!(
                    "[{}/{}] {} {} k={}: {}{} in {seconds:.1}s",
                    index + 1,
                    tasks.len(),
                    task.pass.name(),
                    task.family.name,
                    task.k,
                    outcome
                        .as_ref()
                        .map_or(0, |counts| counts.nodes.unwrap_or_default()),
                    match &outcome {
                        Ok(counts) => counts
                            .error
                            .as_ref()
                            .map(|error| format!(" nodes, error: {error}"))
                            .unwrap_or(" nodes".to_string()),
                        Err(error) => format!(" nodes, error: {error}"),
                    },
                );
                timings
                    .lock()
                    .expect("timings lock")
                    .insert((task.family.name, task.pass, task.k), seconds);
                results
                    .lock()
                    .expect("results lock")
                    .insert((task.family.name, task.pass, task.k), outcome);
            });
        }
    });

    let results = results.into_inner().expect("results lock");
    let mut file = ScaleFile {
        schema: SCHEMA,
        source: source.key.clone(),
        min_k: args.min_k,
        max_k: args.max_k,
        families: BTreeMap::new(),
    };

    for &family in &chosen {
        let mut passes = BTreeMap::new();

        for pass in PASSES {
            let runs: Vec<(u32, Outcome)> = results
                .iter()
                .filter(|((name, run, _), _)| *name == family.name && *run == pass)
                .map(|((_, _, k), outcome)| (*k, outcome.clone()))
                .collect();

            passes.insert(pass.name().to_string(), pass_scale(&runs));
        }

        file.families.insert(
            family.name.to_string(),
            FamilyScale {
                shape: family.shape.to_string(),
                passes,
            },
        );
    }

    let text = serde_json::to_string_pretty(&file).expect("scale serializes");
    let parent = out.parent().expect("the scale file has a parent");

    std::fs::create_dir_all(parent)
        .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
    std::fs::write(&out, text + "\n")
        .map_err(|error| format!("cannot write {}: {error}", out.display()))?;

    let timings = timings.into_inner().expect("timings lock");
    let mut timing_text = String::new();

    for ((family, pass, k), seconds) in &timings {
        let _ = writeln!(timing_text, "{family} {} k={k} {seconds:.1}s", pass.name());
    }

    let timing_path = runs.join("timings.txt");

    std::fs::create_dir_all(&runs)
        .map_err(|error| format!("cannot create {}: {error}", runs.display()))?;
    std::fs::write(&timing_path, timing_text)
        .map_err(|error| format!("cannot write {}: {error}", timing_path.display()))?;

    print!("{}", render(&file));
    eprintln!("scale finished in {:.1}s", started.elapsed().as_secs_f64());

    Ok(())
}

/// A text table of every family and pass's fitted orders.
pub fn render(file: &ScaleFile) -> String {
    let mut text = String::new();

    for (name, family) in &file.families {
        for (pass, scale) in &family.passes {
            let reached = scale.max_k.map_or("none".to_string(), |k| k.to_string());
            let _ = writeln!(
                text,
                "{name} {pass}: max k {reached}{}",
                scale
                    .failure
                    .as_ref()
                    .map(|failure| format!(" (failed {failure})"))
                    .unwrap_or_default()
            );

            if let Some(k) = scale.exhausted_k {
                let _ = writeln!(
                    text,
                    "  work limits exhausted from k={k}: counts from there read the limits"
                );
            }

            for (metric, fitted) in &scale.metrics {
                let _ = writeln!(
                    text,
                    "  {metric}: {}",
                    fitted.order.map_or("no fit", Order::text)
                );
            }
        }
    }

    text
}

/// §5.3: every family, pass and compared metric whose fitted order is higher in `head` than in `base`, every family
/// and pass that failed deterministically (not by timeout) at a smaller size in `head`, and every one that reached a
/// scheduler work limit at a smaller size.
pub fn raised_orders(base: &ScaleFile, head: &ScaleFile) -> Vec<String> {
    let mut problems = Vec::new();

    if (base.min_k, base.max_k) != (head.min_k, head.max_k) {
        problems.push(format!(
            "scaling runs cover different sizes: base k={}..={}, head k={}..={}",
            base.min_k, base.max_k, head.min_k, head.max_k
        ));
    }

    for (name, before) in &base.families {
        let Some(after) = head.families.get(name) else {
            problems.push(format!("scaling family {name} is missing from head"));

            continue;
        };

        for (pass, old) in &before.passes {
            let Some(new) = after.passes.get(pass) else {
                continue;
            };

            // A timeout measures wall-clock time, which §7.5 leaves out, so only a deterministic failure counts here.
            let timed_out = new
                .failure
                .as_ref()
                .is_some_and(|failure| failure.contains("timed out"));

            if new.max_k < old.max_k && !timed_out {
                problems.push(format!(
                    "{name} {pass}: head reaches k={} where base reached k={}",
                    new.max_k.map_or("none".to_string(), |k| k.to_string()),
                    old.max_k.map_or("none".to_string(), |k| k.to_string())
                ));
            }

            let never = |k: Option<u32>| k.unwrap_or(u32::MAX);

            if never(new.exhausted_k) < never(old.exhausted_k) {
                problems.push(format!(
                    "{name} {pass}: head exhausts a scheduler work limit at k={} where base {}",
                    never(new.exhausted_k),
                    old.exhausted_k
                        .map_or("never did".to_string(), |k| format!("did at k={k}"))
                ));
            }

            for (metric, prior) in &old.metrics {
                if UNCOMPARED.contains(&metric.as_str()) {
                    continue;
                }

                let (Some(was), Some(now)) = (
                    prior.order,
                    new.metrics.get(metric).and_then(|metric| metric.order),
                ) else {
                    continue;
                };

                if now > was {
                    problems.push(format!(
                        "{name} {pass} {metric}: growth order rose from {} to {}",
                        was.text(),
                        now.text()
                    ));
                }
            }
        }
    }

    problems
}

pub fn read_scale(path: &Path) -> Result<ScaleFile, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let file: ScaleFile = serde_json::from_str(&text)
        .map_err(|error| format!("{} is malformed: {error}", path.display()))?;

    match file.schema == SCHEMA {
        true => Ok(file),
        false => Err(format!(
            "{} has scale schema {}, expected {SCHEMA}",
            path.display(),
            file.schema
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sizes(scale: f64, offset: f64) -> Vec<f64> {
        (6..=14)
            .map(|k| scale * f64::from(1u32 << k) + offset)
            .collect()
    }

    fn through(xs: &[f64], f: impl Fn(f64) -> f64) -> Vec<f64> {
        xs.iter().map(|&x| f(x)).collect()
    }

    #[test]
    fn exact_candidates_fit_themselves() {
        for xs in [sizes(1.0, 0.0), sizes(3.0, 17.0)] {
            for order in [
                Order::Log,
                Order::Linear,
                Order::Linearithmic,
                Order::Quadratic,
                Order::Cubic,
                Order::AboveCubic,
            ] {
                let ys = through(&xs, |x| 5.0 * order.at(x));

                assert_eq!(fit(&xs, &ys), Some(order), "{order:?}");
            }

            assert_eq!(fit(&xs, &through(&xs, |_| 42.0)), Some(Order::Constant));
        }
    }

    #[test]
    fn additive_constants_and_lower_terms_leave_the_order() {
        let xs = sizes(1.0, 0.0);

        assert_eq!(
            fit(&xs, &through(&xs, |x| x + 10_000.0)),
            Some(Order::Linear)
        );
        assert_eq!(fit(&xs, &through(&xs, |x| x.ln() + 50.0)), Some(Order::Log));
        assert_eq!(
            fit(&xs, &through(&xs, |x| x * x.ln() - 5.0 * x)),
            Some(Order::Linearithmic)
        );
        assert_eq!(
            fit(&xs, &through(&xs, |x| x * x + 1000.0 * x)),
            Some(Order::Quadratic)
        );
        assert_eq!(
            fit(&xs, &through(&xs, |x| 2.0 * x + 3.0 * x.ln() + 7.0)),
            Some(Order::Linear)
        );
        assert_eq!(
            fit(&xs, &through(&xs, |x| x * x * x + x * x)),
            Some(Order::Cubic)
        );
    }

    #[test]
    fn small_noise_leaves_the_order() {
        let xs = sizes(1.0, 0.0);
        let jitter = [0.0, 3.0, -2.0, 1.0, 0.0, -3.0, 2.0, 1.0, -1.0];
        let noisy = |f: &dyn Fn(f64) -> f64| -> Vec<f64> {
            xs.iter()
                .zip(jitter)
                .map(|(&x, noise)| f(x) + noise)
                .collect()
        };

        assert_eq!(fit(&xs, &noisy(&|_| 5_000_000.0)), Some(Order::Constant));
        assert_eq!(fit(&xs, &noisy(&|x| 40.0 * x)), Some(Order::Linear));
        assert_eq!(
            fit(&xs, &noisy(&|x| 40.0 * x * x.ln())),
            Some(Order::Linearithmic)
        );
        assert_eq!(fit(&xs, &noisy(&|x| x * x)), Some(Order::Quadratic));
    }

    #[test]
    fn edges() {
        let xs = sizes(1.0, 0.0);

        assert_eq!(fit(&xs, &[0.0; 9]), Some(Order::Constant));
        assert_eq!(
            fit(&xs, &[9.0, 8.0, 7.0, 6.0, 5.0, 4.0, 3.0, 2.0, 1.0]),
            Some(Order::Constant)
        );
        assert_eq!(
            fit(&xs, &[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5.0]),
            None
        );
        assert_eq!(fit(&xs[..3], &[1.0, 2.0, 3.0]), None);
        assert_eq!(
            fit(&[64.0, 64.0, 128.0, 256.0], &[1.0, 2.0, 3.0, 4.0]),
            None
        );

        let late: Vec<f64> = xs
            .iter()
            .enumerate()
            .map(|(index, &x)| if index < 6 { 0.0 } else { x })
            .collect();

        assert_eq!(fit(&xs, &late), Some(Order::Linear));
    }

    #[test]
    fn short_ranges_still_separate_n_from_n_log_n() {
        let xs: Vec<f64> = (6..=9).map(|k| f64::from(1u32 << k)).collect();

        assert_eq!(
            fit(&xs, &through(&xs, |x| 7.0 * x + 3.0)),
            Some(Order::Linear)
        );
        assert_eq!(
            fit(&xs, &through(&xs, |x| x * x.ln())),
            Some(Order::Linearithmic)
        );
    }

    fn file(order: Order, max_k: u32) -> ScaleFile {
        let pass = PassScale {
            max_k: Some(max_k),
            failure: None,
            exhausted_k: None,
            sizes: Vec::new(),
            metrics: BTreeMap::from([
                (
                    "WalkerNode".to_string(),
                    Metric {
                        values: Vec::new(),
                        order: Some(order),
                    },
                ),
                (
                    "nodes".to_string(),
                    Metric {
                        values: Vec::new(),
                        order: Some(order),
                    },
                ),
            ]),
        };

        ScaleFile {
            schema: SCHEMA,
            source: "s".to_string(),
            min_k: 6,
            max_k: 14,
            families: BTreeMap::from([(
                "flat".to_string(),
                FamilyScale {
                    shape: String::new(),
                    passes: BTreeMap::from([("syntactic".to_string(), pass)]),
                },
            )]),
        }
    }

    #[test]
    fn raised_orders_fail_and_equal_or_lower_orders_pass() {
        assert!(raised_orders(&file(Order::Linear, 14), &file(Order::Linear, 14)).is_empty());
        assert!(raised_orders(&file(Order::Quadratic, 14), &file(Order::Linear, 14)).is_empty());

        let raised = raised_orders(&file(Order::Linear, 14), &file(Order::Linearithmic, 14));

        assert_eq!(
            raised,
            vec!["flat syntactic WalkerNode: growth order rose from n to n log n".to_string()]
        );
        assert_eq!(
            raised_orders(&file(Order::Linear, 14), &file(Order::Linear, 12)).len(),
            1
        );

        let mut timed_out = file(Order::Linear, 12);

        for family in timed_out.families.values_mut() {
            for pass in family.passes.values_mut() {
                pass.failure = Some("k=13: timed out after 900s".to_string());
            }
        }

        assert!(raised_orders(&file(Order::Linear, 14), &timed_out).is_empty());
    }

    #[test]
    fn a_failed_size_ends_the_series() {
        let counts = |nodes: u64| MemberCounts {
            nodes: Some(nodes),
            ..MemberCounts::default()
        };
        let scale = pass_scale(&[
            (6, Ok(counts(100))),
            (7, Ok(counts(200))),
            (8, Err("timed out".to_string())),
            (9, Ok(counts(800))),
        ]);

        assert_eq!(scale.max_k, Some(7));
        assert_eq!(scale.sizes.len(), 2);
        assert_eq!(scale.failure.as_deref(), Some("k=8: timed out"));
        assert_eq!(scale.metrics["nodes"].values, vec![100, 200]);
        assert_eq!(scale.exhausted_k, None);
    }

    #[test]
    fn exhausted_limits_are_recorded_and_compared() {
        let counts = |exhausted: &[&str]| MemberCounts {
            nodes: Some(100),
            exhausted: exhausted.iter().map(|event| event.to_string()).collect(),
            ..MemberCounts::default()
        };
        let scale = pass_scale(&[(6, Ok(counts(&[]))), (7, Ok(counts(&["TaskKey"])))]);

        assert_eq!(scale.exhausted_k, Some(7));
        assert_eq!(scale.sizes[1].exhausted, vec!["TaskKey".to_string()]);

        let base = file(Order::Linear, 14);
        let mut head = base.clone();

        for family in head.families.values_mut() {
            for pass in family.passes.values_mut() {
                pass.exhausted_k = Some(12);
            }
        }

        assert_eq!(raised_orders(&base, &head).len(), 1);
        assert!(raised_orders(&head, &base).is_empty());
    }
}

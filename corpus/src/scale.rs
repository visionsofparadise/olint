//! `scale` measures how olint's work and memory grow on the scaling families (spec §7.5).
//!
//! It materializes and builds `--src` as `snapshot` does, generates each family at n = 2^k for k in
//! `--min-k..=--max-k`, and snapshots every size and pass in its own `snapshot-member` subprocess. Each run records
//! |G| (`MemberCounts::nodes`), the 26 scheduler `Event` counts, the scheduler task and body-pass counts, peak live
//! bytes from the counting allocator and, in the tsc pass, the checker's `TscCounts`. A size that fails or times out
//! ends that family and pass: larger sizes are skipped, and the fit uses the sizes below it.
//!
//! A size whose run exhausted or reached a scheduler work limit reads the limit instead of olint's unbounded work, so
//! it and every larger size are left out of the fits; `exhausted_k` records where that began.
//!
//! # Fitting
//!
//! Each metric y is fitted against x = |G| over every fitted size, using counts only, never wall-clock time. The
//! candidates are 1, log n, n, n log n, n², n³ and "above n³" (n⁴):
//!
//! 1. **Constant.** When max y − min y is at most `CONSTANT_TOLERANCE` of max |y|, or y does not rise from the middle
//!    size to the last, the order is 1.
//! 2. **Leading zeros.** Sizes before the first positive y are dropped; fewer than `MINIMUM_POINTS` remaining sizes
//!    have no fit.
//! 3. **Models.** Each candidate g is a least-squares model over g, the two candidates below it (log n and above)
//!    and a constant, capped at one parameter fewer than the sizes, fitted with each residual taken relative to y so
//!    the smallest sizes weigh as much as the largest. R_g is the model's root-mean-square relative residual.
//! 4. **Order.** The order is the lowest candidate whose leading coefficient is positive (for 1, any) and whose
//!    R_g ≤ `FIT_TOLERANCE` + `FIT_RATIO` · min R. The absolute part rejects a lower order that only approximates
//!    the data, such as n for x ln x + 50x; the relative part keeps step-shaped counts (allocation doubling) at the
//!    order every model fits equally badly.
//! 5. **Ambiguity.** When R of the order exceeds half of `FIT_TOLERANCE`, the fit is marginal, and `upper` is the lowest
//!    higher candidate whose R is at most half of the order's; otherwise `upper` is the order. §5.3 fails a head whose
//!    order or upper is higher than the base's.
//!
//! The fit is fixed floating-point arithmetic (Householder least squares) on the recorded integers followed by fixed
//! comparisons, so it is deterministic. A class off the candidate list reads as the nearest candidate that fits it
//! (n log² n as n log n).
//!
//! The result is `corpus/.cache/scale/<sha>.json`, which `diff` compares under §5.3.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::families::{self, Family, FAMILIES};
use crate::members::Member;
use crate::snapshot::{
    absolute, built, in_parallel, run_member, Built, MemberCounts, Pass, PASSES,
};

/// Scale file schema. Version 2 adds each metric's `upper` order and excludes limit-reading sizes from the fits.
pub const SCHEMA: u32 = 2;
/// The largest spread of y, as a fraction of max |y|, that still reads as constant.
pub const CONSTANT_TOLERANCE: f64 = 0.005;
/// The root-mean-square relative residual below which a model fits regardless of the others.
pub const FIT_TOLERANCE: f64 = 0.002;
/// How many times the best model's residual a lower model may have and still fit.
pub const FIT_RATIO: f64 = 2.0;
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

/// Every candidate, lowest order first.
const CANDIDATES: [Order; 7] = [
    Order::Constant,
    Order::Log,
    Order::Linear,
    Order::Linearithmic,
    Order::Quadratic,
    Order::Cubic,
    Order::AboveCubic,
];

/// A fitted growth order and the highest order the data leaves plausible.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fit {
    pub order: Order,
    pub upper: Order,
}

impl Fit {
    fn exact(order: Order) -> Fit {
        Fit {
            order,
            upper: order,
        }
    }
}

/// Reflects `vector` from index `from` on through the Householder `reflector` of squared length `length`.
fn reflect(vector: &mut [f64], reflector: &[f64], from: usize, length: f64) {
    let scale = 2.0
        * vector[from..]
            .iter()
            .zip(&reflector[from..])
            .map(|(value, direction)| value * direction)
            .sum::<f64>()
        / length;

    for (value, direction) in vector[from..].iter_mut().zip(&reflector[from..]) {
        *value -= scale * direction;
    }
}

/// Solves the least-squares problem `A · coefficients ≈ target` by Householder reflections, where `columns` holds A
/// column by column; `None` when the columns are dependent.
fn least_squares(mut columns: Vec<Vec<f64>>, mut target: Vec<f64>) -> Option<Vec<f64>> {
    let count = columns.len();

    for column in 0..count {
        let norm = columns[column][column..]
            .iter()
            .map(|value| value * value)
            .sum::<f64>()
            .sqrt();

        if norm == 0.0 {
            return None;
        }

        let alpha = match columns[column][column] > 0.0 {
            true => -norm,
            false => norm,
        };
        let mut reflector = columns[column].clone();

        reflector[..column].fill(0.0);

        reflector[column] -= alpha;

        let length: f64 = reflector.iter().map(|value| value * value).sum();

        if length == 0.0 {
            continue;
        }

        for other in columns.iter_mut().skip(column) {
            reflect(other, &reflector, column, length);
        }

        reflect(&mut target, &reflector, column, length);
    }

    let mut solution = vec![0.0; count];

    for column in (0..count).rev() {
        let pivot = columns[column][column];

        if pivot.abs() < f64::MIN_POSITIVE {
            return None;
        }

        let known: f64 = (column + 1..count)
            .map(|other| columns[other][column] * solution[other])
            .sum();

        solution[column] = (target[column] - known) / pivot;
    }

    Some(solution)
}

/// The terms of candidate `index`'s model: the candidate, up to two candidates below it (log n and above), then the
/// constant, with at most `points − 1` terms in all.
fn terms_of(index: usize, points: usize) -> Vec<Order> {
    if index == 0 {
        return vec![Order::Constant];
    }

    let mut terms: Vec<Order> = (1..=index)
        .rev()
        .take(3)
        .map(|lower| CANDIDATES[lower])
        .collect();

    terms.truncate(points.saturating_sub(2).max(1));
    terms.push(Order::Constant);

    terms
}

/// Fits candidate `index`'s model and returns its root-mean-square relative residual and leading coefficient.
fn residual_of(index: usize, xs: &[f64], ys: &[f64]) -> (f64, f64) {
    let terms = terms_of(index, xs.len());
    let columns: Vec<Vec<f64>> = terms
        .iter()
        .map(|term| xs.iter().map(|&x| term.at(x)).collect())
        .collect();
    let scales: Vec<f64> = columns
        .iter()
        .map(|column| {
            column
                .iter()
                .fold(0.0f64, |most, value| most.max(value.abs()))
        })
        .collect();
    let weights: Vec<f64> = ys.iter().map(|&y| 1.0 / y.max(1.0)).collect();
    let matrix: Vec<Vec<f64>> = columns
        .iter()
        .zip(&scales)
        .map(|(column, scale)| {
            column
                .iter()
                .zip(&weights)
                .map(|(value, weight)| value / scale * weight)
                .collect()
        })
        .collect();
    let target: Vec<f64> = (0..xs.len()).map(|row| ys[row] * weights[row]).collect();
    let Some(solution) = least_squares(matrix, target) else {
        return (f64::INFINITY, 0.0);
    };
    let coefficients: Vec<f64> = solution
        .iter()
        .zip(&scales)
        .map(|(value, scale)| value / scale)
        .collect();
    let squares: f64 = (0..xs.len())
        .map(|row| {
            let model: f64 = (0..terms.len())
                .map(|column| coefficients[column] * columns[column][row])
                .sum();

            ((ys[row] - model) * weights[row]).powi(2)
        })
        .sum();

    ((squares / xs.len() as f64).sqrt(), coefficients[0])
}

/// Fits the growth order of `ys` against `xs` (strictly increasing program sizes) per the module's method.
pub fn fit(xs: &[f64], ys: &[f64]) -> Option<Fit> {
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

    if high - low <= CONSTANT_TOLERANCE * largest || ys[count - 1] <= ys[(count - 1) / 2] {
        return Some(Fit::exact(Order::Constant));
    }

    let first = ys.iter().position(|&y| y > 0.0)?;
    let (xs, ys) = (&xs[first..], &ys[first..]);

    if xs.len() < MINIMUM_POINTS {
        return None;
    }

    let models: Vec<(f64, f64)> = (0..CANDIDATES.len())
        .map(|index| residual_of(index, xs, ys))
        .collect();
    let best = models
        .iter()
        .fold(f64::INFINITY, |least, (residual, _)| least.min(*residual));
    let admissible = |index: usize, bar: f64| {
        let (residual, leading) = models[index];

        residual <= bar && (index == 0 || leading > 0.0)
    };
    let order =
        (0..CANDIDATES.len()).find(|&index| admissible(index, FIT_TOLERANCE + FIT_RATIO * best))?;
    let residual = models[order].0;
    let upper = match residual > FIT_TOLERANCE / 2.0 {
        true => (order + 1..CANDIDATES.len())
            .find(|&index| admissible(index, residual / 2.0))
            .unwrap_or(order),
        false => order,
    };

    Some(Fit {
        order: CANDIDATES[order],
        upper: CANDIDATES[upper],
    })
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
    /// One value per successful size, in size order, limit-reading sizes included.
    pub values: Vec<u64>,
    /// The fitted order over the sizes below `exhausted_k`.
    pub order: Option<Order>,
    /// The highest order the fit leaves plausible, equal to `order` unless the fit is marginal.
    #[serde(default)]
    pub upper: Option<Order>,
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

    // Sizes at and after the first limit-reading size count the limit, not olint's work, so the fit leaves them out.
    let fitted = scale
        .sizes
        .iter()
        .take_while(|size| size.exhausted.is_empty())
        .count();
    let xs: Vec<f64> = scale.sizes[..fitted]
        .iter()
        .map(|size| size.nodes as f64)
        .collect();

    for (name, values) in series {
        let ys: Vec<f64> = values[..fitted.min(values.len())]
            .iter()
            .map(|&value| value as f64)
            .collect();
        let fitted = match values.len() == scale.sizes.len() {
            true => fit(&xs, &ys),
            false => None,
        };

        scale.metrics.insert(
            name,
            Metric {
                values,
                order: fitted.map(|fit| fit.order),
                upper: fitted.map(|fit| fit.upper),
            },
        );
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
    let Built {
        cache,
        source,
        binary,
    } = built(&args.src)?;
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

    let results: Mutex<BTreeMap<(&'static str, Pass, u32), Outcome>> = Mutex::new(BTreeMap::new());
    let timings: Mutex<BTreeMap<(&'static str, Pass, u32), f64>> = Mutex::new(BTreeMap::new());
    let started = Instant::now();

    eprintln!(
        "scale {} runs of {} families into {}",
        tasks.len(),
        chosen.len(),
        out.display()
    );

    in_parallel(&tasks, args.jobs, |index, task| {
        let earlier_failed =
            results
                .lock()
                .expect("results lock")
                .iter()
                .any(|((family, pass, k), outcome)| {
                    *family == task.family.name
                        && *pass == task.pass
                        && *k < task.k
                        && outcome
                            .as_ref()
                            .map_or(true, |counts| counts.error.is_some())
                });

        if earlier_failed {
            return;
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
                let upper = match (fitted.order, fitted.upper) {
                    (Some(order), Some(upper)) if upper != order => {
                        format!(" (marginal, up to {})", upper.text())
                    }
                    _ => String::new(),
                };
                let _ = writeln!(
                    text,
                    "  {metric}: {}{upper}",
                    fitted.order.map_or("no fit", Order::text)
                );
            }
        }
    }

    text
}

/// §5.3, comparing `head` against `base` conservatively:
///
/// - a family or pass missing from `head` fails;
/// - a head that reaches a smaller k, or fewer sizes, fails, whatever ended it: a timeout is wall-clock time, which
///   §7.5 leaves out, so it cannot excuse a shorter series;
/// - a head that reaches a scheduler work limit at a smaller k fails;
/// - per compared metric, a head order or upper order above the base's fails; a metric fitted on one side only, or
///   missing from the head, fails; a metric fitted on neither side fails unless both sides recorded identical values.
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
                problems.push(format!("{name} {pass}: missing from head"));

                continue;
            };

            if new.max_k < old.max_k || new.sizes.len() < old.sizes.len() {
                problems.push(format!(
                    "{name} {pass}: head reaches k={} over {} sizes where base reached k={} over {}{}",
                    new.max_k.map_or("none".to_string(), |k| k.to_string()),
                    new.sizes.len(),
                    old.max_k.map_or("none".to_string(), |k| k.to_string()),
                    old.sizes.len(),
                    new.failure
                        .as_ref()
                        .map(|failure| format!(" (head failed {failure})"))
                        .unwrap_or_default()
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

                let Some(current) = new.metrics.get(metric) else {
                    problems.push(format!("{name} {pass} {metric}: missing from head"));

                    continue;
                };

                match (prior.order, current.order) {
                    (Some(was), Some(now)) => {
                        let upper = |metric: &Metric, order: Order| metric.upper.unwrap_or(order);

                        if now > was {
                            problems.push(format!(
                                "{name} {pass} {metric}: growth order rose from {} to {}",
                                was.text(),
                                now.text()
                            ));
                        } else if upper(current, now) > upper(prior, was) {
                            problems.push(format!(
                                "{name} {pass} {metric}: the head fit is marginal and could be {} where the base is at most {}",
                                upper(current, now).text(),
                                upper(prior, was).text()
                            ));
                        }
                    }
                    (None, None) if prior.values == current.values => {}
                    (was, now) => problems.push(format!(
                        "{name} {pass} {metric}: no comparable fit (base {}, head {}); a missing fit cannot show the order held",
                        was.map_or("no fit", Order::text),
                        now.map_or("no fit", Order::text)
                    )),
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

    fn order_of(xs: &[f64], ys: &[f64]) -> Option<Order> {
        fit(xs, ys).map(|fit| fit.order)
    }

    #[test]
    fn exact_candidates_fit_themselves() {
        for xs in [sizes(1.0, 0.0), sizes(3.0, 17.0), sizes(20.0, 0.0)] {
            for order in CANDIDATES[1..].iter().copied() {
                let ys = through(&xs, |x| 5.0 * order.at(x));

                assert_eq!(fit(&xs, &ys), Some(Fit::exact(order)), "{order:?}");
            }

            assert_eq!(
                order_of(&xs, &through(&xs, |_| 42.0)),
                Some(Order::Constant)
            );
        }
    }

    #[test]
    fn additive_constants_and_lower_terms_leave_the_order() {
        let xs = sizes(1.0, 0.0);

        assert_eq!(
            order_of(&xs, &through(&xs, |x| x + 10_000.0)),
            Some(Order::Linear)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x.ln() + 50.0)),
            Some(Order::Log)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x * x.ln() - 5.0 * x)),
            Some(Order::Linearithmic)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x * x + 1000.0 * x)),
            Some(Order::Quadratic)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| 2.0 * x + 3.0 * x.ln() + 7.0)),
            Some(Order::Linear)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x * x * x + x * x)),
            Some(Order::Cubic)
        );
    }

    #[test]
    fn dominant_lower_terms_leave_the_order_at_twenty_nodes_per_n() {
        let xs = sizes(20.0, 0.0);

        for linear in [10.0, 50.0] {
            assert_eq!(
                fit(&xs, &through(&xs, |x| x * x.ln() + linear * x)),
                Some(Fit::exact(Order::Linearithmic)),
                "x ln x + {linear}x"
            );
        }

        assert_eq!(
            fit(&xs, &through(&xs, |x| x * x + 5000.0 * x)),
            Some(Fit::exact(Order::Quadratic))
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x + 1e-6 * x * x)),
            Some(Order::Quadratic)
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

        assert_eq!(
            fit(&xs, &noisy(&|_| 5_000_000.0)),
            Some(Fit::exact(Order::Constant))
        );
        assert_eq!(
            fit(&xs, &noisy(&|x| 40.0 * x)),
            Some(Fit::exact(Order::Linear))
        );
        assert_eq!(
            fit(&xs, &noisy(&|x| 40.0 * x * x.ln())),
            Some(Fit::exact(Order::Linearithmic))
        );
        assert_eq!(
            fit(&xs, &noisy(&|x| x * x)),
            Some(Fit::exact(Order::Quadratic))
        );
    }

    #[test]
    fn step_shaped_counts_keep_their_order() {
        let xs = sizes(1.0, 0.0);
        let steps: Vec<f64> = xs
            .iter()
            .enumerate()
            .map(|(index, &x)| x * if index % 2 == 0 { 1.0 } else { 1.3 })
            .collect();

        assert_eq!(order_of(&xs, &steps), Some(Order::Linear));
    }

    #[test]
    fn edges() {
        let xs = sizes(1.0, 0.0);

        assert_eq!(order_of(&xs, &[0.0; 9]), Some(Order::Constant));
        assert_eq!(
            order_of(&xs, &[9.0, 8.0, 7.0, 6.0, 5.0, 4.0, 3.0, 2.0, 1.0]),
            Some(Order::Constant)
        );
        assert_eq!(
            order_of(&xs, &[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5.0]),
            None
        );
        assert_eq!(order_of(&xs[..3], &[1.0, 2.0, 3.0]), None);
        assert_eq!(
            order_of(&[64.0, 64.0, 128.0, 256.0], &[1.0, 2.0, 3.0, 4.0]),
            None
        );

        let late = |zeros: usize| -> Vec<f64> {
            xs.iter()
                .enumerate()
                .map(|(index, &x)| if index < zeros { 0.0 } else { x })
                .collect()
        };

        assert_eq!(order_of(&xs, &late(6)), None);
        assert_eq!(order_of(&xs, &late(3)), Some(Order::Linear));
    }

    #[test]
    fn short_ranges_still_separate_n_from_n_log_n() {
        let xs: Vec<f64> = (6..=9).map(|k| f64::from(1u32 << k)).collect();

        assert_eq!(
            order_of(&xs, &through(&xs, |x| 7.0 * x + 3.0)),
            Some(Order::Linear)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x * x.ln())),
            Some(Order::Linearithmic)
        );
        assert_eq!(
            order_of(&xs, &through(&xs, |x| x * x)),
            Some(Order::Quadratic)
        );
    }

    fn file(order: Order, max_k: u32) -> ScaleFile {
        let metric = Metric {
            values: Vec::new(),
            order: Some(order),
            upper: Some(order),
        };
        let pass = PassScale {
            max_k: Some(max_k),
            failure: None,
            exhausted_k: None,
            sizes: Vec::new(),
            metrics: BTreeMap::from([
                ("WalkerNode".to_string(), metric.clone()),
                ("nodes".to_string(), metric),
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

    fn edit(file: &mut ScaleFile, change: impl Fn(&mut PassScale)) {
        for family in file.families.values_mut() {
            for pass in family.passes.values_mut() {
                change(pass);
            }
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

        edit(&mut timed_out, |pass| {
            pass.failure = Some("k=13: timed out after 900s".to_string());
        });

        assert_eq!(raised_orders(&file(Order::Linear, 14), &timed_out).len(), 1);
    }

    #[test]
    fn marginal_and_missing_fits_fail() {
        let base = file(Order::Linear, 14);
        let mut marginal = base.clone();

        edit(&mut marginal, |pass| {
            pass.metrics.get_mut("WalkerNode").expect("metric").upper = Some(Order::Linearithmic);
        });

        assert_eq!(raised_orders(&base, &marginal).len(), 1);
        assert!(raised_orders(&marginal, &marginal).is_empty());

        let mut unfitted = base.clone();

        edit(&mut unfitted, |pass| {
            let metric = pass.metrics.get_mut("WalkerNode").expect("metric");

            metric.order = None;
            metric.upper = None;
        });

        assert_eq!(raised_orders(&base, &unfitted).len(), 1);
        assert!(raised_orders(&unfitted, &unfitted).is_empty());

        let mut different = unfitted.clone();

        edit(&mut different, |pass| {
            pass.metrics.get_mut("WalkerNode").expect("metric").values = vec![1];
        });

        assert_eq!(raised_orders(&unfitted, &different).len(), 1);

        let mut missing = base.clone();

        edit(&mut missing, |pass| {
            pass.metrics.remove("WalkerNode");
        });

        assert_eq!(raised_orders(&base, &missing).len(), 1);
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
    fn exhausted_limits_are_recorded_excluded_and_compared() {
        let counts = |nodes: u64, exhausted: &[&str]| MemberCounts {
            nodes: Some(nodes),
            exhausted: exhausted.iter().map(|event| event.to_string()).collect(),
            ..MemberCounts::default()
        };
        let runs: Vec<(u32, Outcome)> = (6..=11)
            .map(|k| {
                let nodes = 1u64 << k;

                (
                    k,
                    Ok(counts(nodes, if k >= 10 { &["TaskKey"] } else { &[] })),
                )
            })
            .collect();
        let scale = pass_scale(&runs);

        assert_eq!(scale.exhausted_k, Some(10));
        assert_eq!(scale.sizes[4].exhausted, vec!["TaskKey".to_string()]);
        assert_eq!(scale.metrics["nodes"].values.len(), 6);
        assert_eq!(scale.metrics["nodes"].order, Some(Order::Linear));

        let short = pass_scale(&runs[..5]);

        assert_eq!(short.metrics["nodes"].order, Some(Order::Linear));

        let base = file(Order::Linear, 14);
        let mut head = base.clone();

        edit(&mut head, |pass| pass.exhausted_k = Some(12));

        assert_eq!(raised_orders(&base, &head).len(), 1);
        assert!(raised_orders(&head, &base).is_empty());
    }
}

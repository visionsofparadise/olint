use crate::analysis::Analysis;
use crate::config::Config;
use crate::cost::{Cost, CostComparison, Part, State};
use crate::declarations::FunctionNode;
use crate::directives::cost_tag_of;
use crate::paths::relative_path_of;
use crate::project::{FileId, Project, Site};
use crate::public::PublicFunction;
use crate::trace::{RenderBudget, TraceArena, TraceId};
use crate::unknowns::{UnknownId, Unknowns};
use crate::values::Values;

fn padded_text_of(text: &str, width: usize) -> String {
    let length: usize = text.chars().map(char::len_utf16).sum();

    if length >= width {
        return text.to_string();
    }

    format!("{text}{}", " ".repeat(width - length))
}

fn location_of(project: &Project<'_>, site: Site) -> String {
    format!("{}:{}", project.file(site.file).relative, site.line)
}

pub fn chain_lines(
    values: &Values,
    traces: &TraceArena,
    project: &Project<'_>,
    trace: Option<TraceId>,
    depth: usize,
    out: &mut Vec<String>,
) {
    lines_of_chain(values, traces, trace, depth, out, &|site, out| {
        write!(out, "{}:{}", project.file(site.file).relative, site.line)
    });
}

fn lines_of_chain(
    values: &Values,
    traces: &TraceArena,
    trace: Option<TraceId>,
    depth: usize,
    out: &mut Vec<String>,
    location: &dyn Fn(Site, &mut dyn std::fmt::Write) -> std::fmt::Result,
) {
    let Some(trace) = trace else {
        return;
    };
    let rendered = crate::trace::render(
        traces,
        trace,
        depth,
        RenderBudget::default(),
        &|site, out| location(site, out),
        &|cost, call, out| cost.write_with(out, call, &|id, out| values.write_label(id, out)),
    );

    match rendered {
        Ok(rendered) => out.extend(rendered.text.lines().map(str::to_owned)),
        Err(_) => out.push(crate::trace::TRUNCATION_MARKER.trim_end().to_owned()),
    }
}

/// A report row: the bound, the floor or `unknown` (§4.7), the name, an `[asserted]` mark when the cost depends on
/// a `@perf` directive, the location, and a `[partial]` mark after a floor.
fn row_text_of(values: &Values, row: &ReportRow, location: &str) -> String {
    let cost = match row.state {
        State::Unknown => "unknown".to_string(),
        State::Known | State::Partial => row.cost.text_with(&|id| values.label(id)),
    };
    let asserted = if row.asserted { " [asserted]" } else { "" };
    let partial = if row.state == State::Partial {
        " [partial]"
    } else {
        ""
    };

    format!(
        "{} {}{asserted}  {location}{partial}",
        padded_text_of(&cost, 14),
        row.name
    )
}

/// Spec §4.1-§4.3: an entry's verdict against a limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The entry is Known and olint proves its bound at or below the limit.
    Within,
    /// olint proves the entry's bound or floor above the limit.
    Exceeds,
    Inconclusive,
}

/// The verdict of a reading against `limit`. A Known reading's cost is its bound, and any other reading's cost its
/// floor, the join of its proven contributions. Ceilings (§4.2) join the Exceeds side in action 7.3.
pub fn verdict_of(part: &Part, limit: &Cost) -> Verdict {
    match (part.state(), part.cost.compare(limit)) {
        (State::Known, CostComparison::Within) => Verdict::Within,
        (_, CostComparison::Exceeds) => Verdict::Exceeds,
        _ => Verdict::Inconclusive,
    }
}

pub struct Finding<'a> {
    pub public: PublicFunction<'a>,
    pub part: Part,
    pub name: String,
    pub site: Site,
}

impl Finding<'_> {
    /// The entry's verdict against each of its limits, in the order of `public.limits`.
    pub fn verdicts(&self) -> impl Iterator<Item = Verdict> + '_ {
        self.public
            .limits
            .iter()
            .map(|applicable| verdict_of(&self.part, &applicable.limit.cost))
    }

    /// The entry's verdict: Exceeds when it exceeds any limit, else Inconclusive when any verdict is, else Within;
    /// `None` for an entry without a limit.
    pub fn verdict(&self) -> Option<Verdict> {
        self.verdicts()
            .fold(None, |held, verdict| match (held, verdict) {
                (Some(Verdict::Exceeds), _) | (_, Verdict::Exceeds) => Some(Verdict::Exceeds),
                (Some(Verdict::Inconclusive), _) | (_, Verdict::Inconclusive) => {
                    Some(Verdict::Inconclusive)
                }
                _ => Some(Verdict::Within),
            })
    }
}

/// Lint's reading of each public entry: its summary, the one the report reads (§3.5).
pub fn findings_of<'a>(
    analysis: &mut Analysis<'_, 'a>,
    public: Vec<PublicFunction<'a>>,
) -> Vec<Finding<'a>> {
    public
        .into_iter()
        .map(|public| {
            let part = analysis
                .summarize(public.file, public.function)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            Finding {
                name: analysis.name_of(public.file, public.function),
                site: analysis.function_site_of(public.file, public.function),
                public,
                part,
            }
        })
        .collect()
}

pub struct ReportRow {
    pub envelope: Option<Cost>,
    pub unknowns: Option<UnknownId>,
    pub state: State,
    /// The cost depends on a `@perf` directive (spec Terms, Asserted).
    pub asserted: bool,
    pub cost: Cost,
    pub latent: Option<Part>,
    pub name: String,
    /// The text of the function's own `@perf O(...)` directive.
    pub mark: Option<String>,
    pub site: Site,
    pub trace: Option<TraceId>,
}

pub fn report_rows_of<'a>(
    analysis: &mut Analysis<'_, 'a>,
    functions: &[(FileId, FunctionNode<'a>)],
) -> Vec<ReportRow> {
    let mut rows = Vec::with_capacity(functions.len());

    for (file, function) in functions.iter().copied() {
        let tags = analysis.function_tags(file, function);
        let mark = cost_tag_of(&tags).map(|(cost, text)| {
            if let Err(error) = analysis.bind_function_cost(file, function, &cost) {
                if matches!(error, crate::cost::CostError::UnresolvedQuantity(_)) {
                    return text;
                }

                analysis.errors.insert(format!(
                    "invalid {text} at {}:{}: {error:?}",
                    analysis.project.file(file).relative,
                    analysis.function_site_of(file, function).line
                ));
            }

            text
        });
        // The row reads the summary lint reads, so a function whose cost a directive sets shows that cost (§3.3,
        // §3.5), and a directive applied anywhere beneath it marks the row asserted.
        let assertions = analysis.assertions;
        let reading = analysis.summarize(file, function);
        let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let latent = reading.latent(&mut analysis.unknowns, &mut analysis.traces);
        let asserted = mark.is_some() || analysis.assertions != assertions;
        // The envelope only filters rows under `--min`; a row whose envelope cannot be bound keeps its state (§3.5).
        let envelope = analysis.bind_function_cost(file, function, &Cost::N).ok();

        rows.push(ReportRow {
            envelope,
            unknowns: part.unknowns,
            state: part.state(),
            asserted,
            cost: part.cost,
            latent: (!latent.is_absent()).then_some(latent),
            name: analysis.name_of(file, function),
            mark,
            site: analysis.function_site_of(file, function),
            trace: part.trace,
        });
    }

    rows
}

fn tsconfig_text_of(project: &Project<'_>) -> String {
    relative_path_of(&project.root, &project.tsconfig_path)
}

pub fn order_by_cost_descending(left: &Cost, right: &Cost) -> std::cmp::Ordering {
    right.structural_key().cmp(&left.structural_key())
}

fn lint_header_of(tsconfig: &str, config: &Config, entries: &[String], checked: usize) -> String {
    format!(
        "# {tsconfig}  {}: max {}, {} entrypoint{} ({}), {checked} public functions",
        config.source,
        config.max.text,
        entries.len(),
        if entries.len() == 1 { "" } else { "s" },
        entries.join(", ")
    )
}

pub fn lint_lines(
    values: &Values,
    traces: &TraceArena,
    project: &Project<'_>,
    config: &Config,
    checked: &[Finding<'_>],
    over: &[&Finding<'_>],
) -> Vec<String> {
    let entries: Vec<String> = config
        .entrypoints
        .iter()
        .map(|(path, _)| relative_path_of(&project.root, path))
        .collect();
    let mut lines = vec![
        lint_header_of(&tsconfig_text_of(project), config, &entries, checked.len()),
        String::new(),
    ];

    for finding in over {
        for (applicable, _) in finding
            .public
            .limits
            .iter()
            .zip(finding.verdicts())
            .filter(|(_, verdict)| *verdict == Verdict::Exceeds)
        {
            lines.push(format!(
                "{}, above the limit {}{}  {}  {}  via {}",
                proven_text(values, &finding.part),
                applicable.limit.text,
                if finding.public.own_limit {
                    " [@perf max]"
                } else {
                    ""
                },
                finding.name,
                location_of(project, finding.site),
                applicable.entry
            ));
        }

        chain_lines(values, traces, project, finding.part.trace, 1, &mut lines);

        lines.push(String::new());
    }

    lines.push(format!("{} over limit", over.len()));

    if !over.is_empty() {
        lines.push(
            "each cost over its limit is what olint proves; an instance's work may fall below it"
                .into(),
        );
    }

    let incomplete = checked
        .iter()
        .filter(|finding| finding.part.unknowns.is_some())
        .count();

    if incomplete > 0 {
        lines.push(format!("{incomplete} partial results"));
    }

    lines
}

pub fn report_lines(
    values: &Values,
    traces: &TraceArena,
    project: &Project<'_>,
    unknowns: &Unknowns,
    rows: &[ReportRow],
    minimum_exponent: u32,
) -> Vec<String> {
    lines_of_report(
        values,
        traces,
        &tsconfig_text_of(project),
        rows,
        minimum_exponent,
        &|site, out| write!(out, "{}:{}", project.file(site.file).relative, site.line),
        &|root| unknowns.lines_with(project, root, &|id, out| values.write_label(id, out)),
    )
}

/// §4.7: the source origin of every unknown contribution of a row, one `unknown origin:` line each, whatever the
/// policy, since the policy governs diagnostics only (§4.9).
fn origin_lines(
    roots: impl IntoIterator<Item = UnknownId>,
    origins: &dyn Fn(UnknownId) -> Vec<String>,
    out: &mut Vec<String>,
) {
    let mut shown = std::collections::HashSet::new();

    for root in roots {
        for line in origins(root) {
            let line = match line.strip_prefix("unknown ") {
                Some(origin) => format!("    unknown origin: {origin}"),
                None => format!("    {line}"),
            };

            if shown.insert(line.clone()) {
                out.push(line);
            }
        }
    }
}

fn lines_of_report(
    values: &Values,
    traces: &TraceArena,
    tsconfig: &str,
    rows: &[ReportRow],
    minimum_exponent: u32,
    location: &dyn Fn(Site, &mut dyn std::fmt::Write) -> std::fmt::Result,
    origins: &dyn Fn(UnknownId) -> Vec<String>,
) -> Vec<String> {
    let mut files: Vec<FileId> = rows.iter().map(|row| row.site.file).collect();

    files.sort();
    files.dedup();

    let mut buckets: Vec<(String, usize)> = Vec::new();

    for row in rows {
        let text = text_of_state(values, &row.cost, row.state);

        match buckets.iter_mut().find(|(known, _)| *known == text) {
            Some(bucket) => bucket.1 += 1,
            None => buckets.push((text, 1)),
        }
    }

    buckets.sort_by_key(|(_, count)| std::cmp::Reverse(*count));

    let count_of = |state: State| rows.iter().filter(|row| row.state == state).count();
    let mut lines = vec![
        format!(
            "# {tsconfig}  ({} functions in {} files: {} known, {} partial, {} unknown)",
            rows.len(),
            files.len(),
            count_of(State::Known),
            count_of(State::Partial),
            count_of(State::Unknown)
        ),
        String::new(),
    ];

    for (text, count) in buckets {
        lines.push(format!("{} {count:>4}", padded_text_of(&text, 16)));
    }

    lines.push(String::new());

    let mut flagged: Vec<&ReportRow> = rows
        .iter()
        .filter(|row| {
            if minimum_exponent == 0 {
                return true;
            }

            let Some(envelope) = &row.envelope else {
                return false;
            };
            let cost = row
                .cost
                .bind(&|_| None, std::slice::from_ref(envelope))
                .unwrap_or_else(|_| row.cost.clone());
            let threshold = Cost::power(
                envelope.clone(),
                Cost::constant(u64::from(minimum_exponent)),
            );

            threshold.is_ok_and(|threshold| threshold.compare(&cost) == CostComparison::Within)
                || cost.has_polynomial_log_growth(envelope)
        })
        .collect();

    flagged.sort_by(|left, right| {
        order_by_cost_descending(&left.cost, &right.cost).then_with(|| {
            (left.site.file, left.site.line, &left.name).cmp(&(
                right.site.file,
                right.site.line,
                &right.name,
            ))
        })
    });

    for row in flagged {
        lines.push(row_text_of(values, row, &location_text(row.site, location)));

        if let Some(latent) = &row.latent {
            lines.push(format!(
                "    lazy {} when consumed",
                text_of_state(values, &latent.cost, latent.state())
            ));
        }

        origin_lines(
            row.unknowns
                .into_iter()
                .chain(row.latent.as_ref().and_then(|latent| latent.unknowns)),
            origins,
            &mut lines,
        );

        lines_of_chain(values, traces, row.trace, 1, &mut lines, location);

        lines.push(String::new());
    }

    lines
}

/// A reading's state as the report renders it (§4.7): its bound, its floor marked `[partial]`, or `unknown`.
fn text_of_state(values: &Values, cost: &Cost, state: State) -> String {
    match state {
        State::Known => cost.text_with(&|id| values.label(id)),
        State::Partial => format!("{} [partial]", cost.text_with(&|id| values.label(id))),
        State::Unknown => "unknown".into(),
    }
}

/// An entry's state as the report renders it, for diagnostics that name it.
pub fn state_text(values: &Values, part: &Part) -> String {
    text_of_state(values, &part.cost, part.state())
}

/// §4.4: an Exceeds line states what olint proves, a bound or a floor, which an instance's work may fall below.
fn proven_text(values: &Values, part: &Part) -> String {
    let text = part.cost.text_with(&|id| values.label(id));

    match part.state() {
        State::Known => format!("olint proves {text}"),
        State::Partial | State::Unknown => format!("olint proves at least {text}"),
    }
}

#[cfg(test)]
#[path = "report.test.rs"]
mod tests;

fn location_text(
    site: Site,
    location: &dyn Fn(Site, &mut dyn std::fmt::Write) -> std::fmt::Result,
) -> String {
    let mut out = crate::trace::BoundedText {
        text: String::new(),
        limit: 4096,
        exhausted: false,
    };

    if location(site, &mut out).is_err() {
        return "<location truncated>".into();
    }

    out.text
}

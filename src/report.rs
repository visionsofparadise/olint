use crate::analysis::Analysis;
use crate::config::Config;
use crate::cost::{Cost, CostComparison, Part};
use crate::declarations::FunctionNode;
use crate::directives::cost_tag_of;
use crate::paths::relative_path_of;
use crate::project::{FileId, Project, Site};
use crate::public::PublicFunction;
use crate::summaries::Substitutions;
use crate::trace::{RenderBudget, TraceArena, TraceId};
use crate::unknowns::UnknownId;
use crate::values::Values;
use oxc_span::GetSpan;

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

fn row_text_of(
    values: &Values,
    cost: &Cost,
    name: &str,
    mark: Option<&str>,
    location: &str,
) -> String {
    let mark = match mark {
        Some(mark) => format!(" [@perf {mark}]"),
        None => String::new(),
    };

    format!(
        "{} {name}{mark}  {location}",
        padded_text_of(&cost.text_with(&|id| values.label(id)), 14)
    )
}

pub struct Finding<'a> {
    pub public: PublicFunction<'a>,
    pub part: Part,
    pub name: String,
    pub site: Site,
}

pub struct ReportRow {
    pub envelope: Option<Cost>,
    pub unknowns: Option<UnknownId>,
    pub cost: Cost,
    pub latent: Option<Part>,
    pub name: String,
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
        let reading = match mark {
            Some(_) => analysis.summarize_with(file, function, Substitutions::new(), true),
            None => analysis.summarize(file, function),
        };
        let mut part = reading.total(&mut analysis.unknowns, &mut analysis.traces);
        let latent = reading.latent(&mut analysis.unknowns, &mut analysis.traces);

        let envelope = match analysis.bind_function_cost(file, function, &Cost::N) {
            Ok(cost) => Some(cost),
            Err(_) => {
                let origin = analysis
                    .source_span(file, analysis.kind_of_node(file, function.node_id()).span());
                let unknown = analysis
                    .unknowns
                    .origin(origin, crate::unknowns::UnknownReason::ResourceExhaustion);
                part.unknowns = analysis.unknowns.join(part.unknowns, Some(unknown));

                None
            }
        };

        rows.push(ReportRow {
            envelope,
            unknowns: part.unknowns,
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
        for applicable in finding.public.limits.iter().filter(|applicable| {
            finding.part.cost.compare(&applicable.limit.cost) == CostComparison::Exceeds
        }) {
            lines.push(format!(
                "{} > {}{}  {}  {}  via {}",
                partial_text(values, &finding.part.cost, finding.part.unknowns),
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
    )
}

fn lines_of_report(
    values: &Values,
    traces: &TraceArena,
    tsconfig: &str,
    rows: &[ReportRow],
    minimum_exponent: u32,
    location: &dyn Fn(Site, &mut dyn std::fmt::Write) -> std::fmt::Result,
) -> Vec<String> {
    let mut files: Vec<FileId> = rows.iter().map(|row| row.site.file).collect();

    files.sort();
    files.dedup();

    let mut buckets: Vec<(String, usize)> = Vec::new();

    for row in rows {
        let text = partial_text(values, &row.cost, row.unknowns);

        match buckets.iter_mut().find(|(known, _)| *known == text) {
            Some(bucket) => bucket.1 += 1,
            None => buckets.push((text, 1)),
        }
    }

    buckets.sort_by_key(|(_, count)| std::cmp::Reverse(*count));

    let mut lines = vec![
        format!(
            "# {tsconfig}  ({} functions in {} files)",
            rows.len(),
            files.len()
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
        let row_text = row_text_of(
            values,
            &row.cost,
            &row.name,
            row.mark.as_deref(),
            &location_text(row.site, location),
        );

        lines.push(if row.unknowns.is_some() {
            format!("{row_text} [partial]")
        } else {
            row_text
        });

        if let Some(latent) = &row.latent {
            lines.push(format!(
                "    lazy {} when consumed",
                partial_text(values, &latent.cost, latent.unknowns)
            ));
        }

        lines_of_chain(values, traces, row.trace, 1, &mut lines, location);

        lines.push(String::new());
    }

    lines
}

fn partial_text(values: &Values, cost: &Cost, unknowns: Option<UnknownId>) -> String {
    if unknowns.is_some() {
        format!("{} [partial]", cost.text_with(&|id| values.label(id)))
    } else {
        cost.text_with(&|id| values.label(id))
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

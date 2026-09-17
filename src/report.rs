use crate::analysis::Analysis;
use crate::config::Config;
use crate::cost::{Cost, CostComparison, Factor, Part};
use crate::declarations::FunctionNode;
use crate::directives::cost_tag_of;
use crate::paths::relative_path_of;
use crate::project::{FileId, Project, Site};
use crate::public::PublicFunction;
use crate::summaries::Substitutions;
use crate::unknowns::UnknownId;
use crate::values::Values;
use oxc_span::GetSpan;

const LOOP_LABELS: &[&str] = &["for", "for-of", "for-in", "while", "do-while"];

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
    project: &Project<'_>,
    chain: &[Factor],
    depth: usize,
    out: &mut Vec<String>,
) {
    lines_of_chain(values, chain, depth, out, &|site| {
        location_of(project, site)
    });
}

fn lines_of_chain(
    values: &Values,
    chain: &[Factor],
    depth: usize,
    out: &mut Vec<String>,
    location: &dyn Fn(Site) -> String,
) {
    let mut depth = depth;

    for factor in chain {
        let label = factor.label.as_str();
        let is_loop = LOOP_LABELS.iter().any(|name| {
            label == *name
                || label
                    .strip_prefix(name)
                    .is_some_and(|rest| rest.starts_with(' '))
        });
        let is_tag = label.starts_with("@perf ");
        let is_call = label.starts_with("call ")
            || label.starts_with("new ")
            || label.starts_with("recursive call ")
            || is_tag;
        let relation = if is_loop {
            "in loop"
        } else if is_tag {
            "reads as"
        } else if is_call {
            "calls"
        } else {
            "does"
        };
        let cost = if factor.cost.is_one() {
            String::new()
        } else if is_call {
            format!("  = {}", factor.cost.text_with(&|id| values.label(id)))
        } else {
            let text = factor.cost.text_with(&|id| values.label(id));

            format!("  x {}", &text[2..text.len() - 1])
        };
        let shown = ["call ", "new ", "recursive call "]
            .iter()
            .find_map(|prefix| label.strip_prefix(prefix))
            .unwrap_or(label);
        let width = 52 - (depth * 4).min(32);

        out.push(format!(
            "{}{relation} {} {}{cost}",
            "    ".repeat(depth),
            padded_text_of(shown, width),
            location(factor.site)
        ));

        if !factor.inner.is_empty() {
            lines_of_chain(values, &factor.inner, depth, out, location);
        }

        if !is_call && !factor.cost.is_one() {
            depth += 1;
        }
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
    pub name: String,
    pub mark: Option<String>,
    pub site: Site,
    pub chain: Vec<Factor>,
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
        let mut part = match mark {
            Some(_) => analysis.summarize_with(file, function, Substitutions::new(), true),
            None => analysis.summarize(file, function),
        }
        .total(&mut analysis.unknowns);

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
            name: analysis.name_of(file, function),
            mark,
            site: analysis.function_site_of(file, function),
            chain: part.chain,
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

        chain_lines(values, project, &finding.part.chain, 1, &mut lines);

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
    project: &Project<'_>,
    rows: &[ReportRow],
    minimum_exponent: u32,
) -> Vec<String> {
    lines_of_report(
        values,
        &tsconfig_text_of(project),
        rows,
        minimum_exponent,
        &|site| location_of(project, site),
    )
}

fn lines_of_report(
    values: &Values,
    tsconfig: &str,
    rows: &[ReportRow],
    minimum_exponent: u32,
    location: &dyn Fn(Site) -> String,
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
            &location(row.site),
        );

        lines.push(if row.unknowns.is_some() {
            format!("{row_text} [partial]")
        } else {
            row_text
        });

        lines_of_chain(values, &row.chain, 1, &mut lines, location);

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

use crate::analysis::Analysis;
use crate::config::Config;
use crate::cost::{Cost, Factor, Part};
use crate::declarations::FunctionNode;
use crate::directives::cost_tag_of;
use crate::paths::relative_path_of;
use crate::project::{FileId, Project, Site};
use crate::public::PublicFunction;
use crate::summaries::Substitutions;

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

pub fn chain_lines(project: &Project<'_>, chain: &[Factor], depth: usize, out: &mut Vec<String>) {
    lines_of_chain(chain, depth, out, &|site| location_of(project, site));
}

fn lines_of_chain(
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
            format!("  = {}", factor.cost.text())
        } else {
            let text = factor.cost.text();

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
            lines_of_chain(&factor.inner, depth, out, location);
        }

        if !is_call && !factor.cost.is_one() {
            depth += 1;
        }
    }
}

fn row_text_of(cost: Cost, name: &str, mark: Option<&str>, location: &str) -> String {
    let mark = match mark {
        Some(mark) => format!(" [@perf {mark}]"),
        None => String::new(),
    };

    format!(
        "{} {name}{mark}  {location}",
        padded_text_of(&cost.text(), 14)
    )
}

pub struct Finding<'a> {
    pub public: PublicFunction<'a>,
    pub part: Part,
    pub name: String,
    pub site: Site,
}

pub struct ReportRow {
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
        let mark = cost_tag_of(&tags).map(|(_, text)| text);
        let part = match mark {
            Some(_) => analysis.summarize_with(file, function, Substitutions::new(), true),
            None => analysis.summarize(file, function),
        }
        .total();

        rows.push(ReportRow {
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

pub fn order_by_cost_descending(left: Cost, right: Cost) -> std::cmp::Ordering {
    if left.exceeds(right) {
        std::cmp::Ordering::Less
    } else if right.exceeds(left) {
        std::cmp::Ordering::Greater
    } else {
        std::cmp::Ordering::Equal
    }
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
        lines.push(format!(
            "{} > {}{}  {}  {}  via {}",
            finding.part.cost.text(),
            finding.public.limit.text,
            if finding.public.own_limit {
                " [@perf max]"
            } else {
                ""
            },
            finding.name,
            location_of(project, finding.site),
            finding.public.entry
        ));

        chain_lines(project, &finding.part.chain, 1, &mut lines);

        lines.push(String::new());
    }

    lines.push(format!("{} over limit", over.len()));

    lines
}

pub fn report_lines(
    project: &Project<'_>,
    rows: &[ReportRow],
    minimum_exponent: u32,
) -> Vec<String> {
    lines_of_report(
        &tsconfig_text_of(project),
        rows,
        minimum_exponent,
        &|site| location_of(project, site),
    )
}

fn lines_of_report(
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
        let text = row.cost.text();

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
        .filter(|row| row.cost.n >= minimum_exponent || (row.cost.n >= 1 && row.cost.log >= 1))
        .collect();

    flagged.sort_by(|left, right| order_by_cost_descending(left.cost, right.cost));

    for row in flagged {
        lines.push(row_text_of(
            row.cost,
            &row.name,
            row.mark.as_deref(),
            &location(row.site),
        ));

        lines_of_chain(&row.chain, 1, &mut lines, location);

        lines.push(String::new());
    }

    lines
}

#[cfg(test)]
#[path = "report.test.rs"]
mod tests;

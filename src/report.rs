use crate::cost::{Cost, Factor};
use crate::project::{Project, Site};

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

pub fn report_row(
    project: &Project<'_>,
    cost: Cost,
    name: &str,
    mark: Option<&str>,
    site: Site,
) -> String {
    let mark = match mark {
        Some(mark) => format!(" [@perf {mark}]"),
        None => String::new(),
    };

    format!(
        "{} {name}{mark}  {}",
        padded_text_of(&cost.text(), 14),
        location_of(project, site)
    )
}

#[cfg(test)]
#[path = "report.test.rs"]
mod tests;

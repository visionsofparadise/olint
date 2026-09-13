use std::path::{Path, PathBuf};

use serde_json::{Map, Value};

use crate::budgets::collapsed_text_of;
use crate::cost::Cost;
use crate::project::{relative_path_of, Project};
use crate::tsconfig::normalized_path_of;

#[derive(Clone, Debug)]
pub struct Limit {
    pub cost: Cost,
    pub text: String,
}

pub struct Config {
    pub max: Limit,
    pub entrypoints: Vec<(PathBuf, Limit)>,
    pub ignore: Vec<IgnorePattern>,
    pub source: String,
}

#[derive(Debug)]
pub enum ConfigError {
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Json {
        path: PathBuf,
        message: String,
    },
    Limit {
        field: String,
        text: String,
    },
    Ignore {
        pattern: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Atom {
    Unit(u16),
    AnyUnit,
    NonSlashRun,
    OptionalDirectory,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Term {
    atom: Atom,
    optional: bool,
    quantified: bool,
    lazy: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IgnorePattern {
    terms: Vec<Term>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Piece {
    Star,
    Slash,
    Question,
    Unit(u16),
    Done(Atom),
}

const SLASH: u16 = b'/' as u16;

impl IgnorePattern {
    pub fn parse(glob: &str) -> Option<IgnorePattern> {
        let mut pieces: Vec<Piece> = glob
            .encode_utf16()
            .map(|unit| match unit {
                unit if unit == u16::from(b'*') => Piece::Star,
                unit if unit == SLASH => Piece::Slash,
                unit if unit == u16::from(b'?') => Piece::Question,
                unit => Piece::Unit(unit),
            })
            .collect();

        pieces = replaced_runs_of(
            &pieces,
            &[Piece::Star, Piece::Star, Piece::Slash],
            &[Atom::OptionalDirectory],
        );
        pieces = replaced_runs_of(
            &pieces,
            &[Piece::Star, Piece::Star],
            &[Atom::AnyUnit, Atom::NonSlashRun],
        );
        pieces = replaced_runs_of(&pieces, &[Piece::Star], &[Atom::NonSlashRun]);

        let mut terms: Vec<Term> = Vec::new();

        for piece in pieces {
            let atom = match piece {
                Piece::Question => {
                    let last = terms.last_mut()?;

                    if !last.quantified {
                        last.optional = true;
                        last.quantified = true;
                    } else if !last.lazy {
                        last.lazy = true;
                    } else {
                        return None;
                    }

                    continue;
                }
                Piece::Slash => Atom::Unit(SLASH),
                Piece::Unit(unit) => Atom::Unit(unit),
                Piece::Done(atom) => atom,
                Piece::Star => Atom::NonSlashRun,
            };

            terms.push(Term {
                atom,
                optional: false,
                quantified: matches!(atom, Atom::NonSlashRun | Atom::OptionalDirectory),
                lazy: false,
            });
        }

        Some(IgnorePattern { terms })
    }

    pub fn matches(&self, relative: &str) -> bool {
        let units: Vec<u16> = relative.encode_utf16().collect();

        matches_terms(&self.terms, &units)
    }
}

fn replaced_runs_of(pieces: &[Piece], run: &[Piece], atoms: &[Atom]) -> Vec<Piece> {
    let mut replaced = Vec::with_capacity(pieces.len());
    let mut index = 0;

    while index < pieces.len() {
        if pieces[index..].starts_with(run) {
            replaced.extend(atoms.iter().map(|atom| Piece::Done(*atom)));

            index += run.len();
        } else {
            replaced.push(pieces[index]);

            index += 1;
        }
    }

    replaced
}

fn is_line_terminator(unit: u16) -> bool {
    matches!(unit, 0x0a | 0x0d | 0x2028 | 0x2029)
}

fn matches_terms(terms: &[Term], units: &[u16]) -> bool {
    let Some((term, rest)) = terms.split_first() else {
        return units.is_empty();
    };

    if term.optional && matches_terms(rest, units) {
        return true;
    }

    match term.atom {
        Atom::Unit(unit) => units.first() == Some(&unit) && matches_terms(rest, &units[1..]),
        Atom::AnyUnit => {
            units.first().is_some_and(|unit| !is_line_terminator(*unit))
                && matches_terms(rest, &units[1..])
        }
        Atom::NonSlashRun => {
            let run = units.iter().take_while(|unit| **unit != SLASH).count();

            (0..=run).any(|length| matches_terms(rest, &units[length..]))
        }
        Atom::OptionalDirectory => {
            if matches_terms(rest, units) {
                return true;
            }

            if !units.first().is_some_and(|unit| !is_line_terminator(*unit)) {
                return false;
            }

            let run = units[1..].iter().take_while(|unit| **unit != SLASH).count();

            units.get(1 + run) == Some(&SLASH) && matches_terms(rest, &units[2 + run..])
        }
    }
}

pub const LIMIT_FORMS: &str = "O(1), O(log N), O(N), O(N log N) or O(N^k)";

pub fn limit_of(text: &str, field: &str) -> Result<Limit, ConfigError> {
    match Cost::parse(text) {
        Some(cost) => Ok(Limit {
            cost,
            text: collapsed_text_of(text),
        }),
        None => Err(ConfigError::Limit {
            field: field.to_string(),
            text: Value::String(text.to_string()).to_string(),
        }),
    }
}

fn json_limit_of(value: &Value, field: &str) -> Result<Limit, ConfigError> {
    match value {
        Value::String(text) => limit_of(text, field),
        other => Err(ConfigError::Limit {
            field: field.to_string(),
            text: other.to_string(),
        }),
    }
}

fn is_array_index(key: &str) -> bool {
    key.parse::<u32>()
        .is_ok_and(|index| index < u32::MAX && index.to_string() == key)
}

fn entries_of(map: &Map<String, Value>) -> Vec<(&String, &Value)> {
    let mut entries: Vec<(&String, &Value)> = map.iter().collect();

    entries.sort_by_key(|(key, _)| match is_array_index(key) {
        true => (0, key.parse::<u32>().unwrap_or_default()),
        false => (1, 0),
    });

    entries
}

fn values_of(value: &Value) -> Vec<(String, &Value)> {
    match value {
        Value::Object(map) => entries_of(map)
            .into_iter()
            .map(|(key, value)| (key.clone(), value))
            .collect(),
        Value::Array(items) => items
            .iter()
            .enumerate()
            .map(|(index, value)| (index.to_string(), value))
            .collect(),
        _ => Vec::new(),
    }
}

fn collect_strings<'v>(value: &'v Value, targets: &mut Vec<&'v str>) {
    match value {
        Value::String(text) => targets.push(text),
        Value::Object(_) | Value::Array(_) => {
            for (_, inner) in values_of(value) {
                collect_strings(inner, targets);
            }
        }
        _ => {}
    }
}

fn is_truthy(value: &Value) -> bool {
    match value {
        Value::Null => false,
        Value::Bool(flag) => *flag,
        Value::Number(number) => number.as_f64().is_some_and(|float| float != 0.0),
        Value::String(text) => !text.is_empty(),
        Value::Array(_) | Value::Object(_) => true,
    }
}

fn candidates_of(target: &str) -> Vec<String> {
    let base = target.strip_prefix("./").unwrap_or(target).to_string();
    let declaration = match base.strip_suffix(".d.ts") {
        Some(stem) => format!("{stem}.ts"),
        None => base.clone(),
    };
    let script = [".cjs", ".mjs", ".js"]
        .iter()
        .find_map(|extension| declaration.strip_suffix(extension))
        .map(|stem| format!("{stem}.ts"))
        .unwrap_or(declaration);
    let mut candidates = vec![base, script];

    for index in 0..candidates.len() {
        if let Some(rest) = candidates[index].strip_prefix("dist/") {
            candidates.push(format!("src/{rest}"));
        }
    }

    for index in 0..candidates.len() {
        if let Some(stem) = candidates[index].strip_suffix(".ts") {
            candidates.push(format!("{stem}/index.ts"));
        }
    }

    candidates
}

pub fn package_entries(project: &Project<'_>) -> Vec<PathBuf> {
    let Ok(text) = std::fs::read_to_string(project.root.join("package.json")) else {
        return Vec::new();
    };
    let Ok(package) = serde_json::from_str::<Value>(&text) else {
        return Vec::new();
    };
    let mut targets: Vec<&str> = Vec::new();

    match package.get("exports") {
        Some(exports) if is_truthy(exports) => collect_strings(exports, &mut targets),
        _ => {
            for field in ["source", "types", "module", "main"] {
                if let Some(Value::String(target)) = package.get(field) {
                    targets.push(target);
                }
            }
        }
    }

    let mut found: Vec<PathBuf> = Vec::new();

    for target in targets {
        let entry = candidates_of(target)
            .into_iter()
            .map(|candidate| normalized_path_of(&project.root.join(candidate)))
            .find(|candidate| project.file_by_path(candidate).is_some());

        if let Some(entry) = entry {
            if !found.contains(&entry) {
                found.push(entry);
            }
        }
    }

    found
}

pub fn read_config(project: &Project<'_>, explicit: Option<&Path>) -> Result<Config, ConfigError> {
    let path = match explicit {
        Some(explicit) => std::path::absolute(explicit)
            .map(|absolute| normalized_path_of(&absolute))
            .map_err(|source| ConfigError::Read {
                path: explicit.to_path_buf(),
                source,
            })?,
        None => project.root.join("olint.config.json"),
    };
    let exists = path.is_file();
    let raw = match exists {
        true => {
            let text = std::fs::read_to_string(&path).map_err(|source| ConfigError::Read {
                path: path.clone(),
                source,
            })?;

            serde_json::from_str::<Value>(&text).map_err(|error| ConfigError::Json {
                path: path.clone(),
                message: error.to_string(),
            })?
        }
        false => Value::Object(Map::new()),
    };
    let field_of = |name: &str| raw.get(name).filter(|value| !value.is_null());
    let max = match field_of("max") {
        Some(value) => json_limit_of(value, "max")?,
        None => limit_of("O(N^2)", "max")?,
    };
    let mut entrypoints: Vec<(PathBuf, Limit)> = Vec::new();

    match raw.get("entrypoints") {
        Some(value @ (Value::Object(_) | Value::Array(_))) => {
            for (key, limit) in values_of(value) {
                let limit = json_limit_of(limit, &format!("entrypoints[\"{key}\"]"))?;
                let entry = normalized_path_of(&project.root.join(&key));

                match entrypoints.iter_mut().find(|(known, _)| *known == entry) {
                    Some(known) => known.1 = limit,
                    None => entrypoints.push((entry, limit)),
                }
            }
        }
        _ => {
            for entry in package_entries(project) {
                entrypoints.push((entry, max.clone()));
            }
        }
    }

    let ignore = match raw.get("ignore") {
        Some(Value::Array(patterns)) => patterns
            .iter()
            .map(|pattern| {
                pattern
                    .as_str()
                    .and_then(IgnorePattern::parse)
                    .ok_or_else(|| ConfigError::Ignore {
                        pattern: pattern.to_string(),
                    })
            })
            .collect::<Result<Vec<IgnorePattern>, ConfigError>>()?,
        _ => Vec::new(),
    };
    let source = match exists {
        true => relative_path_of(&project.root, &path),
        false => "defaults".to_string(),
    };

    Ok(Config {
        max,
        entrypoints,
        ignore,
        source,
    })
}

impl Config {
    pub fn is_ignored(&self, relative: &str) -> bool {
        self.ignore.iter().any(|pattern| pattern.matches(relative))
    }
}

#[cfg(test)]
#[path = "config.test.rs"]
mod tests;

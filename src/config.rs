use std::path::{Path, PathBuf};

use globset::{GlobBuilder, GlobMatcher};
use serde_json::{Map, Value};

use crate::cost::Cost;
use crate::paths::{normalized_path_of, relative_path_of};
use crate::project::Project;
use crate::syntax::collapsed_text_of;

#[derive(Clone, Debug)]
pub struct Limit {
    pub cost: Cost,
    pub text: String,
}

pub struct Config {
    pub unknown: UnknownPolicy,
    pub max: Limit,
    pub entrypoints: Vec<(PathBuf, Vec<Limit>)>,
    pub ignore: Vec<GlobMatcher>,
    pub source: String,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum UnknownPolicy {
    Ignore,
    #[default]
    Warn,
    Error,
}

pub fn unknown_policy_of(value: Option<&Value>) -> Result<UnknownPolicy, ConfigError> {
    match value {
        None => Ok(UnknownPolicy::Warn),
        Some(Value::String(value)) if value == "ignore" => Ok(UnknownPolicy::Ignore),
        Some(Value::String(value)) if value == "warn" => Ok(UnknownPolicy::Warn),
        Some(Value::String(value)) if value == "error" => Ok(UnknownPolicy::Error),
        Some(value) => Err(ConfigError::Unknown {
            value: value.to_string(),
        }),
    }
}

#[derive(Debug)]
pub enum ConfigError {
    Unknown {
        value: String,
    },
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
    Entrypoints {
        text: String,
    },
    Entrypoint {
        field: String,
        text: String,
    },
    Ignore {
        pattern: String,
    },
}

fn ignore_pattern_of(value: &Value) -> Result<GlobMatcher, ConfigError> {
    let invalid = || ConfigError::Ignore {
        pattern: value.to_string(),
    };
    let pattern = value.as_str().ok_or_else(invalid)?;

    GlobBuilder::new(pattern)
        .literal_separator(true)
        .backslash_escape(true)
        .build()
        .map(|glob| glob.compile_matcher())
        .map_err(|_| invalid())
}

pub const LIMIT_FORMS: &str = "O(...) using constants, named input sizes, N, sums, products, max, log, powers, positive ratios or factorials";

pub const ENTRYPOINT_FORMS: &str = r#"a path string or { "path": string, "max": string }"#;

pub fn limit_of(text: &str, field: &str) -> Result<Limit, ConfigError> {
    match Cost::parse(text) {
        Ok(cost) => Ok(Limit {
            cost,
            text: collapsed_text_of(text),
        }),
        Err(_) => Err(ConfigError::Limit {
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

fn entrypoint_of(item: &Value, field: &str, max: &Limit) -> Result<(String, Limit), ConfigError> {
    let invalid = || ConfigError::Entrypoint {
        field: field.to_string(),
        text: item.to_string(),
    };

    match item {
        Value::String(path) => Ok((path.clone(), max.clone())),
        Value::Object(fields) => {
            if fields.keys().any(|key| key != "path" && key != "max") {
                return Err(invalid());
            }

            let Some(Value::String(path)) = fields.get("path") else {
                return Err(invalid());
            };
            let Some(limit) = fields.get("max") else {
                return Err(invalid());
            };

            Ok((path.clone(), json_limit_of(limit, &format!("{field}.max"))?))
        }
        _ => Err(invalid()),
    }
}

pub fn entrypoints_of(
    value: &Value,
    root: &Path,
    max: &Limit,
) -> Result<Vec<(PathBuf, Vec<Limit>)>, ConfigError> {
    let Value::Array(items) = value else {
        return Err(ConfigError::Entrypoints {
            text: value.to_string(),
        });
    };
    let mut entrypoints: Vec<(PathBuf, Vec<Limit>)> = Vec::new();

    for (index, item) in items.iter().enumerate() {
        let (path, limit) = entrypoint_of(item, &format!("entrypoints[{index}]"), max)?;
        let entry = normalized_path_of(&root.join(path));

        match entrypoints.iter_mut().find(|(known, _)| *known == entry) {
            Some(known) => {
                if !known.1.iter().any(|old| old.cost == limit.cost) {
                    known.1.push(limit);
                }
            }
            None => entrypoints.push((entry, vec![limit])),
        }
    }

    Ok(entrypoints)
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
    let exists = path.exists();
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
    let entrypoints = match raw.get("entrypoints") {
        Some(value) => entrypoints_of(value, &project.root, &max)?,
        None => package_entries(project)
            .into_iter()
            .map(|entry| (entry, vec![max.clone()]))
            .collect(),
    };

    let ignore = match raw.get("ignore") {
        Some(Value::Array(patterns)) => patterns
            .iter()
            .map(ignore_pattern_of)
            .collect::<Result<Vec<GlobMatcher>, ConfigError>>()?,
        _ => Vec::new(),
    };
    let source = match exists {
        true => relative_path_of(&project.root, &path),
        false => "defaults".to_string(),
    };

    Ok(Config {
        unknown: unknown_policy_of(raw.get("unknown"))?,
        max,
        entrypoints,
        ignore,
        source,
    })
}

impl Config {
    pub fn is_ignored(&self, relative: &str) -> bool {
        self.ignore.iter().any(|pattern| pattern.is_match(relative))
    }
}

#[cfg(test)]
#[path = "config.test.rs"]
mod tests;

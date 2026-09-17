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
    Root {
        path: PathBuf,
        text: String,
    },
    Selection {
        path: PathBuf,
        message: String,
    },
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

fn output_paths(project: &Project<'_>) -> Vec<(PathBuf, PathBuf)> {
    let mut mappings = Vec::new();

    for (owner, config) in project.configurations.iter().enumerate() {
        let sources: Vec<_> = project
            .files
            .iter()
            .filter(|file| file.owners.contains(&owner) && project.is_project_file(file.id))
            .collect();
        let options = &config.output;

        if options.no_emit == Some(true) || options.out_file.is_some() {
            continue;
        }

        let root = options.root_dir.clone().unwrap_or_else(|| {
            if options.composite == Some(true) {
                return config.path.parent().unwrap_or(Path::new("")).to_path_buf();
            }

            let mut root = sources
                .first()
                .and_then(|file| file.path.parent())
                .unwrap_or(Path::new(""))
                .to_path_buf();

            for file in &sources {
                while !file.path.starts_with(&root) && root.pop() {}
            }

            root
        });

        for file in sources {
            let Ok(relative) = file.path.strip_prefix(&root) else {
                continue;
            };
            let extension = file
                .path
                .extension()
                .and_then(|value| value.to_str())
                .unwrap_or("");
            let script_extension = match extension {
                "mts" | "mjs" => "mjs",
                "cts" | "cjs" => "cjs",
                "tsx" | "jsx"
                    if options
                        .jsx
                        .as_deref()
                        .is_some_and(|jsx| jsx.eq_ignore_ascii_case("preserve")) =>
                {
                    "jsx"
                }
                _ => "js",
            };

            if options.emit_declaration_only != Some(true) {
                let path = options.out_dir.as_ref().map_or_else(
                    || file.path.with_extension(script_extension),
                    |directory| directory.join(relative).with_extension(script_extension),
                );

                mappings.push((normalized_path_of(&path), file.path.clone()));
            }

            if options.declaration == Some(true) || options.composite == Some(true) {
                let extension = match extension {
                    "mts" | "mjs" => "d.mts",
                    "cts" | "cjs" => "d.cts",
                    _ => "d.ts",
                };
                let path = options
                    .declaration_dir
                    .as_ref()
                    .or(options.out_dir.as_ref())
                    .map_or_else(
                        || file.path.with_extension(extension),
                        |directory| directory.join(relative).with_extension(extension),
                    );

                mappings.push((normalized_path_of(&path), file.path.clone()));
            }
        }
    }

    mappings
}

fn pattern_capture<'s>(pattern: &str, candidate: &'s str) -> Option<&'s str> {
    let Some((prefix, suffix)) = pattern.split_once('*') else {
        return (pattern == candidate).then_some("");
    };
    let rest = candidate.strip_prefix(prefix)?;
    let count = suffix.bytes().filter(|byte| *byte == b'*').count() + 1;
    let literal = suffix.len() - (count - 1);
    let capture_length = rest.len().checked_sub(literal)?;

    if capture_length % count != 0 {
        return None;
    }

    let capture = rest.get(..capture_length / count)?;

    (pattern.replace('*', capture) == candidate).then_some(capture)
}

fn winning_export<'s>(keys: &'s [&str], subpath: &str) -> Option<&'s str> {
    if let Some(key) = keys.iter().find(|key| **key == subpath) {
        return Some(key);
    }

    keys.iter()
        .copied()
        .filter(|key| key.contains('*') && pattern_capture(key, subpath).is_some())
        .max_by_key(|key| (key.find('*').unwrap_or(0), key.len()))
}

pub fn package_entries(project: &Project<'_>) -> Result<Vec<PathBuf>, ConfigError> {
    let path = project.root.join("package.json");
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(source) => return Err(ConfigError::Read { path, source }),
    };
    let package: Value = serde_json::from_str(&text).map_err(|error| ConfigError::Json {
        path: path.clone(),
        message: error.to_string(),
    })?;

    if !package.is_object() {
        return Err(ConfigError::Root {
            path,
            text: package.to_string(),
        });
    }

    let mut targets = Vec::new();
    let mut keys = Vec::new();

    if let Some(exports) = package.get("exports") {
        if let Some(map) = exports
            .as_object()
            .filter(|map| map.keys().any(|key| key.starts_with('.')))
        {
            for (key, value) in entries_of(map) {
                keys.push(key.as_str());

                let mut values = Vec::new();

                collect_strings(value, &mut values);
                targets.extend(values.into_iter().map(|target| (key.as_str(), target)));
            }
        } else {
            let mut values = Vec::new();

            collect_strings(exports, &mut values);
            targets.extend(values.into_iter().map(|target| (".", target)));
            keys.push(".");
        }
    } else {
        for field in ["source", "types", "module", "main"] {
            if let Some(Value::String(target)) = package.get(field) {
                targets.push(("", target.as_str()));
            }
        }
    }

    let mut mappings: Vec<_> = project
        .files
        .iter()
        .filter(|file| project.is_project_file(file.id))
        .map(|file| (file.path.clone(), file.path.clone()))
        .collect();

    mappings.extend(output_paths(project));

    let mut found = Vec::new();

    for (key, target) in targets {
        if target.ends_with(".json") {
            continue;
        }

        if target.contains('*') && !key.contains('*') {
            return Err(ConfigError::Selection { path: project.root.join(target), message: "package target pattern requires a subpath pattern; configure explicit entrypoints".into() });
        }

        let pattern =
            crate::paths::forward_slashes_of(normalized_path_of(&project.root.join(target)));
        let mut matched = false;
        let mut entries = Vec::new();
        let mut selected_outputs = std::collections::HashMap::new();

        for (output, source) in &mappings {
            let output = crate::paths::forward_slashes_of(output);
            let Some(capture) = pattern_capture(&pattern, &output) else {
                continue;
            };
            matched = true;
            let subpath = key.replace('*', capture);

            if !key.is_empty() && winning_export(&keys, &subpath) != Some(key) {
                continue;
            }

            if selected_outputs
                .insert(output, source)
                .is_some_and(|previous| previous != source)
            {
                return Err(ConfigError::Selection { path: project.root.join(target), message: "package output maps to multiple source files; configure explicit entrypoints".into() });
            }

            if !entries.contains(source) {
                entries.push(source.clone());
            }
        }

        if !matched {
            return Err(ConfigError::Selection { path: project.root.join(target), message: "declared package entry has no proved source/output mapping; configure explicit entrypoints".into() });
        }

        for entry in entries {
            if !found.contains(&entry) {
                found.push(entry);
            }
        }
    }

    Ok(found)
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
    let (raw, exists) = match std::fs::read_to_string(&path) {
        Ok(text) => (
            serde_json::from_str::<Value>(&text).map_err(|error| ConfigError::Json {
                path: path.clone(),
                message: error.to_string(),
            })?,
            true,
        ),
        Err(source) if explicit.is_none() && source.kind() == std::io::ErrorKind::NotFound => {
            (Value::Object(Map::new()), false)
        }
        Err(source) => return Err(ConfigError::Read { path, source }),
    };

    if !raw.is_object() {
        return Err(ConfigError::Root {
            path,
            text: raw.to_string(),
        });
    }

    let max = match raw.get("max") {
        Some(value) => json_limit_of(value, "max")?,
        None => limit_of("O(N^2)", "max")?,
    };
    let entrypoints = match raw.get("entrypoints") {
        Some(value) => entrypoints_of(value, &project.root, &max)?,
        None => package_entries(project)?
            .into_iter()
            .map(|entry| (entry, vec![max.clone()]))
            .collect(),
    };

    let ignore = match raw.get("ignore") {
        Some(Value::Array(patterns)) => patterns
            .iter()
            .map(ignore_pattern_of)
            .collect::<Result<Vec<GlobMatcher>, ConfigError>>()?,
        None => Vec::new(),
        Some(value) => {
            return Err(ConfigError::Ignore {
                pattern: value.to_string(),
            })
        }
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

pub fn validate_entries(project: &Project<'_>, config: &Config) -> Result<(), ConfigError> {
    for (path, _) in &config.entrypoints {
        let invalid = |message: &str| ConfigError::Selection {
            path: path.clone(),
            message: message.to_string(),
        };

        if !path.is_file() {
            return Err(invalid("entrypoint must be an existing regular file"));
        }

        let file = project
            .file_by_path(path)
            .ok_or_else(|| invalid("entrypoint is not in the selected project"))?;

        if !project.is_project_file(file) || project.is_test_path(file) {
            return Err(invalid(
                "entrypoint is excluded by the current implementation-source policy",
            ));
        }
    }

    Ok(())
}

impl Config {
    pub fn is_ignored(&self, relative: &str) -> bool {
        self.ignore.iter().any(|pattern| pattern.is_match(relative))
    }
}

#[cfg(test)]
#[path = "config.test.rs"]
mod tests;

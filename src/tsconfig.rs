use std::collections::HashSet;
use std::path::{Path, PathBuf};

use globset::{GlobBuilder, GlobSet, GlobSetBuilder};
use oxc_resolver::{ExtendsField, ResolveOptions, Resolver, TsConfig};

use crate::project::{canonical_path, forward_slashes, ProjectError};

pub struct TsconfigFiles {
    pub root_dir: PathBuf,
    pub files: Vec<PathBuf>,
}

const TYPESCRIPT_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts"];
const JAVASCRIPT_EXTENSIONS: &[&str] = &["js", "jsx", "mjs", "cjs"];
const DEFAULT_EXCLUDES: &[&str] = &["node_modules", "bower_components", "jspm_packages"];

pub fn select_files(tsconfig: &Path) -> Result<TsconfigFiles, ProjectError> {
    let tsconfig_path = canonical_path(tsconfig).map_err(|source| ProjectError::Read {
        path: tsconfig.to_path_buf(),
        source,
    })?;
    let mut visited = HashSet::new();
    let merged = load_tsconfig(&tsconfig_path, true, &mut visited)?;
    let root_dir = tsconfig_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let root_text = forward_slashes(&root_dir);

    let include_patterns: Vec<String> = match (&merged.include, &merged.files) {
        (Some(include), _) => include.iter().map(forward_slashes).collect(),
        (None, Some(_)) => Vec::new(),
        (None, None) => vec![absolute_pattern(&root_text, "**/*")],
    };
    let exclude_patterns: Vec<String> = match &merged.exclude {
        Some(exclude) => exclude.iter().map(forward_slashes).collect(),
        None => {
            let mut defaults: Vec<String> = DEFAULT_EXCLUDES
                .iter()
                .map(|directory| absolute_pattern(&root_text, directory))
                .collect();

            if let Some(out_dir) = &merged.compiler_options.out_dir {
                defaults.push(absolute_pattern(&forward_slashes(out_dir), ""));
            }

            defaults
        }
    };

    let include_set = glob_set(&include_patterns, tsconfig)?;
    let exclude_set = glob_set(&exclusion_patterns(&exclude_patterns), tsconfig)?;
    let allow_js = merged.compiler_options.allow_js.unwrap_or(false);
    let mut files = Vec::new();
    let mut walked = HashSet::new();

    for pattern in &include_patterns {
        let base: PathBuf = Path::new(&literal_base_of(pattern)).components().collect();

        walk(
            &base,
            &include_set,
            &exclude_set,
            allow_js,
            &mut walked,
            &mut files,
        );
    }

    for file in merged.files.iter().flatten() {
        if let Ok(path) = canonical_path(file) {
            if path.is_file() {
                files.push(path);
            }
        }
    }

    files.sort();
    files.dedup();

    Ok(TsconfigFiles { root_dir, files })
}

pub fn merge_extends(child: TsConfig, parent: &TsConfig) -> TsConfig {
    let mut merged = child;

    if merged.files.is_none() {
        merged.files.clone_from(&parent.files);
    }

    if merged.include.is_none() {
        merged.include.clone_from(&parent.include);
    }

    if merged.exclude.is_none() {
        merged.exclude.clone_from(&parent.exclude);
    }

    let options = &mut merged.compiler_options;
    let parent_options = &parent.compiler_options;

    if options.allow_js.is_none() {
        options.allow_js = parent_options.allow_js;
    }

    if options.out_dir.is_none() {
        options.out_dir.clone_from(&parent_options.out_dir);
    }

    if options.base_url.is_none() {
        options.base_url.clone_from(&parent_options.base_url);
    }

    if options.paths.is_none() {
        options.paths.clone_from(&parent_options.paths);
    }

    merged
}

fn load_tsconfig(
    path: &Path,
    root: bool,
    visited: &mut HashSet<PathBuf>,
) -> Result<TsConfig, ProjectError> {
    if !visited.insert(path.to_path_buf()) {
        return Err(ProjectError::Tsconfig {
            path: path.to_path_buf(),
            message: "extends forms a cycle".to_string(),
        });
    }

    let text = std::fs::read_to_string(path).map_err(|source| ProjectError::Read {
        path: path.to_path_buf(),
        source,
    })?;
    let mut config =
        TsConfig::parse(root, path, path, text).map_err(|error| ProjectError::Tsconfig {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
    let directory = path.parent().map(forward_slashes).unwrap_or_default();

    absolutize(&mut config.include, &directory);
    absolutize(&mut config.exclude, &directory);

    if let Some(files) = &mut config.files {
        for file in files.iter_mut() {
            *file = Path::new(&directory).join(&*file);
        }
    }

    let parents = match config.extends.take() {
        Some(ExtendsField::Single(specifier)) => vec![specifier],
        Some(ExtendsField::Multiple(specifiers)) => specifiers,
        None => Vec::new(),
    };
    let mut base: Option<TsConfig> = None;

    for specifier in parents {
        let parent_path = extended_path(path, &specifier)?;
        let parent = load_tsconfig(&parent_path, false, visited)?;

        base = Some(match base {
            Some(earlier) => merge_extends(parent, &earlier),
            None => parent,
        });
    }

    visited.remove(path);

    Ok(match base {
        Some(parent) => merge_extends(config, &parent),
        None => config,
    })
}

fn extended_path(tsconfig: &Path, specifier: &str) -> Result<PathBuf, ProjectError> {
    let directory = tsconfig.parent().unwrap_or(Path::new(""));
    let relative = specifier.starts_with('.') || Path::new(specifier).is_absolute();
    let candidates: Vec<PathBuf> = if relative {
        let joined = directory.join(specifier);
        let mut with_json = joined.clone().into_os_string();

        with_json.push(".json");

        vec![joined, PathBuf::from(with_json)]
    } else {
        let resolver = Resolver::new(ResolveOptions::default());

        [specifier.to_string(), format!("{specifier}/tsconfig.json")]
            .iter()
            .filter_map(|candidate| resolver.resolve(directory, candidate).ok())
            .map(|resolution| resolution.into_path_buf())
            .collect()
    };

    candidates
        .iter()
        .find(|candidate| candidate.is_file())
        .and_then(|candidate| canonical_path(candidate).ok())
        .ok_or_else(|| ProjectError::Tsconfig {
            path: tsconfig.to_path_buf(),
            message: format!("cannot find extended configuration {specifier}"),
        })
}

fn absolutize(patterns: &mut Option<Vec<PathBuf>>, directory: &str) {
    if let Some(patterns) = patterns {
        for pattern in patterns.iter_mut() {
            *pattern = PathBuf::from(absolute_pattern(directory, &forward_slashes(&*pattern)));
        }
    }
}

fn absolute_pattern(directory: &str, pattern: &str) -> String {
    let pattern = pattern.replace('\\', "/");
    let absolute = pattern.starts_with('/') || Path::new(&pattern).is_absolute();
    let mut segments: Vec<String> = Vec::new();

    if !absolute {
        for segment in directory.split('/') {
            segments.push(escape_literal(segment));
        }
    }

    for (index, segment) in pattern.split('/').enumerate() {
        match segment {
            "." => {}
            "" if !(absolute && index == 0) => {}
            ".." => {
                segments.pop();
            }
            _ => segments.push(escape_pattern(segment)),
        }
    }

    let last = segments.last().map(String::as_str).unwrap_or("");

    if !last.contains(['.', '*', '?']) {
        segments.push("**".to_string());
        segments.push("*".to_string());
    }

    segments.join("/")
}

fn escape_literal(segment: &str) -> String {
    globset::escape(segment)
}

fn escape_pattern(segment: &str) -> String {
    segment
        .chars()
        .map(|character| match character {
            '[' | ']' | '{' | '}' => format!("[{character}]"),
            other => other.to_string(),
        })
        .collect()
}

fn exclusion_patterns(patterns: &[String]) -> Vec<String> {
    let mut expanded = Vec::new();

    for pattern in patterns {
        let trimmed = pattern.strip_suffix("/**/*").unwrap_or(pattern);

        expanded.push(pattern.clone());
        expanded.push(format!("{trimmed}/**"));

        if let Some(directory) = trimmed.strip_suffix("/**") {
            expanded.push(directory.to_string());
        } else {
            expanded.push(trimmed.to_string());
        }
    }

    expanded
}

fn glob_set(patterns: &[String], tsconfig: &Path) -> Result<GlobSet, ProjectError> {
    let mut builder = GlobSetBuilder::new();

    for pattern in patterns {
        let glob = GlobBuilder::new(pattern)
            .literal_separator(true)
            .case_insensitive(cfg!(any(windows, target_os = "macos")))
            .build()
            .map_err(|error| ProjectError::Tsconfig {
                path: tsconfig.to_path_buf(),
                message: error.to_string(),
            })?;

        builder.add(glob);
    }

    builder.build().map_err(|error| ProjectError::Tsconfig {
        path: tsconfig.to_path_buf(),
        message: error.to_string(),
    })
}

fn literal_base_of(pattern: &str) -> String {
    let segments: Vec<&str> = pattern.split('/').collect();
    let literal_count = segments
        .iter()
        .position(|segment| segment.contains(['*', '?', '[', '{']))
        .unwrap_or(segments.len().saturating_sub(1));
    let base = segments[..literal_count].join("/");

    if base.is_empty() || base.ends_with(':') {
        format!("{base}/")
    } else {
        base
    }
}

fn walk(
    directory: &Path,
    include_set: &GlobSet,
    exclude_set: &GlobSet,
    allow_js: bool,
    walked: &mut HashSet<PathBuf>,
    files: &mut Vec<PathBuf>,
) {
    if !walked.insert(directory.to_path_buf()) {
        return;
    }

    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().collect();

    entries.sort_by_key(|entry| entry.file_name());

    for entry in entries {
        let name = entry.file_name();

        let name = name.to_string_lossy();

        if name.starts_with('.') || DEFAULT_EXCLUDES.contains(&name.as_ref()) {
            continue;
        }

        let path = entry.path();
        let text = forward_slashes(&path);

        if exclude_set.is_match(&text) {
            continue;
        }

        let Ok(file_type) = entry.file_type() else {
            continue;
        };

        if file_type.is_dir() {
            walk(&path, include_set, exclude_set, allow_js, walked, files);
        } else if has_selected_extension(&path, allow_js) && include_set.is_match(&text) {
            files.push(path);
        }
    }
}

fn has_selected_extension(path: &Path, allow_js: bool) -> bool {
    let extension = path
        .extension()
        .map(|extension| extension.to_string_lossy().to_ascii_lowercase())
        .unwrap_or_default();

    TYPESCRIPT_EXTENSIONS.contains(&extension.as_str())
        || (allow_js && JAVASCRIPT_EXTENSIONS.contains(&extension.as_str()))
}

#[cfg(test)]
#[path = "tsconfig.test.rs"]
mod tests;

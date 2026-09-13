use std::collections::HashSet;
use std::path::{Path, PathBuf};

use globset::{GlobBuilder, GlobSet, GlobSetBuilder};
use indexmap::IndexMap;
use oxc_resolver::{ExtendsField, ResolveOptions, Resolver, TsConfig};

use crate::project::{canonical_path_of, forward_slashes_of, ProjectError};

pub struct TsconfigFiles {
    pub root_dir: PathBuf,
    pub files: Vec<PathBuf>,
    pub allow_js: bool,
}

const TYPESCRIPT_EXTENSION_GROUPS: &[&[&str]] = &[
    &[".ts", ".tsx", ".d.ts"],
    &[".cts", ".d.cts"],
    &[".mts", ".d.mts"],
];
const ALL_EXTENSION_GROUPS: &[&[&str]] = &[
    &[".ts", ".tsx", ".d.ts", ".js", ".jsx"],
    &[".cts", ".d.cts", ".cjs"],
    &[".mts", ".d.mts", ".mjs"],
];
const PACKAGE_FOLDERS: &[&str] = &["node_modules", "bower_components", "jspm_packages"];
const CASE_INSENSITIVE: bool = cfg!(any(windows, target_os = "macos"));

pub fn select_files(tsconfig: &Path) -> Result<TsconfigFiles, ProjectError> {
    let tsconfig_path = canonical_path_of(tsconfig).map_err(|source| ProjectError::Read {
        path: tsconfig.to_path_buf(),
        source,
    })?;
    let mut visited = HashSet::new();
    let merged = load_tsconfig(&tsconfig_path, true, &mut visited)?;
    let root_dir = tsconfig_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let root_text = forward_slashes_of(&root_dir);
    let include_patterns: Vec<String> = match (&merged.include, &merged.files) {
        (Some(include), _) => include.iter().map(forward_slashes_of).collect(),
        (None, Some(_)) => Vec::new(),
        (None, None) => vec![absolute_pattern_of(&root_text, "**/*")],
    };
    let exclude_patterns: Vec<String> = match &merged.exclude {
        Some(exclude) => exclude.iter().map(forward_slashes_of).collect(),
        None => [
            &merged.compiler_options.out_dir,
            &merged.compiler_options.declaration_dir,
        ]
        .into_iter()
        .flatten()
        .map(|directory| absolute_pattern_of(&forward_slashes_of(directory), ""))
        .collect(),
    };
    let includes: Vec<Vec<String>> = include_patterns
        .iter()
        .filter(|pattern| !pattern.ends_with("/**"))
        .map(|pattern| pattern.split('/').map(str::to_string).collect())
        .collect();
    let exclude_set = glob_set_of(&exclusion_patterns_of(&exclude_patterns), tsconfig)?;
    let allow_js = merged.compiler_options.allow_js.unwrap_or(false);
    let groups = if allow_js {
        ALL_EXTENSION_GROUPS
    } else {
        TYPESCRIPT_EXTENSION_GROUPS
    };
    let mut walk = Walk {
        includes: &includes,
        exclude_set: &exclude_set,
        groups,
        visited: HashSet::new(),
        buckets: vec![Vec::new(); includes.len()],
    };

    for base in base_paths_of(&root_text, &include_patterns) {
        walk.visit(&Path::new(&base).components().collect::<PathBuf>());
    }

    let mut literal: IndexMap<String, PathBuf> = IndexMap::new();

    for file in merged.files.iter().flatten() {
        if let Ok(path) = canonical_path_of(file) {
            if path.is_file() {
                literal.insert(key_of(&path), path);
            }
        }
    }

    let mut wildcard: IndexMap<String, PathBuf> = IndexMap::new();

    for file in walk.buckets.into_iter().flatten() {
        if has_higher_priority_file(&file, &literal, &wildcard, groups) {
            continue;
        }

        remove_lower_priority_files(&file, &mut wildcard, groups);

        let key = key_of(&file);

        if !literal.contains_key(&key) && !wildcard.contains_key(&key) {
            wildcard.insert(key, file);
        }
    }

    Ok(TsconfigFiles {
        root_dir,
        files: literal
            .into_values()
            .chain(wildcard.into_values())
            .collect(),
        allow_js,
    })
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

    if options.declaration_dir.is_none() {
        options
            .declaration_dir
            .clone_from(&parent_options.declaration_dir);
    }

    if options.base_url.is_none() {
        options.base_url.clone_from(&parent_options.base_url);
    }

    if options.paths.is_none() {
        options.paths.clone_from(&parent_options.paths);
    }

    merged
}

fn include_matches(pattern: &[String], path: &[&str], directory: bool) -> bool {
    let Some((component, rest)) = pattern.split_first() else {
        return path.is_empty();
    };
    let Some((segment, remaining)) = path.split_first() else {
        return directory;
    };

    if component == "**" {
        return include_matches(rest, path, directory)
            || (!segment.starts_with('.')
                && !is_package_folder(segment)
                && include_matches(pattern, remaining, directory));
    }

    let last = !directory && rest.is_empty() && remaining.is_empty();

    component_matches(component, segment, last) && include_matches(rest, remaining, directory)
}

struct Walk<'w> {
    includes: &'w [Vec<String>],
    exclude_set: &'w GlobSet,
    groups: &'static [&'static [&'static str]],
    visited: HashSet<PathBuf>,
    buckets: Vec<Vec<PathBuf>>,
}

impl Walk<'_> {
    fn visit(&mut self, directory: &Path) {
        let Ok(canonical) = canonical_path_of(directory) else {
            return;
        };

        if !self.visited.insert(canonical) {
            return;
        }

        let Ok(entries) = std::fs::read_dir(directory) else {
            return;
        };
        let mut files = Vec::new();
        let mut directories = Vec::new();

        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();

            match std::fs::metadata(entry.path()) {
                Ok(metadata) if metadata.is_dir() => directories.push(name),
                Ok(_) => files.push(name),
                Err(_) => {}
            }
        }

        files.sort();
        directories.sort();

        for name in files {
            let path = directory.join(&name);
            let text = forward_slashes_of(&path);

            if !self
                .groups
                .iter()
                .any(|group| extension_of(&text, group).is_some())
                || self.exclude_set.is_match(&text)
            {
                continue;
            }

            let segments: Vec<&str> = text.split('/').collect();

            if let Some(index) = self
                .includes
                .iter()
                .position(|pattern| include_matches(pattern, &segments, false))
            {
                self.buckets[index].push(path);
            }
        }

        for name in directories {
            let path = directory.join(&name);
            let text = forward_slashes_of(&path);
            let segments: Vec<&str> = text.split('/').collect();

            if self
                .includes
                .iter()
                .any(|pattern| include_matches(pattern, &segments, true))
                && !self.exclude_set.is_match(&text)
            {
                self.visit(&path);
            }
        }
    }
}

fn component_matches(component: &str, segment: &str, last: bool) -> bool {
    if !component.contains(['*', '?']) {
        return is_same_name(component, segment);
    }

    if is_package_folder(segment) {
        return false;
    }

    let pattern: Vec<char> = component.chars().collect();
    let name: Vec<char> = segment.chars().collect();

    wildcard_matches(&pattern, &name, 0, true, last)
}

fn wildcard_matches(
    pattern: &[char],
    name: &[char],
    index: usize,
    start: bool,
    last: bool,
) -> bool {
    let Some((token, rest)) = pattern.split_first() else {
        return index == name.len();
    };

    match token {
        '*' if start => {
            wildcard_matches(rest, name, index, false, last)
                || (index < name.len()
                    && name[index] != '.'
                    && star_matches(rest, name, index + 1, last))
        }
        '*' => star_matches(rest, name, index, last),
        '?' => {
            index < name.len()
                && !(start && name[index] == '.')
                && wildcard_matches(rest, name, index + 1, false, last)
        }
        literal => {
            index < name.len()
                && is_same_name(&literal.to_string(), &name[index].to_string())
                && wildcard_matches(rest, name, index + 1, false, last)
        }
    }
}

fn star_matches(rest: &[char], name: &[char], from: usize, last: bool) -> bool {
    let mut index = from;

    loop {
        if wildcard_matches(rest, name, index, false, last) {
            return true;
        }

        if index == name.len() {
            return false;
        }

        if name[index] == '.' && last {
            let after: String = name[index + 1..].iter().collect();

            if is_same_name(&after, "min.js") {
                return false;
            }
        }

        index += 1;
    }
}

fn is_same_name(left: &str, right: &str) -> bool {
    if CASE_INSENSITIVE {
        left.to_lowercase() == right.to_lowercase()
    } else {
        left == right
    }
}

fn is_package_folder(segment: &str) -> bool {
    PACKAGE_FOLDERS
        .iter()
        .any(|folder| is_same_name(folder, segment))
}

fn base_paths_of(root: &str, include_patterns: &[String]) -> Vec<String> {
    let mut bases = vec![root.to_string()];
    let mut include_bases: Vec<String> = include_patterns
        .iter()
        .map(|pattern| include_base_of(pattern))
        .collect();

    if CASE_INSENSITIVE {
        include_bases.sort_by_key(|base| base.to_uppercase());
    } else {
        include_bases.sort();
    }

    for base in include_bases {
        if bases.iter().all(|existing| !contains_path(existing, &base)) {
            bases.push(base);
        }
    }

    bases
}

fn include_base_of(pattern: &str) -> String {
    match pattern.find(['*', '?']) {
        Some(offset) => pattern[..pattern[..offset].rfind('/').unwrap_or(0)].to_string(),
        None => {
            let name = pattern.rsplit('/').next().unwrap_or("");

            if name.contains('.') {
                pattern[..pattern.rfind('/').unwrap_or(0)].to_string()
            } else {
                pattern.to_string()
            }
        }
    }
}

fn contains_path(parent: &str, child: &str) -> bool {
    let parent = parent.trim_end_matches('/');

    is_same_name(parent, child)
        || (child.len() > parent.len()
            && child.is_char_boundary(parent.len())
            && is_same_name(parent, &child[..parent.len()])
            && child[parent.len()..].starts_with('/'))
}

fn key_of(path: &Path) -> String {
    let text = forward_slashes_of(path);

    if CASE_INSENSITIVE {
        text.to_lowercase()
    } else {
        text
    }
}

fn extension_of<'e>(path: &str, group: &[&'e str]) -> Option<&'e str> {
    group
        .iter()
        .filter(|extension| path.len() > extension.len() && path.ends_with(*extension))
        .max_by_key(|extension| extension.len())
        .copied()
}

fn stem_of<'s>(path: &'s str, groups: &[&[&str]]) -> &'s str {
    let length = groups
        .iter()
        .filter_map(|group| extension_of(path, group))
        .map(str::len)
        .max()
        .unwrap_or(0);

    &path[..path.len() - length]
}

fn has_higher_priority_file(
    file: &Path,
    literal: &IndexMap<String, PathBuf>,
    wildcard: &IndexMap<String, PathBuf>,
    groups: &[&[&str]],
) -> bool {
    let text = forward_slashes_of(file);
    let Some(group) = groups
        .iter()
        .find(|group| extension_of(&text, group).is_some())
    else {
        return false;
    };
    let own = extension_of(&text, group);
    let stem = stem_of(&text, groups);

    for extension in group.iter() {
        if own == Some(*extension) {
            return false;
        }

        let key = key_of(Path::new(&format!("{stem}{extension}")));

        if literal.contains_key(&key) || wildcard.contains_key(&key) {
            if *extension == ".d.ts" && matches!(own, Some(".js" | ".jsx")) {
                continue;
            }

            return true;
        }
    }

    false
}

fn remove_lower_priority_files(
    file: &Path,
    wildcard: &mut IndexMap<String, PathBuf>,
    groups: &[&[&str]],
) {
    let text = forward_slashes_of(file);
    let Some(group) = groups
        .iter()
        .find(|group| extension_of(&text, group).is_some())
    else {
        return;
    };
    let own = extension_of(&text, group);
    let stem = stem_of(&text, groups);

    for extension in group.iter().rev() {
        if own == Some(*extension) {
            return;
        }

        wildcard.shift_remove(&key_of(Path::new(&format!("{stem}{extension}"))));
    }
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
    let directory = path.parent().map(forward_slashes_of).unwrap_or_default();

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
        let parent_path = extended_path_of(path, &specifier)?;
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

fn extended_path_of(tsconfig: &Path, specifier: &str) -> Result<PathBuf, ProjectError> {
    let directory = tsconfig.parent().unwrap_or(Path::new(""));
    let normalized = specifier.replace('\\', "/");
    let relative = normalized.starts_with("./")
        || normalized.starts_with("../")
        || normalized.starts_with('/')
        || Path::new(&normalized).is_absolute();
    let candidates: Vec<PathBuf> = if relative {
        let joined = directory.join(&normalized);
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
        .and_then(|candidate| canonical_path_of(candidate).ok())
        .ok_or_else(|| ProjectError::Tsconfig {
            path: tsconfig.to_path_buf(),
            message: format!("cannot find extended configuration {specifier}"),
        })
}

fn absolutize(patterns: &mut Option<Vec<PathBuf>>, directory: &str) {
    if let Some(patterns) = patterns {
        for pattern in patterns.iter_mut() {
            *pattern = PathBuf::from(absolute_pattern_of(
                directory,
                &forward_slashes_of(&*pattern),
            ));
        }
    }
}

fn absolute_pattern_of(directory: &str, pattern: &str) -> String {
    let pattern = pattern.replace('\\', "/");
    let absolute = pattern.starts_with('/') || Path::new(&pattern).is_absolute();
    let mut segments: Vec<String> = Vec::new();

    if !absolute {
        segments.extend(directory.split('/').map(str::to_string));
    }

    for (index, segment) in pattern.split('/').enumerate() {
        match segment {
            "." => {}
            "" if !(absolute && index == 0) => {}
            ".." => {
                segments.pop();
            }
            _ => segments.push(segment.to_string()),
        }
    }

    let last = segments.last().map(String::as_str).unwrap_or("");

    if !last.contains(['.', '*', '?']) {
        segments.push("**".to_string());
        segments.push("*".to_string());
    }

    segments.join("/")
}

fn escape_brackets(pattern: &str) -> String {
    pattern
        .chars()
        .map(|character| match character {
            '[' | ']' | '{' | '}' => format!("[{character}]"),
            other => other.to_string(),
        })
        .collect()
}

fn exclusion_patterns_of(patterns: &[String]) -> Vec<String> {
    let mut expanded = Vec::new();

    for pattern in patterns.iter().map(|pattern| escape_brackets(pattern)) {
        let trimmed = pattern.strip_suffix("/**/*").unwrap_or(&pattern);

        expanded.push(format!("{trimmed}/**"));
        expanded.push(trimmed.strip_suffix("/**").unwrap_or(trimmed).to_string());
        expanded.push(pattern.clone());
    }

    expanded
}

fn glob_set_of(patterns: &[String], tsconfig: &Path) -> Result<GlobSet, ProjectError> {
    let mut builder = GlobSetBuilder::new();

    for pattern in patterns {
        let glob = GlobBuilder::new(pattern)
            .literal_separator(true)
            .case_insensitive(CASE_INSENSITIVE)
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

#[cfg(test)]
#[path = "tsconfig.test.rs"]
mod tests;

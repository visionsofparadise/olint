use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Component, Path, PathBuf};

use oxc_allocator::Allocator;
use oxc_ast::ast::Program;
use oxc_parser::Parser;
use oxc_resolver::{
    ResolveOptions, Resolver, TsconfigDiscovery, TsconfigOptions, TsconfigReferences,
};
use oxc_semantic::{Semantic, SemanticBuilder};
use oxc_span::{SourceType, Span};
use oxc_syntax::module_record::ModuleRecord;

use crate::tsconfig::select_files;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

pub struct SourceFile<'a> {
    pub id: FileId,
    pub path: PathBuf,
    pub relative: String,
    pub text: &'a str,
    pub program: &'a Program<'a>,
    pub semantic: Semantic<'a>,
    pub module_record: &'a ModuleRecord<'a>,
    pub line_starts: Vec<u32>,
}

pub struct Project<'a> {
    pub root: PathBuf,
    pub tsconfig_path: PathBuf,
    pub files: Vec<SourceFile<'a>>,
    by_path: HashMap<PathBuf, FileId>,
    resolver: Resolver,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolved {
    File(FileId),
    External(PathBuf),
    Unresolved,
}

#[derive(Debug)]
pub enum ProjectError {
    Tsconfig {
        path: PathBuf,
        message: String,
    },
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Parse {
        path: PathBuf,
        message: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Site {
    pub file: FileId,
    pub line: u32,
}

const PARSED_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts", "js", "jsx", "mjs", "cjs"];

impl<'a> Project<'a> {
    pub fn load(allocator: &'a Allocator, tsconfig: &Path) -> Result<Project<'a>, ProjectError> {
        let selection = select_files(tsconfig)?;
        let tsconfig_path = canonical_path(tsconfig).map_err(|source| ProjectError::Read {
            path: tsconfig.to_path_buf(),
            source,
        })?;
        let resolver = Resolver::new(ResolveOptions {
            extensions: [".ts", ".tsx", ".mts", ".cts", ".js", ".json"]
                .map(String::from)
                .to_vec(),
            extension_alias: vec![
                (
                    ".js".to_string(),
                    [".ts", ".tsx", ".js"].map(String::from).to_vec(),
                ),
                (
                    ".mjs".to_string(),
                    [".mts", ".mjs"].map(String::from).to_vec(),
                ),
                (
                    ".cjs".to_string(),
                    [".cts", ".cjs"].map(String::from).to_vec(),
                ),
            ],
            main_files: vec!["index".to_string()],
            condition_names: ["import", "types", "default"].map(String::from).to_vec(),
            tsconfig: Some(TsconfigDiscovery::Manual(TsconfigOptions {
                config_file: tsconfig_path.clone(),
                references: TsconfigReferences::Disabled,
            })),
            ..ResolveOptions::default()
        });
        let mut project = Project {
            root: selection.root_dir,
            tsconfig_path,
            files: Vec::new(),
            by_path: HashMap::new(),
            resolver,
        };
        let mut queue: VecDeque<PathBuf> = selection
            .files
            .into_iter()
            .filter(|path| is_parsed_path(path))
            .collect();
        let mut queued: HashSet<PathBuf> = queue.iter().cloned().collect();

        while let Some(path) = queue.pop_front() {
            let id = FileId(project.files.len() as u32);
            let file = parse_file(allocator, id, path, &project.root)?;
            let directory = file.path.parent().unwrap_or(Path::new("")).to_path_buf();
            let mut specifiers: Vec<(u32, &str)> = file
                .module_record
                .requested_modules
                .iter()
                .map(|(specifier, requests)| {
                    let start = requests.iter().map(|request| request.span.start).min();

                    (start.unwrap_or(0), specifier.as_str())
                })
                .collect();

            specifiers.sort_unstable();

            for (_, specifier) in specifiers {
                let Ok(resolution) = project.resolver.resolve(&directory, specifier) else {
                    continue;
                };
                let target = strip_verbatim_prefix(resolution.path());

                if target.starts_with(&project.root)
                    && is_parsed_path(&target)
                    && !forward_slashes(&target).contains("/node_modules/")
                    && queued.insert(target.clone())
                {
                    queue.push_back(target);
                }
            }

            project.by_path.insert(file.path.clone(), id);
            project.files.push(file);
        }

        Ok(project)
    }

    pub fn file(&self, id: FileId) -> &SourceFile<'a> {
        &self.files[id.0 as usize]
    }

    pub fn file_by_path(&self, path: &Path) -> Option<FileId> {
        if let Some(id) = self.by_path.get(path) {
            return Some(*id);
        }

        canonical_path(path)
            .ok()
            .and_then(|canonical| self.by_path.get(&canonical).copied())
    }

    pub fn resolve(&self, from: FileId, specifier: &str) -> Resolved {
        let directory = self.file(from).path.parent().unwrap_or(Path::new(""));

        let resolution = self
            .resolver
            .resolve(directory, specifier)
            .or_else(|_| self.resolver.resolve_dts(&self.file(from).path, specifier));

        match resolution {
            Ok(resolution) => {
                let target = strip_verbatim_prefix(resolution.path());

                match self.file_by_path(&target) {
                    Some(id) => Resolved::File(id),
                    None => Resolved::External(target),
                }
            }
            Err(_) => Resolved::Unresolved,
        }
    }

    pub fn line_of(&self, id: FileId, offset: u32) -> u32 {
        line_in(&self.file(id).line_starts, offset)
    }

    pub fn site_of(&self, id: FileId, span: Span) -> Site {
        Site {
            file: id,
            line: self.line_of(id, span.start),
        }
    }

    pub fn is_project_file(&self, id: FileId) -> bool {
        let file = self.file(id);

        file.path.starts_with(&self.root)
            && !is_declaration_path(&file.path)
            && !forward_slashes(&file.path).contains("/node_modules/")
    }

    pub fn is_test_path(&self, id: FileId) -> bool {
        let file = self.file(id);

        is_test_relative(&forward_slashes(&file.path), &file.relative)
    }
}

pub fn is_test_relative(absolute_forward: &str, relative: &str) -> bool {
    const SUFFIXES: &[&str] = &[".test", ".spec", ".bench", ".benchmark", ".stories"];

    const SEGMENTS: &[&str] = &[
        "test",
        "tests",
        "__tests__",
        "fixtures",
        "scripts",
        "mock",
        "mocks",
    ];

    let has_test_suffix = || {
        let rest = absolute_forward
            .strip_suffix('x')
            .unwrap_or(absolute_forward);
        let rest = rest.strip_suffix('s')?;
        let rest = rest.strip_suffix(['j', 't'])?;
        let rest = rest.strip_suffix(['c', 'm']).unwrap_or(rest);
        let rest = rest.strip_suffix('.')?;

        Some(SUFFIXES.iter().any(|suffix| rest.ends_with(suffix)))
    };

    if has_test_suffix().unwrap_or(false) {
        return true;
    }

    let mut directories: Vec<&str> = relative.split('/').collect();

    directories.pop();

    directories
        .iter()
        .any(|directory| SEGMENTS.contains(directory))
}

pub fn canonical_path(path: &Path) -> std::io::Result<PathBuf> {
    std::fs::canonicalize(path).map(|canonical| strip_verbatim_prefix(&canonical))
}

pub fn forward_slashes(path: impl AsRef<Path>) -> String {
    path.as_ref().to_string_lossy().replace('\\', "/")
}

fn strip_verbatim_prefix(path: &Path) -> PathBuf {
    let text = path.to_string_lossy();

    if let Some(rest) = text.strip_prefix(r"\\?\UNC\") {
        return PathBuf::from(format!(r"\\{rest}"));
    }

    if let Some(rest) = text.strip_prefix(r"\\?\") {
        return PathBuf::from(rest);
    }

    path.to_path_buf()
}

fn is_parsed_path(path: &Path) -> bool {
    let extension = path
        .extension()
        .map(|extension| extension.to_string_lossy().to_ascii_lowercase())
        .unwrap_or_default();

    PARSED_EXTENSIONS.contains(&extension.as_str()) && !is_declaration_path(path)
}

fn is_declaration_path(path: &Path) -> bool {
    let name = path
        .file_name()
        .map(|name| name.to_string_lossy().to_ascii_lowercase())
        .unwrap_or_default();

    [".d.ts", ".d.mts", ".d.cts"]
        .iter()
        .any(|suffix| name.ends_with(suffix))
        || (name.ends_with(".ts") && name.contains(".d."))
}

fn relative_path(root: &Path, path: &Path) -> String {
    let root_components: Vec<Component> = root.components().collect();
    let path_components: Vec<Component> = path.components().collect();
    let shared = root_components
        .iter()
        .zip(&path_components)
        .take_while(|(left, right)| left == right)
        .count();
    let mut segments: Vec<String> = vec!["..".to_string(); root_components.len() - shared];

    segments.extend(
        path_components[shared..]
            .iter()
            .map(|component| component.as_os_str().to_string_lossy().into_owned()),
    );

    segments.join("/")
}

fn line_starts_of(text: &str) -> Vec<u32> {
    let bytes = text.as_bytes();
    let mut starts = vec![0];
    let mut index = 0;

    while index < bytes.len() {
        match bytes[index] {
            b'\r' => {
                if bytes.get(index + 1) == Some(&b'\n') {
                    index += 1;
                }

                starts.push(index as u32 + 1);
            }
            b'\n' => starts.push(index as u32 + 1),
            0xE2 if bytes.get(index + 1) == Some(&0x80)
                && matches!(bytes.get(index + 2), Some(0xA8 | 0xA9)) =>
            {
                index += 2;

                starts.push(index as u32 + 1);
            }
            _ => {}
        }

        index += 1;
    }

    starts
}

fn line_in(line_starts: &[u32], offset: u32) -> u32 {
    line_starts.partition_point(|start| *start <= offset) as u32
}

fn parse_file<'a>(
    allocator: &'a Allocator,
    id: FileId,
    path: PathBuf,
    root: &Path,
) -> Result<SourceFile<'a>, ProjectError> {
    let content = std::fs::read_to_string(&path).map_err(|source| ProjectError::Read {
        path: path.clone(),
        source,
    })?;
    let source_type = SourceType::from_path(&path).map_err(|error| ProjectError::Parse {
        path: path.clone(),
        message: error.to_string(),
    })?;
    let text: &'a str = allocator.alloc_str(&content);
    let parsed = Parser::new(allocator, text, source_type).parse();

    if parsed.fatal_error {
        let message = parsed
            .diagnostics
            .iter()
            .next()
            .map(ToString::to_string)
            .unwrap_or_else(|| "unrecoverable syntax error".to_string());

        return Err(ProjectError::Parse { path, message });
    }

    let program: &'a Program<'a> = allocator.alloc(parsed.program);
    let module_record: &'a ModuleRecord<'a> = allocator.alloc(parsed.module_record);
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(program)
        .semantic;

    Ok(SourceFile {
        id,
        relative: relative_path(root, &path),
        path,
        text,
        program,
        semantic,
        module_record,
        line_starts: line_starts_of(text),
    })
}

#[cfg(test)]
#[path = "project.test.rs"]
mod tests;

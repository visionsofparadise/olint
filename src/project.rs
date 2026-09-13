use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};

use oxc_allocator::Allocator;
use oxc_ast::ast::{Program, Statement, TSModuleReference};
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
    pub external_library: bool,
}

pub struct Project<'a> {
    pub root: PathBuf,
    pub tsconfig_path: PathBuf,
    pub files: Vec<SourceFile<'a>>,
    by_path: HashMap<PathBuf, FileId>,
    resolver: Resolver,
    configless_resolver: Resolver,
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

enum Frame<'a> {
    Open {
        file: Box<SourceFile<'a>>,
        next: usize,
    },
    Rewalk {
        path: PathBuf,
        next: usize,
    },
}

struct Walk<'a> {
    imports: HashMap<PathBuf, Vec<Import>>,
    externally_walked: HashSet<PathBuf>,
    stack: Vec<Frame<'a>>,
}

struct Import {
    target: PathBuf,
    external: bool,
}

const PARSED_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts", "js", "jsx", "mjs", "cjs"];
const TYPESCRIPT_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts"];
const JAVASCRIPT_EXTENSIONS: &[&str] = &["js", "jsx", "mjs", "cjs"];

impl<'a> Project<'a> {
    pub fn load(allocator: &'a Allocator, tsconfig: &Path) -> Result<Project<'a>, ProjectError> {
        let selection = select_files(tsconfig)?;
        let tsconfig_path = canonical_path_of(tsconfig).map_err(|source| ProjectError::Read {
            path: tsconfig.to_path_buf(),
            source,
        })?;
        let configless_resolver = Resolver::new(ResolveOptions {
            tsconfig: None,
            ..resolve_options_of(&tsconfig_path)
        });
        let resolver = Resolver::new(resolve_options_of(&tsconfig_path));
        let mut project = Project {
            root: selection.root_dir,
            tsconfig_path,
            files: Vec::new(),
            by_path: HashMap::new(),
            resolver,
            configless_resolver,
        };
        let allow_js = selection.allow_js;
        let mut walk = Walk {
            imports: HashMap::new(),
            externally_walked: HashSet::new(),
            stack: Vec::new(),
        };

        for root in selection.files {
            if is_parsed_path(&root, allow_js) {
                project.visit(allocator, root, false, allow_js, &mut walk)?;
            }

            while let Some(top) = walk.stack.last_mut() {
                let (path, next) = match top {
                    Frame::Open { file, next } => (file.path.clone(), next),
                    Frame::Rewalk { path, next } => (path.clone(), next),
                };
                let external = walk.externally_walked.contains(&path);
                let import = walk
                    .imports
                    .get(&path)
                    .and_then(|found| found.get(*next))
                    .map(|import| (import.target.clone(), external || import.external));

                match import {
                    Some((target, external)) => {
                        *next += 1;

                        project.visit(allocator, target, external, allow_js, &mut walk)?;
                    }
                    None => {
                        if let Some(Frame::Open { mut file, .. }) = walk.stack.pop() {
                            file.id = FileId(project.files.len() as u32);

                            if let Ok(canonical) = canonical_path_of(&file.path) {
                                if canonical == file.path {
                                    project.by_path.insert(canonical, file.id);
                                } else {
                                    project.by_path.entry(canonical).or_insert(file.id);
                                }
                            }

                            project.by_path.insert(file.path.clone(), file.id);
                            project.files.push(*file);
                        }
                    }
                }
            }
        }

        Ok(project)
    }

    fn visit(
        &mut self,
        allocator: &'a Allocator,
        path: PathBuf,
        external: bool,
        allow_js: bool,
        walk: &mut Walk<'a>,
    ) -> Result<(), ProjectError> {
        let declaration = is_declaration_path(&path);
        let stored = self
            .by_path
            .get(&path)
            .copied()
            .filter(|id| is_same_written_path(&self.files[id.0 as usize].path, &path));
        let open = stored.is_none()
            && walk
                .stack
                .iter()
                .any(|frame| matches!(frame, Frame::Open { file, .. } if file.path == path));

        if stored.is_some() || open {
            if !external && walk.externally_walked.remove(&path) {
                if !declaration {
                    match stored {
                        Some(id) => self.files[id.0 as usize].external_library = false,
                        None => {
                            for frame in &mut walk.stack {
                                if let Frame::Open { file, .. } = frame {
                                    if file.path == path {
                                        file.external_library = false;
                                    }
                                }
                            }
                        }
                    }
                }

                walk.stack.push(Frame::Rewalk { path, next: 0 });
            }

            return Ok(());
        }

        let mut file = match parse_file(allocator, path, &self.root) {
            Ok(file) => file,
            Err(_) if declaration => return Ok(()),
            Err(error) => return Err(error),
        };

        file.external_library = external || declaration;

        if external {
            walk.externally_walked.insert(file.path.clone());
        }

        walk.imports
            .insert(file.path.clone(), self.imports_of(&file, allow_js));
        walk.stack.push(Frame::Open {
            file: Box::new(file),
            next: 0,
        });

        Ok(())
    }

    fn imports_of(&self, file: &SourceFile<'a>, allow_js: bool) -> Vec<Import> {
        let directory = file.path.parent().unwrap_or(Path::new("")).to_path_buf();
        let tsconfig = self.resolver.resolve_tsconfig(&self.tsconfig_path).ok();

        import_specifiers_of(file)
            .into_iter()
            .filter_map(|specifier| {
                let resolution = self.resolver.resolve(&directory, &specifier).ok()?;
                let target = strip_verbatim_prefix(resolution.path());
                let target = canonical_path_of(&target).unwrap_or(target);
                let mapped = tsconfig.as_ref().is_some_and(|tsconfig| {
                    tsconfig
                        .resolve_path_alias_or_base_url(&specifier)
                        .iter()
                        .filter_map(|candidate| {
                            self.configless_resolver
                                .resolve(&directory, &candidate.to_string_lossy())
                                .ok()
                        })
                        .any(|candidate| {
                            let candidate = strip_verbatim_prefix(candidate.path());

                            canonical_path_of(&candidate).unwrap_or(candidate) == target
                        })
                });
                let package_lookup = is_package_specifier(&specifier) && !mapped;
                let external =
                    package_lookup || forward_slashes_of(&target).contains("/node_modules/");

                (is_parsed_path(&target, allow_js)
                    && !(package_lookup && is_javascript_path(&target)))
                .then_some(Import { target, external })
            })
            .collect()
    }

    pub fn file(&self, id: FileId) -> &SourceFile<'a> {
        &self.files[id.0 as usize]
    }

    pub fn file_by_path(&self, path: &Path) -> Option<FileId> {
        if let Some(id) = self.by_path.get(path) {
            return Some(*id);
        }

        canonical_path_of(path)
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
        line_of_offset(&self.file(id).line_starts, offset)
    }

    pub fn site_of(&self, id: FileId, span: Span) -> Site {
        Site {
            file: id,
            line: self.line_of(id, span.start),
        }
    }

    pub fn is_project_file(&self, id: FileId) -> bool {
        let file = self.file(id);

        !file.external_library
            && !is_declaration_path(&file.path)
            && !forward_slashes_of(&file.path).contains("/node_modules/")
    }

    pub fn is_test_path(&self, id: FileId) -> bool {
        let file = self.file(id);

        is_test_relative(&forward_slashes_of(&file.path), &file.relative)
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

pub fn canonical_path_of(path: &Path) -> std::io::Result<PathBuf> {
    std::fs::canonicalize(path).map(|canonical| strip_verbatim_prefix(&canonical))
}

pub fn forward_slashes_of(path: impl AsRef<Path>) -> String {
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

fn is_same_written_path(stored: &Path, path: &Path) -> bool {
    if cfg!(any(windows, target_os = "macos")) {
        stored
            .to_string_lossy()
            .eq_ignore_ascii_case(&path.to_string_lossy())
    } else {
        stored == path
    }
}

fn is_parsed_path(path: &Path, allow_js: bool) -> bool {
    let extension = path
        .extension()
        .map(|extension| extension.to_string_lossy().into_owned())
        .unwrap_or_default();
    let allowed = if allow_js {
        PARSED_EXTENSIONS
    } else {
        TYPESCRIPT_EXTENSIONS
    };

    allowed.contains(&extension.as_str())
}

fn resolve_options_of(tsconfig: &Path) -> ResolveOptions {
    ResolveOptions {
        extensions: [".ts", ".tsx", ".d.ts", ".mts", ".cts", ".js", ".json"]
            .map(String::from)
            .to_vec(),
        extension_alias: vec![
            (
                ".js".to_string(),
                [".ts", ".tsx", ".d.ts", ".js"].map(String::from).to_vec(),
            ),
            (
                ".mjs".to_string(),
                [".mts", ".d.mts", ".mjs"].map(String::from).to_vec(),
            ),
            (
                ".cjs".to_string(),
                [".cts", ".d.cts", ".cjs"].map(String::from).to_vec(),
            ),
        ],
        main_fields: ["typings", "types", "main"].map(String::from).to_vec(),
        main_files: vec!["index".to_string()],
        condition_names: ["import", "types", "default"].map(String::from).to_vec(),
        tsconfig: Some(TsconfigDiscovery::Manual(TsconfigOptions {
            config_file: tsconfig.to_path_buf(),
            references: TsconfigReferences::Disabled,
        })),
        ..ResolveOptions::default()
    }
}

fn is_package_specifier(specifier: &str) -> bool {
    !(specifier.starts_with('.')
        || specifier.starts_with('/')
        || specifier.starts_with('#')
        || Path::new(specifier).is_absolute())
}

fn is_javascript_path(path: &Path) -> bool {
    path.extension().is_some_and(|extension| {
        JAVASCRIPT_EXTENSIONS.contains(&extension.to_string_lossy().as_ref())
    })
}

fn import_specifiers_of(file: &SourceFile<'_>) -> Vec<String> {
    let mut static_imports: Vec<(u32, String)> = file
        .module_record
        .requested_modules
        .iter()
        .filter_map(|(specifier, requests)| {
            let start = requests.iter().map(|request| request.span.start).min()?;

            Some((start, specifier.to_string()))
        })
        .collect();

    for statement in &file.program.body {
        if let Statement::TSImportEqualsDeclaration(declaration) = statement {
            if let TSModuleReference::ExternalModuleReference(reference) =
                &declaration.module_reference
            {
                static_imports.push((
                    declaration.span.start,
                    reference.expression.value.to_string(),
                ));
            }
        }
    }

    static_imports.sort_by_key(|(start, _)| *start);

    let dynamic_imports = file
        .module_record
        .dynamic_imports
        .iter()
        .filter_map(|import| {
            let text = import.module_request.source_text(file.text);
            let quote = text.chars().next()?;

            matches!(quote, '"' | '\'' | '`')
                .then(|| text.strip_prefix(quote)?.strip_suffix(quote))
                .flatten()
                .filter(|inner| !(quote == '`' && inner.contains("${")))
                .map(str::to_string)
        });

    static_imports
        .into_iter()
        .map(|(_, specifier)| specifier)
        .chain(dynamic_imports)
        .collect()
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

fn relative_path_of(root: &Path, path: &Path) -> String {
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

fn line_of_offset(line_starts: &[u32], offset: u32) -> u32 {
    line_starts.partition_point(|start| *start <= offset) as u32
}

fn parse_file<'a>(
    allocator: &'a Allocator,
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
        id: FileId(u32::MAX),
        relative: relative_path_of(root, &path),
        path,
        text,
        program,
        semantic,
        module_record,
        line_starts: line_starts_of(text),
        external_library: false,
    })
}

#[cfg(test)]
#[path = "project.test.rs"]
mod tests;

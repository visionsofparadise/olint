use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use oxc_allocator::Allocator;
use oxc_ast::ast::{Argument, CallExpression, Expression, Program, Statement, TSModuleReference};
use oxc_ast::AstKind;
use oxc_parser::Parser;
use oxc_resolver::{
    ResolveOptions, Resolver, TsconfigDiscovery, TsconfigOptions, TsconfigReferences,
};
use oxc_semantic::{NodeId, Semantic, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::module_record::ModuleRecord;

use crate::flow::{FlowContext, FlowError, FlowIndex, FlowSummary};
use crate::unknowns::UnknownReason;

use crate::paths::{
    canonical_path_of, forward_slashes_of, relative_path_of, strip_verbatim_prefix,
};
use crate::tsconfig::{select_files, SelectedProject};

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
    pub implementation: bool,
    pub owners: Vec<usize>,
    pub diagnostics: Vec<SourceDiagnostic>,
    flow_index: FlowIndex,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticPhase {
    Parse,
    Semantic,
}

#[derive(Clone, Debug)]
pub struct SourceDiagnostic {
    pub phase: DiagnosticPhase,
    pub message: String,
    pub spans: Vec<Span>,
}

#[derive(Clone, Debug)]
pub struct FlowFailure {
    pub file: FileId,
    pub span: Span,
    pub error: FlowError,
}

impl FlowFailure {
    pub fn unknown_reason(&self) -> UnknownReason {
        match self.error {
            FlowError::ResourceLimit => UnknownReason::ResourceExhaustion,
            _ => UnknownReason::UnsupportedSyntax,
        }
    }
}

impl<'a> SourceFile<'a> {
    pub(crate) fn children_of(&self, node: NodeId) -> &[NodeId] {
        self.flow_index.children_of(node)
    }

    pub fn flow_context(&self) -> Result<FlowContext<'_, 'a>, FlowFailure> {
        if !self.diagnostics.is_empty() {
            return Err(self.flow_failure(FlowError::InvalidSource, self.program.span));
        }

        Ok(FlowContext::from_index(&self.semantic, &self.flow_index))
    }

    pub fn flow(&self, function: NodeId) -> Result<FlowSummary, FlowFailure> {
        self.flow_with_limit(function, 20_000)
    }

    pub fn flow_with_limit(
        &self,
        function: NodeId,
        limit: usize,
    ) -> Result<FlowSummary, FlowFailure> {
        self.flow_context()?
            .build_with_limit(self.id, function, limit)
            .map_err(|error| {
                let node = match error {
                    FlowError::InvalidTarget(node) | FlowError::Unsupported(node) => node,
                    _ => function,
                };
                let span = if node.index() < self.semantic.nodes().len() {
                    self.semantic.nodes().kind(node).span()
                } else {
                    self.program.span
                };

                self.flow_failure(error, span)
            })
    }

    fn flow_failure(&self, error: FlowError, span: Span) -> FlowFailure {
        FlowFailure {
            file: self.id,
            span,
            error,
        }
    }
}

pub struct Project<'a> {
    pub root: PathBuf,
    pub tsconfig_path: PathBuf,
    pub files: Vec<SourceFile<'a>>,
    by_path: HashMap<PathBuf, FileId>,
    resolvers: Vec<Resolver>,
    pub configurations: Vec<SelectedProject>,
    configless_resolver: Resolver,
    runtime_resolvers: [Resolver; 2],
    counterparts: HashMap<FileId, FileId>,
    implementation_limit: usize,
    implementation_stats: Cell<ImplementationStats>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolved {
    File(FileId),
    External(PathBuf),
    Unresolved,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RequestKind {
    Static,
    Dynamic,
    Require,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuntimeCondition {
    Import,
    Require,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RuntimeTarget {
    Implementation(PathBuf),
    Boundary(PathBuf),
    Unresolved,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ImplementationStats {
    pub resolutions: usize,
    pub files: usize,
    pub exhausted: bool,
}

pub const IMPLEMENTATION_FILE_LIMIT: usize = 4096;

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
    owner: usize,
    imports: HashMap<PathBuf, Vec<Import>>,
    externally_walked: HashSet<PathBuf>,
    stack: Vec<Frame<'a>>,
    pairs: Vec<(PathBuf, PathBuf)>,
}

struct Import {
    target: PathBuf,
    external: bool,
    runtime: bool,
}

const PARSED_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts", "js", "jsx", "mjs", "cjs"];
const TYPESCRIPT_EXTENSIONS: &[&str] = &["ts", "tsx", "mts", "cts"];
const JAVASCRIPT_EXTENSIONS: &[&str] = &["js", "jsx", "mjs", "cjs"];

impl<'a> Project<'a> {
    pub fn load(allocator: &'a Allocator, tsconfig: &Path) -> Result<Project<'a>, ProjectError> {
        Self::load_with_limit(allocator, tsconfig, IMPLEMENTATION_FILE_LIMIT)
    }

    pub fn load_with_limit(
        allocator: &'a Allocator,
        tsconfig: &Path,
        implementation_limit: usize,
    ) -> Result<Project<'a>, ProjectError> {
        let selection = select_files(tsconfig)?;
        let tsconfig_path = canonical_path_of(tsconfig).map_err(|source| ProjectError::Read {
            path: tsconfig.to_path_buf(),
            source,
        })?;
        let configless_resolver = Resolver::new(ResolveOptions {
            tsconfig: None,
            ..resolve_options_of(&tsconfig_path)
        });
        let resolvers = selection
            .projects
            .iter()
            .map(|selected| Resolver::new(resolve_options_of(&selected.path)))
            .collect();
        let mut project = Project {
            root: selection.root_dir,
            tsconfig_path,
            files: Vec::new(),
            by_path: HashMap::new(),
            resolvers,
            configurations: selection.projects,
            configless_resolver,
            runtime_resolvers: [
                Resolver::new(runtime_options_of(RuntimeCondition::Import)),
                Resolver::new(runtime_options_of(RuntimeCondition::Require)),
            ],
            counterparts: HashMap::new(),
            implementation_limit,
            implementation_stats: Cell::new(ImplementationStats::default()),
        };
        let mut pairs: Vec<(PathBuf, PathBuf)> = Vec::new();

        for owner in 0..project.configurations.len() {
            let selected = project.configurations[owner].clone();
            let allow_js = selected.allow_js;
            let mut walk = Walk {
                owner,
                imports: HashMap::new(),
                externally_walked: HashSet::new(),
                stack: Vec::new(),
                pairs: Vec::new(),
            };

            for root in selected.files {
                if is_parsed_path(&root, allow_js) {
                    project.visit(allocator, root, false, false, allow_js, &mut walk)?;
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
                        .map(|import| {
                            (
                                import.target.clone(),
                                external || import.external,
                                import.runtime,
                            )
                        });

                    match import {
                        Some((target, external, runtime)) => {
                            *next += 1;

                            project
                                .visit(allocator, target, external, runtime, allow_js, &mut walk)?;
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

            pairs.append(&mut walk.pairs);
        }

        let mut counterparts: HashMap<FileId, Option<FileId>> = HashMap::new();

        for (runtime, declared) in pairs {
            let (Some(runtime), Some(declared)) = (
                project.file_by_path(&runtime),
                project.file_by_path(&declared),
            ) else {
                continue;
            };
            let entry = counterparts.entry(runtime).or_insert(Some(declared));

            if *entry != Some(declared) {
                *entry = None;
            }
        }

        project.counterparts = counterparts
            .into_iter()
            .filter_map(|(runtime, declared)| Some((runtime, declared?)))
            .collect();

        Ok(project)
    }

    fn visit(
        &mut self,
        allocator: &'a Allocator,
        path: PathBuf,
        external: bool,
        runtime: bool,
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

        if let Some(id) = stored {
            if !self.files[id.0 as usize].owners.contains(&walk.owner) {
                let imports = self.imports_of(&self.files[id.0 as usize], allow_js, walk)?;
                let file = &mut self.files[id.0 as usize];

                file.owners.push(walk.owner);

                file.external_library &= external || declaration;

                if external {
                    walk.externally_walked.insert(path.clone());
                }

                walk.imports.insert(path.clone(), imports);
                walk.stack.push(Frame::Rewalk { path, next: 0 });

                return Ok(());
            }
        }

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

        if runtime {
            let mut stats = self.implementation_stats.get();

            if stats.files >= self.implementation_limit {
                stats.exhausted = true;

                self.implementation_stats.set(stats);

                return Ok(());
            }

            stats.files += 1;

            self.implementation_stats.set(stats);
        }

        let mut file = match parse_file(allocator, path, &self.root) {
            Ok(file) => file,
            Err(_) if declaration || runtime => return Ok(()),
            Err(error) => return Err(error),
        };

        file.external_library = external || declaration;
        file.implementation = runtime;

        file.owners.push(walk.owner);

        if external {
            walk.externally_walked.insert(file.path.clone());
        }

        let imports = self.imports_of(&file, allow_js, walk)?;

        walk.imports.insert(file.path.clone(), imports);
        walk.stack.push(Frame::Open {
            file: Box::new(file),
            next: 0,
        });

        Ok(())
    }

    fn imports_of(
        &self,
        file: &SourceFile<'a>,
        allow_js: bool,
        walk: &mut Walk<'a>,
    ) -> Result<Vec<Import>, ProjectError> {
        let owner = walk.owner;
        let directory = file.path.parent().unwrap_or(Path::new("")).to_path_buf();
        let resolver = &self.resolvers[owner];
        let tsconfig = resolver
            .resolve_tsconfig(&self.configurations[owner].path)
            .ok();
        let mut imports: Vec<Import> = Vec::new();

        for (specifier, kind, typed) in module_requests_of(file) {
            let mut declared = None;

            if typed && !file.implementation {
                if let Ok(resolution) = resolver.resolve(&directory, &specifier) {
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
                    let loaded = is_parsed_path(&target, allow_js)
                        && !(package_lookup && is_javascript_path(&target));

                    if loaded {
                        imports.push(Import {
                            target: target.clone(),
                            external,
                            runtime: false,
                        });
                    }

                    if !package_lookup {
                        if let Some(implementation) =
                            local_implementation_of(&target, &specifier, allow_js)
                        {
                            walk.pairs.push((implementation.clone(), target.clone()));
                            imports.push(Import {
                                target: implementation,
                                external: false,
                                runtime: false,
                            });
                        }
                    }

                    declared = Some((target, external, loaded));
                }
            }

            let runtime = file.implementation
                || (is_package_specifier(&specifier)
                    && !self.is_path_mapped(&directory, owner, &specifier)
                    && declared.as_ref().is_none_or(|(_, external, _)| *external));

            if !runtime {
                continue;
            }

            if let RuntimeTarget::Implementation(target) =
                self.runtime_target_of(file, &specifier, kind, &[owner])
            {
                if let Some((declared, _, loaded)) = &declared {
                    if *declared == target && *loaded {
                        continue;
                    }

                    if *declared != target {
                        walk.pairs.push((target.clone(), declared.clone()));
                    }
                }

                imports.push(Import {
                    target,
                    external: true,
                    runtime: true,
                });
            }
        }

        for reference in reference_paths_of(file.text) {
            let path = reference_target_of(&directory, reference, allow_js);
            let target =
                canonical_path_of(&path).map_err(|source| ProjectError::Read { path, source })?;

            if !target.is_file() || !is_parsed_path(&target, allow_js) {
                return Err(ProjectError::Parse {
                    path: file.path.clone(),
                    message: format!(
                        "referenced path {} must be a supported source file",
                        target.display()
                    ),
                });
            }

            imports.push(Import {
                target,
                external: false,
                runtime: false,
            });
        }

        Ok(imports)
    }

    fn is_path_mapped(&self, directory: &Path, owner: usize, specifier: &str) -> bool {
        self.resolvers[owner]
            .resolve_tsconfig(&self.configurations[owner].path)
            .ok()
            .is_some_and(|tsconfig| {
                tsconfig
                    .resolve_path_alias_or_base_url(specifier)
                    .iter()
                    .any(|candidate| {
                        self.configless_resolver
                            .resolve(directory, &candidate.to_string_lossy())
                            .is_ok()
                    })
            })
    }

    fn runtime_target_of(
        &self,
        file: &SourceFile<'a>,
        specifier: &str,
        kind: RequestKind,
        owners: &[usize],
    ) -> RuntimeTarget {
        let directory = file.path.parent().unwrap_or(Path::new(""));
        let mut found: Option<RuntimeTarget> = None;

        for condition in self.conditions_of(file, kind, owners) {
            let mut stats = self.implementation_stats.get();

            stats.resolutions += 1;

            self.implementation_stats.set(stats);

            let resolver = match condition {
                RuntimeCondition::Import => &self.runtime_resolvers[0],
                RuntimeCondition::Require => &self.runtime_resolvers[1],
            };
            let target = match resolver.resolve(directory, specifier) {
                Ok(resolution) => {
                    let path = strip_verbatim_prefix(resolution.path());
                    let path = canonical_path_of(&path).unwrap_or(path);

                    if is_parsed_path(&path, true) && !is_declaration_path(&path) {
                        RuntimeTarget::Implementation(path)
                    } else {
                        RuntimeTarget::Boundary(path)
                    }
                }
                Err(_) => RuntimeTarget::Unresolved,
            };

            match &found {
                None => found = Some(target),
                Some(previous) if *previous != target => return RuntimeTarget::Unresolved,
                Some(_) => {}
            }
        }

        found.unwrap_or(RuntimeTarget::Unresolved)
    }

    fn conditions_of(
        &self,
        file: &SourceFile<'a>,
        kind: RequestKind,
        owners: &[usize],
    ) -> Vec<RuntimeCondition> {
        if kind == RequestKind::Require {
            return vec![RuntimeCondition::Require];
        }

        let extension = file
            .path
            .extension()
            .map(|extension| extension.to_string_lossy().to_ascii_lowercase())
            .unwrap_or_default();

        match extension.as_str() {
            "mjs" | "mts" => return vec![RuntimeCondition::Import],
            "cjs" | "cts" if kind == RequestKind::Static => return vec![RuntimeCondition::Require],
            "cjs" | "cts" => return vec![RuntimeCondition::Import],
            _ => {}
        }

        if file.implementation || file.external_library {
            return vec![RuntimeCondition::Import];
        }

        let mut conditions = Vec::new();

        for owner in owners {
            let module = self.configurations[*owner]
                .output
                .module
                .as_deref()
                .map(str::to_ascii_lowercase);
            let found: &[RuntimeCondition] = match module.as_deref() {
                Some("commonjs") => &[RuntimeCondition::Require],
                Some("node16" | "node18" | "node20" | "nodenext") => {
                    if kind == RequestKind::Dynamic || is_module_package_path(&file.path) {
                        &[RuntimeCondition::Import]
                    } else {
                        &[RuntimeCondition::Require]
                    }
                }
                Some("es6" | "es2015" | "es2020" | "es2022" | "esnext" | "preserve") => {
                    &[RuntimeCondition::Import]
                }
                _ => &[RuntimeCondition::Import, RuntimeCondition::Require],
            };

            for condition in found {
                if !conditions.contains(condition) {
                    conditions.push(*condition);
                }
            }
        }

        conditions
    }

    pub fn implementation_of(&self, from: FileId, specifier: &str, kind: RequestKind) -> Resolved {
        let file = self.file(from);
        let declared = self.resolve(from, specifier);

        if !file.implementation {
            let directory = file.path.parent().unwrap_or(Path::new(""));

            if !is_package_specifier(specifier)
                || file
                    .owners
                    .iter()
                    .any(|owner| self.is_path_mapped(directory, *owner, specifier))
                || matches!(declared, Resolved::File(id) if self.is_project_file(id))
            {
                return match declared {
                    Resolved::File(id) => file
                        .owners
                        .iter()
                        .map(|owner| {
                            local_implementation_of(
                                &self.file(id).path,
                                specifier,
                                self.configurations[*owner].allow_js,
                            )
                        })
                        .reduce(|left, right| if left == right { left } else { None })
                        .flatten()
                        .and_then(|implementation| self.file_by_path(&implementation))
                        .map_or(declared, Resolved::File),
                    declared => declared,
                };
            }
        }

        match self.runtime_target_of(file, specifier, kind, &file.owners) {
            RuntimeTarget::Implementation(path) => match self.file_by_path(&path) {
                Some(id) => Resolved::File(id),
                None => Resolved::External(path),
            },
            RuntimeTarget::Boundary(path) => Resolved::External(path),
            RuntimeTarget::Unresolved => Resolved::Unresolved,
        }
    }

    pub fn counterpart_of(&self, id: FileId) -> Option<FileId> {
        self.counterparts.get(&id).copied()
    }

    pub fn implementation_stats(&self) -> ImplementationStats {
        self.implementation_stats.get()
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

        let mut answers = self.file(from).owners.iter().map(|owner| {
            let resolver = &self.resolvers[*owner];

            match resolver
                .resolve(directory, specifier)
                .or_else(|_| resolver.resolve_dts(&self.file(from).path, specifier))
            {
                Ok(resolution) => {
                    let target = strip_verbatim_prefix(resolution.path());

                    match self.file_by_path(&target) {
                        Some(id) => Resolved::File(id),
                        None => Resolved::External(target),
                    }
                }
                Err(_) => Resolved::Unresolved,
            }
        });
        let first = answers.next().unwrap_or(Resolved::Unresolved);

        if answers.all(|answer| answer == first) {
            first
        } else {
            Resolved::Unresolved
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

fn is_same_written_path(stored: &Path, path: &Path) -> bool {
    if cfg!(any(windows, target_os = "macos")) {
        stored
            .to_string_lossy()
            .eq_ignore_ascii_case(&path.to_string_lossy())
    } else {
        stored == path
    }
}

fn reference_target_of(directory: &Path, reference: &str, allow_js: bool) -> PathBuf {
    let path = directory.join(reference);

    if path
        .file_name()
        .is_some_and(|name| !name.to_string_lossy().contains('.'))
    {
        for extension in [".ts", ".tsx", ".d.ts", ".js", ".jsx"] {
            if !allow_js && matches!(extension, ".js" | ".jsx") {
                continue;
            }

            let mut candidate = path.as_os_str().to_os_string();

            candidate.push(extension);

            let candidate = PathBuf::from(candidate);

            if candidate.is_file() {
                return candidate;
            }
        }
    }

    path
}

pub fn reference_paths_of(text: &str) -> Vec<&str> {
    let mut text = text.trim_start_matches('\u{feff}');
    let mut paths = Vec::new();

    if text.starts_with("#!") {
        text = text.find(['\r', '\n']).map_or("", |end| &text[end..]);
    }

    loop {
        text = text.trim_start_matches(|character: char| {
            character.is_whitespace() || character == '\u{feff}'
        });

        if text.starts_with("//") {
            let end = text
                .find(['\r', '\n', '\u{2028}', '\u{2029}'])
                .unwrap_or(text.len());
            let comment = &text[..end];

            if let Some(directive) = comment
                .strip_prefix("///")
                .map(|value| value.trim_start_matches(reference_whitespace))
                .and_then(|value| value.strip_prefix('<'))
            {
                let name_end = directive
                    .find(reference_whitespace)
                    .unwrap_or(directive.len());

                if directive[..name_end].eq_ignore_ascii_case("reference")
                    && directive[name_end..].contains("/>")
                    && reference_attribute(comment, "types").is_none()
                    && reference_attribute(comment, "lib").is_none()
                    && reference_attribute(comment, "no-default-lib") != Some("true")
                {
                    if let Some(path) = reference_attribute(comment, "path") {
                        paths.push(path);
                    }
                }
            }

            text = &text[end..];
        } else if let Some(comment) = text.strip_prefix("/*") {
            let Some(end) = comment.find("*/") else {
                break;
            };
            text = &comment[end + 2..];
        } else {
            break;
        }
    }

    paths
}

fn reference_attribute<'s>(text: &'s str, name: &str) -> Option<&'s str> {
    for (offset, character) in text.char_indices() {
        if !reference_whitespace(character) {
            continue;
        }

        let rest = &text[offset + character.len_utf8()..];
        let Some(prefix) = rest.get(..name.len()) else {
            continue;
        };

        if !prefix.eq_ignore_ascii_case(name) {
            continue;
        }

        let Some(value) = rest[name.len()..]
            .trim_start_matches(reference_whitespace)
            .strip_prefix('=')
            .map(|value| value.trim_start_matches(reference_whitespace))
        else {
            continue;
        };
        let quote = value.chars().next()?;

        if quote != '\'' && quote != '"' {
            continue;
        }

        let value = &value[1..];

        if let Some(end) = value.find(quote) {
            return Some(&value[..end]);
        }
    }

    None
}

fn reference_whitespace(character: char) -> bool {
    matches!(character, '\u{0009}'..='\u{000d}' | '\u{0020}' | '\u{00a0}' | '\u{1680}' | '\u{2000}'..='\u{200a}' | '\u{2028}' | '\u{2029}' | '\u{202f}' | '\u{205f}' | '\u{3000}' | '\u{feff}')
}

pub(crate) fn is_parsed_path(path: &Path, allow_js: bool) -> bool {
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
        extensions: [
            ".ts", ".tsx", ".d.ts", ".mts", ".cts", ".js", ".jsx", ".json",
        ]
        .map(String::from)
        .to_vec(),
        extension_alias: vec![
            (
                ".js".to_string(),
                [".ts", ".tsx", ".d.ts", ".js", ".jsx"]
                    .map(String::from)
                    .to_vec(),
            ),
            (
                ".jsx".to_string(),
                [".tsx", ".ts", ".d.ts", ".jsx", ".js"]
                    .map(String::from)
                    .to_vec(),
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

fn runtime_options_of(condition: RuntimeCondition) -> ResolveOptions {
    let condition = match condition {
        RuntimeCondition::Import => "import",
        RuntimeCondition::Require => "require",
    };

    ResolveOptions {
        condition_names: ["node", condition, "default"].map(String::from).to_vec(),
        node_path: false,
        builtin_modules: true,
        ..ResolveOptions::default()
    }
}

fn is_module_package_path(path: &Path) -> bool {
    path.ancestors().skip(1).find_map(|directory| {
        let text = std::fs::read_to_string(directory.join("package.json")).ok()?;
        let manifest: serde_json::Value = serde_json::from_str(&text).ok()?;

        Some(manifest.get("type").and_then(serde_json::Value::as_str) == Some("module"))
    }) == Some(true)
}

fn local_implementation_of(declared: &Path, specifier: &str, allow_js: bool) -> Option<PathBuf> {
    let text = declared.to_string_lossy();
    let lowered = text.to_ascii_lowercase();

    if forward_slashes_of(declared).contains("/node_modules/") {
        return None;
    }

    let (suffix, extensions): (&str, &[&str]) = if lowered.ends_with(".d.mts") {
        (".d.mts", &[".mjs"])
    } else if lowered.ends_with(".d.cts") {
        (".d.cts", &[".cjs"])
    } else if !lowered.ends_with(".d.ts") {
        return None;
    } else if specifier.ends_with(".jsx") {
        (".d.ts", &[".jsx"])
    } else if specifier.ends_with(".js") {
        (".d.ts", &[".js"])
    } else {
        (".d.ts", &[".js", ".jsx"])
    };
    let stem = &text[..text.len() - suffix.len()];

    extensions
        .iter()
        .map(|extension| PathBuf::from(format!("{stem}{extension}")))
        .find(|candidate| candidate.is_file())
        .filter(|candidate| is_parsed_path(candidate, allow_js))
        .map(|candidate| canonical_path_of(&candidate).unwrap_or(candidate))
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

fn module_requests_of(file: &SourceFile<'_>) -> Vec<(String, RequestKind, bool)> {
    let mut static_imports: Vec<(u32, String, RequestKind)> = file
        .module_record
        .requested_modules
        .iter()
        .filter_map(|(specifier, requests)| {
            let start = requests.iter().map(|request| request.span.start).min()?;

            Some((start, specifier.to_string(), RequestKind::Static))
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
                    RequestKind::Require,
                ));
            }
        }
    }

    static_imports.sort_by_key(|(start, _, _)| *start);

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

    let mut requires = required_specifiers_of(file);

    requires.sort_by_key(|(start, _)| *start);

    static_imports
        .into_iter()
        .map(|(_, specifier, kind)| (specifier, kind, true))
        .chain(dynamic_imports.map(|specifier| (specifier, RequestKind::Dynamic, true)))
        .chain(
            requires
                .into_iter()
                .map(|(_, specifier)| (specifier, RequestKind::Require, false)),
        )
        .collect()
}

fn required_specifiers_of(file: &SourceFile<'_>) -> Vec<(u32, String)> {
    let scoping = file.semantic.scoping();
    let nodes = file.semantic.nodes();
    let Some(references) = scoping.root_unresolved_references().get("require") else {
        return Vec::new();
    };

    references
        .iter()
        .filter_map(|reference| {
            let node = scoping.get_reference(*reference).node_id();
            let AstKind::CallExpression(call) = nodes.parent_kind(node) else {
                return None;
            };

            required_specifier_of(file, call).map(|specifier| (call.span.start, specifier))
        })
        .collect()
}

pub(crate) fn required_specifier_of(
    file: &SourceFile<'_>,
    call: &CallExpression<'_>,
) -> Option<String> {
    let Expression::Identifier(callee) = &call.callee else {
        return None;
    };
    let reference = callee.reference_id.get()?;

    if callee.name != "require"
        || file
            .semantic
            .scoping()
            .get_reference(reference)
            .symbol_id()
            .is_some()
    {
        return None;
    }

    match call.arguments.as_slice() {
        [Argument::StringLiteral(literal)] => Some(literal.value.to_string()),
        [Argument::TemplateLiteral(template)] if template.expressions.is_empty() => template
            .quasis
            .first()
            .and_then(|quasi| quasi.value.cooked.as_ref())
            .map(ToString::to_string),
        _ => None,
    }
}

pub(crate) fn is_declaration_path(path: &Path) -> bool {
    let name = path
        .file_name()
        .map(|name| name.to_string_lossy().to_ascii_lowercase())
        .unwrap_or_default();

    [".d.ts", ".d.mts", ".d.cts"]
        .iter()
        .any(|suffix| name.ends_with(suffix))
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
    let built = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_class_table(true)
        .with_enum_eval(false)
        .with_check_syntax_error(true)
        .build(program);
    let diagnostics = parsed
        .diagnostics
        .iter()
        .map(|diagnostic| (DiagnosticPhase::Parse, diagnostic))
        .chain(
            built
                .diagnostics
                .iter()
                .map(|diagnostic| (DiagnosticPhase::Semantic, diagnostic)),
        )
        .map(|(phase, diagnostic)| SourceDiagnostic {
            phase,
            message: diagnostic.to_string(),
            spans: diagnostic
                .labels
                .iter()
                .map(|label| Span::new(label.offset(), label.offset() + label.len()))
                .collect(),
        })
        .collect();
    let semantic = built.semantic;
    let flow_index = FlowIndex::new(&semantic);

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
        implementation: false,
        owners: Vec::new(),
        diagnostics,
        flow_index,
    })
}

#[cfg(test)]
#[path = "project.test.rs"]
mod tests;

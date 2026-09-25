#![allow(dead_code)]

use std::fs;
use std::path::Path;

use olint::analysis::{Analysis, Options, TypeMode};
use olint::declarations::FunctionNode;
use olint::project::{FileId, Project};
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, CallExpression, Expression, MemberExpression};
use oxc_ast::AstKind;
use oxc_span::GetSpan;
use tempfile::TempDir;

pub const TYPED_PACKAGE: [(&str, &str); 2] = [
    (
        "node_modules/pkg/package.json",
        r#"{ "name": "pkg", "types": "index.d.ts" }"#,
    ),
    (
        "node_modules/pkg/index.d.ts",
        "export declare function run(): void;",
    ),
];

pub fn project_of(files: &[(&str, &str)]) -> TempDir {
    let directory = tempfile::tempdir().expect("temporary directory");

    for (relative, text) in files {
        let path = directory.path().join(relative);

        fs::create_dir_all(path.parent().expect("parent")).expect("directories");
        fs::write(path, text).expect("file");
    }

    directory
}

pub fn run_in_project(files: &[(&str, &str)], body: impl for<'a> FnOnce(&Project<'a>, &Path)) {
    let directory = project_of(files);
    let allocator = Allocator::default();
    let project =
        Project::load(&allocator, &directory.path().join("tsconfig.json")).expect("project loads");

    body(&project, directory.path());
}

pub fn file_of(project: &Project<'_>, root: &Path, relative: &str) -> FileId {
    project
        .file_by_path(&root.join(relative))
        .unwrap_or_else(|| panic!("{relative} is loaded"))
}

pub const SYNTACTIC: Options = Options {
    minimum_exponent: 2,
    types: TypeMode::Syntactic,
};

pub fn assert_scheduler_terminal(stats: olint::summaries::SchedulerStats) {
    assert_eq!(stats.ready, stats.tasks, "{stats:?}");
    assert_eq!(stats.waiting, 0, "{stats:?}");
    assert_eq!(stats.queued, 0, "{stats:?}");

    for event in olint::analysis::work::EVENTS {
        assert_eq!(
            stats.work.reserved().count(event),
            0,
            "{event:?}: {stats:?}"
        );
    }
}

pub fn unknown_reasons(
    analysis: &Analysis<'_, '_>,
    root: Option<olint::unknowns::UnknownId>,
) -> std::collections::BTreeSet<olint::unknowns::UnknownReason> {
    use olint::unknowns::UnknownNode;

    let mut pending: Vec<_> = root.into_iter().collect();
    let mut visited = std::collections::HashSet::new();
    let mut found = std::collections::BTreeSet::new();

    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }

        match analysis.unknowns.node(id) {
            UnknownNode::Origin(unknown) => {
                found.insert(unknown.reason);
            }
            UnknownNode::Call { child, .. } | UnknownNode::Scale { child, .. } => {
                pending.push(*child)
            }
            UnknownNode::Join { children } => pending.extend(children),
        }
    }

    found
}

pub fn probes_of<'a>(project: &Project<'a>, file: FileId) -> Vec<&'a Expression<'a>> {
    project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .filter_map(|node| match node.kind() {
            AstKind::CallExpression(call)
                if matches!(&call.callee, Expression::Identifier(callee) if callee.name == "probe") =>
            {
                call.arguments.first().and_then(|argument| argument.as_expression())
            }
            _ => None,
        })
        .collect()
}

pub fn probe_results_of<T>(
    files: &[(&str, &str)],
    evaluate: impl for<'p, 'a> Fn(&mut Analysis<'p, 'a>, FileId, &'a Expression<'a>) -> T,
) -> Vec<T> {
    let mut found = Vec::new();

    run_in_project(files, |project, root| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let file = file_of(project, root, "index.ts");

        found = probes_of(project, file)
            .into_iter()
            .map(|probe| evaluate(&mut analysis, file, probe))
            .collect();
    });

    found
}

pub fn call_of<'a>(project: &Project<'a>, file: FileId, callee: &str) -> &'a CallExpression<'a> {
    let text = project.file(file).text;

    first_node_of(project, file, |kind| match kind {
        AstKind::CallExpression(call) if call.callee.span().source_text(text) == callee => {
            Some(call)
        }
        _ => None,
    })
}

pub fn member_callee_of<'a>(
    project: &Project<'a>,
    file: FileId,
    callee: &str,
) -> &'a MemberExpression<'a> {
    call_of(project, file, callee)
        .callee
        .as_member_expression()
        .unwrap_or_else(|| panic!("{callee} is a member callee"))
}

pub fn first_node_of<'a, T>(
    project: &Project<'a>,
    file: FileId,
    pick: impl Fn(AstKind<'a>) -> Option<T>,
) -> T {
    project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .find_map(|node| pick(node.kind()))
        .expect("a matching node")
}

pub fn function_of_name<'a>(project: &Project<'a>, file: FileId, name: &str) -> FunctionNode<'a> {
    let nodes = project.file(file).semantic.nodes();

    first_node_of(project, file, |kind| match kind {
        AstKind::Function(function) if function.id.as_ref().is_some_and(|id| id.name == name) => {
            Some(FunctionNode::Function(function))
        }
        AstKind::ArrowFunctionExpression(arrow) => match nodes.parent_kind(arrow.node_id()) {
            AstKind::VariableDeclarator(declarator) if matches!(&declarator.id, BindingPattern::BindingIdentifier(id) if id.name == name) => {
                Some(FunctionNode::Arrow(arrow))
            }
            _ => None,
        },
        _ => None,
    })
}

pub fn run_with_source(source: &str, body: impl for<'p, 'a> FnOnce(&mut Analysis<'p, 'a>, FileId)) {
    let files = [("tsconfig.json", "{}"), ("index.ts", source)];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(project, SYNTACTIC);

        body(&mut analysis, file);
    });
}

pub fn summary_of(analysis: &mut Analysis<'_, '_>, file: FileId, name: &str) -> olint::cost::Part {
    let function = function_of_name(analysis.project, file, name);

    analysis
        .summarize(file, function)
        .total(&mut analysis.unknowns, &mut analysis.traces)
}

pub type LegacyResult = (
    olint::cost::Cost,
    bool,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
);

pub fn legacy_result_of(source: &str, name: &str) -> LegacyResult {
    prepared_result_of(source, name, |_| {})
}

pub fn repository_helper_of() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join(olint::regex::HELPER_NAME)
}

pub fn classified_result_of(source: &str, name: &str) -> LegacyResult {
    prepared_result_of(source, name, |analysis| {
        let helper = repository_helper_of();
        let limits = olint::regex::RegexLimits::default();

        analysis
            .gather_regex_answers(|requests| olint::regex::ask(&helper, requests, &limits))
            .expect("the regex helper answers");
    })
}

pub fn prepared_result_of(
    source: &str,
    name: &str,
    prepare: impl for<'p, 'a> FnOnce(&mut Analysis<'p, 'a>),
) -> LegacyResult {
    let mut found = None;

    run_with_source(source, |analysis, file| {
        prepare(analysis);

        let function = function_of_name(analysis.project, file, name);
        let part = summary_of(analysis, file, name);
        let cost = legacy_class_of(analysis, file, function, &part.cost);
        let reasons = unknown_reasons(analysis, part.unknowns);

        found = Some((cost, part.is_complete(), reasons));
    });

    found.expect("the source declares the named function")
}

pub fn legacy_class_of<'a>(
    analysis: &mut Analysis<'_, 'a>,
    file: FileId,
    function: FunctionNode<'a>,
    cost: &olint::cost::Cost,
) -> olint::cost::Cost {
    use olint::cost::{Cost, CostComparison};

    for text in [
        "O(1)",
        "O(log N)",
        "O(N)",
        "O(N log N)",
        "O(N^2)",
        "O(N^2 log N)",
        "O(N^3)",
        "O(N^4)",
    ] {
        let legacy = Cost::parse(text).unwrap();
        let expected = analysis
            .bind_function_cost(file, function, &legacy)
            .unwrap();

        if cost.compare(&expected) == CostComparison::Within
            && expected.compare(cost) == CostComparison::Within
        {
            return legacy;
        }
    }

    cost.clone()
}

pub fn legacy_reading_of<'a>(
    analysis: &mut Analysis<'_, 'a>,
    file: FileId,
    function: FunctionNode<'a>,
) -> olint::cost::Reading {
    let mut reading =
        analysis.summarize_with(file, function, olint::summaries::Substitutions::new(), true);

    for (_, _, part) in &mut reading.completions {
        part.cost = legacy_class_of(analysis, file, function, &part.cost);
    }

    reading
}

pub fn trace_nodes(
    traces: &olint::trace::TraceArena,
    root: Option<olint::trace::TraceId>,
) -> Vec<&olint::trace::TraceNode> {
    let mut pending: Vec<_> = root.into_iter().collect();
    let mut out = Vec::new();

    while let Some(id) = pending.pop() {
        let node = traces.node(id).unwrap();

        match traces.layout(id).unwrap() {
            olint::trace::TraceLayout::Group | olint::trace::TraceLayout::Sequence => {
                pending.extend(node.children.iter().rev().copied())
            }
            olint::trace::TraceLayout::Factor { inner_children } => {
                out.push(node);
                pending.extend(
                    node.children
                        .iter()
                        .skip(inner_children as usize)
                        .rev()
                        .copied(),
                );
            }
        }
    }

    out
}

pub type SelectedResult = (
    olint::cost::Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
);

pub fn selected_result_in(
    sources: &[(&str, &str)],
    types: olint::analysis::TypeMode,
) -> SelectedResult {
    let entry = sources[0].0;
    let options = match entry.ends_with(".ts") {
        true => r#""strict":true,"noEmit":true"#,
        false => r#""allowJs":true,"noEmit":true"#,
    };
    let tsconfig = format!(r#"{{"compilerOptions":{{{options}}},"files":["{entry}"]}}"#);
    let mut files = vec![("tsconfig.json", tsconfig.as_str())];

    files.extend_from_slice(sources);

    let (cost, reasons, _) = project_result_of(&files, entry, types);

    (cost, reasons)
}

pub type ProjectResult = (
    olint::cost::Cost,
    std::collections::BTreeSet<olint::unknowns::UnknownReason>,
    Vec<String>,
);

pub fn project_result_of(
    files: &[(&str, &str)],
    entry: &str,
    types: olint::analysis::TypeMode,
) -> ProjectResult {
    let directory = project_of(files);

    project_result_in(directory.path(), entry, types)
}

pub fn project_result_in(
    root: &Path,
    entry: &str,
    types: olint::analysis::TypeMode,
) -> ProjectResult {
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &root.join("tsconfig.json")).expect("project loads");
    let file = file_of(&project, root, entry);
    let mut analysis = olint::analysis::Analysis::new(
        &project,
        olint::analysis::Options {
            minimum_exponent: 2,
            types,
        },
    );

    if types == olint::analysis::TypeMode::Tsc {
        let functions = analysis.reportable();
        let tsconfig = root.join("tsconfig.json");

        analysis
            .gather_answers(&functions, |queries| {
                olint::tsc::ask(
                    std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
                    &tsconfig,
                    queries,
                )
            })
            .expect("the compiler helper answers");
    }

    let part = summary_of(&mut analysis, file, "selected");
    let reasons = unknown_reasons(&analysis, part.unknowns);
    let selected = function_of_name(analysis.project, file, "selected");
    let cost = legacy_class_of(&mut analysis, file, selected, &part.cost);
    let mut labels = Vec::new();
    let mut pending: Vec<_> = part.trace.into_iter().collect();

    while let Some(id) = pending.pop() {
        let node = analysis.traces.node(id).unwrap();

        if let Ok(olint::trace::TraceLayout::Factor { .. }) = analysis.traces.layout(id) {
            labels.push(node.label.clone());
        }

        pending.extend(node.children.iter().rev().copied());
    }

    (cost, reasons, labels)
}

pub type ProjectCase<'s> = (Vec<(&'s str, String)>, &'s str, bool);

pub fn assert_project_cases(entry: &str, cases: &[ProjectCase<'_>]) {
    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for (files, expected, partial) in cases {
            let files: Vec<(&str, &str)> = files
                .iter()
                .map(|(name, source)| (*name, source.as_str()))
                .collect();
            let (cost, reasons, _) = project_result_of(&files, entry, types);

            assert_eq!(
                cost,
                olint::cost::Cost::parse(expected).unwrap(),
                "{types:?} {files:?}"
            );
            assert_eq!(
                !reasons.is_empty(),
                *partial,
                "{types:?} {files:?}: {reasons:?}"
            );
        }
    }
}

pub type SelectedCase<'s> = (Vec<(&'s str, String)>, &'s str, bool);

pub fn selected_case_of(
    sources: &[(&str, String)],
    types: olint::analysis::TypeMode,
) -> SelectedResult {
    let sources: Vec<(&str, &str)> = sources
        .iter()
        .map(|(name, source)| (*name, source.as_str()))
        .collect();

    selected_result_in(&sources, types)
}

pub fn assert_selected(cases: &[SelectedCase<'_>]) {
    for types in [
        olint::analysis::TypeMode::Syntactic,
        olint::analysis::TypeMode::Tsc,
    ] {
        for (sources, expected, partial) in cases {
            let (cost, reasons) = selected_case_of(sources, types);

            assert_eq!(
                cost,
                olint::cost::Cost::parse(expected).unwrap(),
                "{types:?} {sources:?}"
            );
            assert_eq!(
                reasons.contains(&olint::unknowns::UnknownReason::Target),
                *partial,
                "{types:?} {sources:?}: {reasons:?}"
            );
        }
    }
}

pub fn index_of(source: String) -> Vec<(&'static str, String)> {
    vec![("index.ts", source)]
}

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
    strings_linear: true,
    callbacks: true,
    minimum_exponent: 2,
    types: TypeMode::Syntactic,
};

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

pub fn function_named<'a>(project: &Project<'a>, file: FileId, name: &str) -> FunctionNode<'a> {
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

pub fn with_source(source: &str, body: impl for<'p, 'a> FnOnce(&mut Analysis<'p, 'a>, FileId)) {
    let files = [("tsconfig.json", "{}"), ("index.ts", source)];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(project, SYNTACTIC);

        body(&mut analysis, file);
    });
}

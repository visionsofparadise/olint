#![allow(dead_code)]

use std::fs;
use std::path::Path;

use olint::project::{FileId, Project};
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
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

use super::*;
use crate::analysis::Options;
use crate::project::Project;
use oxc_allocator::Allocator;

#[test]
fn retained_lazy_callbacks_cannot_alias_a_new_generation() {
    let directory = tempfile::tempdir().unwrap();

    std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
    std::fs::write(
        directory.path().join("index.ts"),
        "function pure(){return 1} function capture(cb:()=>number){} capture(pure);",
    )
    .unwrap();

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &directory.path().join("tsconfig.json")).unwrap();
    let file = project
        .file_by_path(&directory.path().join("index.ts"))
        .unwrap();
    let call = project
        .file(file)
        .semantic
        .nodes()
        .iter()
        .find_map(|node| match node.kind() {
            AstKind::CallExpression(call) => Some(call),
            _ => None,
        })
        .unwrap();
    let mut analysis = Analysis::new(
        &project,
        Options {
            minimum_exponent: 2,
            types: crate::analysis::TypeMode::Syntactic,
        },
    );
    let old = analysis.argument_facts_of(file, &call.arguments[0]);

    assert!(analysis
        .invoke_argument(&old, file, call.span, &[])
        .is_complete());
    analysis.reset_between_passes();

    let stale = analysis.invoke_argument(&old, file, call.span, &[]);

    assert!(!stale.is_complete());

    let fresh = analysis.argument_facts_of(file, &call.arguments[0]);

    assert_ne!(old.value.value, fresh.value.value);
    assert!(analysis
        .invoke_argument(&fresh, file, call.span, &[])
        .is_complete());
    assert_eq!(analysis.invoke_argument(&old, file, call.span, &[]), stale);
}

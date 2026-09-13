use std::path::Path;

use olint::analysis::Analysis;
use olint::config::read_config;
use olint::project::Project;
use olint::public::public_functions;
use oxc_allocator::Allocator;

mod support;

use support::SYNTACTIC;

#[test]
fn tags_fixture_public_functions_follow_exports_and_limits() {
    let tsconfig = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/tags/tsconfig.json");
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).expect("fixture loads");
    let mut analysis = Analysis::new(&project, SYNTACTIC);
    let config = read_config(&project, None).expect("config reads");
    let public = public_functions(&mut analysis, &config);
    let names: Vec<String> = public
        .iter()
        .map(|function| analysis.name_of(function.file, function.function))
        .collect();

    assert_eq!(names.len(), 10, "{names:?}");
    assert!(!names.contains(&"Engine.helper".to_string()));
    assert!(!names.contains(&"hidden".to_string()));

    let accepted = public
        .iter()
        .find(|function| analysis.name_of(function.file, function.function) == "acceptedCubic")
        .expect("acceptedCubic is public");

    assert!(accepted.own_limit);
    assert_eq!(accepted.limit.text, "O(N^3)");
}

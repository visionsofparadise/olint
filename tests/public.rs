use std::path::Path;

use olint::analysis::Analysis;
use olint::config::read_config;
use olint::project::Project;
use olint::public::public_functions;
use oxc_allocator::Allocator;

mod support;

use support::SYNTACTIC;

#[test]
fn explicit_surfaces_override_names_while_ignore_still_wins() {
    for source_path in ["part.d.worker.ts", "scripts/run.ts", "tests/run.spec.ts"] {
        for ignored in [None, Some(source_path), Some("index.ts")] {
            let config = serde_json::json!({"entrypoints":["index.ts",source_path],"ignore":ignored.into_iter().collect::<Vec<_>>()}).to_string();
            let entry = format!(
                "export {{ selected }} from './{}';",
                source_path.trim_end_matches(".ts")
            );

            support::run_in_project(&[
                ("tsconfig.json", "{}"),
                ("index.ts", &entry),
                (source_path, "export function selected(xs:number[]){for(const a of xs)for(const b of xs)for(const c of xs)void c}"),
                ("olint.config.json", &config),
            ], |project, _| {
                let mut analysis = Analysis::new(project, SYNTACTIC);
                let config = read_config(project, None).unwrap();
                let public = public_functions(&mut analysis, &config).unwrap();

                assert_eq!(public.len(), usize::from(ignored != Some(source_path)), "{source_path} {ignored:?}");

                if let Some(function) = public.first() {
                    assert_eq!(function.limits.len(), if ignored == Some("index.ts") {1} else {2});
                }
            });
        }
    }
}

#[test]
fn invalid_direct_config_returns_before_summary_work() {
    support::run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", "export function selected() {}"),
            ("olint.config.json", r#"{"entrypoints":["missing.ts"]}"#),
        ],
        |project, _| {
            let mut analysis = Analysis::new(project, SYNTACTIC);
            let before = analysis.scheduler_stats();
            let config = read_config(project, None).unwrap();

            assert!(public_functions(&mut analysis, &config).is_err());
            assert_eq!(analysis.scheduler_stats().work, before.work);
            assert_eq!(analysis.scheduler_stats().tasks, 0);
        },
    );
}

#[test]
fn valid_ignored_or_nonexporting_entries_can_select_no_public_functions() {
    for (source, ignored) in [
        ("export function selected() {}", true),
        ("function local() {}", false),
    ] {
        let config = serde_json::json!({"entrypoints":["index.ts"], "ignore":if ignored {vec!["index.ts"]} else {vec![]}}).to_string();

        support::run_in_project(
            &[
                ("tsconfig.json", "{}"),
                ("index.ts", source),
                ("olint.config.json", &config),
            ],
            |project, _| {
                let mut analysis = Analysis::new(project, SYNTACTIC);
                let config = read_config(project, None).unwrap();

                assert!(public_functions(&mut analysis, &config).unwrap().is_empty());
            },
        );
    }
}

#[test]
fn tags_fixture_public_functions_follow_exports_and_limits() {
    let tsconfig = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/tags/tsconfig.json");
    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).expect("fixture loads");
    let mut analysis = Analysis::new(&project, SYNTACTIC);
    let config = read_config(&project, None).expect("config reads");
    let public = public_functions(&mut analysis, &config).expect("valid selection");
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
    assert_eq!(accepted.limits.len(), 1);
    assert_eq!(accepted.limits[0].limit.text, "O(N^3)");
}

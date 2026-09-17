use super::*;

#[test]
fn invalid_selections_precede_the_compiler_callback() {
    for (config, tsconfig, explicit_missing) in [
        ("{}", "{}", true),
        ("[]", "{}", false),
        (r#"{"max":null}"#, "{}", false),
        (r#"{"entrypoints":["missing.ts"]}"#, "{}", false),
        ("{}", r#"{"files":["missing.ts"]}"#, false),
    ] {
        for report in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let root = directory.path();

            std::fs::write(
                root.join("index.ts"),
                "export function selected(value:any){ return value.method(); }",
            )
            .unwrap();
            std::fs::write(root.join("tsconfig.json"), tsconfig).unwrap();
            std::fs::write(root.join("olint.config.json"), config).unwrap();

            let cli = Cli {
                min: 0,
                report,
                types: TypeMode::Tsc,
                config: explicit_missing.then(|| root.join("missing.json")),
                tsconfig: root.join("tsconfig.json"),
            };
            let result = run_with_ask(cli, |_, _, _| panic!("invalid selection reached compiler"));

            assert!(matches!(
                result,
                Err(Failure::Config(_) | Failure::Project(_))
            ));
        }
    }
}

#[test]
fn valid_selection_can_reach_the_compiler_callback() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();

    std::fs::write(
        root.join("index.ts"),
        "export function selected(value:any){ return value.method(); }",
    )
    .unwrap();
    std::fs::write(root.join("tsconfig.json"), "{}").unwrap();

    let cli = Cli {
        min: 0,
        report: false,
        types: TypeMode::Tsc,
        config: None,
        tsconfig: root.join("tsconfig.json"),
    };
    let mut calls = 0;
    let result = run_with_ask(cli, |_, _, queries| {
        calls += 1;

        assert!(!queries.is_empty());

        Err(TscError::Malformed("test callback".to_string()))
    });

    assert!(matches!(result, Err(Failure::Tsc(TscError::Malformed(_)))));
    assert_eq!(calls, 1);
}

use super::*;

#[test]
fn explicitly_selected_scripts_reach_compiler_recording_in_both_modes() {
    for report in [false, true] {
        for ignored in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let root = directory.path();

            std::fs::create_dir(root.join("scripts")).unwrap();
            std::fs::write(
                root.join("scripts/run.ts"),
                "export function selected(value:any){return value.method()}",
            )
            .unwrap();
            std::fs::write(
                root.join("index.ts"),
                "export {selected} from './scripts/run';",
            )
            .unwrap();
            std::fs::write(root.join("tsconfig.json"), "{}").unwrap();
            std::fs::write(root.join("olint.config.json"), serde_json::json!({"entrypoints":["index.ts"],"ignore":if ignored {vec!["scripts/**"]} else {vec![]}}).to_string()).unwrap();

            let mut calls = 0;
            let result = run_with_ask(
                Cli {
                    min: 0,
                    report,
                    types: TypeMode::Tsc,
                    config: None,
                    tsconfig: root.join("tsconfig.json"),
                },
                |_, _, queries| {
                    calls += 1;

                    if ignored {
                        assert!(queries.is_empty());

                        return Ok(TscReply {
                            typescript: "static test".into(),
                            from: "test".into(),
                            answers: Vec::new(),
                        });
                    }

                    assert!(
                        queries.iter().any(|query| match query {
                            Query::Type { file, .. } | Query::Callee { file, .. } =>
                                file.replace('\\', "/").ends_with("scripts/run.ts"),
                        }),
                        "{queries:?}"
                    );

                    Err(TscError::Malformed("recorded explicit script".into()))
                },
            );

            assert_eq!(calls, 1);

            if ignored {
                assert!(matches!(result, Ok(0)));
            } else {
                assert!(matches!(result, Err(Failure::Tsc(TscError::Malformed(_)))));
            }
        }
    }
}

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

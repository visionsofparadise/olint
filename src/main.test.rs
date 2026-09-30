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
    std::fs::write(
        root.join("olint.config.json"),
        r#"{"entrypoints":["index.ts"]}"#,
    )
    .unwrap();

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

#[test]
fn lint_queries_follow_selected_roots_and_their_ignored_dependencies() {
    for report in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();

        for (path, text) in [
            ("tsconfig.json", "{}"),
            ("index.ts", "import {dependency} from './ignored'; export function selected(value:any){return dependency(value)} function unreachable(value:any){return value.unreachable()}"),
            ("ignored.ts", "export function dependency(value:any){return value.reachable()} export function ignored(value:any){return value.ignored()}"),
            ("olint.config.json", r#"{"entrypoints":["index.ts"],"ignore":["ignored.ts"]}"#),
        ] {
            std::fs::write(root.join(path), text).unwrap();
        }

        let mut asked = Vec::new();
        let result = run_with_ask(
            Cli {
                min: 0,
                report,
                types: TypeMode::Tsc,
                config: None,
                tsconfig: root.join("tsconfig.json"),
            },
            |_, _, queries| {
                for query in queries {
                    let (file, pos, end) = match query {
                        Query::Type { file, pos, end } | Query::Callee { file, pos, end } => {
                            (file, pos, end)
                        }
                    };
                    let text = std::fs::read_to_string(file).unwrap();

                    asked.push(text[*pos as usize..*end as usize].to_string());
                }

                Ok(TscReply {
                    typescript: "static test".into(),
                    from: "test".into(),
                    answers: vec![None; queries.len()],
                })
            },
        );

        assert!(matches!(result, Ok(0)), "{asked:?}");
        assert!(
            asked.iter().any(|site| site == "value.reachable"),
            "{asked:?}"
        );
        assert_eq!(
            asked.iter().any(|site| site == "value.unreachable"),
            report,
            "{asked:?}"
        );
        assert_eq!(
            asked.iter().any(|site| site == "value.ignored"),
            report,
            "{asked:?}"
        );
    }
}

#[test]
fn empty_selected_batches_preserve_explicit_type_availability() {
    for types in [TypeMode::Tsc, TypeMode::Auto, TypeMode::Syntactic] {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();

        std::fs::write(
            root.join("index.ts"),
            "export function selected(){return 1}",
        )
        .unwrap();
        std::fs::write(root.join("tsconfig.json"), "{}").unwrap();
        std::fs::write(
            root.join("olint.config.json"),
            r#"{"entrypoints":["index.ts"]}"#,
        )
        .unwrap();

        let mut calls = 0;
        let result = run_with_ask(
            Cli {
                min: 0,
                report: false,
                types,
                config: None,
                tsconfig: root.join("tsconfig.json"),
            },
            |_, _, queries| {
                calls += 1;

                assert!(queries.is_empty());

                Err(TscError::TypescriptUnavailable("test availability".into()))
            },
        );

        assert_eq!(calls, usize::from(types != TypeMode::Syntactic));

        // G42: `auto` fails without a checker as `tsc` does; declaration-only typing is the explicit `syntactic`.
        match types {
            TypeMode::Tsc | TypeMode::Auto => assert!(matches!(
                result,
                Err(Failure::Tsc(TscError::TypescriptUnavailable(_)))
            )),
            TypeMode::Syntactic => assert!(matches!(result, Ok(0))),
        }
    }
}

/// G42: `auto`, the default, exits 2 when node or typescript is unavailable rather than analysing with
/// declaration-only types, so node states never depend on the environment (§3.4).
#[test]
fn auto_types_fail_the_run_when_the_checker_is_unavailable() {
    let unavailable: [fn() -> TscError; 2] = [
        || TscError::NodeUnavailable(std::io::Error::from(std::io::ErrorKind::NotFound)),
        || TscError::TypescriptUnavailable("Cannot find module 'typescript'".into()),
    ];

    for error_of in unavailable {
        for report in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let root = directory.path();

            std::fs::write(
                root.join("index.ts"),
                "export function selected(value: any) { return value.method(); }",
            )
            .unwrap();
            std::fs::write(root.join("tsconfig.json"), "{}").unwrap();
            std::fs::write(
                root.join("olint.config.json"),
                r#"{"entrypoints":["index.ts"]}"#,
            )
            .unwrap();

            let result = run_with_ask(
                Cli {
                    min: 0,
                    report,
                    types: TypeMode::Auto,
                    config: None,
                    tsconfig: root.join("tsconfig.json"),
                },
                |_, _, _| Err(error_of()),
            );

            assert!(
                matches!(
                    result,
                    Err(Failure::Tsc(
                        TscError::NodeUnavailable(_) | TscError::TypescriptUnavailable(_)
                    ))
                ),
                "{report}"
            );
        }
    }
}

use std::path::Path;

use olint::config::{package_entries, read_config, Config, ConfigError};

mod support;

use support::run_in_project;

const TSCONFIG: (&str, &str) = (
    "tsconfig.json",
    r#"{ "include": ["src"], "compilerOptions":{"rootDir":"src","outDir":"dist","declaration":true} }"#,
);

#[test]
fn module_specific_and_pattern_exports_preserve_package_order() {
    assert_eq!(
        entries_of(&[
            TSCONFIG,
            (
                "package.json",
                r#"{"exports":{".":{"types":"./dist/z.d.mts","import":"./dist/z.mjs","require":"./dist/a.cjs"},"./*":"./dist/*.js","./private":null,"./package.json":"./package.json"}}"#
            ),
            ("src/z.mts", "export const z=1;"),
            ("src/a.cts", "export const a=1;"),
            ("src/deep/run.ts", "export const run=1;"),
            ("src/private.ts", "export const hidden=1;"),
        ]),
        ["src/z.mts", "src/a.cts", "src/deep/run.ts"]
    );
}

#[test]
fn unproved_mappings_require_explicit_entries() {
    for package in [
        r#"{"main":"dist/x.js"}"#,
        r#"{"exports":{"./*":"./missing/*.js"}}"#,
        r#"{"exports":"./src/view.vue"}"#,
    ] {
        assert_unmapped(&[
            TSCONFIG,
            ("package.json", package),
            ("src/x/index.ts", "export const x=1;"),
            ("src/view.vue", "<script>export const x=1</script>"),
        ]);
    }

    for options in [r#"{"noEmit":true}"#, r#"{"outFile":"dist/bundle.js"}"#] {
        let config = format!(r#"{{"include":["src"],"compilerOptions":{options}}}"#);

        assert_unmapped(&[
            ("tsconfig.json", &config),
            ("package.json", r#"{"main":"dist/index.js"}"#),
            ("src/index.ts", "export const index=1;"),
        ]);
    }
}

fn assert_unmapped(files: &[(&str, &str)]) {
    assert!(
        matches!(read_error_of(files), Some(ConfigError::Selection { message, .. }) if message.contains("explicit entrypoints"))
    );
}

#[test]
fn direct_source_and_disabled_exports_preserve_intentional_selection() {
    for (package, expected) in [
        (r#"{"source":"src/index.ts"}"#, vec!["src/index.ts"]),
        (r#"{"main":"missing.js","exports":null}"#, vec![]),
        (r#"{"exports":{"./metadata":"./data.json"}}"#, vec![]),
    ] {
        assert_eq!(
            entries_of(&[
                (
                    "tsconfig.json",
                    r#"{"compilerOptions":{"noEmit":true},"include":["src"]}"#
                ),
                ("package.json", package),
                ("src/index.ts", "export const index=1;"),
            ]),
            expected
        );
    }
}

#[test]
fn colliding_project_outputs_require_explicit_sources() {
    assert!(matches!(read_error_of(&[
        ("tsconfig.json", r#"{"files":[],"references":[{"path":"left"},{"path":"right"}]}"#),
        ("left/tsconfig.json", r#"{"files":["index.ts"],"compilerOptions":{"outDir":"../dist"}}"#),
        ("right/tsconfig.json", r#"{"files":["index.ts"],"compilerOptions":{"outDir":"../dist"}}"#),
        ("left/index.ts", "export const left=1;"),
        ("right/index.ts", "export const right=1;"),
        ("package.json", r#"{"main":"dist/index.js"}"#),
    ]), Some(ConfigError::Selection { message, .. }) if message.contains("multiple source")));
}

#[test]
fn inherited_output_metadata_matches_typescript_output_names() {
    let configurations = [
        r#"{"rootDir":"${configDir}/src","outDir":"${configDir}/build","declarationDir":"${configDir}/types","declaration":true}"#,
        r#"{"rootDir":"../src","outDir":"../build","declarationDir":"../types","declaration":true,"jsx":"preserve"}"#,
        r#"{"outDir":"../build","composite":true}"#,
        r#"{"outDir":"../build","declaration":true,"emitDeclarationOnly":true}"#,
    ];

    for options in configurations {
        let base = format!("/* options */{{\"compilerOptions\":{options},}}");

        run_in_project(
            &[
                (
                    "tsconfig.json",
                    r#"{"extends":"./configs/base.json","include":["src"]}"#,
                ),
                ("configs/base.json", &base),
                ("src/a.mts", "export const a=1;"),
                ("src/b.cts", "export const b=1;"),
                ("src/nested/c.tsx", "export const c=1;"),
            ],
            |project, root| {
                let script = "const ts=require('typescript'); const p=ts.getParsedCommandLineOfConfigFile(process.argv[1],{}, {...ts.sys,onUnRecoverableConfigFileDiagnostic:d=>{throw d}}); console.log(JSON.stringify(p.fileNames.flatMap(source=>ts.getOutputFileNames(p,source,!ts.sys.useCaseSensitiveFileNames).filter(output=>!output.endsWith('.tsbuildinfo')).map(output=>({source,output})))));";
                let output = std::process::Command::new("node")
                    .args(["-e", script])
                    .arg(root.join("tsconfig.json"))
                    .current_dir(env!("CARGO_MANIFEST_DIR"))
                    .output()
                    .expect("static compiler output qualification");

                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );

                let pairs: Vec<serde_json::Value> =
                    serde_json::from_slice(&output.stdout).expect("outputs");

                assert!(!pairs.is_empty());

                for pair in pairs {
                    let package = serde_json::json!({"main":pair["output"]});

                    std::fs::write(root.join("package.json"), package.to_string()).unwrap();

                    let entries = package_entries(project).expect("qualified mapping");

                    assert_eq!(
                        entries,
                        [olint::paths::normalized_path_of(Path::new(
                            pair["source"].as_str().unwrap()
                        ))]
                    );
                }
            },
        );
    }
}

#[test]
fn optional_absence_and_invalid_read_are_distinct() {
    run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", "export const value=1"),
        ],
        |project, root| {
            assert_eq!(read_config(project, None).unwrap().source, "defaults");
            assert!(matches!(
                read_config(project, Some(&root.join("missing.json"))),
                Err(ConfigError::Read { .. })
            ));
            std::fs::create_dir(root.join("olint.config.json")).unwrap();
            assert!(matches!(
                read_config(project, None),
                Err(ConfigError::Read { .. })
            ));
        },
    );
}

fn entries_of(files: &[(&str, &str)]) -> Vec<String> {
    let mut entries = Vec::new();

    run_in_project(files, |project, _| {
        entries = package_entries(project)
            .expect("package entries")
            .iter()
            .map(|entry| olint::paths::relative_path_of(&project.root, entry))
            .collect();
    });

    entries
}

fn with_config(files: &[(&str, &str)], body: impl FnOnce(&Config, Vec<(String, String)>)) {
    run_in_project(files, |project, _| {
        let config = read_config(project, None).expect("config reads");
        let limits = config
            .entrypoints
            .iter()
            .flat_map(|(path, limits)| {
                limits.iter().map(move |limit| {
                    (
                        olint::paths::relative_path_of(&project.root, path),
                        limit.text.clone(),
                    )
                })
            })
            .collect();

        body(&config, limits);
    });
}

fn read_error_of(files: &[(&str, &str)]) -> Option<ConfigError> {
    let mut error = None;

    run_in_project(files, |project, _| {
        error = read_config(project, None).err();
    });

    error
}

#[test]
fn package_exports_nested_by_condition_resolve_to_source() {
    let entries = entries_of(&[
        TSCONFIG,
        (
            "package.json",
            r#"{ "main": "dist/other.js", "exports": { ".": { "types": "./dist/index.d.ts", "import": "./dist/index.js" } } }"#,
        ),
        ("src/index.ts", "export const a = 1;"),
        ("src/other.ts", "export const b = 1;"),
    ]);

    assert_eq!(entries, vec!["src/index.ts"]);
}

#[test]
fn package_main_resolves_to_its_configured_directory_output() {
    let entries = entries_of(&[
        TSCONFIG,
        ("package.json", r#"{ "main": "./dist/x/index.js" }"#),
        ("src/x/index.ts", "export const a = 1;"),
    ]);

    assert_eq!(entries, vec!["src/x/index.ts"]);
}

#[test]
fn read_config_keeps_entrypoints_in_array_order_with_their_limits() {
    let files = [
        TSCONFIG,
        (
            "olint.config.json",
            r#"{ "max": "O(N  log N)", "entrypoints": [{ "path": "./src/z.ts", "max": "O(N)" }, "src/a.ts"], "ignore": ["src/gen/**"] }"#,
        ),
        ("src/z.ts", "export const z = 1;"),
        ("src/a.ts", "export const a = 1;"),
    ];

    with_config(&files, |config, limits| {
        assert_eq!(config.max.text, "O(N log N)");
        assert_eq!(config.source, "olint.config.json");
        assert_eq!(
            limits,
            vec![
                ("src/z.ts".to_string(), "O(N)".to_string()),
                ("src/a.ts".to_string(), "O(N log N)".to_string())
            ]
        );
        assert!(config.is_ignored("src/gen/types.ts"));
        assert!(config.is_ignored("src/gen/deep/types.ts"));
        assert!(config.is_ignored(&olint::paths::forward_slashes_of(r"src\gen\deep\types.ts")));
        assert!(!config.is_ignored(&olint::paths::forward_slashes_of(r"src\a.ts")));
    });
}

#[test]
fn read_config_without_entrypoints_gives_package_entries_the_top_level_max() {
    let files = [
        TSCONFIG,
        ("package.json", r#"{ "main": "dist/index.js" }"#),
        ("olint.config.json", r#"{ "max": "O(N)" }"#),
        ("src/index.ts", "export const a = 1;"),
    ];

    with_config(&files, |_, limits| {
        assert_eq!(
            limits,
            vec![("src/index.ts".to_string(), "O(N)".to_string())]
        );
    });
}

#[test]
fn read_config_rejects_the_keyed_entrypoints_object() {
    let error = read_error_of(&[
        TSCONFIG,
        (
            "olint.config.json",
            r#"{ "entrypoints": { "src/index.ts": "O(N)" } }"#,
        ),
        ("src/index.ts", "export const index = 1;"),
    ]);

    assert!(matches!(error, Some(ConfigError::Entrypoints { .. })));
}

#[test]
fn a_config_path_that_is_a_directory_fails_to_read() {
    let error = read_error_of(&[
        TSCONFIG,
        ("olint.config.json/keep.txt", ""),
        ("src/a.ts", "export const a = 1;"),
    ]);

    assert!(matches!(error, Some(ConfigError::Read { .. })));
}

#[test]
fn an_invalid_ignore_glob_names_the_pattern() {
    let error = read_error_of(&[
        TSCONFIG,
        ("olint.config.json", r#"{ "ignore": ["src/["] }"#),
        ("src/a.ts", "export const a = 1;"),
    ]);

    assert!(matches!(
        error,
        Some(ConfigError::Ignore { pattern }) if pattern == r#""src/[""#
    ));
}

#[test]
fn read_config_rejects_unsupported_root_fields_by_name() {
    for (config, expected) in [
        (
            r#"{ "max": "O(N^2)", "entrypoint": ["src/index.ts"] }"#,
            "entrypoint",
        ),
        (
            r#"{ "entrypoints": ["src/index.ts"], "limit": "O(N)" }"#,
            "limit",
        ),
    ] {
        let error = read_error_of(&[
            TSCONFIG,
            ("olint.config.json", config),
            ("src/index.ts", "export const index = 1;"),
        ]);

        assert!(
            matches!(&error, Some(ConfigError::Field { field, .. }) if field == expected),
            "{config}: {error:?}"
        );
    }
}

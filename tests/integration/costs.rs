use crate::support;

use olint::cost::{Cost, CostComparison};
use support::{function_of_name, run_with_source, summary_of};

#[test]
fn independent_assumptions_compare_against_the_root_envelope() {
    run_with_source(
        "/** @perf O(n*m) */ export function work(n:number,m:number) {}",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "work");
            let part = summary_of(analysis, file, "work");

            for (limit, expected) in [
                ("O(N^2)", CostComparison::Within),
                ("O(N)", CostComparison::Exceeds),
                ("O(n^2)", CostComparison::Inconclusive),
            ] {
                let limit = analysis
                    .bind_function_cost(file, function, &Cost::parse(limit).unwrap())
                    .unwrap();

                assert_eq!(part.cost.compare(&limit), expected);
            }
        },
    );
}

#[test]
fn callee_assumptions_follow_actual_arguments_through_forwarding() {
    run_with_source(
        r#"
        /** @perf O(a.length*b.length) */ function kernel(a:string,b:string) {}
        function forward(a:string,b:string) { kernel(a,b); }
        export function independent(xs:string,ys:string) { forward(xs,ys); }
        export function repeated(xs:string,ys:string) { forward(xs,xs); }
    "#,
        |analysis, file| {
            for (name, expected) in [
                ("independent", "O(xs.length*ys.length)"),
                ("repeated", "O(xs.length^2)"),
            ] {
                let function = function_of_name(analysis.project, file, name);
                let part = summary_of(analysis, file, name);
                let expected = analysis
                    .bind_function_cost(file, function, &Cost::parse(expected).unwrap())
                    .unwrap();

                assert_eq!(
                    part.cost.compare(&expected),
                    CostComparison::Within,
                    "{name}: {}",
                    part.cost.text()
                );
                assert_eq!(
                    expected.compare(&part.cost),
                    CostComparison::Within,
                    "{name}: {}",
                    part.cost.text()
                );
                assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
            }
        },
    );
}

#[test]
fn direct_length_arguments_preserve_quantity_identity() {
    run_with_source(
        r#"
        /** @perf O(n^2) */ function kernel(n:number) {}
        export function work(xs:string) { kernel(xs.length); }
    "#,
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "work");
            let part = summary_of(analysis, file, "work");
            let expected = analysis
                .bind_function_cost(file, function, &Cost::parse("O(xs.length^2)").unwrap())
                .unwrap();

            assert_eq!(part.cost.compare(&expected), CostComparison::Within);
            assert_eq!(expected.compare(&part.cost), CostComparison::Within);
        },
    );
}

#[test]
fn invalid_nested_annotations_remain_diagnostics() {
    for annotation in ["O(max(n,log(n))", "O(n/0)", "O(missing)", "O(n logger)"] {
        run_with_source(
            &format!("/** @perf {annotation} */ export function work(n:number) {{}}"),
            |analysis, file| {
                let _ = summary_of(analysis, file, "work");

                assert!(!analysis.errors.is_empty(), "{annotation}");
            },
        );
    }
}

#[test]
fn coefficients_in_exponents_survive_source_binding() {
    run_with_source(
        "/** @perf O(2^(2*n)) */ export function work(n:number) {}",
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "work");
            let part = summary_of(analysis, file, "work");
            let limit = analysis
                .bind_function_cost(file, function, &Cost::parse("O(2^n)").unwrap())
                .unwrap();

            assert_eq!(part.cost.compare(&limit), CostComparison::Exceeds);
        },
    );
}

#[test]
fn a_shared_legacy_helper_uses_each_selected_root_envelope() {
    run_with_source(
        r#"
        /** @perf O(N^3) */ function helper() {}
        export function first(n:number) { helper(); }
        export function second(xs:string,ys:string) { helper(); }
        export function standalone() { helper(); }
    "#,
        |analysis, file| {
            let mut costs = Vec::new();

            for name in ["first", "second", "standalone"] {
                let function = function_of_name(analysis.project, file, name);
                let part = summary_of(analysis, file, name);
                let limit = analysis
                    .bind_function_cost(file, function, &Cost::parse("O(N^2)").unwrap())
                    .unwrap();

                assert_eq!(part.cost.compare(&limit), CostComparison::Exceeds, "{name}");

                let count = analysis.summaries_arena.len();

                assert_eq!(part, summary_of(analysis, file, name));
                assert_eq!(analysis.summaries_arena.len(), count);
                costs.push(part.cost);
            }

            assert_ne!(costs[0], costs[1]);
            assert_ne!(costs[0], costs[2]);
        },
    );
}

#[test]
fn numeric_formals_reject_a_length_alias() {
    run_with_source(
        "/** @perf O(n.length) */ export function work(n:number) {}",
        |analysis, file| {
            let _ = summary_of(analysis, file, "work");

            assert!(analysis
                .errors
                .iter()
                .any(|message| message.contains("UnknownName")));
        },
    );
}

#[test]
fn unrelated_named_assumptions_do_not_change_recursive_preference() {
    for mark in ["cold", "hot"] {
        for unrelated in [
            "",
            "/** @perf O(xs.length^2) */ function unrelated(xs:string) {}",
        ] {
            let source = format!("/** @perf {mark} */ export function walk(n:number):number {{ return n > 0 && n <= 1000000000 ? walk(n-1) : 0; }}\n{unrelated}");

            run_with_source(&source, |analysis, file| {
                let walk = function_of_name(analysis.project, file, "walk");
                let part = summary_of(analysis, file, "walk");
                let expected = analysis
                    .bind_function_cost(file, walk, &Cost::N)
                    .expect("the recursion measure binds to its own parameter");

                assert_eq!(part.cost.compare(&expected), CostComparison::Within);
                assert_eq!(expected.compare(&part.cost), CostComparison::Within);
                assert!(part.is_complete());

                if !unrelated.is_empty() {
                    let other = function_of_name(analysis.project, file, "unrelated");
                    let tagged = summary_of(analysis, file, "unrelated");
                    let expected = analysis
                        .bind_function_cost(file, other, &Cost::parse("O(xs.length^2)").unwrap())
                        .unwrap();

                    assert_eq!(expected.compare(&tagged.cost), CostComparison::Within);
                    assert_eq!(tagged.cost.compare(&expected), CostComparison::Within);
                }
            });
        }
    }
}

#[test]
fn recursive_callback_specializations_retain_their_known_work() {
    run_with_source(
        r#"
        /** @perf O(N^3) */
        function expensive() {}
        function cheap() {}
        function visit(cb:()=>void,recur:boolean) {
            if(recur) visit(expensive,false);
            cb();
        }
        export function entry() { visit(cheap,true); }
    "#,
        |analysis, file| {
            let function = function_of_name(analysis.project, file, "entry");
            let part = summary_of(analysis, file, "entry");
            let expected = analysis
                .bind_function_cost(file, function, &Cost::parse("O(N^3)").unwrap())
                .unwrap();

            assert_eq!(
                part.cost.compare(&expected),
                CostComparison::Within,
                "{}",
                part.cost.text()
            );
            assert_eq!(
                expected.compare(&part.cost),
                CostComparison::Within,
                "{}",
                part.cost.text()
            );
        },
    );
}

#[test]
fn direct_nested_calls_bind_lexical_captures_and_inner_formals_shadow_them() {
    for (body, expected) in [
        (
            "/** @perf O(xs.length) */ function inner() {} inner();",
            "O(xs.length)",
        ),
        (
            "/** @perf O(ys.length) */ function inner() {} inner();",
            "O(ys.length)",
        ),
        (
            "/** @perf O(xs.length) */ function inner(xs:string) {} inner(ys);",
            "O(ys.length)",
        ),
    ] {
        run_with_source(
            &format!("export function entry(xs:string,ys:string) {{\n{body}\n}}"),
            |analysis, file| {
                let function = function_of_name(analysis.project, file, "entry");
                let part = summary_of(analysis, file, "entry");
                let expected = analysis
                    .bind_function_cost(file, function, &Cost::parse(expected).unwrap())
                    .unwrap();

                assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
                assert_eq!(part.cost.compare(&expected), CostComparison::Within);
                assert_eq!(expected.compare(&part.cost), CostComparison::Within);
            },
        );
    }
}

#[test]
fn opaque_actual_relations_are_partial_instead_of_invalid_or_provably_over() {
    for argument in ["n+1", "n-n", "m"] {
        run_with_source(&format!("/** @perf O(n^2) */ function kernel(n:number) {{}}\nexport function work(n:number) {{ let m=n; m+=1; kernel({argument}); }}"), |analysis, file| {
            let part = summary_of(analysis, file, "work");

            assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
            assert!(!part.is_complete(), "{argument}");
            assert_eq!(part.cost.compare(&Cost::ONE), CostComparison::Within);
        });
    }

    run_with_source("/** @perf O(n^2) */ function kernel(n:number) {}\nexport function work(n:number) { const m=n; kernel(m); }", |analysis, file| {
        let part = summary_of(analysis, file, "work");

        assert!(part.is_complete());
        assert_eq!(part.cost.compare(&Cost::ONE), CostComparison::Exceeds);
    });

    for argument in ["1", "2"] {
        run_with_source(&format!("/** @perf O(n^2) */ function kernel(n:number) {{}}\nexport function work(n:number) {{ kernel({argument}); }}"), |analysis, file| {
            let part = summary_of(analysis, file, "work");

            assert!(part.is_complete());
            assert_eq!(part.cost.compare(&Cost::ONE), CostComparison::Within);
        });
    }
}

fn lint(files: &[(&str, &str)]) -> std::process::Output {
    let project = support::project_of(files);

    std::process::Command::new(env!("CARGO_BIN_EXE_olint"))
        .current_dir(project.path())
        .args(["--types=syntactic", "--tsconfig=tsconfig.json"])
        .output()
        .unwrap()
}

#[test]
fn unresolved_actuals_obey_unknown_policy_without_a_false_constant_limit_violation() {
    for (policy, exit) in [("ignore", 0), ("warn", 0), ("error", 1)] {
        let config = format!(r#"{{"entrypoints":["index.ts"],"max":"O(1)","unknown":"{policy}"}}"#);
        let output = lint(&[("tsconfig.json", "{}"), ("olint.config.json", &config), ("index.ts", "/** @perf O(n^2) */ function kernel(n:number) {}\nexport function work(n:number) { kernel(n-n); }")]);

        assert_size_relation(&output, policy != "ignore", exit);
    }
}

#[test]
fn failed_constraints_keep_their_own_entry_provenance() {
    let output = lint(&[
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "/** @perf O(N) */ export function work(n:number) {}",
        ),
        ("left.ts", "export {work} from './index';"),
        ("right.ts", "export {work} from './index';"),
        (
            "olint.config.json",
            r#"{"entrypoints":[{"path":"left.ts","max":"O(1)"},{"path":"right.ts","max":"O(N^2)"}]}"#,
        ),
    ]);

    assert_eq!(output.status.code(), Some(1));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let violation = stdout
        .lines()
        .find(|line| line.contains(", above the limit "))
        .unwrap();

    assert!(violation.ends_with("via left.ts"), "{violation}");
    assert!(!violation.contains("right.ts"));
}

#[test]
fn independent_conjunctions_preserve_both_failure_and_unknown_context() {
    let output = lint(&[
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "/** @perf O(n^2) */ export function work(n:number,m:number) {}",
        ),
        ("left.ts", "export {work} from './index';"),
        ("right.ts", "export {work} from './index';"),
        (
            "olint.config.json",
            r#"{"entrypoints":[{"path":"left.ts","max":"O(n)"},{"path":"right.ts","max":"O(m)"}]}"#,
        ),
    ]);

    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout)
        .contains("olint proves O(n^2), above the limit O(n)"));
    assert!(String::from_utf8_lossy(&output.stderr).contains("against O(m) via right.ts"));
}

#[test]
fn raw_report_validates_annotation_names_before_showing_the_body() {
    for cost in ["O(missing)", "O(n.length)"] {
        let source = format!("/** @perf {cost} */\nexport function work(n:number) {{ void 0; }}");
        let project = support::project_of(&[("tsconfig.json", "{}"), ("index.ts", &source)]);
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_olint"))
            .current_dir(project.path())
            .args(["--types=syntactic", "--report", "--min=0"])
            .output()
            .unwrap();

        assert_eq!(output.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&output.stderr).contains("UnknownName"));
    }
}

#[test]
fn unknown_actuals_do_not_hide_invalid_declared_names() {
    let output = lint(&[("tsconfig.json", "{}"), ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#), ("index.ts", "/** @perf O(a + missing) */ function kernel(a:number) {}\nexport function work(n:number) { kernel(n+1); }")]);

    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("UnknownName"));
}

#[test]
fn own_max_replaces_the_inherited_conjunction() {
    let output = lint(&[
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "/** @perf O(xs.length^2) @perf max O(N^3) */\nexport function work(xs:string) {}",
        ),
        (
            "olint.config.json",
            r#"{"entrypoints":[{"path":"index.ts","max":"O(1)"},{"path":"index.ts","max":"O(log N)"}]}"#,
        ),
    ]);

    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("0 over limit"));
}

#[test]
fn incomparable_duplicates_keep_both_constraints_in_either_order() {
    for limits in [["O(n)", "O(m)"], ["O(m)", "O(n)"]] {
        for policy in ["ignore", "warn", "error"] {
            let config = format!(
                r#"{{"unknown":"{policy}","entrypoints":[{{"path":"index.ts","max":"{}"}},{{"path":"index.ts","max":"{}"}}]}}"#,
                limits[0], limits[1]
            );
            let output = lint(&[
                ("tsconfig.json", "{}"),
                ("olint.config.json", &config),
                (
                    "index.ts",
                    "/** @perf O(n^2) */ export function work(n:number,m:number) {}",
                ),
            ]);

            assert_eq!(output.status.code(), Some(1));
            assert!(String::from_utf8_lossy(&output.stdout)
                .contains("olint proves O(n^2), above the limit O(n)"));
            assert_eq!(
                String::from_utf8_lossy(&output.stderr).contains("against O(m)"),
                policy != "ignore"
            );
        }
    }
}

#[test]
fn source_dimension_names_follow_ecmascript_identifier_spelling() {
    for name in ["$items", "π", "𐐀", "a\u{200c}b"] {
        run_with_source(
            &format!("/** @perf O({name}.length^2) */ export function work({name}:string) {{}}"),
            |analysis, file| {
                let function = function_of_name(analysis.project, file, "work");
                let part = summary_of(analysis, file, "work");

                assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);

                let expected = analysis
                    .bind_function_cost(file, function, &Cost::parse("O(N)").unwrap())
                    .unwrap();

                assert_eq!(part.cost.compare(&expected), CostComparison::Exceeds);
                assert!(part
                    .cost
                    .text_with(&|id| analysis.values.label(id))
                    .contains(name));
            },
        );
    }

    for text in ["O(n logπ)", "O(n log$items)", "O(n..length)", "O(.n)"] {
        assert!(Cost::parse(text).is_err(), "{text}");
    }
}

#[test]
fn structural_length_properties_do_not_supply_an_argument_size_proof() {
    run_with_source("/** @perf O(n^2) */ function kernel(n:number) {}\nexport function work(object:{length:number}) { kernel(object.length); }", |analysis, file| {
        let part = summary_of(analysis, file, "work");

        assert!(!part.is_complete());
        assert!(analysis.errors.is_empty());
        assert_eq!(part.cost.compare(&Cost::ONE), CostComparison::Within);
    });
}

#[test]
fn high_report_minimum_keeps_size_relation_diagnostics_and_unknown_histogram() {
    let project = support::project_of(&[("tsconfig.json", "{}"), ("index.ts", "/** @perf O(n^2) */ function kernel(n:number) {}\nexport function work(n:number) { kernel(n-n); }")]);
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_olint"))
        .current_dir(project.path())
        .args(["--types=syntactic", "--report", "--min=100"])
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&output.stdout)
        .lines()
        .any(|line| line.starts_with("unknown ")));
    assert!(String::from_utf8_lossy(&output.stderr).contains("input size relation"));
}

/// G40: a directive naming a quantity the call leaves unresolved is a directive error, a diagnostic under every
/// policy and an Unknown node, whatever known terms it adds beside that quantity.
#[test]
fn unresolved_directive_quantities_are_unknown_whatever_their_known_terms() {
    for annotation in ["n^2+N^3", "max(n^2,N^3)", "max(n^2+N^3,N^2)"] {
        for policy in ["ignore", "warn", "error"] {
            let config =
                format!(r#"{{"entrypoints":["index.ts"],"max":"O(N^2)","unknown":"{policy}"}}"#);
            let source = format!("/** @perf O({annotation}) */ function kernel(n:number) {{}}\nexport function work(n:number) {{ kernel(n-n); }}");
            let output = lint(&[
                ("tsconfig.json", "{}"),
                ("olint.config.json", &config),
                ("index.ts", &source),
            ]);
            let stdout = String::from_utf8_lossy(&output.stdout);

            let stderr = String::from_utf8_lossy(&output.stderr);

            assert_eq!(
                output.status.code(),
                Some(i32::from(policy == "error")),
                "{annotation}: {stdout}"
            );
            assert!(stdout.contains("0 over limit"), "{annotation}: {stdout}");
            assert!(
                stderr.contains(&format!(
                    "olint: warning: @perf O({annotation}) at index.ts:1 names n, whose size this call leaves unresolved"
                )),
                "{annotation}: {stderr}"
            );
            assert_eq!(stderr.contains("input size relation"), policy != "ignore");
        }
    }
}

#[test]
fn unresolved_dependent_branches_do_not_invent_a_known_factor() {
    for annotation in ["n^2*N^3", "N^3/n", "N^n", "log(n)", "n!"] {
        run_with_source(&format!("/** @perf O({annotation}) */ function kernel(n:number) {{}}\nexport function work(n:number) {{ kernel(n-n); }}"), |analysis, file| {
            let part = summary_of(analysis, file, "work");

            assert!(analysis.errors.is_empty(), "{annotation}: {:?}", analysis.errors);
            assert!(!part.is_complete(), "{annotation}");
            assert_eq!(part.cost.compare(&Cost::ONE), CostComparison::Within, "{annotation}");
        });
    }
}

/// G40: a statement directive naming a quantity the call leaves unresolved is Unknown, whatever its known terms.
#[test]
fn unresolved_statement_annotations_are_unknown() {
    let output = lint(&[("tsconfig.json", "{}"), ("olint.config.json", r#"{"entrypoints":["index.ts"],"max":"O(N^2)"}"#), ("index.ts", "function kernel(n:number) {\n/** @perf O(n^2 + N^3) */\nvoid 0;\n}\nexport function work(n:number) { kernel(n-n); }")]);

    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(output.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&output.stdout).contains("0 over limit"));
    assert!(stderr.contains("input size relation"), "{stderr}");
    assert!(
        stderr.contains("names n, whose size this call leaves unresolved"),
        "{stderr}"
    );
}

#[test]
fn omitted_actual_arguments_do_not_acquire_unbounded_formal_sizes() {
    for parameter in ["n=1", "n:number"] {
        for (policy, exit) in [("ignore", 0), ("warn", 0), ("error", 1)] {
            let config =
                format!(r#"{{"entrypoints":["index.ts"],"max":"O(1)","unknown":"{policy}"}}"#);
            let source = format!("/** @perf O(n^2) */ function kernel({parameter}) {{}}\nexport function work() {{ kernel(); }}");
            let output = lint(&[
                ("tsconfig.json", "{}"),
                ("olint.config.json", &config),
                ("index.ts", &source),
            ]);

            assert_size_relation(&output, policy != "ignore", exit);
        }
    }
}

fn assert_size_relation(output: &std::process::Output, unresolved: bool, exit: i32) {
    assert_eq!(
        output.status.code(),
        Some(exit),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("0 over limit"));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr).contains("input size relation"),
        unresolved
    );
}

#[test]
fn parameter_patterns_supply_names_without_inventing_quantity_relations() {
    for (parameters, cost, argument, unresolved) in [
        ("{n}:{n:number}", "n^2", "{n:1}", true),
        ("{n:local}:{n:number}", "local^2", "{n:1}", true),
        ("{xs}:{xs:string}", "xs.length", "{xs:'x'}", true),
        ("[n]:number[]", "n^2", "[1]", true),
        ("{a:[n]}:{a:number[]}", "n^2", "{a:[1]}", true),
        ("...xs:number[]", "xs.length", "1,2", false),
    ] {
        let source = format!("/** @perf O({cost}) */ function kernel({parameters}) {{}}\nexport function work() {{kernel({argument});}}");
        let output = lint(&[
            ("tsconfig.json", "{}"),
            (
                "olint.config.json",
                r#"{"entrypoints":["index.ts"],"max":"O(1)"}"#,
            ),
            ("index.ts", &source),
        ]);

        assert_size_relation(&output, unresolved, 0);
    }

    let invalid = lint(&[
        ("tsconfig.json", "{}"),
        ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#),
        (
            "index.ts",
            "/** @perf O(n^2) */ export function work({n:local}:{n:number}) {}",
        ),
    ]);

    assert_eq!(invalid.status.code(), Some(2));
}

#[test]
fn unavailable_parameter_limits_are_comparison_unknowns() {
    let output = lint(&[
        ("tsconfig.json", "{}"),
        ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#),
        (
            "index.ts",
            "/** @perf max O(xs.length) */ export function work([...xs]:number[]) {}",
        ),
    ]);

    assert_ne!(
        output.status.code(),
        Some(2),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("comparison"));
}

use std::path::Path;

use olint::analysis::Analysis;
use olint::config::read_config;
use olint::declarations::FunctionNode;
use olint::project::Project;
use olint::public::public_functions;
use oxc_allocator::Allocator;

use crate::support;

use support::SYNTACTIC;

#[test]
fn descriptor_order_keeps_only_surviving_getters_setters_and_data() {
    for (definitions, expected) in [
        (vec!["data", "get"], 1),
        (vec!["get", "set"], 2),
        (vec!["get", "data", "set"], 1),
        (vec!["set", "data", "get"], 1),
        (vec!["get", "set", "data"], 1),
        (vec!["get", "get", "set"], 2),
    ] {
        for shape in ["object", "commonjs", "class"] {
            let members: Vec<_> = definitions
                .iter()
                .map(|definition| match *definition {
                    "get" => "get selected(){return 1;}",
                    "set" => "set selected(value){void value;}",
                    _ if shape == "class" => "selected=()=>{};",
                    _ => "selected:()=>{}",
                })
                .collect();
            let body = members.join(if shape == "class" { " " } else { "," });
            let source = match shape {
                "class" => format!("export class API {{{body}}}"),
                "commonjs" => format!("module.exports={{{body}}};"),
                _ => format!("export const api={{{body}}};"),
            };

            let constructed = usize::from(shape == "class" && definitions.contains(&"data"));

            with_surface(&source, |_, coverage| {
                assert_eq!(coverage.functions.len(), expected + constructed, "{source}");
                assert!(coverage.unknowns.is_none(), "{source}");
            });
        }
    }
}

#[test]
fn primitive_fields_are_not_unresolved_callable_surfaces() {
    with_surface("export class API { total:number; name:string; enabled:boolean; constructor(){this.total=1;this.name='x';this.enabled=true;} }",|_,coverage| {
        assert_eq!(coverage.functions.len(),1);
        assert!(coverage.unknowns.is_none());
    });
    with_surface("export declare const total:number;", |_, coverage| {
        assert!(coverage.functions.is_empty());
        assert!(coverage.unknowns.is_none());
    });
}

#[test]
fn computed_methods_require_a_structurally_surviving_definition() {
    for (members, retained) in [
        ("[key](){void 987654;}", true),
        ("ordinary(){} [key](){void 987654;}", true),
        ("[key](){void 987654;} ordinary(){}", false),
        ("field=0; [key](){void 987654;}", false),
        ("selected(){void 987654;} [key]=0;", false),
        ("[key]=0; selected(){void 987654;}", false),
        ("static [key]=0; static selected(){void 987654;}", false),
        ("static selected(){void 987654;} static [key]=0;", false),
        ("static [key]=0; selected(){void 987654;}", true),
        ("[key]=0; static selected(){void 987654;}", true),
        ("[key]=0; constructor(){void 987654;}", true),
    ] {
        with_surface(
            &format!("declare const key:string; export class API {{{members}}}"),
            |analysis, coverage| {
                let present = coverage
                    .functions
                    .iter()
                    .filter(|public| !matches!(public.function, FunctionNode::Construction(_)))
                    .any(|public| {
                        let span = oxc_span::GetSpan::span(
                            &analysis
                                .project
                                .file(public.file)
                                .semantic
                                .nodes()
                                .kind(public.function.node_id()),
                        );

                        analysis.project.file(public.file).text
                            [span.start as usize..span.end as usize]
                            .contains("987654")
                    });

                assert_eq!(present, retained, "{members}");
                assert!(coverage.unknowns.is_some());
            },
        );
    }

    with_surface("declare const key:string; class Base { selected(){void 987654;} } export class API extends Base {[key]=0;}",|_,coverage| {
        assert_eq!(coverage.functions.len(),1);
        assert!(matches!(coverage.functions[0].function,FunctionNode::Construction(_)));
        assert!(coverage.unknowns.is_some());
    });

    for (base, method, expected) in [
        ("[key]=0;", "selected(){}", 1),
        ("selected=0;", "selected(){}", 1),
        ("static [key]=0;", "static selected(){}", 1),
        ("[key]=0;", "static selected(){}", 2),
    ] {
        with_surface(&format!("declare const key:string; class Base {{{base}}} export class API extends Base {{{method}}}"),|_,coverage| {
            assert_eq!(coverage.functions.len(),expected,"{base} {method}");
        });
    }
}

#[test]
fn implicit_construction_is_a_named_surface_only_where_it_initializes() {
    for (source, expected) in [
        (
            "export class HeavyField { rows: number[] = []; }",
            vec!["new HeavyField()"],
        ),
        (
            "export class HeavyField { rows: number[] = []; constructor(){} }",
            vec!["HeavyField.constructor"],
        ),
        (
            "class Base { constructor(){} } export class Derived extends Base {}",
            vec!["Base.constructor"],
        ),
        (
            "class Base { rows: number[] = []; } export class Derived extends Base {}",
            vec!["new Derived()"],
        ),
        ("export class Empty {}", vec![]),
        (
            "export class Uninitialized { count: number = 0; }",
            vec!["new Uninitialized()"],
        ),
        ("export class Statics { static total = 1; }", vec![]),
        ("export declare class Ambient { size: number; }", vec![]),
        ("export abstract class Shape { size = 1; }", vec![]),
        (
            "abstract class Shape { size = 1; } export class Concrete extends Shape {}",
            vec!["new Concrete()"],
        ),
        (
            "export const Named = class { size = 1; };",
            vec!["new Named()"],
        ),
        (
            "export default class { size = 1; }",
            vec!["new <default>()"],
        ),
        ("export class Hidden { #size = 1; }", vec!["new Hidden()"]),
        (
            "export class Accessors { accessor size = 1; }",
            vec!["new Accessors()"],
        ),
    ] {
        with_surface(source, |analysis, coverage| {
            let names: Vec<String> = coverage
                .functions
                .iter()
                .map(|public| analysis.name_of(public.file, public.function))
                .collect();

            assert_eq!(names, expected, "{source}");
        });
    }
}

#[test]
fn discovery_is_pure_until_final_coverage_origins_are_requested() {
    support::run_in_project(&[("tsconfig.json","{}"),("index.ts","declare const condition:boolean; condition && (module.exports=()=>{}); export function selected(){}"),("olint.config.json",r#"{"entrypoints":["index.ts"]}"#)],|project,_| {
        let mut analysis=Analysis::new(project,SYNTACTIC);
        let config=read_config(project,None).unwrap();
        let before=analysis.scheduler_stats();
        let unknowns=analysis.unknowns.len();

        assert_eq!(olint::public::public_roots(&mut analysis,&config).unwrap().len(),1);
        assert_eq!(analysis.scheduler_stats().work,before.work);
        assert_eq!(analysis.scheduler_stats().tasks,before.tasks);
        assert_eq!(analysis.unknowns.len(),unknowns);
        assert!(public_functions(&mut analysis,&config).unwrap().unknowns.is_some());
    });
}

#[test]
fn value_surfaces_follow_aliases_members_namespaces_and_assignments() {
    for source in [
        "function selected(){} const first=selected; const second=first; export {second};",
        "function selected(){} export const api={nested:{selected}};",
        "export namespace API { export function selected(){} function hidden(){} }",
        "function selected(){} const api={selected}; export = api;",
        "function selected(){} module.exports={selected};",
        "function selected(){} exports.selected=selected;",
        "function selected(){} module.exports.selected=selected;",
        "function selected(){} export default {selected};",
        "export function selected(x:string):void; export function selected(x:number):void; export function selected(x:unknown){}",
    ] {
        with_surface(source, |analysis, coverage| {
            assert_eq!(coverage.functions.len(),1,"{source}");

            let function=&coverage.functions[0];

            assert_eq!(analysis.name_of(function.file,function.function),"selected","{source}");
            assert!(coverage.unknowns.is_none(),"{source}");
        });
    }
}

#[test]
fn inherited_accessors_and_implementations_preserve_accessibility() {
    let source = "class Base { selected(){} private hidden(){} protected guarded(){} overridden(){} } export const API=class extends Base { private overridden(){} get pair(){return 0;} set pair(value:number){} method(x:number):void; method(x:unknown){} };";

    with_surface(source, |analysis, coverage| {
        let names: Vec<_> = coverage
            .functions
            .iter()
            .map(|public| analysis.name_of(public.file, public.function))
            .collect();

        assert_eq!(names.len(), 4, "{names:?}");
        assert!(
            names.iter().any(|name| name.ends_with("selected")),
            "{names:?}"
        );
        assert!(
            names.iter().all(|name| !name.ends_with("hidden")
                && !name.ends_with("guarded")
                && !name.ends_with("overridden")),
            "{names:?}"
        );
        assert!(coverage.unknowns.is_none());
    });
}

#[test]
fn commonjs_replacements_and_shadowed_names_do_not_export_stale_functions() {
    for source in [
        "function hidden(){} exports.hidden=hidden; module.exports=0;",
        "function hidden(){} module.exports=0; exports.hidden=hidden;",
        "function hidden(){} module.exports=0; exports['hidden']=hidden;",
        "const exports={}; function hidden(){} exports.hidden=hidden;",
        "const module={exports:{}}; function hidden(){} module.exports.hidden=hidden;",
    ] {
        with_surface(source, |_, coverage| {
            assert!(coverage.functions.is_empty(), "{source}");
            assert!(coverage.unknowns.is_none(), "{source}");
        });
    }
}

#[test]
fn overwritten_properties_exclude_cost_and_commonjs_additions_keep_other_members() {
    for source in [
        "function hidden(){} export const api={selected:hidden,get selected(){return 0}};",
        "function hidden(){} module.exports={selected:hidden,get selected(){return 0}};",
        "function selected(){} module.exports={selected}; module.exports.extra=0;",
    ] {
        with_surface(source, |analysis, coverage| {
            assert_eq!(coverage.functions.len(), 1);
            assert!(coverage
                .functions
                .iter()
                .all(|public| analysis.name_of(public.file, public.function) != "hidden"));
            assert!(coverage.unknowns.is_none());
        });
    }
}

#[test]
fn unimplemented_fields_and_conditional_commonjs_have_partial_coverage() {
    for source in [
        "export class API { selected!:()=>void; }",
        "export declare class API { constructor(); }",
        "export declare function selected():void;",
        "export declare const selected:()=>void;",
        "declare const condition:boolean; if(condition) module.exports=()=>{};",
        "declare const condition:boolean; condition && (module.exports=()=>{});",
    ] {
        with_surface(source, |_, coverage| {
            assert!(coverage.unknowns.is_some(), "{source}")
        });
    }

    support::run_in_project(
        &[
            ("tsconfig.json", "{}"),
            (
                "index.ts",
                "export * as api from './types'; export {callable} from './types';",
            ),
            ("types.d.ts", "export declare const callable:()=>void;"),
            ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#),
        ],
        |project, _| {
            let mut analysis = Analysis::new(project, SYNTACTIC);

            assert!(final_coverage(&mut analysis).unknowns.is_some());
        },
    );
}

#[test]
fn type_only_exports_and_namespace_cycles_are_complete() {
    support::run_in_project(&[
        ("tsconfig.json","{}"),
        ("olint.config.json",r#"{"entrypoints":["index.ts"]}"#),
        ("index.ts","export type * from './types'; export type { selected } from './types'; export * as api from './bridge';"),
        ("types.ts","export function selected(){}"),
        ("bridge.ts","export * as cycle from './index'; export function ordinary(){}"),
    ],|project,_| {
        let mut analysis=Analysis::new(project,SYNTACTIC);
        let config=read_config(project,None).unwrap();
        let coverage=public_functions(&mut analysis,&config).unwrap();

        assert_eq!(coverage.functions.len(),1);
        assert!(coverage.unknowns.is_none());
    });
}

fn with_surface(
    source: &str,
    check: impl FnOnce(&Analysis<'_, '_>, olint::public::PublicCoverage<'_>),
) {
    support::run_in_project(
        &[
            ("tsconfig.json", "{}"),
            ("index.ts", source),
            ("olint.config.json", r#"{"entrypoints":["index.ts"]}"#),
        ],
        |project, _| {
            let mut analysis = Analysis::new(project, SYNTACTIC);
            let coverage = final_coverage(&mut analysis);

            check(&analysis, coverage);
        },
    );
}

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
                let public = public_functions(&mut analysis, &config).unwrap().functions;

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

                assert!(final_coverage(&mut analysis).functions.is_empty());
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
    let public = public_functions(&mut analysis, &config)
        .expect("valid selection")
        .functions;
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

fn final_coverage<'a>(analysis: &mut Analysis<'_, 'a>) -> olint::public::PublicCoverage<'a> {
    let config = read_config(analysis.project, None).unwrap();

    public_functions(analysis, &config).unwrap()
}

#[test]
fn model_includes_namespace_and_class_expression_implementations() {
    let allocator = Allocator::default();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/model/tsconfig.json");
    let project = Project::load(&allocator, &path).unwrap();
    let mut analysis = Analysis::new(&project, SYNTACTIC);
    let coverage = final_coverage(&mut analysis);
    let sites: Vec<_> = coverage
        .functions
        .iter()
        .map(|public| {
            let span = oxc_span::GetSpan::span(
                &project
                    .file(public.file)
                    .semantic
                    .nodes()
                    .kind(public.function.node_id()),
            );

            (
                project.file(public.file).relative.as_str(),
                project.line_of(public.file, span.start),
            )
        })
        .collect();

    for expected in [
        ("src/budgets.ts", 62),
        ("src/budgets.ts", 123),
        ("src/budgets.ts", 140),
        ("src/classes.ts", 64),
        ("src/classes.ts", 75),
        ("src/classes.ts", 88),
        ("src/classes.ts", 118),
        ("src/classes.ts", 140),
    ] {
        assert!(sites.contains(&expected), "{expected:?}");
    }

    assert_eq!(coverage.functions.len(), 135);
}

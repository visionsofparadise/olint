use std::path::Path;

use olint::analysis::Analysis;
use olint::declarations::{Declaration, FunctionNode};
use olint::declared_types::Kind;
use olint::project::{FileId, Project};
use olint::tsc::{CalleeAnswer, CalleeTarget, Query, TscAnswer, TscError, TscReply, TypeAnswer};
use olint::types::TscPass;
use oxc_ast::ast::Expression;

mod support;

#[test]
fn recovered_callable_targets_keep_dispatch_closedness_separate() {
    let files = [
        ("tsconfig.json", "{}"),
        ("helper.ts", "export function work(xs:number[]):void; export function work(xs:number[]){ for(const x of xs) void x; }"),
        ("index.ts", "import helper = require('./helper'); import {work} from './helper'; const a=work; const alias=a; let mutable=work; const x=y; const y=x; class API {work(xs:number[]):void; work(xs:number[]){for(const x of xs) void x;}} export function root(xs:number[]){work(xs); alias(xs); mutable(xs); x(); helper.work(xs); new API().work(xs);}"),
    ];

    assert_call_targets(
        &files,
        &[
            ("work", 1, false),
            ("alias", 1, false),
            ("mutable", 1, true),
            ("x", 0, true),
            ("helper.work", 1, true),
            ("new API().work", 1, true),
        ],
    );
}

#[test]
fn sidecar_signature_spans_recover_bodies_without_closing_dispatch() {
    let source = "function work(xs:number[]):void; function work(xs:number[]){for(const x of xs) void x;} class API {work(xs:number[]):void;work(xs:number[]){for(const x of xs) void x;}} declare const loose:any; loose.first([]);loose.second([]);";
    let files = [("tsconfig.json", "{}"), ("index.ts", source)];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");

        for (callee, signature) in [
            ("loose.first", "function work(xs:number[]):void;"),
            ("loose.second", "work(xs:number[]):void;"),
        ] {
            let mut analysis = Analysis::new(project, SYNTACTIC);
            let call = call_of(project, file, callee);

            analysis.set_pass(TscPass::Recording);
            assert!(analysis.callee_targets_of(file, call).known.is_empty());

            let start = if callee == "loose.second" {
                source.rfind(signature).unwrap()
            } else {
                source.find(signature).unwrap()
            };

            analysis
                .take_answers(reply_of(vec![Some(callee_answer_of(
                    &[(
                        project.file(file).path.to_string_lossy().into_owned(),
                        start as u32,
                        (start + signature.len()) as u32,
                    )],
                    true,
                ))]))
                .unwrap();
            analysis.set_pass(TscPass::Answering);

            let targets = analysis.callee_targets_of(file, call);

            assert_eq!(targets.known.len(), 1, "{callee}");
            assert!(targets.open);
            assert!(
                matches!(project.file(file).semantic.nodes().kind(targets.known[0].node),oxc_ast::AstKind::Function(function) if function.body.is_some())
            );
        }
    });
}

#[test]
fn internal_import_equals_follows_assignments_and_qualified_names_with_cycle_guards() {
    let files = [
        ("tsconfig.json", "{}"),
        ("helper.ts", "function work(){} export = work;"),
        ("qualified.ts", "namespace N {export function work(){}} export import alias=N.work;"),
        ("forward.ts", "export {alias} from './qualified';"),
        ("index.ts", "import work = require('./helper'); import {alias as forwarded} from './forward'; namespace N {export function run(){}} import alias = N.run; const equivalent=N.run; N.run=()=>{}; import first = second; import second = first; work();alias();equivalent();first();forwarded();"),
    ];

    assert_call_targets(
        &files,
        &[
            ("work", 1, false),
            ("alias", 1, true),
            ("equivalent", 2, true),
            ("first", 0, true),
            ("forwarded", 1, true),
        ],
    );
}

#[test]
fn runtime_values_join_initializer_and_write_targets() {
    let files = [
        ("tsconfig.json", r#"{"compilerOptions":{"allowJs":true}}"#),
        (
            "index.js",
            "function dear(){} function a(){} function b(){} function work(){} var work = dear; const pick = globalThis.flag ? a : b; let current = a; current = b; function makeA(){ return a; } const made = makeA(); function run(xs, ys){work(); pick(); current(); made(); xs.map = b; xs.map(); const zs = [1]; zs.map(); ys.map();} const shared = [1]; shared.filter = a; other(shared); function other(ws){ws.filter();} const kept = [1]; kept.find = a; function third(vs){vs.find();}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.js");
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let expected: [(&str, &[&str], bool); 9] = [
            ("work", &["dear", "work"], true),
            ("pick", &["a", "b"], false),
            ("current", &["a", "b"], true),
            ("made", &["a"], false),
            ("xs.map", &["b"], true),
            ("zs.map", &["b"], true),
            ("ys.map", &["b"], true),
            ("ws.filter", &["a"], true),
            ("vs.find", &[], true),
        ];

        for (callee, names, open) in expected {
            let targets = analysis.callee_targets_of(file, call_of(project, file, callee));
            let mut found: Vec<String> = targets
                .known
                .iter()
                .map(
                    |known| match project.file(file).semantic.nodes().kind(known.node) {
                        oxc_ast::AstKind::Function(function) => function
                            .id
                            .as_ref()
                            .map_or_else(String::new, |id| id.name.to_string()),
                        _ => String::new(),
                    },
                )
                .collect();

            found.sort();

            assert_eq!(
                (found, targets.open),
                (
                    names
                        .iter()
                        .map(|name| name.to_string())
                        .collect::<Vec<_>>(),
                    open
                ),
                "{callee}"
            );
        }
    });
}

fn assert_call_targets(files: &[(&str, &str)], expected: &[(&str, usize, bool)]) {
    run_in_project(files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(project, SYNTACTIC);

        for (callee, count, open) in expected {
            let target = analysis.callee_targets_of(file, call_of(project, file, callee));

            assert_eq!(
                (target.known.len(), target.open),
                (*count, *open),
                "{callee}"
            );
        }
    });
}

use support::{call_of, file_of, member_callee_of, run_in_project, SYNTACTIC};

const SOURCE: &str = "class Engine {\n\tgo() {}\n}\nexport function run() {}\nfunction make(): any {\n\treturn 1;\n}\nexport function f(loose: any, xs: number[], other: any) {\n\tloose.map((x: number) => x);\n\txs.includes(1);\n\tother.map((x: number) => x);\n\tmake().run();\n\tconst engine = new Engine();\n\tengine.go();\n\tmake().go();\n}\n";

fn receiver_of<'a>(project: &Project<'a>, file: FileId, callee: &str) -> &'a Expression<'a> {
    member_callee_of(project, file, callee).object()
}

fn reply_of(answers: Vec<Option<TscAnswer>>) -> TscReply {
    TscReply {
        typescript: "5.9.3".to_string(),
        from: "typescript.js".to_string(),
        answers,
    }
}

fn callee_answer_of(targets: &[(String, u32, u32)], open: bool) -> TscAnswer {
    TscAnswer::Callee(CalleeAnswer {
        targets: targets
            .iter()
            .map(|(file, start, end)| CalleeTarget {
                file: file.clone(),
                start: *start,
                end: *end,
            })
            .collect(),
        open,
    })
}

fn byte_span_of(needle: &str) -> (u32, u32) {
    let start = SOURCE.find(needle).expect("needle occurs");

    (start as u32, (start + needle.len()) as u32)
}

fn run_with_source(body: impl for<'a> FnOnce(&Project<'a>, FileId)) {
    let files = [("tsconfig.json", "{}"), ("index.ts", SOURCE)];

    run_in_project(&files, |project, root| {
        body(project, file_of(project, root, "index.ts"));
    });
}

#[test]
fn recording_asks_only_for_sites_syntax_leaves_open() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);

        analysis.set_pass(TscPass::Recording);

        assert_eq!(
            analysis.kind_of(file, receiver_of(project, file, "loose.map"), "map"),
            Kind::Unknown
        );
        assert_eq!(
            analysis.kind_of(file, receiver_of(project, file, "xs.includes"), "includes"),
            Kind::Array
        );
        assert_eq!(analysis.needed_queries().len(), 1);
        assert!(analysis
            .callee_declaration_of(file, call_of(project, file, "make().run"))
            .is_none());
        assert!(analysis
            .callee_declaration_of(file, call_of(project, file, "engine.go"))
            .is_some());

        let needed = analysis.needed_queries();

        assert_eq!(needed.len(), 2);
        assert!(matches!(needed[0], Query::Type { .. }));
        assert!(matches!(needed[1], Query::Callee { .. }));
    });
}

#[test]
fn answering_takes_recorded_answers_and_counts_misses() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let loose = receiver_of(project, file, "loose.map");
        let other = receiver_of(project, file, "other.map");

        analysis.set_pass(TscPass::Recording);
        analysis.kind_of(file, loose, "map");
        analysis
            .take_answers(reply_of(vec![Some(TscAnswer::Type(TypeAnswer {
                kind: Kind::Array,
                tuple: false,
                structural: false,
            }))]))
            .expect("the reply answers every query");
        analysis.set_pass(TscPass::Answering);

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Array);
        assert_eq!(analysis.kind_of(file, other, "map"), Kind::Unknown);
        assert!(analysis
            .stats
            .lines()
            .contains(&format!("{:>5}  tsc: miss", 1)));
        assert_eq!(analysis.tsc_info, "typescript 5.9.3 at typescript.js");
    });
}

#[test]
fn callee_answers_map_to_the_declaration_they_span() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let path = project.file(file).path.to_string_lossy().replace('\\', "/");
        let (function_start, function_end) = byte_span_of("export function run() {}");
        let (method_start, method_end) = byte_span_of("go() {}");

        analysis.set_pass(TscPass::Recording);
        analysis.callee_declaration_of(file, call_of(project, file, "make().run"));
        analysis.callee_declaration_of(file, call_of(project, file, "make().go"));
        analysis
            .take_answers(reply_of(vec![
                Some(callee_answer_of(
                    &[(path.clone(), function_start, function_end)],
                    true,
                )),
                Some(callee_answer_of(&[(path, method_start, method_end)], true)),
            ]))
            .expect("the reply answers every query");
        analysis.set_pass(TscPass::Answering);

        let function = analysis.callee_declaration_of(file, call_of(project, file, "make().run"));
        let method = analysis.callee_declaration_of(file, call_of(project, file, "make().go"));

        assert!(matches!(
            function,
            Some(Declaration::Function { function: FunctionNode::Function(function), .. })
                if function.id.as_ref().is_some_and(|id| id.name == "run")
        ));
        assert!(matches!(method, Some(Declaration::Member { .. })));
        assert!(analysis
            .declarations
            .function_of(method.expect("member"))
            .is_some());
    });
}

#[test]
fn recording_uses_types_from_earlier_rounds() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let loose = receiver_of(project, file, "loose.map");

        analysis.set_pass(TscPass::Recording);
        analysis.kind_of(file, loose, "map");
        analysis
            .take_answers(reply_of(vec![Some(TscAnswer::Type(TypeAnswer {
                kind: Kind::Set,
                tuple: false,
                structural: false,
            }))]))
            .expect("the reply answers every query");

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Set);
        assert!(analysis.needed_queries().is_empty());

        let other = receiver_of(project, file, "other.map");

        assert_eq!(analysis.kind_of(file, other, "map"), Kind::Unknown);

        let needed = analysis.needed_queries();
        let (start, end) = byte_span_of("other.map");

        assert!(
            matches!(needed.as_slice(), [Query::Type { pos, end: query_end, .. }] if *pos == start && *query_end == end - 4)
        );

        analysis.set_pass(TscPass::Answering);

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Set);
        assert!(!analysis
            .stats
            .lines()
            .iter()
            .any(|line| line.ends_with("tsc: miss")));
    });
}

#[test]
fn a_reply_missing_answers_ends_the_rounds_as_malformed() {
    run_with_source(|project, _| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let functions = analysis.reportable();
        let mut asked = 0;
        let gathered = analysis.gather_answers(&functions, |queries| {
            asked += 1;

            assert!(!queries.is_empty());

            Ok(reply_of(Vec::new()))
        });

        assert!(matches!(gathered, Err(TscError::Malformed(_))));
        assert_eq!(asked, 1);
    });
}

#[test]
fn compiler_type_descriptions_are_not_constant_size_evidence() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let loose = receiver_of(project, file, "loose.map");

        analysis.set_pass(TscPass::Recording);

        assert!(!analysis.is_tuple(file, loose));
        assert!(!analysis.is_closed(file, loose));
        assert!(analysis.needed_queries().is_empty());

        analysis.kind_of(file, loose, "map");
        analysis
            .take_answers(reply_of(vec![Some(TscAnswer::Type(TypeAnswer {
                kind: Kind::Array,
                tuple: true,
                structural: true,
            }))]))
            .expect("the reply answers every query");
        analysis.set_pass(TscPass::Answering);

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Array);
        assert!(!analysis.is_tuple(file, loose));
        assert!(!analysis.is_closed(file, loose));
    });
}

const CANDIDATES: &str = "class A { go(xs: number[]) { for (const x of xs) void x; } }\nclass B { go(xs: number[]) { void xs; } }\nconst arrow = (xs: number[]) => xs.length;\ndeclare const first: any;\ndeclare const second: any;\ndeclare const third: any;\ndeclare const fourth: any;\nfirst.go([]);\nsecond.go([]);\nthird.go([]);\nfourth.go([]);\n\u{e9}\n";

fn candidate_span_of(needle: &str) -> (u32, u32) {
    let start = CANDIDATES.find(needle).expect("needle occurs");

    (start as u32, (start + needle.len()) as u32)
}

fn run_with_candidates(body: impl for<'a> FnOnce(&Project<'a>, &Path, FileId, String)) {
    let files = [("tsconfig.json", "{}"), ("index.ts", CANDIDATES)];

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let path = project.file(file).path.to_string_lossy().into_owned();

        body(project, root, file, path);
    });
}

#[test]
fn callee_answers_map_every_candidate_and_keep_the_open_remainder() {
    run_with_candidates(|project, root, file, path| {
        let target = |needle: &str| {
            let (start, end) = candidate_span_of(needle);

            (path.clone(), start, end)
        };
        let first = target("go(xs: number[]) { for (const x of xs) void x; }");
        let second = target("go(xs: number[]) { void xs; }");
        let arrow = target("(xs: number[]) => xs.length");
        let elsewhere = (
            root.join("elsewhere/lib.ts").to_string_lossy().into_owned(),
            0,
            1,
        );
        let cases = [
            ("first.go", vec![first.clone(), second], true, 2, true),
            ("second.go", Vec::new(), true, 0, true),
            ("third.go", vec![first, elsewhere], false, 1, true),
            ("fourth.go", vec![arrow.clone(), arrow], false, 1, false),
        ];
        let mut analysis = Analysis::new(project, SYNTACTIC);

        analysis.set_pass(TscPass::Recording);

        for (callee, ..) in &cases {
            analysis.callee_targets_of(file, call_of(project, file, callee));
        }

        let answers = analysis
            .needed_queries()
            .iter()
            .map(|query| {
                let Query::Callee { pos, end, .. } = query else {
                    panic!("only callees are asked: {query:?}");
                };
                let callee = &CANDIDATES[*pos as usize..*end as usize];
                let (_, targets, open, ..) = cases
                    .iter()
                    .find(|(name, ..)| *name == callee)
                    .expect("a recorded callee");

                Some(callee_answer_of(targets, *open))
            })
            .collect();

        analysis
            .take_answers(reply_of(answers))
            .expect("the reply answers every query");
        analysis.set_pass(TscPass::Answering);

        for (callee, _, _, count, open) in &cases {
            let call = call_of(project, file, callee);
            let targets = analysis.callee_targets_of(file, call);

            assert_eq!(
                (targets.known.len(), targets.open),
                (*count, *open),
                "{callee}"
            );
            assert_eq!(
                analysis.callee_declaration_of(file, call).is_some(),
                *count == 1,
                "{callee}"
            );
        }
    });
}

#[test]
fn callee_targets_outside_the_utf8_text_are_malformed() {
    run_with_candidates(|project, _, file, path| {
        let length = CANDIDATES.len() as u32;
        let accent = CANDIDATES.find('\u{e9}').expect("accent occurs") as u32;

        for (start, end) in [(0, length + 1), (accent + 1, length), (4, 2)] {
            let mut analysis = Analysis::new(project, SYNTACTIC);

            analysis.set_pass(TscPass::Recording);
            analysis.callee_targets_of(file, call_of(project, file, "first.go"));

            let needed = analysis.needed_queries();
            let result = analysis.take_answers(reply_of(vec![Some(callee_answer_of(
                &[(path.clone(), start, end)],
                true,
            ))]));

            assert!(
                matches!(result, Err(TscError::Malformed(_))),
                "{start}..{end}: {result:?}"
            );
            assert_eq!(analysis.needed_queries(), needed);
        }
    });
}

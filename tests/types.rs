use olint::analysis::Analysis;
use olint::declarations::{Declaration, FunctionNode};
use olint::declared_types::Kind;
use olint::project::{FileId, Project};
use olint::tsc::{CalleeAnswer, Query, TscAnswer, TscError, TscReply, TypeAnswer};
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
            ("mutable", 0, true),
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
                .take_answers(reply_of(vec![Some(TscAnswer::Callee(CalleeAnswer {
                    file: project.file(file).path.to_string_lossy().into_owned(),
                    start: start as u32,
                    end: (start + signature.len()) as u32,
                }))]))
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
            ("equivalent", 1, true),
            ("first", 0, true),
            ("forwarded", 1, true),
        ],
    );
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
                closed: false,
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
                Some(TscAnswer::Callee(CalleeAnswer {
                    file: path.clone(),
                    start: function_start,
                    end: function_end,
                })),
                Some(TscAnswer::Callee(CalleeAnswer {
                    file: path,
                    start: method_start,
                    end: method_end,
                })),
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
                closed: false,
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

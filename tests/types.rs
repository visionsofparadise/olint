use olint::analysis::Analysis;
use olint::declarations::{Declaration, FunctionNode};
use olint::declared_types::Kind;
use olint::oracle::{CalleeAnswer, OracleAnswer, OracleReply, Query, TypeAnswer};
use olint::project::{FileId, Project};
use olint::types::OraclePass;
use oxc_ast::ast::Expression;

mod support;

use support::{call_of, file_of, member_callee_of, run_in_project, SYNTACTIC};

const SOURCE: &str = "class Engine {\n\tgo() {}\n}\nexport function run() {}\nfunction make(): any {\n\treturn 1;\n}\nexport function f(loose: any, xs: number[], other: any) {\n\tloose.map((x: number) => x);\n\txs.includes(1);\n\tother.map((x: number) => x);\n\tmake().run();\n\tconst engine = new Engine();\n\tengine.go();\n\tmake().go();\n}\n";

fn receiver_of<'a>(project: &Project<'a>, file: FileId, callee: &str) -> &'a Expression<'a> {
    member_callee_of(project, file, callee).object()
}

fn reply_of(answers: Vec<Option<OracleAnswer>>) -> OracleReply {
    OracleReply {
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

        analysis.set_pass(OraclePass::Recording);

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

        analysis.set_pass(OraclePass::Recording);
        analysis.kind_of(file, loose, "map");
        analysis.take_answers(reply_of(vec![Some(OracleAnswer::Type(TypeAnswer {
            kind: Kind::Array,
            tuple: false,
            closed: false,
        }))]));
        analysis.set_pass(OraclePass::Answering);

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Array);
        assert_eq!(analysis.kind_of(file, other, "map"), Kind::Unknown);
        assert!(analysis
            .stats
            .lines()
            .contains(&format!("{:>5}  oracle: miss", 1)));
        assert_eq!(analysis.oracle_info, "typescript 5.9.3 at typescript.js");
    });
}

#[test]
fn callee_answers_map_to_the_declaration_they_span() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let path = project.file(file).path.to_string_lossy().replace('\\', "/");
        let (function_start, function_end) = byte_span_of("export function run() {}");
        let (method_start, method_end) = byte_span_of("go() {}");

        analysis.set_pass(OraclePass::Recording);
        analysis.callee_declaration_of(file, call_of(project, file, "make().run"));
        analysis.callee_declaration_of(file, call_of(project, file, "make().go"));
        analysis.take_answers(reply_of(vec![
            Some(OracleAnswer::Callee(CalleeAnswer {
                file: path.clone(),
                start: function_start,
                end: function_end,
            })),
            Some(OracleAnswer::Callee(CalleeAnswer {
                file: path,
                start: method_start,
                end: method_end,
            })),
        ]));
        analysis.set_pass(OraclePass::Answering);

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
fn recording_keeps_declared_types_for_sites_earlier_rounds_answered() {
    run_with_source(|project, file| {
        let mut analysis = Analysis::new(project, SYNTACTIC);
        let loose = receiver_of(project, file, "loose.map");

        analysis.set_pass(OraclePass::Recording);
        analysis.kind_of(file, loose, "map");
        analysis.take_answers(reply_of(vec![Some(OracleAnswer::Type(TypeAnswer {
            kind: Kind::Set,
            tuple: false,
            closed: false,
        }))]));

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Unknown);
        assert!(analysis.needed_queries().is_empty());

        analysis.set_pass(OraclePass::Answering);

        assert_eq!(analysis.kind_of(file, loose, "map"), Kind::Set);
        assert!(!analysis
            .stats
            .lines()
            .iter()
            .any(|line| line.ends_with("oracle: miss")));
    });
}

use std::path::Path;

use olint::analysis::Analysis;
use olint::declarations::Declaration;
use olint::declared_types::Kind;
use olint::project::Project;
use olint::tsc::{ask, CalleeAnswer, Query, TscAnswer, TscError, TscReply, TypeAnswer};
use olint::types::TscPass;
use oxc_allocator::Allocator;

mod support;

use support::{call_of, file_of, project_of, SYNTACTIC};

const SOURCE: &str = "/* caf\u{e9} \u{1f600} */\nclass Engine {\n\trun() {\n\t\treturn 1;\n\t}\n}\ninterface Shape {\n\twidth: number;\n}\nfunction make() {\n\treturn new Engine();\n}\nexport function probe(xs: number[], pair: [number, string], shape: Shape) {\n\tmake().run();\n\treturn [xs, pair, shape];\n}\n";

fn span_of(needle: &str, occurrence: usize) -> (u32, u32) {
    let start = SOURCE
        .match_indices(needle)
        .nth(occurrence)
        .map(|(index, _)| index)
        .unwrap_or_else(|| panic!("{needle} occurs"));

    (start as u32, (start + needle.len()) as u32)
}

fn type_query_of(file: &str, needle: &str) -> Query {
    let (pos, end) = span_of(needle, 1);

    Query::Type {
        file: file.to_string(),
        pos,
        end,
    }
}

fn reply_of(tsconfig: &Path, queries: &[Query]) -> TscReply {
    match ask(Path::new(env!("CARGO_MANIFEST_DIR")), tsconfig, queries) {
        Ok(reply) => reply,
        Err(TscError::NodeUnavailable(error)) => panic!("node is unavailable: {error}"),
        Err(TscError::TypescriptUnavailable(message)) => {
            panic!("typescript is unavailable: {message}")
        }
        Err(error) => panic!("tsc failed: {error:?}"),
    }
}

fn byte_span_in(text: &str, needle: &str) -> (u32, u32) {
    let start = text
        .find(needle)
        .unwrap_or_else(|| panic!("{needle} occurs"));

    (start as u32, (start + needle.len()) as u32)
}

const MARKED_LIBRARY: &str = "\u{feff}/* caf\u{e9} \u{1f600} */\nexport class Engine {\n\trun(xs: number[]) {\n\t\treturn xs.length;\n\t}\n}\n";

const MARKED_INDEX: &str = "\u{feff}import { Engine } from \"./lib\";\n/* \u{e9}\u{e9} */\nfunction get(): any {\n\treturn new Engine();\n}\nexport function f(items: number[]) {\n\t(get() as Engine).run(items);\n\tJSON.parse(\"1\");\n}\n";

#[test]
fn byte_order_marks_keep_answers_on_their_utf8_spans() {
    let directory = project_of(&[
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "strict": true }, "include": ["src"] }"#,
        ),
        ("src/lib.ts", MARKED_LIBRARY),
        ("src/index.ts", MARKED_INDEX),
    ]);
    let tsconfig = directory.path().join("tsconfig.json");
    let index = directory
        .path()
        .join("src/index.ts")
        .to_string_lossy()
        .into_owned();
    let (items_start, items_end) = byte_span_in(MARKED_INDEX, "items)");
    let (callee_start, callee_end) = byte_span_in(MARKED_INDEX, "(get() as Engine).run");
    let reply = reply_of(
        &tsconfig,
        &[
            Query::Type {
                file: index.clone(),
                pos: items_start,
                end: items_end - 1,
            },
            Query::Callee {
                file: index,
                pos: callee_start,
                end: callee_end,
            },
        ],
    );
    let (method_start, method_end) = byte_span_in(
        MARKED_LIBRARY,
        "run(xs: number[]) {\n\t\treturn xs.length;\n\t}",
    );

    assert!(matches!(
        reply.answers[0],
        Some(TscAnswer::Type(TypeAnswer {
            kind: Kind::Array,
            ..
        }))
    ));
    assert!(matches!(
        &reply.answers[1],
        Some(TscAnswer::Callee(CalleeAnswer { file, start, end }))
            if file.ends_with("src/lib.ts") && (*start, *end) == (method_start, method_end)
    ));

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).expect("project loads");
    let file = file_of(&project, directory.path(), "src/index.ts");
    let parse = call_of(&project, file, "JSON.parse");
    let mut analysis = Analysis::new(&project, SYNTACTIC);

    analysis.set_pass(TscPass::Recording);
    analysis.callee_declaration_of(file, parse);
    analysis
        .take_answers(reply_of(&project.tsconfig_path, &analysis.needed_queries()))
        .expect("the reply answers every query");
    analysis.set_pass(TscPass::Answering);

    assert!(matches!(
        analysis.callee_declaration_of(file, parse),
        Some(Declaration::External)
    ));
}

#[test]
fn the_sidecar_answers_types_and_callees_in_utf8_offsets() {
    let directory = project_of(&[
        (
            "tsconfig.json",
            r#"{ "compilerOptions": { "strict": true }, "include": ["src"] }"#,
        ),
        ("src/index.ts", SOURCE),
    ]);
    let file = directory.path().join("src/index.ts");
    let file_text = file.to_string_lossy().into_owned();
    let (callee_start, callee_end) = span_of("make().run", 0);
    let queries = [
        type_query_of(&file_text, "xs"),
        type_query_of(&file_text, "pair"),
        type_query_of(&file_text, "shape"),
        Query::Callee {
            file: file_text.clone(),
            pos: callee_start,
            end: callee_end,
        },
    ];
    let reply = reply_of(&directory.path().join("tsconfig.json"), &queries);
    let (method_start, method_end) = span_of("run() {\n\t\treturn 1;\n\t}", 0);

    assert!(!reply.typescript.is_empty());
    assert_eq!(reply.answers.len(), 4);
    assert_eq!(
        reply.answers[0],
        Some(TscAnswer::Type(TypeAnswer {
            kind: Kind::Array,
            tuple: false,
            closed: false,
        }))
    );
    assert!(matches!(
        reply.answers[1],
        Some(TscAnswer::Type(TypeAnswer { tuple: true, .. }))
    ));
    assert!(matches!(
        reply.answers[2],
        Some(TscAnswer::Type(TypeAnswer { closed: true, .. }))
    ));

    let Some(TscAnswer::Callee(CalleeAnswer { file, start, end })) = &reply.answers[3] else {
        panic!(
            "the callee query answers a declaration: {:?}",
            reply.answers[3]
        );
    };

    assert_eq!(
        std::fs::canonicalize(file).expect("answered file exists"),
        std::fs::canonicalize(directory.path().join("src/index.ts")).expect("source exists")
    );
    assert_eq!((*start, *end), (method_start, method_end));
}

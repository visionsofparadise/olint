use std::path::Path;

use olint::declared_types::Kind;
use olint::oracle::{ask, CalleeAnswer, OracleAnswer, OracleError, Query, TypeAnswer};

mod support;

use support::project_of;

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
    let reply = match ask(
        Path::new(env!("CARGO_MANIFEST_DIR")),
        &directory.path().join("tsconfig.json"),
        &queries,
    ) {
        Ok(reply) => reply,
        Err(OracleError::NodeUnavailable(error)) => panic!("node is unavailable: {error}"),
        Err(OracleError::TypescriptUnavailable(message)) => {
            panic!("typescript is unavailable: {message}")
        }
        Err(error) => panic!("the oracle failed: {error:?}"),
    };
    let (method_start, method_end) = span_of("run() {\n\t\treturn 1;\n\t}", 0);

    assert!(!reply.typescript.is_empty());
    assert_eq!(reply.answers.len(), 4);
    assert_eq!(
        reply.answers[0],
        Some(OracleAnswer::Type(TypeAnswer {
            kind: Kind::Array,
            tuple: false,
            closed: false,
        }))
    );
    assert!(matches!(
        reply.answers[1],
        Some(OracleAnswer::Type(TypeAnswer { tuple: true, .. }))
    ));
    assert!(matches!(
        reply.answers[2],
        Some(OracleAnswer::Type(TypeAnswer { closed: true, .. }))
    ));

    let Some(OracleAnswer::Callee(CalleeAnswer { file, start, end })) = &reply.answers[3] else {
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

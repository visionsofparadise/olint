use std::path::Path;

use olint::analysis::{Analysis, Options, TypeMode};
use olint::cost::Cost;
use olint::declared_types::Kind;
use olint::project::Project;
use olint::tsc::{
    ask, parse_reply, CalleeAnswer, CalleeTarget, Query, TscAnswer, TscError, TscReply, TypeAnswer,
};
use olint::types::TscPass;
use oxc_allocator::Allocator;

use crate::support;

#[test]
fn triple_path_reader_matches_typescript_leading_directives() {
    let sources = [
        "\u{85}/// <reference path='a.ts' />",
        "/// <reference\u{feff}path='a.ts' />",
        "// first\n\u{feff}/// <reference path='a.ts' />",
        "/// <reference path='a.ts' />\nconst x=1",
        "\u{feff}/* header */\n/// <REFERENCE preserve='true' PATH = \"a.ts\" />",
        "#!/usr/bin/env node\n/// <reference path='a.ts' />",
        "const x=1;\n/// <reference path='a.ts' />",
        "/* /// <reference path='a.ts' /> */",
        "// ordinary\n/// <reference path='a.ts' />\n/// <reference path='b.ts' />",
        "//// <reference path='a.ts' />",
        "/// <reference path='a.ts' >",
        "/// <reference types='node' path='a.ts' />",
        "/// <reference lib='es5' path='a.ts' />",
        "/// <reference no-default-lib='true' path='a.ts' />",
        "/// <reference path='a.ts' /> trailing path='b.ts'",
        "/// <reference other=\" path='b.ts'\" path='a.ts' />",
        "/// <reference path='a.ts' />\u{2028}const x=1",
    ];
    let script = "const ts=require('typescript'); const cases=JSON.parse(process.argv[1]); console.log(JSON.stringify(cases.map(source=>ts.preProcessFile(source).referencedFiles.map(file=>file.fileName))))";
    let output = std::process::Command::new("node")
        .args([
            "-e",
            script,
            &serde_json::to_string(&sources).expect("sources"),
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("static TypeScript qualification");

    assert!(output.status.success());

    let expected: Vec<Vec<String>> = serde_json::from_slice(&output.stdout).expect("paths");

    for (source, expected) in sources.iter().zip(expected) {
        assert_eq!(
            olint::project::reference_paths_of(source),
            expected,
            "{source}"
        );
    }
}

#[test]
fn referenced_programs_answer_child_types_and_reject_conflicts() {
    let right_config = serde_json::json!({"files":["../shared.ts"],"compilerOptions":{"paths":{"@dep":["../b.ts"]}}}).to_string();
    let directory = project_of(&[
        (
            "tsconfig.json",
            r#"{"files":[],"references":[{"path":"./left"},{"path":"./right"}]}"#,
        ),
        (
            "left/tsconfig.json",
            r#"{"files":["index.ts","../shared.ts"],"compilerOptions":{"paths":{"@dep":["../a.ts"]}}}"#,
        ),
        ("right/tsconfig.json", &right_config),
        ("left/index.ts", "export const child = [1]; child;"),
        ("shared.ts", "import { value } from '@dep'; value;"),
        ("a.ts", "export const value = [1];"),
        ("b.ts", "export const value = 'text';"),
    ]);
    let queries =
        [("left/index.ts", 26, 31), ("shared.ts", 29, 34)].map(|(file, pos, end)| Query::Type {
            file: directory.path().join(file).to_string_lossy().into_owned(),
            pos,
            end,
        });
    let reply = reply_of(&directory.path().join("tsconfig.json"), &queries);

    assert!(matches!(
        reply.answers[0],
        Some(TscAnswer::Type(TypeAnswer {
            kind: Kind::Array,
            ..
        }))
    ));
    assert_eq!(reply.answers[1], None);
}

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
        Some(TscAnswer::Callee(CalleeAnswer { targets, open: true }))
            if matches!(targets.as_slice(), [CalleeTarget { file, start, end }]
                if file.ends_with("src/lib.ts") && (*start, *end) == (method_start, method_end))
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

    assert!(analysis.callee_declaration_of(file, parse).is_none());

    let targets = analysis.callee_targets_of(file, parse);

    assert!(targets.known.is_empty() && targets.open);
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
            structural: false,
        }))
    );
    assert!(matches!(
        reply.answers[1],
        Some(TscAnswer::Type(TypeAnswer { tuple: true, .. }))
    ));
    assert!(matches!(
        reply.answers[2],
        Some(TscAnswer::Type(TypeAnswer {
            structural: true,
            ..
        }))
    ));

    let Some(TscAnswer::Callee(CalleeAnswer {
        targets,
        open: true,
    })) = &reply.answers[3]
    else {
        panic!(
            "the callee query answers a declaration: {:?}",
            reply.answers[3]
        );
    };

    let [CalleeTarget { file, start, end }] = targets.as_slice() else {
        panic!("one implementation answers the callee: {targets:?}");
    };

    assert_eq!(
        std::fs::canonicalize(file).expect("answered file exists"),
        std::fs::canonicalize(directory.path().join("src/index.ts")).expect("source exists")
    );
    assert_eq!((*start, *end), (method_start, method_end));
}

fn legacy_classes_of(source: &str, types: TypeMode, names: &[&str]) -> Vec<Cost> {
    results_of(source, types, names)
        .into_iter()
        .map(|(cost, _)| cost)
        .collect()
}

fn results_of(source: &str, types: TypeMode, names: &[&str]) -> Vec<(Cost, bool)> {
    let files = [
        (
            "tsconfig.json",
            r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["index.ts"]}"#,
        ),
        ("index.ts", source),
    ];
    let mut classes = Vec::new();

    support::run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = Analysis::new(
            project,
            Options {
                minimum_exponent: 2,
                types,
            },
        );

        if types == TypeMode::Tsc {
            let functions = analysis.reportable();
            let tsconfig = root.join("tsconfig.json");

            analysis
                .gather_answers(&functions, |queries| {
                    ask(Path::new(env!("CARGO_MANIFEST_DIR")), &tsconfig, queries)
                })
                .expect("the compiler helper answers");
        }

        for name in names {
            let function = support::function_of_name(analysis.project, file, name);
            let part = support::summary_of(&mut analysis, file, name);

            let targeted = support::unknown_reasons(&analysis, part.unknowns)
                .contains(&olint::unknowns::UnknownReason::Target);

            classes.push((
                support::legacy_class_of(&mut analysis, file, function, &part.cost),
                targeted,
            ));
        }
    });

    classes
}

const DESCRIBED_SIZES: &str = "function pad(xs: number[]) {\n\tconst items: [number, ...number[]] = [0, ...xs];\n\treturn items;\n}\nexport function tuples(xs: number[]) {\n\tlet total = 0;\n\tfor (const left of pad(xs)) for (const right of xs) total += left * right;\n\treturn total;\n}\ninterface Shape {\n\twidth: number;\n}\nfunction widen(record: Record<string, number>) {\n\tconst shape = record as unknown as Shape;\n\treturn shape;\n}\nexport function members(record: Record<string, number>, xs: number[]) {\n\tlet total = 0;\n\tfor (const key in widen(record)) for (const right of xs) total += key.length * right;\n\treturn total;\n}\nexport function spreadRows(...rows: [number, number][]) {\n\treturn new Set(...rows);\n}\nexport function fresh(xs: number[]) {\n\tlet total = 0;\n\tfor (const left of [1, 2]) for (const right of xs) total += left * right;\n\treturn total;\n}\n";

#[test]
fn compiler_type_descriptions_create_no_constant_collection_sizes() {
    let names = ["tuples", "members", "spreadRows", "fresh"];
    let expected = ["O(N^2)", "O(N^2)", "O(N)", "O(N)"].map(|text| Cost::parse(text).unwrap());

    for types in [TypeMode::Tsc, TypeMode::Syntactic] {
        assert_eq!(
            legacy_classes_of(DESCRIBED_SIZES, types, &names)
                .iter()
                .map(support::projected_class_of)
                .collect::<Vec<_>>(),
            expected,
            "{types:?}"
        );
    }
}

const UNION_MEMBERS: &str = "function make(flag: boolean) {\n\treturn flag\n\t\t? { kind: \"cheap\" as const, work(xs: number[]) { return xs.length; } }\n\t\t: { kind: \"costly\" as const, work(xs: number[]) { let total = 0; for (const left of xs) for (const right of xs) total += left * right; return total; } };\n}\nclass Engine {\n\trun(xs: number[]): number;\n\trun(xs: number[], scale: number): number;\n\trun(xs: number[], scale = 1) {\n\t\tlet total = 0;\n\t\tfor (const left of xs) for (const right of xs) total += left * right * scale;\n\t\treturn total;\n\t}\n}\nfunction engine() {\n\treturn new Engine();\n}\nexport function union(flag: boolean, xs: number[]) {\n\treturn make(flag).work(xs);\n}\nexport function overload(xs: number[]) {\n\treturn engine().run(xs);\n}\n";

#[test]
fn union_and_overload_candidates_contribute_their_implementation_work() {
    let quadratic = Cost::parse("O(N^2)").unwrap();

    assert_eq!(
        legacy_classes_of(UNION_MEMBERS, TypeMode::Tsc, &["union", "overload"])
            .iter()
            .map(support::projected_class_of)
            .collect::<Vec<_>>(),
        vec![quadratic.clone(), quadratic]
    );
}

#[test]
fn an_empty_batch_replies_without_loading_the_program() {
    let directory = project_of(&[("index.ts", "export const value = 1;")]);
    let reply = ask(
        Path::new(env!("CARGO_MANIFEST_DIR")),
        &directory.path().join("missing/tsconfig.json"),
        &[],
    )
    .expect("an empty batch needs no program");

    assert!(!reply.typescript.is_empty());
    assert!(reply.answers.is_empty());
}

#[test]
fn the_helper_rejects_other_protocol_versions() {
    let directory = project_of(&[("tsconfig.json", "{}"), ("index.ts", "export {};")]);

    for request in [
        serde_json::json!({"tsconfig": directory.path().join("tsconfig.json"), "queries": []}),
        serde_json::json!({"version": 1, "tsconfig": directory.path().join("tsconfig.json"), "queries": []}),
    ] {
        let output = helper_output_of(olint::tsc::SCRIPT, &request);

        assert!(!output.status.success(), "{request}");
        assert!(output.stdout.is_empty(), "{request}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("protocol version"),
            "{request}"
        );
    }
}

const CANDIDATE_LINES: [&str; 28] = [
    "/* caf\u{e9} \u{1f600} */",
    "class Engine {",
    "\trun(xs: number[]): number;",
    "\trun(xs: number[], scale: number): number;",
    "\trun(xs: number[], scale = 1) {",
    "\t\treturn xs.length * scale;",
    "\t}",
    "}",
    "function engine() {",
    "\treturn new Engine();",
    "}",
    "function make(flag: boolean) {",
    "\treturn flag ? { kind: \"cheap\" as const, work(xs: number[]) { return 0; } } : { kind: \"costly\" as const, work(xs: number[]) { return xs.length; } };",
    "}",
    "interface Loose {",
    "\twork(xs: number[]): number;",
    "}",
    "declare const loose: Loose;",
    "const measure = (xs: number[]) => xs.length;",
    "function holder() {",
    "\treturn { work: measure };",
    "}",
    "export function probe(flag: boolean, xs: number[]) {",
    "\tengine().run(xs);",
    "\tmake(flag).work(xs);",
    "\tloose.work(xs);",
    "\tholder().work(xs);",
    "}",
];

#[test]
fn callee_answers_list_every_implementation_body_across_encodings() {
    for (prefix, line_ending) in [("", "\n"), ("\u{feff}", "\r\n")] {
        let source = format!("{prefix}{}{line_ending}", CANDIDATE_LINES.join(line_ending));
        let (directory, tsconfig, path) = strict_project_of(&source);
        let callees = [
            "engine().run",
            "make(flag).work",
            "loose.work",
            "holder().work",
        ];
        let queries = callees.map(|callee| {
            let (pos, end) = byte_span_in(&source, callee);

            Query::Callee {
                file: path.clone(),
                pos,
                end,
            }
        });
        let reply = reply_of(&tsconfig, &queries);
        let implementation = format!(
            "run(xs: number[], scale = 1) {{{line_ending}\t\treturn xs.length * scale;{line_ending}\t}}"
        );
        let expected: [Vec<&str>; 4] = [
            vec![&implementation],
            vec![
                "work(xs: number[]) { return 0; }",
                "work(xs: number[]) { return xs.length; }",
            ],
            Vec::new(),
            vec!["(xs: number[]) => xs.length"],
        ];

        for ((answer, bodies), callee) in reply.answers.iter().zip(&expected).zip(callees) {
            let Some(TscAnswer::Callee(CalleeAnswer { targets, open })) = answer else {
                panic!("{callee} is answered: {answer:?}");
            };
            let mut spans: Vec<(u32, u32)> = targets
                .iter()
                .map(|target| {
                    assert_eq!(
                        std::fs::canonicalize(&target.file).expect("target exists"),
                        std::fs::canonicalize(&path).expect("source exists"),
                        "{callee}"
                    );

                    (target.start, target.end)
                })
                .collect();
            let mut expected_spans: Vec<(u32, u32)> = bodies
                .iter()
                .map(|body| byte_span_in(&source, body))
                .collect();

            spans.sort();
            expected_spans.sort();

            assert!(*open, "{callee}");
            assert_eq!(spans, expected_spans, "{callee} {line_ending:?}");
        }

        let allocator = Allocator::default();
        let project = Project::load(&allocator, &tsconfig).expect("project loads");
        let file = file_of(&project, directory.path(), "index.ts");
        let mut analysis = Analysis::new(&project, SYNTACTIC);

        analysis.set_pass(TscPass::Recording);

        for callee in callees {
            analysis.callee_targets_of(file, call_of(&project, file, callee));
        }

        let needed = analysis.needed_queries();

        assert_eq!(needed.len(), callees.len());
        analysis
            .take_answers(reply_of(&tsconfig, &needed))
            .expect("the reply answers every query");
        analysis.set_pass(TscPass::Answering);

        for (callee, count) in callees.into_iter().zip([1, 2, 0, 1]) {
            let targets = analysis.callee_targets_of(file, call_of(&project, file, callee));

            assert_eq!(
                (targets.known.len(), targets.open),
                (count, true),
                "{callee}"
            );

            for target in targets.known {
                assert!(matches!(
                    project.file(target.file).semantic.nodes().kind(target.node),
                    oxc_ast::AstKind::Function(oxc_ast::ast::Function { body: Some(_), .. })
                        | oxc_ast::AstKind::ArrowFunctionExpression(_)
                ));
            }
        }
    }
}

#[test]
fn malformed_replies_fail_clearly() {
    let queries = [
        Query::Type {
            file: "index.ts".into(),
            pos: 0,
            end: 1,
        },
        Query::Callee {
            file: "index.ts".into(),
            pos: 2,
            end: 3,
        },
    ];
    let valid = r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[null,{"query":"callee","targets":[{"file":"index.ts","start":0,"end":4}],"open":true}]}"#;
    let reply = parse_reply(valid.as_bytes(), &queries).expect("a version 2 reply parses");

    assert_eq!(
        reply.answers[1],
        Some(TscAnswer::Callee(CalleeAnswer {
            targets: vec![CalleeTarget {
                file: "index.ts".into(),
                start: 0,
                end: 4,
            }],
            open: true,
        }))
    );

    for (reply, reason) in [
        (
            r#"{"typescript":"5.9.3","from":"typescript.js","answers":[null,null]}"#,
            "version",
        ),
        (
            r#"{"version":1,"typescript":"5.9.3","from":"typescript.js","answers":[null,null]}"#,
            "protocol version 1",
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[null]}"#,
            "1 answers for 2 queries",
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[{"query":"callee","targets":[],"open":true},null]}"#,
            "query kind",
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[null,{"query":"callee","targets":[{"file":"index.ts","start":5,"end":2}],"open":true}]}"#,
            "inverted span",
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[null,{"query":"callee","file":"index.ts","start":0,"end":4}]}"#,
            "targets",
        ),
    ] {
        match parse_reply(reply.as_bytes(), &queries) {
            Err(TscError::Malformed(message)) => assert!(message.contains(reason), "{message}"),
            other => panic!("{reply} is malformed: {other:?}"),
        }
    }
}

const MEMBER_CONSTRUCTORS: &str = "class Base {
	constructor(xs: number[]) {
		for (const x of xs) void x;
	}
}
class Cubic extends Base {
	constructor(xs: number[]) {
		super(xs);
		for (const a of xs) for (const b of xs) for (const c of xs) void c;
	}
}
const table = { Base };
const named = { Base: Base };
export function viaShorthand(xs: number[]) {
	return new table.Base(xs);
}
export function viaProperty(xs: number[]) {
	return new named.Base(xs);
}
export function direct(xs: number[]) {
	return new Base(xs);
}
export function swap() {
	table.Base = Cubic;
	named.Base = Cubic;
}
";

#[test]
fn compiler_member_constructors_keep_known_work_and_the_open_remainder() {
    let linear = Cost::parse("O(N)").unwrap();
    let cubic = Cost::parse("O(N^3)").unwrap();

    assert_eq!(
        results_of(
            MEMBER_CONSTRUCTORS,
            TypeMode::Tsc,
            &["viaShorthand", "viaProperty", "direct"]
        ),
        vec![(cubic.clone(), true), (cubic, true), (linear, false)]
    );
}

const MEMBER_CALLBACKS: &str = "function each(x: number, xs: number[]) {
	for (const y of xs) void (x + y);
}
function cheap(x: number) {
	return x;
}
const helpers = { each };
export function viaCallback(xs: number[]) {
	xs.forEach((x) => helpers.each(x, xs));
	return xs.map(helpers.each);
}
export function swap() {
	helpers.each = cheap;
}
";

#[test]
fn compiler_member_callbacks_keep_the_open_remainder() {
    let [(_, targeted)] = results_of(MEMBER_CALLBACKS, TypeMode::Tsc, &["viaCallback"])[..] else {
        panic!("one result");
    };

    assert!(targeted);
}

const PRE_INDEX_LOOKUP: &str = "const findNode = (sf, pos, end) => {\n\tlet best;\n\tconst visit = (n) => {\n\t\tif (n.getStart(sf) > pos || n.getEnd() < end) return;\n\t\tif (n.getStart(sf) === pos && n.getEnd() === end) best = n;\n\t\tn.forEachChild(visit);\n\t};\n\tvisit(sf);\n\treturn best;\n};\n";

fn script_of_pre_index_lookup() -> String {
    let start = olint::tsc::SCRIPT
        .find("const findNode = ")
        .expect("the helper defines its lookup");
    let end = start
        + olint::tsc::SCRIPT[start..]
            .find("\n};\n")
            .expect("the lookup ends")
        + "\n};\n".len();

    format!(
        "{}{PRE_INDEX_LOOKUP}{}",
        &olint::tsc::SCRIPT[..start],
        &olint::tsc::SCRIPT[end..]
    )
}

fn answers_of_script(script: &str, tsconfig: &Path, queries: &[Query]) -> serde_json::Value {
    let request = serde_json::json!({"version": 2, "tsconfig": tsconfig, "queries": queries});
    let output = helper_output_of(script, &request);

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    serde_json::from_slice::<serde_json::Value>(&output.stdout).expect("reply")["answers"].clone()
}

const INDEXED_LINES: [&str; 17] = [
    "/* caf\u{e9} \u{1f600} */",
    "class Engine {",
    "\trun(xs: number[]): number[] {",
    "\t\treturn /* inner */ (xs as number[]).map((x) => x + 1);",
    "\t}",
    "}",
    "type Pair = [number, ...string[]];",
    "const table = { engine: new Engine(), pair: [1, \"a\"] as Pair };",
    "function make(): number[] {",
    "\treturn [1];",
    "}",
    "export function probe(xs: number[]) {",
    "\t// \u{e9}\u{e9} comment",
    "\ttable.engine.run(xs)!.length;",
    "\tfor (const item of table.pair) void item;",
    "}",
    "make()",
];

#[test]
fn indexed_lookups_answer_every_span_like_the_pre_index_search() {
    let reference = script_of_pre_index_lookup();

    for (prefix, line_ending) in [("", "\n"), ("\u{feff}", "\r\n")] {
        let source = format!("{prefix}{}", INDEXED_LINES.join(line_ending));
        let (directory, tsconfig, path) = strict_project_of(&source);
        let allocator = Allocator::default();
        let project = Project::load(&allocator, &tsconfig).expect("project loads");
        let file = file_of(&project, directory.path(), "index.ts");
        let mut spans: Vec<(u32, u32)> = project
            .file(file)
            .semantic
            .nodes()
            .iter()
            .map(|node| oxc_span::GetSpan::span(&node.kind()))
            .flat_map(|span| [(span.start, span.end), (span.start, span.end + 1)])
            .collect();

        spans.sort();
        spans.dedup();

        let queries: Vec<Query> = spans
            .iter()
            .flat_map(|(pos, end)| {
                [
                    Query::Type {
                        file: path.clone(),
                        pos: *pos,
                        end: *end,
                    },
                    Query::Callee {
                        file: path.clone(),
                        pos: *pos,
                        end: *end,
                    },
                ]
            })
            .collect();
        let indexed = answers_of_script(olint::tsc::SCRIPT, &tsconfig, &queries);

        assert_eq!(
            indexed,
            answers_of_script(&reference, &tsconfig, &queries),
            "{line_ending:?}"
        );

        let answered = indexed
            .as_array()
            .expect("answers")
            .iter()
            .filter(|answer| !answer.is_null())
            .count();

        assert!(
            answered * 5 > queries.len(),
            "{answered} of {}",
            queries.len()
        );

        let start = source.rfind("make()").expect("the final statement") as u32;
        let end = start + "make()".len() as u32;
        let reply = reply_of(
            &tsconfig,
            &[Query::Type {
                file: path,
                pos: start,
                end,
            }],
        );

        assert!(matches!(
            reply.answers[0],
            Some(TscAnswer::Type(TypeAnswer {
                kind: Kind::Array,
                ..
            }))
        ));
    }
}

#[test]
fn counts_appear_only_when_requested_and_are_validated() {
    let counted = r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[],"counts":{"programs":0,"checkers":0,"indexedFiles":0,"indexedNodes":0,"lookups":0,"visitedNodes":0}}"#;
    let plain = r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[]}"#;

    assert_eq!(
        olint::tsc::parse_counted_reply(counted.as_bytes(), &[])
            .expect("requested counts parse")
            .1,
        olint::tsc::TscCounts::default()
    );
    assert!(parse_reply(plain.as_bytes(), &[]).is_ok());

    for (reply, counted) in [
        (counted, false),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[],"counts":null}"#,
            false,
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[],"counts":null}"#,
            true,
        ),
        (plain, true),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[],"counts":{"lookups":0}}"#,
            true,
        ),
        (
            r#"{"version":2,"typescript":"5.9.3","from":"typescript.js","answers":[],"counts":{"programs":0,"checkers":0,"indexedFiles":0,"indexedNodes":0,"lookups":0,"visitedNodes":0,"visits":0}}"#,
            true,
        ),
    ] {
        let result = if counted {
            olint::tsc::parse_counted_reply(reply.as_bytes(), &[]).map(|(reply, _)| reply)
        } else {
            parse_reply(reply.as_bytes(), &[])
        };

        assert!(
            matches!(result, Err(TscError::Malformed(_))),
            "{reply}: {result:?}"
        );
    }

    let directory = project_of(&[("tsconfig.json", "{}"), ("index.ts", "export {};")]);
    let request = serde_json::json!({"version": 2, "tsconfig": directory.path().join("tsconfig.json"), "queries": [], "counts": "yes"});
    let output = helper_output_of(olint::tsc::SCRIPT, &request);

    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("counts request"));
}

fn helper_output_of(script: &str, request: &serde_json::Value) -> std::process::Output {
    let mut child = std::process::Command::new("node")
        .args(["--input-type=module", "--eval", script])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("node runs the static helper");

    std::io::Write::write_all(
        &mut child.stdin.take().expect("stdin"),
        request.to_string().as_bytes(),
    )
    .expect("request is written");

    child.wait_with_output().expect("helper exits")
}

fn strict_project_of(source: &str) -> (tempfile::TempDir, std::path::PathBuf, String) {
    let directory = project_of(&[
        (
            "tsconfig.json",
            r#"{"compilerOptions":{"strict":true,"noEmit":true},"files":["index.ts"]}"#,
        ),
        ("index.ts", source),
    ]);
    let tsconfig = directory.path().join("tsconfig.json");
    let path = directory
        .path()
        .join("index.ts")
        .to_string_lossy()
        .into_owned();

    (directory, tsconfig, path)
}

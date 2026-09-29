use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;

use super::*;

/// The Lean module `lake build` elaborates the encodings of `ENCODED` in.
const MODULE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/proofs/Olint/Tests/Encoded.lean"
);

/// The node ids of the top-level functions, in source order.
fn top_level(program: &oxc_ast::ast::Program<'_>) -> Vec<NodeId> {
    let mut nodes = Vec::new();

    for statement in &program.body {
        match statement {
            Statement::FunctionDeclaration(function) => nodes.push(function.node_id()),
            Statement::VariableDeclaration(declaration) => {
                let init = declaration.declarations[0].init.as_ref();

                match init.map(unwrap) {
                    Some(Expression::FunctionExpression(function)) => {
                        nodes.push(function.node_id())
                    }
                    Some(Expression::ArrowFunctionExpression(arrow)) => nodes.push(arrow.node_id()),
                    _ => {}
                }
            }
            _ => {}
        }
    }

    nodes
}

/// Encodes the first top-level function citing every other one.
fn encode(source: &str, dimensions: &[Dimension]) -> Result<Encoding, EncodeError> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::ts()).parse();

    assert!(
        parsed.diagnostics.is_empty(),
        "{source}: {:?}",
        parsed.diagnostics
    );

    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;
    let functions = top_level(&parsed.program)
        .into_iter()
        .map(|node| FunctionRef {
            semantic: &semantic,
            node,
        })
        .collect::<Vec<_>>();

    encode_scope(functions[0], &functions[1..], dimensions)
}

fn encoded(source: &str) -> Encoding {
    encode(source, &[]).unwrap_or_else(|error| panic!("{source}: {error}"))
}

/// The encoded statement list of `function f() { <statements> }`.
fn statements(statements: &str) -> String {
    let node = encoded(&format!("function f() {{ {statements} }}")).node;

    node.strip_prefix("⟨⟨.mk [] ")
        .and_then(|rest| rest.strip_suffix(" false, [], []⟩, .entry⟩"))
        .unwrap_or_else(|| panic!("{node}"))
        .to_string()
}

fn statement(source: &str) -> String {
    let list = statements(source);

    list.strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .unwrap_or_else(|| panic!("{list}"))
        .to_string()
}

/// The encoding of `return (<expression>);`'s argument.
fn expression(source: &str) -> String {
    let returned = statement(&format!("return ({source});"));

    returned
        .strip_prefix(".ret (some (")
        .and_then(|rest| rest.strip_suffix("))"))
        .unwrap_or_else(|| panic!("{returned}"))
        .to_string()
}

/// The encoded type of `function f(x: <ty>) {}`'s parameter.
fn ty(source: &str) -> String {
    let node = encoded(&format!("function f(x: {source}) {{}}")).node;

    node.strip_prefix("⟨⟨.mk [(\"x\", ")
        .and_then(|rest| rest.strip_suffix(")] [] false, [], []⟩, .entry⟩"))
        .unwrap_or_else(|| panic!("{node}"))
        .to_string()
}

fn unsupported(source: &str) -> (AstType, Option<&'static str>) {
    match encode(source, &[]) {
        Err(EncodeError::Unsupported { kind, detail, .. }) => (kind, detail),
        other => panic!("{source}: {other:?}"),
    }
}

#[test]
fn literals() {
    assert_eq!(expression("true"), ".lit (.bool true)");
    assert_eq!(expression("false"), ".lit (.bool false)");
    assert_eq!(expression("null"), ".lit .null");
    assert_eq!(expression("42"), ".lit (.num 42)");
    assert_eq!(expression("1e3"), ".lit (.num 1000)");
    assert_eq!(expression("0"), ".lit (.num 0)");
    assert_eq!(expression("1.5"), ".lit (.num (.fin false 3 (-1)))");
    assert_eq!(
        expression("0.1"),
        ".lit (.num (.fin false 3602879701896397 (-55)))"
    );
    assert_eq!(
        expression("9007199254740993"),
        ".lit (.num 9007199254740992)"
    );
    assert_eq!(
        expression("18014398509481984"),
        ".lit (.num (.fin false 1 54))"
    );
    assert_eq!(expression("5e-324"), ".lit (.num (.fin false 1 (-1074)))");
    assert_eq!(expression("1e999"), ".lit (.num (.inf false))");
    assert_eq!(expression(r#""a\"b""#), r#".lit (.str "a\"b")"#);
    assert_eq!(expression("undefined"), ".lit .undefined");
}

#[test]
fn a_bound_undefined_is_an_identifier() {
    assert_eq!(
        encoded("function f(undefined: number) { return undefined; }").node,
        r#"⟨⟨.mk [("undefined", .number)] [.ret (some (.ident "undefined"))] false, [], []⟩, .entry⟩"#
    );
}

#[test]
fn identifiers_this_and_unary() {
    assert_eq!(expression("x"), r#".ident "x""#);
    assert_eq!(expression("this"), ".«this»");
    assert_eq!(expression("!x"), r#".unary .not (.ident "x")"#);
    assert_eq!(expression("-1"), ".unary .neg (.lit (.num 1))");
    assert_eq!(expression("typeof x"), r#".unary .typeof (.ident "x")"#);
    assert_eq!(expression("~x"), r#".unary .bitNot (.ident "x")"#);
}

#[test]
fn binary_and_logical_operators() {
    for (operator, name) in [
        ("+", "add"),
        ("-", "sub"),
        ("*", "mul"),
        ("/", "div"),
        ("%", "mod"),
        ("<", "lt"),
        ("<=", "le"),
        (">", "gt"),
        (">=", "ge"),
        ("===", "strictEq"),
        ("!==", "strictNe"),
        ("&", "band"),
        ("|", "bor"),
        ("^", "bxor"),
        ("<<", "shl"),
        (">>", "shr"),
        (">>>", "ushr"),
        ("&&", "and"),
        ("||", "or"),
        ("??", "nullish"),
    ] {
        assert_eq!(
            expression(&format!("a {operator} b")),
            format!(r#".binary .{name} (.ident "a") (.ident "b")"#)
        );
    }
}

#[test]
fn conditional_and_assignments() {
    assert_eq!(
        expression("c ? 1 : 2"),
        r#".cond (.ident "c") (.lit (.num 1)) (.lit (.num 2))"#
    );
    assert_eq!(expression("x = 1"), r#".assign "x" (.lit (.num 1))"#);
    assert_eq!(
        expression("o.p = 1"),
        r#".assignIndex (.ident "o") (.lit (.str "p")) (.lit (.num 1))"#
    );
    assert_eq!(
        expression("o[k] = 1"),
        r#".assignIndex (.ident "o") (.ident "k") (.lit (.num 1))"#
    );
}

#[test]
fn compound_assignments() {
    for (operator, name) in [
        ("+=", "add"),
        ("-=", "sub"),
        ("*=", "mul"),
        ("/=", "div"),
        ("%=", "mod"),
        ("&=", "band"),
        ("|=", "bor"),
        ("^=", "bxor"),
        ("<<=", "shl"),
        (">>=", "shr"),
        (">>>=", "ushr"),
        ("&&=", "and"),
        ("||=", "or"),
        ("??=", "nullish"),
    ] {
        assert_eq!(
            expression(&format!("x {operator} 1")),
            format!(r#".assignOp .{name} "x" (.lit (.num 1))"#)
        );
    }

    assert_eq!(
        expression("o.p += s"),
        r#".assignOpIndex .add (.ident "o") (.lit (.str "p")) (.ident "s")"#
    );
    assert_eq!(
        expression("o[k] ??= 2"),
        r#".assignOpIndex .nullish (.ident "o") (.ident "k") (.lit (.num 2))"#
    );
}

#[test]
fn updates() {
    assert_eq!(expression("i++"), r#".update true false "i""#);
    assert_eq!(expression("i--"), r#".update false false "i""#);
    assert_eq!(expression("++i"), r#".update true true "i""#);
    assert_eq!(expression("--i"), r#".update false true "i""#);
    assert_eq!(
        expression("o.n++"),
        r#".updateIndex true false (.ident "o") (.lit (.str "n"))"#
    );
    assert_eq!(
        expression("--xs[j]"),
        r#".updateIndex false true (.ident "xs") (.ident "j")"#
    );
}

#[test]
fn members_calls_and_new() {
    assert_eq!(expression("o.p"), r#".member (.ident "o") "p""#);
    assert_eq!(expression("o[0]"), r#".index (.ident "o") (.lit (.num 0))"#);
    assert_eq!(
        expression("g(1, x)"),
        r#".call (.ident "g") [.lit (.num 1), .ident "x"]"#
    );
    assert_eq!(
        expression("xs.push(1)"),
        r#".call (.member (.ident "xs") "push") [.lit (.num 1)]"#
    );
    assert_eq!(expression("new Map()"), r#".new (.ident "Map") []"#);
    assert_eq!(expression("(x as number[])!"), r#".ident "x""#);
}

#[test]
fn functions_and_classes() {
    assert_eq!(
        expression("function (a) { return a; }"),
        r#".func (.mk [("a", .any)] [.ret (some (.ident "a"))] false)"#
    );
    assert_eq!(
        expression("(a: number) => a"),
        r#".func (.mk [("a", .number)] [.ret (some (.ident "a"))] true)"#
    );
    assert_eq!(expression("() => {}"), ".func (.mk [] [] true)");
    assert_eq!(
        expression("class { constructor() {} m() { return this; } }"),
        r#".klass (.mk (some (.mk [] [] false)) [("m", .mk [] [.ret (some (.«this»))] false)])"#
    );
    assert_eq!(expression("class {}"), ".klass (.mk none [])");
}

#[test]
fn collections_and_regex() {
    assert_eq!(
        expression("[1, x]"),
        r#".array [.lit (.num 1), .ident "x"]"#
    );
    assert_eq!(
        expression(r#"{ a: 1, "b c": x, x }"#),
        r#".object [("a", .lit (.num 1)), ("b c", .ident "x"), ("x", .ident "x")]"#
    );
    assert_eq!(
        expression("{ m() { return 1; } }"),
        r#".object [("m", .func (.mk [] [.ret (some (.lit (.num 1)))] false))]"#
    );
    assert_eq!(expression(r"/a\d+/gi"), r#".regex "a\\d+" "gi""#);
}

#[test]
fn simple_statements() {
    assert_eq!(statement("x;"), r#".expr (.ident "x")"#);
    assert_eq!(statement("var a;"), r#".decl .var "a" (.any) none"#);
    assert_eq!(
        statement("let a = 1;"),
        r#".decl .«let» "a" (.any) (some (.lit (.num 1)))"#
    );
    assert_eq!(
        statement("const a = 1;"),
        r#".decl .«const» "a" (.any) (some (.lit (.num 1)))"#
    );
    assert_eq!(
        statement("let a: number[] = [];"),
        r#".decl .«let» "a" (.array (.number)) (some (.array []))"#
    );
    assert_eq!(statement("{ x; }"), r#".block [.expr (.ident "x")]"#);
    assert_eq!(statement(";"), ".block []");
    assert_eq!(statement("return;"), ".ret none");
    assert_eq!(statements(""), "[]");
}

#[test]
fn branches() {
    assert_eq!(
        statement("if (c) x;"),
        r#".ite (.ident "c") (.expr (.ident "x")) none"#
    );
    assert_eq!(
        statement("if (c) x; else y;"),
        r#".ite (.ident "c") (.expr (.ident "x")) (some (.expr (.ident "y")))"#
    );
}

#[test]
fn loops() {
    assert_eq!(
        statement("for (let i = 0; i < n; i = i + 1) break;"),
        concat!(
            r#".forLoop (some (.decl .«let» "i" (.any) (some (.lit (.num 0))))) "#,
            r#"(some (.binary .lt (.ident "i") (.ident "n"))) "#,
            r#"(some (.assign "i" (.binary .add (.ident "i") (.lit (.num 1))))) (.brk)"#
        )
    );
    assert_eq!(
        statement("for (i = 0; ; ) continue;"),
        r#".forLoop (some (.expr (.assign "i" (.lit (.num 0))))) none none (.cont)"#
    );
    assert_eq!(
        statement("for (;;) {}"),
        ".forLoop none none none (.block [])"
    );
    assert_eq!(
        statement("for (const x of xs) x;"),
        r#".forOf "x" (.ident "xs") (.expr (.ident "x"))"#
    );
    assert_eq!(
        statement("for (let k in o) k;"),
        r#".forIn "k" (.ident "o") (.expr (.ident "k"))"#
    );
    assert_eq!(
        statement("while (c) x;"),
        r#".«while» (.ident "c") (.expr (.ident "x"))"#
    );
    assert_eq!(
        statement("do x; while (c);"),
        r#".doWhile (.expr (.ident "x")) (.ident "c")"#
    );
}

#[test]
fn declarations() {
    assert_eq!(
        statement("function g(a: string) { return a; }"),
        r#".funDecl "g" (.mk [("a", .string)] [.ret (some (.ident "a"))] false)"#
    );
    assert_eq!(
        statement("class C { m() {} }"),
        r#".classDecl "C" (.mk none [("m", .mk [] [] false)])"#
    );
}

#[test]
fn types() {
    for (source, expected) in [
        ("any", ".any"),
        ("unknown", ".any"),
        ("undefined", ".undefined"),
        ("null", ".null"),
        ("boolean", ".boolean"),
        ("number", ".number"),
        ("string", ".string"),
        ("number[]", ".array (.number)"),
        ("Array<string>", ".array (.string)"),
        ("Set<number>", ".set (.number)"),
        ("Map<string, number[]>", ".map (.string) (.array (.number))"),
        (
            r#"{ a: number; "b": string[] }"#,
            r#".object [("a", .number), ("b", .array (.string))]"#,
        ),
        ("(a: number) => void", ".func"),
        ("(number)", ".number"),
    ] {
        assert_eq!(ty(source), expected, "{source}");
    }
}

#[test]
fn programs_hold_named_scope_functions_sorted_by_name() {
    let encoding = encode(
        "function main(xs: number[]) { return b(xs) + a(xs); }\nconst b = (xs: number[]) => xs.length;\nfunction a(xs: number[]) { return 0; }",
        &[
            Dimension {
                id: 7,
                measure: Measure::Var("ys".into()),
            },
            Dimension {
                id: 3,
                measure: Measure::Arg(0),
            },
        ],
    )
    .unwrap();

    assert_eq!(
        encoding.program,
        concat!(
            r#"⟨[("a", .mk [("xs", .array (.number))] [.ret (some (.lit (.num 0)))] false), "#,
            r#"("b", .mk [("xs", .array (.number))] [.ret (some (.member (.ident "xs") "length"))] true), "#,
            r#"("main", .mk [("xs", .array (.number))] [.ret (some (.binary .add "#,
            r#"(.call (.ident "b") [.ident "xs"]) (.call (.ident "a") [.ident "xs"])))] false)]⟩"#
        )
    );
    assert!(encoding
        .node
        .ends_with(r#", [], [(3, .arg 0), (7, .var "ys")]⟩, .entry⟩"#));
}

#[test]
fn anonymous_entries_define_nothing_and_scope_errors_are_typed() {
    assert!(matches!(
        encode("function f() {}\nfunction f() {}", &[]),
        Err(EncodeError::DuplicateName { name }) if name == "f"
    ));

    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, "g(() => 1);", SourceType::ts()).parse();
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .build(&parsed.program)
        .semantic;
    let arrow = semantic
        .nodes()
        .iter()
        .find(|node| matches!(node.kind(), AstKind::ArrowFunctionExpression(_)))
        .unwrap()
        .id();
    let statement = parsed.program.body[0].node_id();
    let arrow = FunctionRef {
        semantic: &semantic,
        node: arrow,
    };
    let statement = FunctionRef {
        semantic: &semantic,
        node: statement,
    };

    assert_eq!(encode_scope(arrow, &[], &[]).unwrap().program, "⟨[]⟩");
    assert!(matches!(
        encode_scope(arrow, &[arrow], &[]),
        Err(EncodeError::Anonymous { .. })
    ));
    assert!(matches!(
        encode_scope(statement, &[], &[]),
        Err(EncodeError::NotAFunction {
            kind: AstType::ExpressionStatement,
            ..
        })
    ));
}

#[test]
fn constructs_outside_the_model_name_their_kind() {
    for (source, kind, detail) in [
        (
            "function f() { a == b; }",
            AstType::BinaryExpression,
            Some("=="),
        ),
        (
            "function f() { a ** b; }",
            AstType::BinaryExpression,
            Some("**"),
        ),
        (
            "function f() { x **= 1; }",
            AstType::AssignmentExpression,
            Some("**="),
        ),
        (
            "function f() { (x as number)++; }",
            AstType::TSAsExpression,
            None,
        ),
        (
            "function f() { void 0; }",
            AstType::UnaryExpression,
            Some("void"),
        ),
        ("function f() { a, b; }", AstType::SequenceExpression, None),
        ("function f() { `t`; }", AstType::TemplateLiteral, None),
        ("function f() { +x; }", AstType::UnaryExpression, Some("+")),
        ("function f() { o?.p; }", AstType::ChainExpression, None),
        ("function f() { g(...xs); }", AstType::SpreadElement, None),
        ("function f() { [, 1]; }", AstType::Elision, None),
        ("function f() { ({ ...o }); }", AstType::SpreadElement, None),
        (
            "function f() { ({ [k]: 1 }); }",
            AstType::ObjectProperty,
            Some("key"),
        ),
        (
            "function f() { ({ get p() { return 1; } }); }",
            AstType::ObjectProperty,
            Some("accessor"),
        ),
        (
            "function f() { [a] = xs; }",
            AstType::ArrayAssignmentTarget,
            None,
        ),
        (
            "function f() { switch (x) {} }",
            AstType::SwitchStatement,
            None,
        ),
        ("function f() { throw x; }", AstType::ThrowStatement, None),
        (
            "function f() { l: for (;;) break l; }",
            AstType::LabeledStatement,
            None,
        ),
        (
            "function f() { let a = 1, b = 2; }",
            AstType::VariableDeclaration,
            Some("several declarators"),
        ),
        (
            "function f() { let [a] = xs; }",
            AstType::ArrayPattern,
            None,
        ),
        (
            "function f() { for (var x of xs) {} }",
            AstType::VariableDeclaration,
            Some("binding"),
        ),
        (
            "function f() { for (x of xs) {} }",
            AstType::ForOfStatement,
            Some("assignment target"),
        ),
        ("async function f() {}", AstType::Function, Some("async")),
        ("function* f() {}", AstType::Function, Some("generator")),
        ("function f() { 'use strict'; }", AstType::Directive, None),
        ("function f(...xs) {}", AstType::BindingRestElement, None),
        (
            "function f(x = 1) {}",
            AstType::FormalParameter,
            Some("initializer"),
        ),
        (
            "function f(x?: number) {}",
            AstType::FormalParameter,
            Some("optional"),
        ),
        ("function f({ a }) {}", AstType::ObjectPattern, None),
        (
            "function f(x: number | string) {}",
            AstType::TSUnionType,
            None,
        ),
        (
            "function f(x: readonly number[]) {}",
            AstType::TSTypeOperator,
            None,
        ),
        (
            "function f(x: Record<string, number>) {}",
            AstType::TSTypeReference,
            Some("type reference"),
        ),
        (
            "type Map<K, V> = K; function f(x: Map<number, number>) {}",
            AstType::TSTypeReference,
            Some("local type"),
        ),
        (
            "function f(x: { a?: number }) {}",
            AstType::TSPropertySignature,
            Some("property"),
        ),
        (
            "function f(x: { (): void }) {}",
            AstType::TSCallSignatureDeclaration,
            None,
        ),
        (
            "function f() { class A extends B {} }",
            AstType::Class,
            Some("extends"),
        ),
        (
            "function f() { class A { x = 1; } }",
            AstType::PropertyDefinition,
            None,
        ),
        (
            "function f() { class A { get p() { return 1; } } }",
            AstType::MethodDefinition,
            Some("get"),
        ),
        (
            "function f() { class A { static m() {} } }",
            AstType::MethodDefinition,
            Some("static"),
        ),
    ] {
        assert_eq!(unsupported(source), (kind, detail), "{source}");
    }
}

#[test]
fn lean_strings_escape_quotes_backslashes_and_controls() {
    assert_eq!(string("a\"\\\n\t\r\u{1}é"), r#""a\"\\\n\t\r\u0001é""#);
}

/// Scopes whose encodings `lake build` elaborates in `proofs/Olint/Tests/Encoded.lean`.
const ENCODED: &[(&str, &[(u64, usize)])] = &[
    (
        "function sum(xs: number[]) { let total = 0; for (const x of xs) { total = total + x; } return total; }",
        &[(0, 0)],
    ),
    (
        "function count(n: number) { let i = 0; while (i < n) { i = i + 1; } do { i = i - 1; } while (i > 0); for (let j = 0; j < n; j = j + 1) { if (j % 2 === 0) continue; else break; } return i; }",
        &[],
    ),
    (
        "function dedupe(xs: string[]) { const seen = new Set(); const out: string[] = []; for (const x of xs) { if (!seen.has(x)) { seen.add(x); out.push(x); } } return out; }",
        &[(0, 0)],
    ),
    (
        "function index(keys: string[], m: Map<string, number>) { for (const k in keys) { m.set(keys[k], typeof k === \"string\" ? 1 : -1); } return m.get(\"a\") ?? null; }",
        &[(0, 0), (1, 1)],
    ),
    (
        "function shapes(p: { x: number; y: number }, f: () => void) { const o = { a: p.x, b: [p.y, undefined, true] }; o.a = 2; o[\"b\"] = null; const r = /a+b/g; return o.a && f !== undefined || r; }",
        &[],
    ),
    (
        "function make(n: number) { class Counter { constructor() { this.n = 0; } bump() { this.n = this.n + 1; return this; } } const c = new Counter(); function twice(g: any) { return g(g(n)); } return twice((m: number) => m * 2); }",
        &[],
    ),
    (
        "const main = (xs: Array<number>, s: Set<string>) => helper(xs) + xs.length;\nfunction helper(ys: number[]) { return ys.indexOf(0); }",
        &[(0, 0), (1, 1)],
    ),
    (
        "function bisect(xs: number[], t: number) { let lo: number = 0; let hi = xs.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (xs[mid] < t) lo = mid + 1; else hi = mid; } let s = \"\"; for (let i = 0; i < lo; i++) { s += \"x\"; --hi; } xs[0] *= 0.5; xs[1]++; return ~lo | 1e999 & hi >>> 2 ^ s.length << 1; }",
        &[(0, 0)],
    ),
];

fn encoded_module() -> String {
    let mut module = String::from(concat!(
        "import Olint.Model.Cost\n",
        "\n",
        "/-!\n",
        "# Encoded syntax\n",
        "\n",
        "Program scopes encoded by `src/lean_syntax.rs`, so `lake build` elaborates the encoder's\n",
        "output against `Olint.Model.Syntax`.\n",
        "\n",
        "Generated by the `encoded_lean_module_is_in_sync` unit test in `src/lean_syntax.test.rs`, which\n",
        "fails when this file differs from the encoder's output. Regenerate it with\n",
        "`OLINT_BLESS=1 cargo test --locked --lib lean_syntax`.\n",
        "-/\n",
        "\n",
        "namespace Olint.Tests.Encoded\n",
        "\n",
        "open Olint.Model\n",
    ));

    for (source, dimensions) in ENCODED {
        let dimensions = dimensions
            .iter()
            .map(|&(id, k)| Dimension {
                id,
                measure: Measure::Arg(k),
            })
            .collect::<Vec<_>>();
        let encoding =
            encode(source, &dimensions).unwrap_or_else(|error| panic!("{source}: {error}"));

        module.push('\n');

        for line in source.lines() {
            module.push_str(&format!("-- {line}\n"));
        }

        module.push_str(&format!("example : Program := {}\n", encoding.program));
        module.push_str(&format!("example : Node := {}\n", encoding.node));
    }

    module.push_str("\nend Olint.Tests.Encoded\n");

    module
}

#[test]
fn encoded_lean_module_is_in_sync() {
    let expected = encoded_module();

    if std::env::var_os("OLINT_BLESS").is_some() {
        std::fs::write(MODULE, &expected).unwrap();
    }

    let actual = std::fs::read_to_string(MODULE).unwrap_or_default();

    assert!(
        actual == expected,
        "{MODULE} is stale; regenerate it with `OLINT_BLESS=1 cargo test --locked --lib lean_syntax`"
    );
}

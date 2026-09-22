use olint::analysis::{Analysis, Options, TypeMode};
use olint::declarations::FunctionNode;
use olint::directives::PerfTag;
use oxc_ast::ast::Expression;
use oxc_ast::AstKind;

mod support;

use support::{file_of, first_node_of, run_in_project};

const OPTIONS: Options = Options {
    minimum_exponent: 2,
    types: TypeMode::Syntactic,
};

fn arrow_of<'a>(initializer: Option<&'a Expression<'a>>) -> Option<FunctionNode<'a>> {
    match initializer? {
        Expression::ArrowFunctionExpression(arrow) => Some(FunctionNode::Arrow(arrow)),
        _ => None,
    }
}

#[test]
fn function_tags_climb_to_the_tagged_declaration() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "engine.ts",
            "/** @perf max O(N^3) */\nexport const exported = () => {};\nexport class Engine {\n\t// @perf O(N log N)\n\trun() {}\n\t/** @perf cold */\n\thandle = () => {};\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let mut analysis = Analysis::new(project, OPTIONS);
        let file = file_of(project, root, "engine.ts");
        let exported = first_node_of(project, file, |kind| match kind {
            AstKind::VariableDeclarator(declarator) => arrow_of(declarator.init.as_ref()),
            _ => None,
        });
        let method = first_node_of(project, file, |kind| match kind {
            AstKind::MethodDefinition(method) => Some(FunctionNode::Function(&method.value)),
            _ => None,
        });
        let property = first_node_of(project, file, |kind| match kind {
            AstKind::PropertyDefinition(property) => arrow_of(property.value.as_ref()),
            _ => None,
        });

        assert_eq!(
            analysis.function_tags(file, exported),
            vec![PerfTag::Max("O(N^3)".to_string())]
        );
        assert_eq!(
            analysis.function_tags(file, method),
            vec![PerfTag::Cost("O(N log N)".to_string())]
        );
        assert_eq!(analysis.function_tags(file, property), vec![PerfTag::Cold]);
    });
}

#[test]
fn perf_tags_belong_to_the_outermost_node_at_a_position() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "loop.ts",
            "export function walk(items: number[]) {\n\t// @perf bounded\n\tfor (const item of items) {\n\t\t// @perf hot\n\t\titems.sort();\n\t}\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let mut analysis = Analysis::new(project, OPTIONS);
        let file = file_of(project, root, "loop.ts");
        let pick = |wanted: fn(&AstKind<'_>) -> bool| {
            first_node_of(project, file, move |kind| wanted(&kind).then_some(kind))
        };
        let loop_statement = pick(|kind| matches!(kind, AstKind::ForOfStatement(_)));
        let statement = pick(|kind| matches!(kind, AstKind::ExpressionStatement(_)));
        let call = pick(|kind| matches!(kind, AstKind::CallExpression(_)));
        let body = pick(|kind| matches!(kind, AstKind::BlockStatement(_)));

        assert_eq!(analysis.perf_tags(file, loop_statement), [PerfTag::Bounded]);
        assert_eq!(analysis.perf_tags(file, statement), [PerfTag::Hot]);
        assert!(analysis.perf_tags(file, call).is_empty());
        assert!(analysis.perf_tags(file, body).is_empty());
    });
}

#[test]
fn comments_before_the_first_line_break_are_not_leading() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "same.ts",
            "export function s(xs: number[], k: number) {\n\tswitch (k) {\n\t\tcase 0: // @perf hot\n\t\t\txs.sort();\n\t\t\tbreak;\n\t}\n\txs.pop(); /* @perf cold */ xs.reverse();\n\tconst y = // @perf O(N)\n\t\txs.length;\n\t/* one */ // @perf bounded\n\txs.shift();\n\treturn y;\n}\n",
        ),
    ];

    run_in_project(&files, |project, root| {
        let mut analysis = Analysis::new(project, OPTIONS);
        let file = file_of(project, root, "same.ts");
        let tagged: Vec<(String, Vec<PerfTag>)> = project
            .file(file)
            .semantic
            .nodes()
            .iter()
            .map(|node| node.kind())
            .filter_map(|kind| {
                let tags = analysis.perf_tags(file, kind).to_vec();
                let text = oxc_span::GetSpan::span(&kind).source_text(project.file(file).text);

                (!tags.is_empty()).then(|| (text.to_string(), tags))
            })
            .collect();

        assert_eq!(
            tagged,
            vec![("xs.shift();".to_string(), vec![PerfTag::Bounded])]
        );
    });
}

#[test]
fn a_mark_follows_retained_completion_work_to_the_channel_that_carries_it() {
    let quadratic = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) total += a + b;\n\treturn total;\n}\n";
    let caught = |mark: &str| {
        format!(
            "{quadratic}export function f(xs: number[]) {{\n\tlet total = 0;\n\tfor (const x of xs) {{\n\t\t{mark}try {{\n\t\t\tthrow quadratic(xs);\n\t\t}} catch (error) {{\n\t\t\ttotal += 1;\n\t\t}}\n\t\ttotal += xs.length;\n\t}}\n\treturn total;\n}}"
        )
    };
    let cost_of = |source: String| {
        let mut found = olint::cost::Cost::ONE;

        support::run_with_source(&source, |analysis, file| {
            let function = support::function_of_name(analysis.project, file, "f");
            let reading = support::legacy_reading_of(analysis, file, function);
            let part = reading.total(&mut analysis.unknowns, &mut analysis.traces);

            found = part.cost;
        });

        found
    };

    assert_eq!(
        cost_of(caught("")),
        olint::cost::Cost::parse("O(N^3)").unwrap()
    );
    assert_eq!(cost_of(caught("// @perf cold\n\t\t")), olint::cost::Cost::N);
}

const HELPERS: &str = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) for (const y of xs) total += x + y;\n\treturn total;\n}\n// @perf cold\nfunction coldQuadratic(xs: number[]) {\n\treturn quadratic(xs);\n}\n/** @perf hot */\nfunction hotQuadratic(xs: number[]) {\n\treturn quadratic(xs);\n}\nclass Cold {\n\t// @perf cold\n\tconstructor(xs: number[]) {\n\t\tquadratic(xs);\n\t}\n}\n";

fn selected_result_of(body: &str) -> support::SelectedResult {
    selected_result_with(HELPERS, body)
}

fn selected_result_with(prefix: &str, body: &str) -> support::SelectedResult {
    let source = format!("{prefix}export function selected{body}");

    support::selected_result_in(&[("index.ts", &source)], TypeMode::Syntactic)
}

#[test]
fn an_absent_completion_channel_keeps_the_only_cold_contribution() {
    let quadratic = olint::cost::Cost::parse("O(N^2)").unwrap();

    for body in [
        "(xs: number[]) {\n\tfor (const x of xs) {\n\t\treturn coldQuadratic(xs);\n\t}\n}",
        "(xs: number[]) {\n\tfor (const x of xs) {\n\t\tthrow coldQuadratic(xs);\n\t}\n}",
        "(xs: number[]) {\n\treturn coldQuadratic(xs);\n}",
    ] {
        assert_eq!(selected_result_of(body).0, quadratic, "{body}");
    }
}

#[test]
fn executed_constant_statements_still_outrank_a_cold_contribution() {
    for (body, expected) in [
        (
            "(xs: number[]) {\n\tfor (const x of xs) {\n\t\tcoldQuadratic(xs);\n\t}\n}",
            "O(N^3)",
        ),
        (
            "(xs: number[]) {\n\tfor (const x of xs) {\n\t\tconst y = x + 1;\n\n\t\tif (y > 0) {\n\t\t\treturn coldQuadratic(xs);\n\t\t}\n\t}\n}",
            "O(N)",
        ),
        (
            "(xs: number[]) {\n\tfor (const x of xs) {\n\t\treturn coldQuadratic(xs);\n\t}\n\n\treturn 0;\n}",
            "O(1)",
        ),
        ("(xs: number[]) {\n\tfor (const x of xs) {\n\t}\n}", "O(N)"),
    ] {
        assert_eq!(
            selected_result_of(body).0,
            olint::cost::Cost::parse(expected).unwrap(),
            "{body}"
        );
    }
}

#[test]
fn an_open_call_target_stays_partial_beside_every_known_mark() {
    use olint::unknowns::UnknownReason;

    for (body, expected) in [
        (
            "(xs: number[], flag: boolean, f: (xs: number[]) => number) {\n\tconst g = flag ? coldQuadratic : f;\n\n\treturn g(xs);\n}",
            "O(1)",
        ),
        (
            "(xs: number[], flag: boolean, k: new (xs: number[]) => object) {\n\tconst c = flag ? Cold : k;\n\n\treturn new c(xs);\n}",
            "O(1)",
        ),
        (
            "(xs: number[], flag: boolean, f: (xs: number[]) => number) {\n\tconst g = flag ? quadratic : f;\n\n\treturn g(xs);\n}",
            "O(N^2)",
        ),
        (
            "(xs: number[], flag: boolean, f: (xs: number[]) => number) {\n\tconst g = flag ? hotQuadratic : f;\n\n\treturn g(xs);\n}",
            "O(N^2)",
        ),
    ] {
        let (cost, reasons) = selected_result_of(body);

        assert_eq!(cost, olint::cost::Cost::parse(expected).unwrap(), "{body}");
        assert!(reasons.contains(&UnknownReason::Target), "{body} {reasons:?}");
    }
}

const ENGINE: &str = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) for (const y of xs) total += x + y;\n\treturn total;\n}\nclass Engine {\n\t// @perf cold\n\trebuild(xs: number[]) {\n\t\treturn quadratic(xs);\n\t}\n}\n";

const HOLDERS: &str = "function quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) for (const y of xs) total += x + y;\n\treturn total;\n}\nclass Holder {\n\txs: number[] = [];\n\n\t// @perf cold\n\tget value() {\n\t\treturn quadratic(this.xs);\n\t}\n}\n";

#[test]
fn an_open_target_marks_a_known_cold_contribution_without_cancelling_it() {
    use olint::unknowns::UnknownReason;

    for (prefix, body, expected) in [
        (
            ENGINE,
            "(xs: number[]) {\n\treturn new Engine().rebuild(xs);\n}",
            "O(N^2)",
        ),
        (
            HELPERS,
            "(xs: number[], flag: boolean, base: any) {\n\tclass Derived extends (flag ? Cold : base) {}\n\n\treturn new Derived(xs);\n}",
            "O(N^2)",
        ),
        (
            HOLDERS,
            "(flag: boolean, other: { value: number }) {\n\tconst holder = flag ? new Holder() : other;\n\n\treturn holder.value;\n}",
            "O(1)",
        ),
    ] {
        let (cost, reasons) = selected_result_with(prefix, body);

        assert_eq!(cost, olint::cost::Cost::parse(expected).unwrap(), "{body}");
        assert!(reasons.contains(&UnknownReason::Target), "{body} {reasons:?}");
    }
}

const OPEN_BASE: &str = "declare const OpenBase: new () => object;\ndeclare function opaque(): number;\nfunction quadratic(xs: number[]) {\n\tlet total = 0;\n\tfor (const x of xs) for (const y of xs) total += x + y;\n\treturn total;\n}\n// @perf cold\nfunction coldQuadratic(xs: number[]) {\n\treturn quadratic(xs);\n}\nclass Empty {}\nclass ClosedChild extends Empty {}\nclass OpenChild extends OpenBase {}\nclass ExplicitChild extends OpenBase {\n\tconstructor() {\n\t\tsuper();\n\t}\n}\nclass MixedOpenChild extends OpenBase {\n\tv = opaque();\n}\nclass MixedClosedChild extends Empty {\n\tv = opaque();\n}\ndeclare const data: number[];\nfunction knownLinear() {\n\tlet total = 0;\n\tfor (const item of data) total += item;\n\treturn total;\n}\nclass KnownClosedChild extends Empty {\n\tv = knownLinear();\n}\n";

#[test]
fn an_unresolved_construction_never_manufactures_a_competing_statement() {
    use olint::unknowns::UnknownReason;

    for (body, selected, partial) in [
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new ClosedChild()];\n}",
            "O(N^2)",
            false,
        ),
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new OpenChild()];\n}",
            "O(N^2)",
            true,
        ),
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new ExplicitChild()];\n}",
            "O(N^2)",
            true,
        ),
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new MixedOpenChild()];\n}",
            "O(N^2)",
            true,
        ),
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new MixedClosedChild()];\n}",
            "O(N^2)",
            true,
        ),
        (
            "(xs: number[]) {\n\treturn [coldQuadratic(xs), new KnownClosedChild()];\n}",
            "O(N)",
            false,
        ),
    ] {
        let (cost, reasons) = selected_result_with(OPEN_BASE, body);

        assert_eq!(
            cost,
            olint::cost::Cost::parse(selected).unwrap(),
            "{body} {reasons:?}"
        );
        assert_eq!(
            reasons.contains(&UnknownReason::Target),
            partial,
            "{body} {reasons:?}"
        );
    }
}

#[test]
fn an_absent_completion_channel_stays_absent_through_every_enclosing_loop() {
    let quadratic = olint::cost::Cost::parse("O(N^2)").unwrap();

    for body in [
        "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const x of xs) {\n\t\t\treturn coldQuadratic(xs);\n\t\t}\n\t}\n}",
        "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const b of xs) {\n\t\t\tfor (const x of xs) {\n\t\t\t\treturn coldQuadratic(xs);\n\t\t\t}\n\t\t}\n\t}\n}",
        "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const x of xs) {\n\t\t\tthrow coldQuadratic(xs);\n\t\t}\n\t}\n}",
    ] {
        assert_eq!(selected_result_of(body).0, quadratic, "{body}");
    }
}

#[test]
fn nested_loops_around_an_executed_body_still_charge_their_iterations() {
    for (body, expected) in [
        (
            "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const b of xs) {\n\t\t}\n\t}\n}",
            "O(N^2)",
        ),
        (
            "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const b of xs) {\n\t\t\tfor (const c of xs) {\n\t\t\t}\n\t\t}\n\t}\n}",
            "O(N^3)",
        ),
        (
            "(xs: number[]) {\n\tfor (const a of xs) {\n\t\tfor (const x of xs) {\n\t\t\treturn coldQuadratic(xs);\n\t\t}\n\t}\n\n\treturn 0;\n}",
            "O(1)",
        ),
    ] {
        assert_eq!(
            selected_result_of(body).0,
            olint::cost::Cost::parse(expected).unwrap(),
            "{body}"
        );
    }
}

const COLD_CUBE: &str = "/** @perf cold */\nfunction coldCube(xs: number[]) {\n\tlet total = 0;\n\tfor (const a of xs) for (const b of xs) for (const c of xs) total += a + b + c;\n\treturn total;\n}\nfunction knownConstant(xs: number[]) {\n\treturn xs.length > 0 ? 1 : 0;\n}\n";

#[test]
fn an_unresolved_target_retains_a_proved_cold_cost_as_a_partial_result() {
    use olint::unknowns::UnknownReason;

    for (body, expected, unknown) in [
        ("(xs: number[]) {\n\treturn coldCube(xs);\n}", "O(N^3)", None),
        (
            "(xs: number[]) {\n\treturn coldCube(xs) + knownConstant(xs);\n}",
            "O(N^3)",
            None,
        ),
        (
            "(xs: number[], cb: (v: number[]) => number) {\n\treturn coldCube(xs) + cb(xs);\n}",
            "O(N^3)",
            Some(UnknownReason::Target),
        ),
        (
            "(xs: number[], o: unknown) {\n\treturn coldCube(xs) + (o as { f(v: number[]): number }).f(xs);\n}",
            "O(N^3)",
            Some(UnknownReason::UnsupportedModel),
        ),
    ] {
        let (cost, reasons) = selected_result_with(COLD_CUBE, body);

        assert_eq!(
            cost,
            olint::cost::Cost::parse(expected).unwrap(),
            "{body} {reasons:?}"
        );
        assert_eq!(reasons, unknown.into_iter().collect(), "{body}");
    }
}

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

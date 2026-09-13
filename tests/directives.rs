use olint::analysis::{Analysis, Options, TypeMode};
use olint::declarations::FunctionNode;
use olint::directives::PerfTag;
use oxc_ast::ast::Expression;
use oxc_ast::AstKind;

mod support;

use support::{file_of, first_node_of, run_in_project};

const OPTIONS: Options = Options {
    strings_linear: true,
    callbacks: true,
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
        assert!(analysis.is_hot_path(file, body));
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

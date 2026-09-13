use olint::declarations::{Declaration, Declarations, FunctionNode};
use oxc_ast::ast::PropertyKey;

mod support;

use support::{file_of, member_callee_of, run_in_project};

fn described(declarations: &Declarations<'_>, declaration: Option<Declaration<'_>>) -> String {
    let Some(declaration) = declaration else {
        return "none".to_string();
    };
    let function = declarations
        .function_of(declaration)
        .map(|(_, function)| match function {
            FunctionNode::Function(_) => " function",
            FunctionNode::Arrow(_) => " arrow",
        })
        .unwrap_or("");

    let shape = match declaration {
        Declaration::Member { element, .. } => {
            let name = element_label_of(element);

            format!("member {name}")
        }
        Declaration::Property { property, .. } => match &property.key {
            PropertyKey::StaticIdentifier(identifier) => format!("property {}", identifier.name),
            _ => "property".to_string(),
        },
        Declaration::Function {
            function: FunctionNode::Function(function),
            ..
        } => format!(
            "function {}",
            function
                .id
                .as_ref()
                .map(|id| id.name.as_str())
                .unwrap_or("")
        ),
        Declaration::External => "external".to_string(),
        other => format!("{other:?}").chars().take(12).collect(),
    };

    format!("{shape}{function}")
}

fn element_label_of(element: &oxc_ast::ast::ClassElement<'_>) -> String {
    let (key, is_static) = match element {
        oxc_ast::ast::ClassElement::MethodDefinition(method) => (&method.key, method.r#static),
        oxc_ast::ast::ClassElement::PropertyDefinition(property) => {
            (&property.key, property.r#static)
        }
        _ => return "element".to_string(),
    };
    let name = match key {
        PropertyKey::StaticIdentifier(identifier) => identifier.name.to_string(),
        PropertyKey::PrivateIdentifier(identifier) => format!("#{}", identifier.name),
        _ => String::new(),
    };

    if is_static {
        format!("static {name}")
    } else {
        name
    }
}

fn receivers_of(files: &[(&str, &str)], callees: &[&str]) -> Vec<String> {
    let mut found = Vec::new();

    run_in_project(files, |project, root| {
        let declarations = Declarations::new(project);
        let file = file_of(project, root, "index.ts");

        found = callees
            .iter()
            .map(|callee| {
                let member = member_callee_of(project, file, callee);

                described(
                    &declarations,
                    declarations.member_of_receiver(project, file, member),
                )
            })
            .collect();
    });

    found
}

#[test]
fn class_instances_resolve_their_methods() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "class Engine {\n\trun() { return 1; }\n\tstatic run() { return 2; }\n\tstatic create() { return new Engine(); }\n}\nconst Local = class {\n\trun() {}\n\tstatic make() {}\n};\nfunction make() { return new Engine(); }\nexport function f(typed: Engine) {\n\tconst engine = new Engine();\n\tlet later = new Engine();\n\tconst local = new Local();\n\tengine.run();\n\ttyped.run();\n\tEngine.create();\n\tEngine.run();\n\tnew Engine().run();\n\tnew Local().run();\n\tlocal.run();\n\tLocal.make();\n\tlater.run();\n\tmake().run();\n}",
        ),
    ];

    assert_eq!(
        receivers_of(
            &files,
            &[
                "engine.run",
                "typed.run",
                "Engine.create",
                "Engine.run",
                "new Engine().run",
                "new Local().run",
                "local.run",
                "Local.make",
                "later.run",
                "make().run",
            ]
        ),
        vec![
            "member run function",
            "member run function",
            "member static create function",
            "member static run function",
            "member run function",
            "member run function",
            "member run function",
            "member static make function",
            "none",
            "none",
        ]
    );
}

#[test]
fn this_resolves_inside_methods_only() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "class Base {\n\tstop() {}\n}\nexport class Clock extends Base {\n\t#tick() {}\n\tstart() {\n\t\tthis.#tick();\n\t\tfunction nested(this: Clock) {\n\t\t\tthis.#tick();\n\t\t}\n\t\tthis.stop();\n\t\treturn nested;\n\t}\n}",
        ),
    ];

    run_in_project(&files, |project, root| {
        let declarations = Declarations::new(project);
        let file = file_of(project, root, "index.ts");
        let calls: Vec<String> = project
            .file(file)
            .semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                oxc_ast::AstKind::CallExpression(call) => call.callee.as_member_expression(),
                _ => None,
            })
            .map(|member| {
                described(
                    &declarations,
                    declarations.member_of_receiver(project, file, member),
                )
            })
            .collect();

        assert_eq!(
            calls,
            vec!["member #tick function", "none", "member stop function"]
        );
    });
}

#[test]
fn object_literals_and_namespaces_resolve_their_functions() {
    let files = [
        ("tsconfig.json", "{}"),
        ("lib.ts", "export function run() {}"),
        (
            "index.ts",
            "import * as library from \"./lib\";\nconst handlers = { run: () => 1, walk() { return 2; } };\nexport function f() {\n\thandlers.run();\n\thandlers.walk();\n\tlibrary.run();\n}",
        ),
    ];

    assert_eq!(
        receivers_of(&files, &["handlers.run", "handlers.walk", "library.run"]),
        vec![
            "property run arrow",
            "property walk function",
            "function run function",
        ]
    );
}

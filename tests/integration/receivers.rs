use olint::declarations::{Declaration, Declarations, FunctionNode};
use oxc_ast::ast::PropertyKey;

use crate::support;

use support::{file_of, member_callee_of, run_in_project};

fn description_of(declarations: &Declarations<'_>, declaration: Option<Declaration<'_>>) -> String {
    let Some(declaration) = declaration else {
        return "none".to_string();
    };
    let function = declarations
        .function_of(declaration)
        .map(|(_, function)| match function {
            FunctionNode::Function(_) => " function",
            FunctionNode::Arrow(_) => " arrow",
            FunctionNode::Construction(_) => " construction",
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

                description_of(
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
                description_of(
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

#[test]
fn declared_types_and_casts_hide_the_initializer() {
    let files = [
        ("tsconfig.json", "{}"),
        (
            "index.ts",
            "interface IEngine { run(): number; readonly MAX: number }\ninterface Handlers { run(): number }\ninterface Shape { m(): void }\nclass Engine implements IEngine { readonly MAX = 4; run() { return 1; } }\ntype Alias = Engine;\nexport function f(x: any) {\n\tconst a: IEngine = new Engine();\n\ta.run();\n\tconst b = new Engine() as IEngine;\n\tb.run();\n\tconst c: Handlers = { run: () => 1 };\n\tc.run();\n\tconst d = { run: () => 1 } as Handlers;\n\td.run();\n\tconst e = { run: () => 1 } satisfies Handlers;\n\te.run();\n\tconst g: Alias = new Engine();\n\tg.run();\n\tconst h = new Engine()!;\n\th.run();\n\t(x as Shape).m();\n}\nexport class Clock {\n\tm() {}\n\tn() {\n\t\t(this as any).m();\n\t}\n}",
        ),
    ];

    assert_eq!(
        receivers_of(
            &files,
            &[
                "a.run",
                "b.run",
                "c.run",
                "d.run",
                "e.run",
                "g.run",
                "h.run",
                "(x as Shape).m",
                "(this as any).m",
            ]
        ),
        vec![
            "none",
            "none",
            "none",
            "none",
            "property run arrow",
            "member run function",
            "member run function",
            "none",
            "none",
        ]
    );
}

fn label_of(
    project: &olint::project::Project<'_>,
    known: olint::declarations::FunctionId,
) -> String {
    use oxc_ast::AstKind;

    let nodes = project.file(known.file).semantic.nodes();
    let owner = |node| {
        nodes
            .ancestors(node)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::Class(class) => class.id.as_ref().map(|id| id.name.to_string()),
                _ => None,
            })
    };

    match nodes.parent_kind(known.node) {
        AstKind::MethodDefinition(method) => format!(
            "{}.{}",
            owner(known.node).unwrap_or_default(),
            method.key.static_name().unwrap_or_default()
        ),
        AstKind::ObjectProperty(property) => {
            format!("{{}}.{}", property.key.static_name().unwrap_or_default())
        }
        _ => match nodes.kind(known.node) {
            AstKind::Function(function) => function
                .id
                .as_ref()
                .map_or_else(|| "function".to_string(), |id| id.name.to_string()),
            _ => "arrow".to_string(),
        },
    }
}

fn dispatch_of(source: &str, callees: &[&str]) -> Vec<(Vec<String>, bool)> {
    let files = [("tsconfig.json", "{}"), ("index.ts", source)];
    let mut found = Vec::new();

    run_in_project(&files, |project, root| {
        let file = file_of(project, root, "index.ts");
        let mut analysis = olint::analysis::Analysis::new(project, support::SYNTACTIC);

        for callee in callees {
            let targets = analysis.callee_targets_of(file, support::call_of(project, file, callee));
            let mut labels: Vec<String> = targets
                .known
                .iter()
                .map(|known| label_of(project, *known))
                .collect();

            labels.sort();
            found.push((labels, targets.open));
        }
    });

    found
}

fn expected_of(cases: &[(&[&str], bool)]) -> Vec<(Vec<String>, bool)> {
    cases
        .iter()
        .map(|(labels, open)| {
            (
                labels.iter().map(|label| label.to_string()).collect(),
                *open,
            )
        })
        .collect()
}

#[test]
fn class_dispatch_joins_overrides_with_an_open_remainder() {
    let source = "class Base {\n\twork(xs: number[]) {}\n\tinherited() {}\n\trun(xs: number[]) { this.work(xs); }\n\tstatic make() {}\n\tstatic build() { this.make(); }\n}\nclass Derived extends Base {\n\twork(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }\n\tstatic make() {}\n}\nclass Leaf extends Derived {\n\twork(xs: number[]) {}\n}\nclass Unrelated {\n\twork(xs: number[]) {}\n}\nexport function f(x: Base, xs: number[]) {\n\tx.work(xs);\n\tnew Derived().work(xs);\n\tnew Leaf().inherited();\n\tBase.make();\n\t(x as any).work(xs);\n}";

    assert_eq!(
        dispatch_of(
            source,
            &[
                "x.work",
                "this.work",
                "new Derived().work",
                "new Leaf().inherited",
                "Base.make",
                "this.make",
                "(x as any).work",
            ]
        ),
        expected_of(&[
            (&["Base.work", "Derived.work", "Leaf.work"], true),
            (&["Base.work", "Derived.work", "Leaf.work"], true),
            (&["Derived.work"], true),
            (&["Base.inherited"], true),
            (&["Base.make"], true),
            (&["Base.make", "Derived.make"], true),
            (&["Base.work", "Derived.work", "Leaf.work"], true),
        ])
    );
}

#[test]
fn replaced_members_join_prototype_receiver_and_object_writes() {
    let source = "function expensive(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; }\nfunction fast(xs: number[]) {}\nclass Base { work(xs: number[]) {} }\nclass Holder {\n\tconstructor() { this.run = fast; }\n\trun(xs: number[]) {}\n}\n(Base.prototype as any).work = expensive;\nconst obj = { work(xs: number[]) {} };\nobj.work = expensive;\nconst assigned = { work(xs: number[]) {} };\nObject.assign(assigned, { work: fast });\nconst holder = { inner: { run: fast } };\nclass K { get g() { return expensive; } }\nexport function f(x: Base, k: K, xs: number[]) {\n\tx.work(xs);\n\tnew Holder().run(xs);\n\tobj.work(xs);\n\tassigned.work(xs);\n\tholder.inner.run(xs);\n\tk.g(xs);\n}";

    assert_eq!(
        dispatch_of(
            source,
            &[
                "x.work",
                "new Holder().run",
                "obj.work",
                "assigned.work",
                "holder.inner.run",
                "k.g",
            ]
        ),
        expected_of(&[
            (&["Base.work", "expensive"], true),
            (&["Holder.run", "fast"], true),
            (&["expensive", "{}.work"], true),
            (&["fast", "{}.work"], true),
            (&["fast"], true),
            (&["K.g", "expensive"], true),
        ])
    );
}

#[test]
fn union_receivers_join_every_returned_object_member() {
    let source = "function make(flag: boolean) {\n\treturn flag ? { work(xs: number[]) {} } : { work(xs: number[]) { for (const a of xs) for (const b of xs) for (const c of xs) void c; } };\n}\nexport function f(flag: boolean, xs: number[], loose: { work(xs: number[]): void }) {\n\tmake(flag).work(xs);\n\tloose.work(xs);\n}";

    assert_eq!(
        dispatch_of(source, &["make(flag).work", "loose.work"]),
        expected_of(&[(&["{}.work", "{}.work"], true), (&[], true)])
    );
}

#[test]
fn declared_types_keep_the_runtime_initializer_targets() {
    let source = "interface IEngine { run(xs: number[]): void }\nclass Engine implements IEngine { run(xs: number[]) { for (const a of xs) for (const b of xs) void b; } }\nclass Base { run(xs: number[]) {} }\nclass Derived extends Base { run(xs: number[]) {} }\nexport function f(xs: number[]) {\n\tconst a: IEngine = new Engine();\n\ta.run(xs);\n\tconst b: Base = new Derived();\n\tb.run(xs);\n}";

    assert_eq!(
        dispatch_of(source, &["a.run", "b.run"]),
        expected_of(&[
            (&["Engine.run"], true),
            (&["Base.run", "Derived.run"], true),
        ])
    );
}

#[test]
fn open_parameter_sources_keep_declared_runtime_alternatives() {
    let source = "class Base { work() {} } class Derived extends Base { work() {} } function local(x: Base) { x.work(); } export function surfaced(y: Base) { y.work(); local(new Base()); }";

    assert_eq!(
        dispatch_of(source, &["x.work", "y.work"]),
        expected_of(&[
            (&["Base.work"], true),
            (&["Base.work", "Derived.work"], true),
        ])
    );
}

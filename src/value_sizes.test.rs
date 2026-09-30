use super::*;

#[test]
fn shapes_join_toward_the_value_that_needs_history() {
    assert_eq!(Shape::Array.join(Shape::Array), Shape::Array);
    assert_eq!(Shape::Primitive.join(Shape::Array), Shape::Array);
    assert_eq!(Shape::Object.join(Shape::Fixed), Shape::Object);
    assert_eq!(Shape::Fixed.join(Shape::Primitive), Shape::Primitive);
    assert_eq!(Shape::Array.join(Shape::Object), Shape::Unknown);
    assert_eq!(Shape::Unknown.join(Shape::Primitive), Shape::Unknown);
}

#[test]
fn only_linear_shapes_count_their_length() {
    for (shape, linear, history, inherited) in [
        (Shape::Primitive, true, false, Kind::String),
        (Shape::Fixed, true, false, Kind::Unknown),
        (Shape::Array, true, true, Kind::Array),
        (Shape::Object, false, true, Kind::Other),
        (Shape::Unknown, false, true, Kind::Unknown),
    ] {
        let measure = Measure::of(true, shape);

        assert_eq!(measure.counts(), linear, "{shape:?}");
        assert_eq!(shape.needs_history(), history, "{shape:?}");
        assert_eq!(shape.inherited_kind(), inherited, "{shape:?}");
        assert!(!Measure::of(false, shape).counts(), "{shape:?}");
    }
}

#[test]
fn value_facts_receive_only_constant_cardinality() {
    let directory = tempfile::tempdir().unwrap();

    std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
    std::fs::write(
        directory.path().join("index.ts"),
        "export function f(xs: number[], zs: number[]) {\n\tconst ys = xs;\n\tzs.push(1);\n\tfor (const v of [1, 2]) void v;\n\tfor (const v of ys) void v;\n\tfor (const v of [...xs]) void v;\n\tfor (const v of zs) void v;\n}",
    )
    .unwrap();

    let allocator = oxc_allocator::Allocator::default();
    let project =
        crate::project::Project::load(&allocator, &directory.path().join("tsconfig.json")).unwrap();
    let file = project
        .file_by_path(&directory.path().join("index.ts"))
        .unwrap();
    let nodes = project.file(file).semantic.nodes();
    let function = nodes
        .iter()
        .find_map(|node| match node.kind() {
            AstKind::Function(function) => Some(FunctionNode::Function(function)),
            _ => None,
        })
        .unwrap();
    let iterated: Vec<&Expression<'_>> = nodes
        .iter()
        .filter_map(|node| match node.kind() {
            AstKind::ForOfStatement(statement) => Some(&statement.right),
            _ => None,
        })
        .collect();
    let mut analysis = Analysis::new(
        &project,
        crate::analysis::Options {
            minimum_exponent: 2,
            types: crate::analysis::TypeMode::Syntactic,
            record_nodes: false,
        },
    );
    let inputs = analysis.function_inputs(file, function, Default::default());
    let parameters: Vec<Cost> = inputs
        .values()
        .filter_map(|facts| facts.value.size.clone())
        .collect();

    analysis.current_substitutions = inputs;

    let sizes: Vec<_> = iterated
        .iter()
        .map(|expression| analysis.size_of_value(file, expression))
        .collect();

    assert_eq!(parameters.len(), 2);
    assert_eq!(sizes[0], Some(Cost::ONE));
    assert_eq!(sizes[1..], [None, None, None]);
}

#[test]
fn resizing_scans_ended_by_exhausted_work_answer_untracked_and_stay_unkept() {
    let directory = tempfile::tempdir().unwrap();

    std::fs::write(directory.path().join("tsconfig.json"), "{}").unwrap();
    std::fs::write(
        directory.path().join("index.ts"),
        "export function f(xs: number[]) {\n\tfor (const v of [1, 2]) xs.push(v);\n}",
    )
    .unwrap();

    let allocator = oxc_allocator::Allocator::default();
    let project =
        crate::project::Project::load(&allocator, &directory.path().join("tsconfig.json")).unwrap();
    let file = project
        .file_by_path(&directory.path().join("index.ts"))
        .unwrap();
    let scoping = project.file(file).semantic.scoping();
    let symbol = scoping
        .symbol_ids()
        .find(|symbol| scoping.symbol_name(*symbol) == "xs")
        .unwrap();
    let options = crate::analysis::Options {
        minimum_exponent: 2,
        types: crate::analysis::TypeMode::Syntactic,
        record_nodes: false,
    };
    let mut exhausted = Analysis::new(&project, options);

    exhausted
        .set_scheduler_limits(crate::summaries::SchedulerLimits {
            work: crate::analysis::work::Limits::uniform(100_000).with(Event::QueuePush, 0),
            ..Default::default()
        })
        .unwrap();

    assert!(!exhausted.charge_work(Event::QueuePush, 1));
    assert!(exhausted.is_resized_in_place(file, symbol));
    assert!(exhausted.values.sizes.resizings.is_empty());

    let mut admitted = Analysis::new(&project, options);

    assert!(admitted.is_resized_in_place(file, symbol));
    assert_eq!(admitted.values.sizes.resizings.len(), 1);
}

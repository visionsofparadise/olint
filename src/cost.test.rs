use super::*;

#[test]
fn partial_binding_preserves_resource_errors_from_known_children() {
    let cost = Cost::parse("O(n + m)").unwrap();
    let error = cost.bind_known(&mut |part| {
        if part.names().len() > 1 || part.names() == ["n"] {
            Err(CostError::UnresolvedQuantity("n".into()))
        } else {
            Err(CostError::Resource)
        }
    });

    assert_eq!(error, Err(CostError::Resource));
}
#[test]
fn grouped_factors_keep_canonical_presentation_order() {
    let x = Cost::dimension(1, Domain::Size);
    let y = Cost::dimension(2, Domain::Size);
    let direct = Cost::product(vec![x.clone(), x.clone(), y.clone()]).unwrap();
    let nested = Cost::product(vec![Cost::product(vec![x.clone(), x]).unwrap(), y]).unwrap();

    assert_eq!(direct.structural_key(), nested.structural_key());
    assert_eq!(direct.text(), nested.text());
}
#[test]
fn originless_maximum_exhaustion_is_an_explicit_failure() {
    let mut traces = TraceArena::default();
    let left = Cost::parse(&format!("O({})", "a".repeat(40_000))).unwrap();
    let right = Cost::parse(&format!("O({})", "b".repeat(40_000))).unwrap();
    let mut unknowns = Unknowns::default();
    let result = Part::unmarked(left.clone(), None).max(
        Part::unmarked(right, None),
        &mut unknowns,
        &mut traces,
    );

    assert_eq!(result.cost_error, Some(CostError::Resource));
    assert!(!result.is_complete());
    assert_eq!(result.cost, left);
    assert!(result.origin.is_none());
    assert!(result.unknowns.is_none());
}

#[test]
fn maximum_exhaustion_with_a_source_is_partial_and_cold_errors_stay_unselected() {
    let mut traces = TraceArena::default();
    let left = Cost::parse(&format!("O({})", "a".repeat(40_000))).unwrap();
    let right = Cost::parse(&format!("O({})", "b".repeat(40_000))).unwrap();
    let origin = SourceSpan {
        file: FileId(0),
        start: 10,
        end: 20,
    };
    let mut unknowns = Unknowns::default();
    let mut first = Part::unmarked(left, None);
    first.origin = Some(origin);
    let result = first.max(Part::unmarked(right, None), &mut unknowns, &mut traces);

    assert!(!result.is_complete());

    let root = result.unknowns.unwrap();

    assert!(
        matches!(unknowns.node(root), crate::unknowns::UnknownNode::Origin(value) if value.origin == origin && value.reason == UnknownReason::ResourceExhaustion)
    );

    let selected = result.preferred(Preference::Cold).max(
        Part::unmarked(Cost::ONE, None),
        &mut unknowns,
        &mut traces,
    );

    assert!(selected.is_complete());
}
#[test]
fn root_envelope_supports_legacy_growth_and_monotone_fixed_powers() {
    let roots = [
        Cost::dimension(1, Domain::Size),
        Cost::dimension(2, Domain::Size),
    ];
    let bind = |text| {
        Cost::parse(text)
            .unwrap()
            .bind(
                &|name| match name {
                    "n" => Some(roots[0].clone()),
                    "m" => Some(roots[1].clone()),
                    _ => None,
                },
                &roots,
            )
            .unwrap()
    };

    for (cost, limit, expected) in [
        ("O(n*m)", "O(N)", CostComparison::Exceeds),
        ("O(n^2)", "O(N^3)", CostComparison::Within),
        ("O(N^3)", "O(N^2)", CostComparison::Exceeds),
        ("O(log N)", "O(N)", CostComparison::Within),
        ("O(N log N)", "O(N)", CostComparison::Exceeds),
        ("O(N^2)", "O(N log N)", CostComparison::Exceeds),
        ("O(n^2)", "O(m^3)", CostComparison::Inconclusive),
    ] {
        assert_eq!(
            bind(cost).compare(&bind(limit)),
            expected,
            "{cost} vs {limit}"
        );
    }

    let positive = Cost::dimension(3, Domain::PositiveReal);

    assert_eq!(
        Cost::power(positive.clone(), Cost::constant(2))
            .unwrap()
            .compare(&Cost::power(positive, Cost::constant(3)).unwrap()),
        CostComparison::Inconclusive
    );
}
#[test]
fn wide_canonical_text_uses_semantic_node_limit() {
    let terms = (0..2000)
        .map(|id| Cost::logarithm(Cost::dimension(id, Domain::Size)).unwrap())
        .collect();
    let cost = Cost::sum(terms).unwrap();

    assert!(Cost::parse(&cost.text()).is_ok());
}
#[test]
fn implicit_products_require_complete_log_tokens() {
    for source in [
        "O(n logger)",
        "O(2logarithm)",
        "O(n logNonsense)",
        "O(n log.name)",
    ] {
        assert!(Cost::parse(source).is_err(), "{source}");
    }

    for source in [
        "O(N log N)",
        "O(NlogN)",
        "O(N^2logN)",
        "O(n * logger)",
        "O(logarithm)",
    ] {
        assert!(Cost::parse(source).is_ok(), "{source}");
    }
}
#[test]
fn parser_rejects_long_chains_before_recursive_drop_can_grow() {
    let factorial = format!("O(n{})", "!".repeat(20_000));
    let ratio = format!("O(n{})", "/n".repeat(20_000));

    assert!(factorial.len() < MAX_TEXT && ratio.len() < MAX_TEXT);
    assert_eq!(Cost::parse(&factorial), Err(CostError::Resource));
    assert_eq!(Cost::parse(&ratio), Err(CostError::Resource));
}
#[test]
fn constructors_preserve_serialized_parser_budget() {
    let first = Cost::parse(&format!("O({})", "a".repeat(40_000))).unwrap();
    let second = Cost::parse(&format!("O({})", "b".repeat(40_000))).unwrap();

    assert_eq!(Cost::sum(vec![first, second]), Err(CostError::Resource));

    let first = Cost::parse(&format!("O({})", "a".repeat(30_000))).unwrap();
    let second = Cost::parse(&format!("O({})", "b".repeat(30_000))).unwrap();
    let sum = Cost::sum(vec![first, second]).unwrap();

    assert!(sum.text().len() <= MAX_TEXT);
    assert_eq!(Cost::parse(&sum.text()).unwrap(), sum);

    let mut nested = Cost::dimension(1, Domain::Size);

    for _ in 0..60 {
        nested = Cost::logarithm(nested).unwrap();
    }

    let parsed = Cost::parse(&nested.text()).unwrap();

    assert_eq!(
        parsed
            .bind(
                &|name| (name == "size_1").then(|| Cost::dimension(1, Domain::Size)),
                &[]
            )
            .unwrap(),
        nested
    );
}
#[test]
fn public_wrapper_exposes_only_bounded_construction() {
    let n = Cost::dimension(1, Domain::Size);
    let parsed = Cost::parse("O(n^2)")
        .unwrap()
        .bind(
            &|name| (name == "n").then(|| n.clone()),
            std::slice::from_ref(&n),
        )
        .unwrap();

    assert_eq!(parsed.compare(&n), CostComparison::Exceeds);

    let mut nested = n;
    let mut rejected = false;

    for _ in 0..100 {
        match Cost::logarithm(nested.clone()) {
            Ok(next) => nested = next,
            Err(CostError::Resource) => {
                rejected = true;

                break;
            }
            other => panic!("unexpected result {other:?}"),
        }
    }

    assert!(rejected);

    let clone = nested.clone();

    assert_eq!(clone, nested);
    assert!(!format!("{clone:?}").is_empty());
    assert!(nested.text().starts_with("O("));
    drop(clone);
    drop(nested);
}
#[test]
fn comparison_budget_covers_large_maps_and_strict_witnesses() {
    let wide = Expression::product((1..MAX_NODES as u64).map(size).collect()).unwrap();
    let (answer, used) = wide.compare_with_budget(&Expression::ONE, COMPARISON_CREDITS);

    assert_eq!(answer, CostComparison::Inconclusive);
    assert_eq!(used, COMPARISON_CREDITS);

    let a = bound("O(n+m)");
    let b = bound("O(n)");
    let mut small = PROOF_CREDITS_PER_NODE * 8;

    assert!(!strictly_larger(&a, &b, &mut small));
    assert_eq!(small, 0);

    let mut enough = COMPARISON_CREDITS;

    assert!(strictly_larger(&a, &b, &mut enough));
    assert!(enough < COMPARISON_CREDITS);

    let (answer, used) = a.compare_with_budget(&b, 0);

    assert_eq!((answer, used), (CostComparison::Inconclusive, 0));
    assert_eq!(
        Expression::ratio(size(1), size(1))
            .unwrap()
            .compare(&Expression::ONE),
        CostComparison::Within
    );
}
fn size(id: u64) -> Expression {
    Expression::dimension(id, Domain::Size)
}
fn bound(text: &str) -> Expression {
    Expression::parse(text)
        .unwrap()
        .bind(
            &|name| match name {
                "n" => Some(size(1)),
                "m" => Some(size(2)),
                _ => None,
            },
            &[size(1), size(2)],
        )
        .unwrap()
}
#[test]
fn legacy_and_structural_roundtrip() {
    for text in [
        "O(1)",
        "O(log N)",
        "O(logN)",
        "O(NlogN)",
        "O(N^2logN)",
        "O(N log N)",
        "O(log^2 N)",
        "O(N^4294967295)",
        "O(max(n, log(m)))",
        "O(n!)",
        "O(n^n)",
        "O(n/(1/n))",
    ] {
        let parsed = Expression::parse(text).unwrap();
        let again = Expression::parse(&parsed.text()).unwrap();

        assert_eq!(parsed, again, "{text}");
    }
}
#[test]
fn independent_dimensions_and_monomials() {
    assert_eq!(
        bound("O(n*m)").compare(&bound("O(n*n)")),
        CostComparison::Inconclusive
    );
    assert_eq!(
        bound("O(n)").compare(&bound("O(m)")),
        CostComparison::Inconclusive
    );
    assert_eq!(
        bound("O(n^2)").compare(&bound("O(n)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(n*log(n))").compare(&bound("O(n^2)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(log(n)*log(m))").compare(&bound("O(log(n)^2)")),
        CostComparison::Inconclusive
    );
}
#[test]
fn aggregate_and_envelope_bounds() {
    assert_eq!(
        bound("O(n+m)").compare(&bound("O(max(n,m))")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(max(n,m))").compare(&bound("O(n+m)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n*m)").compare(&bound("O(N^2)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n*m)").compare(&bound("O(N)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(n+m)").compare(&bound("O(n)")),
        CostComparison::Exceeds
    );
}
#[test]
fn ratios_respect_domain_and_progress() {
    assert_eq!(
        bound("O(n/(1/n))").compare(&bound("O(n^2)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n/m)").compare(&bound("O(n)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n/m)").compare(&Expression::ONE),
        CostComparison::Inconclusive
    );

    let small = Expression::dimension(3, Domain::PositiveReal);
    let ratio = Expression::ratio(size(1), small).unwrap();

    assert_eq!(ratio.compare(&size(1)), CostComparison::Inconclusive);
    assert_eq!(
        Expression::ratio(size(1), Expression::Constant(0)),
        Err(CostError::Domain)
    );
    assert_eq!(
        Expression::factorial(Expression::dimension(3, Domain::PositiveReal)),
        Err(CostError::Domain)
    );
}
#[test]
fn exponentials_and_factorials() {
    assert_eq!(
        bound("O(2^n)").compare(&bound("O(3^n)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(3^n)").compare(&bound("O(2^n)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(2^n)").compare(&bound("O(n!)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n!)").compare(&bound("O(2^n)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(n!)").compare(&bound("O(n^n)")),
        CostComparison::Within
    );
    assert_eq!(
        bound("O(n^n)").compare(&bound("O(n!)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(n!)").compare(&bound("O(2^m)")),
        CostComparison::Inconclusive
    );
    assert_eq!(
        bound("O(2^(2*n))").compare(&bound("O(2^n)")),
        CostComparison::Exceeds
    );
    assert_eq!(
        bound("O(2^n)").compare(&bound("O(2^(2*n))")),
        CostComparison::Within
    );
}
#[test]
fn logarithm_product_rules_do_not_rewrite_exponent_values() {
    let a = bound("O(log(n*m))");
    let b = bound("O(log(n)+log(m))");

    assert_eq!(a.compare(&b), CostComparison::Within);
    assert_eq!(b.compare(&a), CostComparison::Within);
    assert_ne!(a, b);
    assert_eq!(
        Expression::power(Expression::Constant(2), a)
            .unwrap()
            .compare(&Expression::power(Expression::Constant(2), b).unwrap()),
        CostComparison::Inconclusive
    );
}
#[test]
fn names_bind_and_identity_does_not_use_labels() {
    assert_eq!(
        Expression::parse("O(n)")
            .unwrap()
            .compare(&Expression::parse("O(n)").unwrap()),
        CostComparison::Inconclusive
    );
    assert!(matches!(
        Expression::parse("O(unknown)")
            .unwrap()
            .bind(&|_| None, &[]),
        Err(CostError::UnknownName(_))
    ));
    assert_eq!(size(1), Expression::dimension(1, Domain::Size));
    assert_ne!(size(1), size(2));
    assert_eq!(Expression::N.bind(&|_| None, &[]).unwrap(), Expression::ONE);
}
#[test]
fn errors_are_checked_and_parser_consumes_everything() {
    for text in [
        "O(n^)",
        "O(n/0)",
        "O(max())",
        "O(n))junk",
        "O(n m)",
        "O(18446744073709551616)",
        "O(0^0)",
    ] {
        assert!(Expression::parse(text).is_err(), "{text}");
    }

    assert_eq!(
        Expression::Constant(u64::MAX).multiply(&Expression::Constant(2)),
        Err(CostError::Overflow)
    );

    let n = Expression::power(size(1), Expression::Constant(u64::MAX)).unwrap();

    assert_eq!(
        n.multiply(&size(1)).unwrap().compare(&n),
        CostComparison::Exceeds
    );
    assert_ne!(
        Expression::parse("O(nm)").unwrap(),
        Expression::parse("O(n*m)").unwrap()
    );
    assert!(Expression::parse(&format!("O({}n{})", "(".repeat(1000), ")".repeat(1000))).is_err());
    assert!(Expression::parse("O(0 * log(0))").is_err());
    assert!(Expression::parse("O(0 * (n / denominator))")
        .unwrap()
        .bind(
            &|name| match name {
                "n" => Some(size(1)),
                "denominator" => Some(Expression::Constant(0)),
                _ => None,
            },
            &[]
        )
        .is_err());
}
#[test]
fn structural_order_is_total_and_canonical() {
    assert_eq!(bound("O(n*m)"), bound("O(m*n)"));

    let mut rows = vec![size(1), size(2), bound("O(n^2)")];

    rows.sort_by_key(Expression::structural_key);

    let first = rows.clone();

    rows.reverse();
    rows.sort_by_key(Expression::structural_key);
    assert_eq!(rows, first);
}
#[test]
fn raw_nodes_are_guarded_at_public_operation_boundaries() {
    let mut value = size(1);

    for _ in 0..100 {
        value = Expression::Log(Arc::new(value));
    }

    assert_eq!(value.text(), "O(unknown)");
    assert_eq!(value.structural_key(), "ResourceExceeded");
    assert_eq!(value.compare(&value), CostComparison::Inconclusive);
    assert_eq!(
        Expression::ratio(Expression::ONE, value.clone()),
        Err(CostError::Resource)
    );
    assert_eq!(
        Expression::factorial(value.clone()),
        Err(CostError::Resource)
    );
    assert_eq!(value.multiply(&Expression::ONE), Err(CostError::Resource));

    for source in [
        "O(log())",
        "O(max(n,))",
        "O(max(n,log(m))",
        "O(n/(0))",
        "O(max(n,log(0)))",
    ] {
        assert!(Expression::parse(source).is_err(), "{source}");
    }
}

use crate::project::{FileId, Site};

#[test]
fn streamed_cost_text_matches_existing_expression_format() {
    for source in [
        "O(1)",
        "O(N)",
        "O(log N)",
        "O(N log N)",
        "O(n+m)",
        "O(n*m)",
        "O(max(n,m))",
        "O(log(n))",
        "O(n!)",
        "O(n^3)",
        "O((n+m)^m)",
        "O(n/2)",
    ] {
        let cost = Cost::parse(source).unwrap();
        let mut out = String::new();

        cost.write_with(&mut out, true, &|id, out| write!(out, "size_{id}"))
            .unwrap();
        assert_eq!(out, cost.text(), "{source}");
    }
}
fn part_of(traces: &mut TraceArena, cost: Cost, label: &str) -> Part {
    let trace = traces
        .factor(
            label.into(),
            Site {
                file: FileId(0),
                line: 1,
            },
            SourceSpan {
                file: FileId(0),
                start: 0,
                end: 1,
            },
            cost.clone(),
            None,
            None,
        )
        .unwrap();

    Part::unmarked(cost, Some(trace))
}

#[test]
fn part_max_keeps_the_first_on_ties() {
    let mut traces = TraceArena::default();
    let first = part_of(&mut traces, Cost::N, "first");
    let second = part_of(&mut traces, Cost::N, "second");

    assert_eq!(
        first
            .clone()
            .max(second, &mut Unknowns::default(), &mut traces),
        first
    );
}

#[test]
fn part_max_prefers_hot_then_unmarked_then_cold_over_absent() {
    let mut traces = TraceArena::default();
    let hot = part_of(&mut traces, Cost::ONE, "hot").preferred(Preference::Hot);
    let unmarked = part_of(&mut traces, Cost::N, "unmarked");
    let cold =
        part_of(&mut traces, Cost::parse("O(N^2)").unwrap(), "cold").preferred(Preference::Cold);

    assert_eq!(
        unmarked
            .clone()
            .max(hot.clone(), &mut Unknowns::default(), &mut traces),
        hot
    );
    assert_eq!(
        cold.clone()
            .max(unmarked.clone(), &mut Unknowns::default(), &mut traces),
        unmarked
    );
    assert_eq!(
        Part::none().max(cold.clone(), &mut Unknowns::default(), &mut traces),
        cold
    );
}

#[test]
fn reading_total_takes_the_largest_part() {
    let mut traces = TraceArena::default();
    let reading = Reading {
        phases: [ExecutionPhase::Immediate; 3],
        main: part_of(&mut traces, Cost::N, "main"),
        function_exit: part_of(&mut traces, Cost::LOG, "function exit"),
        loop_exit: part_of(&mut traces, Cost::N_LOG_N, "loop exit"),
    };

    assert_eq!(
        reading.total(&mut Unknowns::default(), &mut traces),
        part_of(&mut traces, Cost::N_LOG_N, "loop exit")
    );
}

#[test]
fn kind_join_ranks_array_over_unknown_over_string() {
    use crate::declared_types::Kind;

    assert_eq!(Kind::Unknown.join(Kind::Array), Kind::Array);
    assert_eq!(Kind::Array.join(Kind::Unknown), Kind::Array);
    assert_eq!(Kind::String.join(Kind::Unknown), Kind::Unknown);
    assert_eq!(Kind::Unknown.join(Kind::String), Kind::Unknown);
}

#[test]
fn report_logarithmic_exception_uses_net_envelope_exponents() {
    for roots in [
        vec![Cost::dimension(101, Domain::Size)],
        vec![
            Cost::dimension(101, Domain::Size),
            Cost::dimension(102, Domain::Size),
        ],
    ] {
        let envelope = Cost::N.bind(&|_| None, &roots).unwrap();

        for (text, expected) in [
            ("O(N log N)", true),
            ("O(N^3 * log(N)^2)", true),
            ("O(N^3)", false),
            ("O(log(N)^2)", false),
            ("O(N^3 / log(N))", false),
            ("O(N^2 * log(N)^2 / (N * log(N)))", true),
            ("O(N * log(N) / log(N))", false),
            ("O(N^3 + log(N))", false),
            ("O(max(N^3, log(N)))", false),
            ("O(N * log(N) + N)", false),
            ("O(max(N * log(N), N))", false),
        ] {
            let cost = Cost::parse(text).unwrap().bind(&|_| None, &roots).unwrap();

            assert_eq!(
                cost.has_polynomial_log_growth(&envelope),
                expected,
                "{text}"
            );
        }
    }
}

#[test]
fn logarithmic_filter_keeps_independent_axes_and_rejects_exponent_overflow() {
    let n = Cost::dimension(101, Domain::Size);
    let m = Cost::dimension(102, Domain::Size);
    let roots = [n.clone(), m.clone()];
    let envelope = Cost::N.bind(&|_| None, &roots).unwrap();
    let mixed = n.multiply(&Cost::logarithm(m.clone()).unwrap()).unwrap();
    let one_axis = n.multiply(&Cost::logarithm(n.clone()).unwrap()).unwrap();

    assert!(!mixed.has_polynomial_log_growth(&envelope));
    assert!(!mixed.has_polynomial_log_growth(&n));
    assert!(!one_axis.has_polynomial_log_growth(&envelope));
    assert!(one_axis.has_polynomial_log_growth(&n));
    assert!(!one_axis.has_polynomial_log_growth(&m));

    let mut overflowing = n.0.clone();

    for _ in 0..3 {
        overflowing = Expression::Power(
            Arc::new(overflowing),
            Arc::new(Expression::Constant(u64::MAX)),
        );
    }

    assert_eq!(envelope_growth(&overflowing, &n.0), None);
}

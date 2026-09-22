use super::*;
use crate::cost::Domain;

fn measure() -> Cost {
    Cost::dimension(7, Domain::Size)
}

fn other() -> Cost {
    Cost::dimension(9, Domain::Size)
}

fn edge(callee: usize, multiplicity: Cost, relation: ArgumentRelation) -> RecurrenceEdge {
    RecurrenceEdge {
        callee,
        multiplicity,
        relation,
        lower_bound: Some(0.0),
    }
}

fn equation(local: Cost, edges: Vec<RecurrenceEdge>) -> RecurrenceEquation {
    RecurrenceEquation {
        local,
        measure: measure(),
        edges,
    }
}

fn solved_of(equations: &[RecurrenceEquation]) -> Vec<Cost> {
    match solution_of(equations) {
        RecurrenceSolution::Solved { factors, .. } => factors,
        RecurrenceSolution::Unsupported { reason } => panic!("unsupported: {reason}"),
    }
}

fn unsupported_of(equations: &[RecurrenceEquation]) -> &'static str {
    match solution_of(equations) {
        RecurrenceSolution::Solved { proof, .. } => panic!("unexpectedly solved: {proof}"),
        RecurrenceSolution::Unsupported { reason } => reason,
    }
}

#[test]
fn a_guarded_unit_decrement_is_linear_in_its_measure() {
    let equations = [equation(
        other(),
        vec![edge(
            0,
            Cost::constant(1),
            ArgumentRelation::Decrement { amount: 1 },
        )],
    )];

    assert_eq!(solved_of(&equations), vec![measure()]);
}

#[test]
fn a_guarded_halving_is_logarithmic_in_its_measure() {
    let equations = [equation(
        Cost::ONE,
        vec![edge(
            0,
            Cost::constant(1),
            ArgumentRelation::Division {
                divisor: 2,
                truncating: true,
            },
        )],
    )];

    assert_eq!(
        solved_of(&equations),
        vec![Cost::logarithm(measure()).unwrap()]
    );
}

#[test]
fn an_unguarded_reduction_stays_unsupported() {
    for relation in [
        ArgumentRelation::Decrement { amount: 1 },
        ArgumentRelation::Division {
            divisor: 2,
            truncating: true,
        },
    ] {
        let equations = [RecurrenceEquation {
            local: Cost::ONE,
            measure: measure(),
            edges: vec![RecurrenceEdge {
                callee: 0,
                multiplicity: Cost::constant(1),
                relation,
                lower_bound: None,
            }],
        }];

        assert_eq!(unsupported_of(&equations), "unguarded reduction");
    }
}

#[test]
fn an_exact_halving_needs_a_positive_measure_floor() {
    let inexact = ArgumentRelation::Division {
        divisor: 2,
        truncating: false,
    };

    for (bound, solved) in [(0.0, false), (1.0, true), (4.0, true)] {
        let equations = [RecurrenceEquation {
            local: Cost::ONE,
            measure: measure(),
            edges: vec![RecurrenceEdge {
                callee: 0,
                multiplicity: Cost::constant(1),
                relation: inexact,
                lower_bound: Some(bound),
            }],
        }];

        assert_eq!(
            matches!(solution_of(&equations), RecurrenceSolution::Solved { .. }),
            solved,
            "{bound}"
        );
    }
}

#[test]
fn constant_branching_over_a_decrement_grows_exponentially() {
    let equations = [equation(
        Cost::ONE,
        vec![
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Decrement { amount: 1 },
            ),
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Decrement { amount: 1 },
            ),
        ],
    )];

    assert_eq!(
        solved_of(&equations),
        vec![Cost::power(Cost::constant(2), measure()).unwrap()]
    );
}

#[test]
fn a_wider_decrement_divides_the_exponent() {
    let equations = [equation(
        Cost::ONE,
        vec![
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Decrement { amount: 3 },
            ),
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Decrement { amount: 3 },
            ),
        ],
    )];
    let exponent = Cost::ratio(measure(), Cost::constant(3)).unwrap();

    assert_eq!(
        solved_of(&equations),
        vec![Cost::power(Cost::constant(2), exponent).unwrap()]
    );
}

#[test]
fn a_measure_sized_multiplicity_is_factorial() {
    let equations = [equation(
        measure(),
        vec![edge(
            0,
            measure(),
            ArgumentRelation::Decrement { amount: 1 },
        )],
    )];

    assert_eq!(
        solved_of(&equations),
        vec![Cost::factorial(measure()).unwrap()]
    );
}

#[test]
fn mutual_members_share_one_depth_when_every_cycle_reduces() {
    let equations = [
        equation(
            other(),
            vec![edge(
                1,
                Cost::constant(1),
                ArgumentRelation::Decrement { amount: 1 },
            )],
        ),
        equation(
            Cost::ONE,
            vec![edge(0, Cost::constant(1), ArgumentRelation::Unchanged)],
        ),
    ];

    assert_eq!(solved_of(&equations), vec![measure(), measure()]);
}

#[test]
fn a_cycle_without_a_reduction_stays_unsupported() {
    let equations = [
        equation(
            Cost::ONE,
            vec![edge(1, Cost::constant(1), ArgumentRelation::Unchanged)],
        ),
        equation(
            Cost::ONE,
            vec![edge(0, Cost::constant(1), ArgumentRelation::Unchanged)],
        ),
    ];

    assert_eq!(unsupported_of(&equations), "no proven measure reduction");
}

#[test]
fn a_neutral_cycle_beside_a_reduction_stays_unsupported() {
    let equations = [
        equation(
            Cost::ONE,
            vec![
                edge(
                    1,
                    Cost::constant(1),
                    ArgumentRelation::Decrement { amount: 1 },
                ),
                edge(2, Cost::constant(1), ArgumentRelation::Unchanged),
            ],
        ),
        equation(
            Cost::ONE,
            vec![edge(0, Cost::constant(1), ArgumentRelation::Unchanged)],
        ),
        equation(
            Cost::ONE,
            vec![edge(1, Cost::constant(1), ArgumentRelation::Unchanged)],
        ),
    ];

    assert!(matches!(
        solution_of(&equations),
        RecurrenceSolution::Unsupported { .. }
    ));
}

#[test]
fn a_recursive_call_that_left_no_multiplicity_stays_unsupported() {
    let equations = [equation(Cost::ONE, Vec::new())];

    assert_eq!(unsupported_of(&equations), "invisible recursive call");
}

#[test]
fn a_component_wider_than_its_cap_stays_unsupported() {
    let members: Vec<RecurrenceEquation> = (0..MAXIMUM_RECURRENCE_MEMBERS + 1)
        .map(|index| {
            equation(
                Cost::ONE,
                vec![edge(
                    (index + 1) % (MAXIMUM_RECURRENCE_MEMBERS + 1),
                    Cost::constant(1),
                    ArgumentRelation::Decrement { amount: 1 },
                )],
            )
        })
        .collect();

    assert_eq!(unsupported_of(&members), "component size");
}

#[test]
fn a_geometric_reduction_beside_branching_stays_unsupported() {
    let equations = [equation(
        Cost::ONE,
        vec![
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Division {
                    divisor: 2,
                    truncating: true,
                },
            ),
            edge(
                0,
                Cost::constant(1),
                ArgumentRelation::Division {
                    divisor: 2,
                    truncating: true,
                },
            ),
        ],
    )];

    assert_eq!(
        unsupported_of(&equations),
        "branching without a uniform decrement"
    );
}

#[test]
fn a_weaker_relation_wins_over_a_stronger_one() {
    let decrement = ArgumentRelation::Decrement { amount: 1 };
    let wider = ArgumentRelation::Decrement { amount: 4 };
    let halving = ArgumentRelation::Division {
        divisor: 2,
        truncating: true,
    };

    assert_eq!(weaker_relation_of(decrement, halving), decrement);
    assert_eq!(weaker_relation_of(decrement, wider), decrement);
    assert_eq!(
        weaker_relation_of(halving, ArgumentRelation::Unchanged),
        ArgumentRelation::Unchanged
    );
    assert_eq!(
        weaker_relation_of(
            halving,
            ArgumentRelation::Division {
                divisor: 4,
                truncating: false
            }
        ),
        ArgumentRelation::Division {
            divisor: 2,
            truncating: false
        }
    );
}

#[test]
fn a_marker_splits_out_of_sums_maxima_and_products() {
    let marker = Cost::dimension(u64::MAX - 1, Domain::Size);
    let loops = Cost::dimension(3, Domain::Size);
    let sum = Cost::sum(vec![loops.clone(), marker.clone()]).unwrap();
    let (local, factor) = sum.split_dimension(u64::MAX - 1).unwrap();

    assert_eq!(local, Cost::sum(vec![loops.clone(), Cost::ONE]).unwrap());
    assert_eq!(factor, Some(Cost::ONE));

    let scaled = Cost::product(vec![loops.clone(), marker.clone()]).unwrap();
    let (local, factor) = scaled.split_dimension(u64::MAX - 1).unwrap();

    assert_eq!(local, loops.clone());
    assert_eq!(factor, Some(loops.clone()));

    let alternative = Cost::maximum(vec![loops.clone(), scaled]).unwrap();
    let (local, factor) = alternative.split_dimension(u64::MAX - 1).unwrap();

    assert_eq!(local, loops.clone());
    assert_eq!(factor, Some(loops.clone()));
}

#[test]
fn a_marker_free_expression_keeps_itself_and_reports_no_factor() {
    let loops = Cost::dimension(3, Domain::Size);
    let (local, factor) = loops.split_dimension(u64::MAX - 1).unwrap();

    assert_eq!(local, loops);
    assert_eq!(factor, None);
}

#[test]
fn a_marker_inside_an_unsupported_position_refuses_to_split() {
    let marker = Cost::dimension(u64::MAX - 1, Domain::Size);
    let squared = Cost::product(vec![marker.clone(), marker.clone()]).unwrap();

    assert_eq!(squared.split_dimension(u64::MAX - 1), None);
    assert_eq!(
        Cost::logarithm(marker.clone())
            .unwrap()
            .split_dimension(u64::MAX - 1),
        None
    );
    assert_eq!(
        Cost::factorial(marker)
            .unwrap()
            .split_dimension(u64::MAX - 1),
        None
    );
}

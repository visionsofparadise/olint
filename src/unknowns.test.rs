use super::*;

fn span(start: u32) -> SourceSpan {
    SourceSpan {
        file: FileId(0),
        start,
        end: start + 1,
    }
}

#[test]
fn joins_share_origins_and_discard_duplicate_edges() {
    let mut arena = Unknowns::default();
    let left = arena.origin(span(0), UnknownReason::Target);
    let right = arena.origin(span(1), UnknownReason::Effect);

    assert_eq!(arena.origin(span(0), UnknownReason::Target), left);
    assert_eq!(arena.join(Some(left), Some(left)), Some(left));

    let joined = arena.join(Some(left), Some(right));

    assert_eq!(arena.join(Some(right), Some(left)), joined);
    assert_eq!(arena.len(), 3);
}

#[test]
fn semantic_keys_ignore_call_context_inside_scales() {
    let mut arena = Unknowns::default();
    let origin = arena.origin(span(0), UnknownReason::Target);
    let first = arena.called(Some(origin), span(1));
    let second = arena.called(Some(origin), span(2));
    let first = arena.scale(first, Some(Cost::N));
    let second = arena.scale(second, Some(Cost::N));
    let direct = arena.scale(Some(origin), Some(Cost::N));

    assert_eq!(
        arena.semantic_key(first, &mut || true).unwrap(),
        arena.semantic_key(second, &mut || true).unwrap()
    );
    assert_eq!(
        arena.semantic_key(first, &mut || true).unwrap(),
        arena.semantic_key(direct, &mut || true).unwrap()
    );

    let repeated = arena.called(first, span(3));

    assert_eq!(
        arena.semantic_key(first, &mut || true).unwrap(),
        arena.semantic_key(repeated, &mut || true).unwrap()
    );

    let unresolved = arena.scale(Some(origin), None);

    assert_ne!(
        arena.semantic_key(first, &mut || true).unwrap(),
        arena.semantic_key(unresolved, &mut || true).unwrap()
    );
}

#[test]
fn wrapping_a_long_call_path_retains_one_node_per_edge() {
    let mut arena = Unknowns::default();
    let origin = arena.origin(span(0), UnknownReason::Target);
    let mut root = Some(origin);

    for start in 1..2049 {
        root = arena.called(root, span(start));
    }

    assert_eq!(arena.len(), 2049);
    assert_eq!(
        arena.semantic_key(root, &mut || true).unwrap(),
        arena.semantic_key(Some(origin), &mut || true).unwrap()
    );
}

#[test]
fn unknown_scaling_overflow_stays_unknown() {
    let mut arena = Unknowns::default();
    let origin = arena.origin(span(0), UnknownReason::Multiplicity);
    let first = arena.scale(Some(origin), Some(Cost::constant(u64::MAX)));
    let second = arena.scale(first, Some(Cost::constant(2)));

    let unknown = arena.scale(Some(origin), None);

    assert_eq!(
        arena.semantic_key(second, &mut || true).unwrap(),
        arena.semantic_key(unknown, &mut || true).unwrap()
    );
}

use crate::cost::Domain;
use std::fmt::Debug;

pub fn old_vector(arena: &Unknowns, root: Option<UnknownId>) -> Vec<(UnknownId, Option<Cost>)> {
    let mut pending: Vec<_> = root.into_iter().map(|id| (id, Some(Cost::ONE))).collect();
    let mut visited = HashSet::new();
    let mut atoms = Vec::new();

    while let Some((id, factor)) = pending.pop() {
        if !visited.insert((id, factor.clone())) {
            continue;
        }

        match arena.node(id) {
            UnknownNode::Origin(_) => atoms.push((id, factor)),
            UnknownNode::Call { child, .. } => pending.push((*child, factor)),
            UnknownNode::Join { children } => {
                pending.extend(children.iter().map(|id| (*id, factor.clone())))
            }
            UnknownNode::Scale {
                child,
                factor: next,
            } => {
                pending.push((
                    *child,
                    factor
                        .and_then(|left| next.as_ref().and_then(|right| left.multiply(right).ok())),
                ));
            }
        }
    }

    atoms.sort_by_key(|(id, factor)| (*id, factor.as_ref().map(Cost::structural_key)));
    atoms.dedup();

    atoms
}

fn source(start: u32) -> SourceSpan {
    SourceSpan {
        file: FileId(0),
        start,
        end: start + 1,
    }
}

pub fn adversarial_roots() -> (Unknowns, Vec<Option<UnknownId>>) {
    let mut arena = Unknowns::default();
    let mut roots = vec![None];

    for index in 0..6 {
        roots.push(Some(arena.origin(source(index), UnknownReason::Target)));
    }

    roots.push(Some(arena.insert(UnknownNode::Origin(Unknown {
        origin: source(0),
        reason: UnknownReason::Target,
        multiplicity: Some(Cost::constant(3)),
    }))));

    let factors = [
        Some(Cost::ONE),
        Some(Cost::constant(0)),
        None,
        Some(Cost::constant(2)),
        Some(Cost::dimension(1, Domain::Size)),
        Some(Cost::logarithm(Cost::dimension(2, Domain::Size)).unwrap()),
    ];

    for factor in &factors {
        let scaled = arena.scale(roots[1], factor.clone());

        roots.push(scaled);
    }

    let mut seed = 17u64;

    for index in 0..256 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let left = roots[(seed as usize) % roots.len()];
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let right = roots[(seed as usize) % roots.len()];
        let root = match index % 3 {
            0 => arena.join(left, right),
            1 => arena.called(left, source(1000 + index)),
            _ => arena.scale(left, factors[(index as usize) % factors.len()].clone()),
        };

        roots.push(root);

        if index % 8 == 0 {
            let reverse = arena.join(right, left);
            let joined = arena.join(left, right);
            let called = arena.called(joined, source(2000 + index));

            roots.extend([reverse, joined, called]);
        }
    }

    let joined = arena.join(roots[1], roots[2]);
    let scaled_union = arena.scale(joined, Some(Cost::constant(7)));
    let left = arena.scale(roots[1], Some(Cost::constant(7)));
    let right = arena.scale(roots[2], Some(Cost::constant(7)));
    let distributed = arena.join(left, right);

    roots.extend([scaled_union, distributed]);

    (arena, roots)
}

pub fn verify_equivalence<K: Copy + Eq + Debug, E: Debug>(
    identify: &mut impl FnMut(&mut Unknowns, Option<UnknownId>) -> Result<K, E>,
) {
    let (mut arena, roots) = adversarial_roots();
    let old: Vec<_> = roots.iter().map(|root| old_vector(&arena, *root)).collect();
    let new: Vec<_> = roots
        .iter()
        .map(|root| identify(&mut arena, *root).unwrap())
        .collect();

    for left in 0..roots.len() {
        for right in 0..roots.len() {
            assert_eq!(
                old[left] == old[right],
                new[left] == new[right],
                "roots {left}/{right}"
            );
        }
    }

    for index in (0..roots.len()).rev() {
        assert_eq!(identify(&mut arena, roots[index]).unwrap(), new[index]);
    }
}

pub fn top_down_failure() -> (Unknowns, Option<UnknownId>, Option<UnknownId>) {
    let left = Cost::sum(
        (0..2047)
            .map(|id| Cost::dimension(id + 100, Domain::Size))
            .collect(),
    )
    .unwrap();
    let right = Cost::sum(
        (0..2047)
            .map(|id| Cost::dimension(id + 10000, Domain::Size))
            .collect(),
    )
    .unwrap();

    assert!(left.multiply(&right).is_err());

    let zero = Cost::constant(0);

    assert_eq!(
        left.multiply(&right.multiply(&zero).unwrap()).unwrap(),
        zero
    );

    let mut arena = Unknowns::default();
    let origin_id = arena.origin(source(0), UnknownReason::Target);
    let origin = Some(origin_id);
    let inner = arena.scale(origin, Some(zero.clone()));
    let middle = arena.scale(inner, Some(right));
    let outer = arena.scale(middle, Some(left));
    let known_zero = arena.scale(origin, Some(zero));

    assert_eq!(old_vector(&arena, outer), vec![(origin_id, None)]);
    assert_eq!(
        old_vector(&arena, known_zero),
        vec![(origin_id, Some(Cost::constant(0)))]
    );

    (arena, outer, known_zero)
}

pub fn unscaled_prefixes(count: u32) -> (Unknowns, Vec<Option<UnknownId>>) {
    let mut arena = Unknowns::default();
    let mut prior = None;
    let mut prefixes = Vec::new();

    for index in 0..count {
        let origin = Some(arena.origin(source(index), UnknownReason::Target));
        let called = arena.called(prior, source(count + index));
        prior = arena.join(origin, called);

        prefixes.push(prior);
    }

    (arena, prefixes)
}
#[test]
fn actual_semantic_sets_match_the_prior_vector_equivalence() {
    verify_equivalence(&mut |arena, root| arena.semantic_key(root, &mut || true));
}
#[test]
fn checked_scaling_keeps_top_down_failure_identity() {
    let (mut arena, outer, zero) = top_down_failure();

    assert_ne!(
        arena.semantic_key(outer, &mut || true).unwrap(),
        arena.semantic_key(zero, &mut || true).unwrap()
    );
}
#[test]
fn growing_semantic_prefixes_share_bounded_structure() {
    let (mut arena, roots) = unscaled_prefixes(2048);

    for root in roots {
        arena.semantic_key(root, &mut || true).unwrap();
    }

    assert!(arena.semantic_stats().nodes <= 64 * 2048);
    assert_eq!(arena.semantic_stats().atoms, 2048);
}

#[test]
fn failed_semantic_construction_never_exposes_a_key_and_can_retry() {
    for allowance in [0, 1, 4, 32, 48, 80, 128] {
        let mut arena = Unknowns::default();
        let first = Some(arena.origin(span(1), UnknownReason::Target));
        let second = Some(arena.origin(span(2), UnknownReason::Effect));
        let root = arena.join(first, second);
        let mut remaining = allowance;
        let result = arena.semantic_key(root, &mut || {
            if remaining == 0 {
                false
            } else {
                remaining -= 1;

                true
            }
        });

        if result.is_err() {
            assert!(arena.semantic_key(root, &mut || false).is_err());
        }

        let joined = arena.semantic_key(root, &mut || true).unwrap();

        assert_ne!(joined, arena.semantic_key(first, &mut || true).unwrap());
        assert_ne!(joined, arena.semantic_key(second, &mut || true).unwrap());

        let reverse = arena.join(second, first);

        assert_eq!(joined, arena.semantic_key(reverse, &mut || true).unwrap());
    }
}

#[test]
fn changing_scale_prefixes_exhaust_checked_work_without_fabricating_identity() {
    let mut arena = Unknowns::default();
    let mut root = None;
    let mut remaining = 500;
    let mut rejected = false;

    for index in 0..64 {
        let origin = Some(arena.origin(span(index), UnknownReason::Target));
        let joined = arena.join(origin, root);
        root = arena.scale(joined, Some(Cost::constant(2)));
        let result = arena.semantic_key(root, &mut || {
            if remaining == 0 {
                false
            } else {
                remaining -= 1;

                true
            }
        });

        if result.is_err() {
            rejected = true;

            break;
        }
    }

    assert!(rejected);
    assert!(arena.semantic_key(root, &mut || false).is_err());

    let recovered = arena.semantic_key(root, &mut || true).unwrap();

    assert_ne!(recovered, arena.semantic_key(None, &mut || true).unwrap());
    assert!(arena.semantic_stats().work < 10_000);
}

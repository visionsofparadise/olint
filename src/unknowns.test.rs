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

    assert_eq!(arena.semantic_key(first), arena.semantic_key(second));
    assert_eq!(arena.semantic_key(first), arena.semantic_key(direct));

    let repeated = arena.called(first, span(3));

    assert_eq!(arena.semantic_key(first), arena.semantic_key(repeated));

    let unresolved = arena.scale(Some(origin), None);

    assert_ne!(arena.semantic_key(first), arena.semantic_key(unresolved));
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
    assert_eq!(arena.semantic_key(root), vec![(origin, Some(Cost::ONE))]);
}

#[test]
fn unknown_scaling_overflow_stays_unknown() {
    let mut arena = Unknowns::default();
    let origin = arena.origin(span(0), UnknownReason::Multiplicity);
    let first = arena.scale(Some(origin), Some(Cost::constant(u64::MAX)));
    let second = arena.scale(first, Some(Cost::constant(2)));

    assert_eq!(arena.semantic_key(second), vec![(origin, None)]);
}

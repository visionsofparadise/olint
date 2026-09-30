//! The spec's knownness order over snapshot rows, shared by the corpus diff and, through a `#[path]` include in
//! `tests/integration/dead_ends.rs`, by the dead-end fixtures.
//!
//! It lives in the harness rather than the olint library because `snapshot` and `scale` build the head's `corpus/`
//! against each base's olint, so the harness may only use library API every base carries: `olint::cost` and the
//! `olint::snapshot` row types.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use olint::cost::{Cost, CostComparison, Domain};
use olint::snapshot::{NodeKey, NodeRow, NodeState};

/// The knownness order:
///
/// - Known ranks above Partial, and Partial above Unknown.
/// - Known against Known ranks at or above when the new bound is at least as tight.
/// - Partial against Partial ranks at or above when the new unknown origins are a subset of the prior ones, every
///   prior proven contribution has a new contribution at the same constituent that is at least as tight, and the new
///   floor is at least as tight as the larger of the prior floor and the new contributions whose constituents the
///   prior row lacks. The floor check stands in for the loop multiplicities and unlisted constituents the
///   contribution lists leave out, so a newly proven constituent that raises the floor without a listed contribution
///   reads as a lowering, the conservative side.
/// - Unknown against Unknown ranks at or above when the new unknown origins are a subset of the prior ones.
///
/// Cost text parses back with each label as one size dimension, shared across every comparison of one `Ranking`, and
/// `N` as the envelope. A comparison `Cost::compare` leaves `Inconclusive`, or text that fails to parse, fails "at
/// least as tight". Identical text is equal without a comparison.
#[derive(Default)]
pub struct Ranking {
    names: RefCell<HashMap<String, u64>>,
    parsed: RefCell<HashMap<String, Option<Cost>>>,
}

impl Ranking {
    pub fn new() -> Ranking {
        Ranking::default()
    }

    fn parse(&self, text: &str) -> Option<Cost> {
        if let Some(cost) = self.parsed.borrow().get(text) {
            return cost.clone();
        }

        let cost = match text {
            "O(unknown)" => None,
            _ => Cost::parse(text).ok().and_then(|cost| {
                let resolve = |name: &str| {
                    let mut names = self.names.borrow_mut();
                    let next = names.len() as u64;
                    let id = *names.entry(name.to_string()).or_insert(next);

                    Some(Cost::dimension(id, Domain::Size))
                };

                cost.bind(&resolve, &[Cost::dimension(u64::MAX, Domain::Size)])
                    .ok()
            }),
        };

        self.parsed
            .borrow_mut()
            .insert(text.to_string(), cost.clone());

        cost
    }

    /// Whether cost `new` is at least as tight as cost `old`.
    pub fn at_least_as_tight(&self, new: Option<&str>, old: Option<&str>) -> bool {
        match (new, old) {
            (Some(new), Some(old)) if new == old => true,
            (Some(new), Some(old)) => match (self.parse(new), self.parse(old)) {
                (Some(new), Some(old)) => new.compare(&old) == CostComparison::Within,
                _ => false,
            },
            (None, None) => true,
            _ => false,
        }
    }

    /// Whether floor `new` is at least as tight as the larger of floor `old` and the `added` contribution bounds.
    fn floor_within(&self, new: Option<&str>, old: Option<&str>, added: &[&str]) -> bool {
        if added.is_empty() || self.at_least_as_tight(new, old) {
            return self.at_least_as_tight(new, old);
        }

        let (Some(new), Some(old)) = (new.and_then(|new| self.parse(new)), old) else {
            return false;
        };
        let mut ceiling = Vec::with_capacity(added.len() + 1);

        for text in std::iter::once(old).chain(added.iter().copied()) {
            match self.parse(text) {
                Some(cost) => ceiling.push(cost),
                None => return false,
            }
        }

        Cost::maximum(ceiling).is_ok_and(|ceiling| new.compare(&ceiling) == CostComparison::Within)
    }

    /// Whether `new` ranks at or above `old` in the knownness order.
    pub fn ranks_at_or_above(&self, new: &NodeRow, old: &NodeRow) -> bool {
        let unknowns_within = || {
            let prior: BTreeSet<&NodeKey> = old.unknowns.iter().map(|(key, _)| key).collect();

            new.unknowns.iter().all(|(key, _)| prior.contains(key))
        };

        match (new.state, old.state) {
            (NodeState::Known, NodeState::Known) => {
                self.at_least_as_tight(new.bound.as_deref(), old.bound.as_deref())
            }
            (NodeState::Known, _) | (NodeState::Partial, NodeState::Unknown) => true,
            (NodeState::Partial, NodeState::Partial) => {
                let proven: BTreeMap<&NodeKey, &str> = new
                    .contributions
                    .iter()
                    .map(|(key, bound)| (key, bound.as_str()))
                    .collect();
                let prior: BTreeSet<&NodeKey> =
                    old.contributions.iter().map(|(key, _)| key).collect();
                let added: Vec<&str> = new
                    .contributions
                    .iter()
                    .filter(|(key, _)| !prior.contains(key))
                    .map(|(_, bound)| bound.as_str())
                    .collect();

                unknowns_within()
                    && old.contributions.iter().all(|(key, bound)| {
                        proven.get(key).is_some_and(|new| {
                            self.at_least_as_tight(Some(new), Some(bound.as_str()))
                        })
                    })
                    && self.floor_within(new.floor.as_deref(), old.floor.as_deref(), &added)
            }
            (NodeState::Unknown, NodeState::Unknown) => unknowns_within(),
            _ => false,
        }
    }
}

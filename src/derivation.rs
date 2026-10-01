//! The derivation arena: each proven bound and proven contribution olint establishes records the
//! proof rule it applied, the syntax it concerns, the derivations of its premises, the side
//! conditions it established and the cost it concludes (spec §6.4, §6.5).
//!
//! Derivations are hash-consed: recording a derivation equal to a recorded one returns the
//! recorded id and charges nothing. Each new node is charged to [`Event::Derivation`] by its
//! size, one unit for the node, one per premise and one per fact, so the arena's memory is the
//! sum of the charges and each unit belongs to the node it is charged at (spec §7.2). A record
//! past the arena's limit is refused, which leaves its bound without a derivation, and so
//! without a certificate, while the bound itself stands.

use indexmap::IndexSet;

use crate::cost::Cost;
use crate::unknowns::SourceSpan;

#[cfg(doc)]
use crate::analysis::work::Event;

/// Every rule id of the Phase 2 ledger (`corpus/ledger.json`), in ledger order. A derivation's
/// rule is one of these.
pub const RULES: &[&str] = &[
    "branch-join",
    "channel-total",
    "expr-validity",
    "limit-compare",
    "max-dominance",
    "max-normalise",
    "nest-product",
    "partial-bind-known",
    "preference-rank",
    "product-normalise",
    "seq-max",
    "bound-additive",
    "bound-best-of",
    "bound-bisection",
    "bound-constant-collection",
    "bound-constant-distance",
    "bound-directive",
    "bound-exact-additive",
    "bound-false-condition",
    "bound-for-in",
    "bound-for-of-native",
    "bound-geometric",
    "bound-iterator-visits",
    "bound-linear-default",
    "bound-live-visits",
    "bound-progression",
    "bound-quantity",
    "bound-share",
    "bound-single-iteration",
    "for-of-produced-length",
    "loop-effect-invalidation",
    "loop-nest",
    "loop-phases",
    "loop-suspension",
    "loop-unbounded",
    "loop-unit",
    "budget-cancel",
    "budget-collect",
    "budget-share",
    "hoisted-join",
    "share-sized-operation",
    "escape-absorb",
    "escape-depth-exhausted",
    "escape-lift",
    "flow-completion",
    "flow-graph",
    "async-assimilation",
    "await-continuation",
    "call-callback-parameter",
    "call-effects-transfer",
    "call-fallback",
    "call-lazy-phase",
    "call-open-remainder",
    "call-returned-function",
    "call-summary",
    "construction-fields",
    "constructor-call",
    "implicit-invocation",
    "iterator-visits",
    "latent-production",
    "lazy-consume",
    "returned-function-facts",
    "size-substitution",
    "target-resolution",
    "tsc-callee-targets",
    "rec-branching-decrement",
    "rec-chain-decrement",
    "rec-chain-division",
    "rec-factorial",
    "rec-forget-multiplicity",
    "rec-guard",
    "rec-markers",
    "rec-measure",
    "rec-reduced-measure-size",
    "rec-relation",
    "rec-relation-join",
    "rec-unsolved",
    "array-method",
    "intrinsic-replacement-scan",
    "linear-constructor",
    "native-callback",
    "native-charge-length",
    "native-model",
    "native-visit-budget",
    "regex-cost",
    "regex-every-match",
    "regex-matched-once",
    "set-map-linear",
    "unmodelled-native",
    "argument-facts",
    "array-method-size",
    "constant-cardinality",
    "count-of",
    "growth-sites",
    "holder-stability",
    "input-size-envelope",
    "iterable-size",
    "parameter-size",
    "produced-size",
    "rest-copy",
    "result-size",
    "size-algebra",
    "size-dimension",
    "size-labels",
    "spread-copy",
    "tsc-type-kind",
    "value-identity",
    "dir-bounded-stmt",
    "dir-cost",
    "dir-function-mark",
    "dir-hot-cold",
    "dir-ignore",
    "dir-ignore-function",
    "explanation-trace",
    "policy-diagnostics",
    "state-knownness",
    "resource-config-graph",
    "resource-effect-scheduling-depth",
    "resource-exhaustion",
    "resource-flow-limit",
    "resource-implementation-files",
    "resource-public-surface",
    "resource-regex-limits",
    "resource-scheduler-budget",
    "resource-specialization-cap",
    "resource-trace-arena",
    "tsc-candidate-cap",
    "definedness",
    "known-value-budget",
    "known-value-declaration",
    "known-value-fold",
    "primitive-length",
    "declared-element-type",
    "declared-kind",
    "declared-primitive",
    "declared-promise",
    "kind-join",
    "receiver-kind",
    "type-container",
    "callee-resolution",
    "class-construction-lineage",
    "name-resolution",
    "surface-and-importers",
    "write-free-and-hoisting",
];

/// Whether `rule` is a ledger rule id.
pub fn is_rule(rule: &str) -> bool {
    RULES.contains(&rule)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DerivationId(pub u32);

/// A side-condition fact a rule application established. The variants are the kinds of
/// `Olint.Fact` in the proof record (`proofs/Olint/Certificate.lean`), which every ledger side
/// condition is stated in.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Fact {
    /// A cost the side condition names.
    Cost(Cost),
    /// A count, index, depth or dimension id.
    Nat(u64),
    /// A variable, property or function name.
    Name(String),
    /// A syntax site.
    Site(SourceSpan),
    /// A decided condition.
    Flag(bool),
    /// The variable `name`, wherever the node's entry reads it, holds a value conforming to the
    /// type annotated at `annotation`.
    Declared {
        name: String,
        annotation: SourceSpan,
    },
}

/// One rule application: the ledger rule, the syntax it concerns, the derivations of its
/// premises, its side-condition facts and the cost it concludes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Derivation {
    pub rule: &'static str,
    pub syntax: SourceSpan,
    pub premises: Vec<DerivationId>,
    pub facts: Vec<Fact>,
    pub cost: Cost,
}

impl Derivation {
    /// The units a new node of this derivation is charged.
    pub fn weight(&self) -> u64 {
        1 + self.premises.len() as u64 + self.facts.len() as u64
    }
}

/// The units the arena admits by default: the scheduler's uniform work limit, so a corpus run
/// reads the arena at its limit exactly when `Event::Derivation` reaches the default limit.
pub const DEFAULT_LIMIT: u64 = 4_000_000;

#[derive(Debug)]
pub struct DerivationArena {
    records: IndexSet<Derivation>,
    limit: u64,
    held: u64,
    charged: u64,
    exhausted: bool,
}

impl Default for DerivationArena {
    fn default() -> Self {
        Self::new(DEFAULT_LIMIT)
    }
}

impl DerivationArena {
    pub fn new(limit: u64) -> Self {
        Self {
            records: IndexSet::new(),
            limit,
            held: 0,
            charged: 0,
            exhausted: false,
        }
    }

    /// Records `derivation`, returning the id of the equal recorded derivation when there is one.
    /// `None` when a premise is not a recorded id or the node's charge exceeds the limit.
    pub fn record(&mut self, derivation: Derivation) -> Option<DerivationId> {
        debug_assert!(
            is_rule(derivation.rule),
            "{} is not a ledger rule",
            derivation.rule
        );

        if let Some(index) = self.records.get_index_of(&derivation) {
            return Some(DerivationId(index as u32));
        }

        if derivation
            .premises
            .iter()
            .any(|premise| premise.0 as usize >= self.records.len())
        {
            return None;
        }

        let weight = derivation.weight();

        if self.records.len() >= u32::MAX as usize || weight > self.limit - self.held {
            self.exhausted = true;

            return None;
        }

        self.held += weight;
        self.charged += weight;

        let (index, _) = self.records.insert_full(derivation);

        Some(DerivationId(index as u32))
    }

    /// Records a rule application with no premises.
    pub fn leaf(
        &mut self,
        rule: &'static str,
        syntax: SourceSpan,
        facts: Vec<Fact>,
        cost: Cost,
    ) -> Option<DerivationId> {
        self.record(Derivation {
            rule,
            syntax,
            premises: Vec::new(),
            facts,
            cost,
        })
    }

    /// Records `rule` concluding `cost` from `premises`, concerning `syntax` or, without it, the syntax of the first
    /// premise. `None` when there is neither.
    pub fn derive(
        &mut self,
        rule: &'static str,
        syntax: Option<SourceSpan>,
        premises: &[DerivationId],
        facts: Vec<Fact>,
        cost: Cost,
    ) -> Option<DerivationId> {
        let syntax = syntax.or_else(|| {
            premises
                .first()
                .and_then(|premise| self.get(*premise))
                .map(|premise| premise.syntax)
        })?;

        self.record(Derivation {
            rule,
            syntax,
            premises: premises.to_vec(),
            facts,
            cost,
        })
    }

    /// Records `rule` concluding `cost` at `syntax` from a part's derivation and cost: a unit cost without derivation
    /// needs no premise, and any other cost without derivation leaves the conclusion underived.
    pub fn over(
        &mut self,
        rule: &'static str,
        syntax: Option<SourceSpan>,
        (premise, premise_cost): (Option<DerivationId>, &Cost),
        facts: Vec<Fact>,
        cost: Cost,
    ) -> Option<DerivationId> {
        match premise {
            Some(premise) => self.derive(rule, syntax, &[premise], facts, cost),
            None if premise_cost.is_one() => self.leaf(rule, syntax?, facts, cost),
            None => None,
        }
    }

    pub fn get(&self, id: DerivationId) -> Option<&Derivation> {
        self.records.get_index(id.0 as usize)
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// The units charged since the scheduler's current generation began.
    pub fn charged(&self) -> u64 {
        self.charged
    }

    /// Whether a record was refused at the limit since the current generation began.
    pub fn exhausted(&self) -> bool {
        self.exhausted
    }

    /// Starts counting charges for a new scheduler generation. Recorded derivations stay, as
    /// explanation traces do, so their memory stays charged against the limit.
    pub(crate) fn begin_generation(&mut self) {
        self.charged = 0;
        self.exhausted = false;
    }
}

#[cfg(test)]
#[path = "derivation.test.rs"]
mod tests;

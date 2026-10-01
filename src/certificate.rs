//! Certificates: a node's derivation as an `Olint.Cert` term over the `lean_syntax` encoding of its function, the
//! record `olint-corpus certify` turns into a theorem the proof record checks (spec §6.4).
//!
//! A certificate is emitted only where every rule application in the derivation has a counterpart in `Olint.Cert`
//! (`proofs/Olint/Certificate.lean`). A rule without a constructor, or one whose constructor fixes a shape the
//! recorded application does not have, leaves the node without a certificate ([`Absence`]) instead of emitting a
//! term the rule's constructor does not mean. The generic constructors of the rules pending their soundness proofs
//! carry the recorded premises at their nodes, the facts and the bound; `check` rejects them until action 5.3 lands
//! their proofs.

use std::collections::{HashMap, HashSet};

use oxc_ast::ast::BindingPattern;
use oxc_span::Span;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::analysis::Analysis;
use crate::declarations::{parameters_of, FunctionId};
use crate::derivation::{DerivationId, Fact};
use crate::lean_syntax::{string, Dimension, EncodeError, FunctionRef, Measure, Scope};
use crate::unknowns::SourceSpan;
use crate::values::{SizeQuantity, ValueId};

/// The longest derivation term a certificate carries, in bytes.
pub const MAXIMUM_TEXT: usize = 1 << 20;

/// A certificate: `theorem c_<sha256> : Bound <program> <node> <bound>` follows from `check` on `derivation`.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CertificateRecord {
    /// SHA-256 of the program, node, derivation and bound texts, each followed by a newline, in lowercase hex.
    pub sha256: String,
    /// The `Olint.Model.Program` of the node's function.
    pub program: String,
    /// The `Olint.Model.Node` the bound concerns: the function's entry over the bound's dimensions, at the node.
    pub node: String,
    /// The `Olint.Cert` term.
    pub derivation: String,
    /// The `Olint.Cost` the derivation concludes.
    pub bound: String,
}

/// Why a node has no certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Absence {
    /// A rule application `Olint.Cert` has no constructor for.
    Unconstructed(&'static str),
    /// A rule application whose constructor fixes a shape the recorded application does not have.
    Unshaped(&'static str),
    /// A derivation the arena does not hold.
    Missing,
    /// A premise or fact concerning syntax outside the node's function.
    Site(SourceSpan),
    /// A dimension the function's entry does not measure as the length of one of its arguments.
    Dimension(u64),
    /// A declared-type fact, which the certificate cannot yet state.
    Declared,
    /// A function or syntax outside the encoded model.
    Encode(EncodeError),
    /// A derivation term longer than [`MAXIMUM_TEXT`].
    Size,
}

/// The ledger rules `Olint.Cert` has no constructor for: `limit-compare`, a comparison rather than a bound, the
/// explanation, diagnostics and knownness rules beside family I, and families K, L and M, whose conclusions enter
/// certificates as facts.
pub const UNCONSTRUCTED: &[&str] = &[
    "limit-compare",
    "explanation-trace",
    "policy-diagnostics",
    "state-knownness",
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

/// The family A rules whose constructors fix their premises' shape: one child certificate per child site
/// (`seqMax`, `branchJoin`), parts checked at the node itself (`channelTotal`), or a single premise at the node
/// (`maxDominance`, `maxNormalise`, `productNormalise`, `exprValidity`). `seq-max` without premises is `seqUnit`,
/// and `channel-total` over parts at its own node is `channelTotal`; every other application of these rules is
/// [`Absence::Unshaped`].
pub const SHAPED: &[&str] = &[
    "seq-max",
    "branch-join",
    "channel-total",
    "max-dominance",
    "max-normalise",
    "product-normalise",
    "expr-validity",
];

/// The `Olint.Cert` constructor name of a rule id: its words in lower camel case.
pub fn constructor_of(rule: &str) -> String {
    let mut name = String::with_capacity(rule.len());
    let mut upper = false;

    for character in rule.chars() {
        match character {
            '-' => upper = true,
            character if upper => {
                name.extend(character.to_uppercase());

                upper = false;
            }
            character => name.push(character),
        }
    }

    name
}

/// Serializes the certificate of the derivation `root` of a node in the function `entry`.
pub fn serialize_certificate(
    analysis: &Analysis<'_, '_>,
    entry: FunctionId,
    root: DerivationId,
) -> Result<CertificateRecord, Absence> {
    Certifier::new(analysis).certify(entry, root)
}

/// Serializes certificates over one analysis, reading its size dimensions once.
pub struct Certifier<'s, 'p, 'a> {
    analysis: &'s Analysis<'p, 'a>,
    dimensions: HashMap<u64, (ValueId, SizeQuantity)>,
}

impl<'s, 'p, 'a> Certifier<'s, 'p, 'a> {
    pub fn new(analysis: &'s Analysis<'p, 'a>) -> Self {
        Self {
            analysis,
            dimensions: analysis
                .values
                .quantity_dimensions()
                .map(|(id, value, quantity)| (id, (value, quantity)))
                .collect(),
        }
    }

    pub fn certify(
        &self,
        entry: FunctionId,
        root: DerivationId,
    ) -> Result<CertificateRecord, Absence> {
        let arena = &self.analysis.traces.derivations;
        let semantic = &self.analysis.project.file(entry.file).semantic;
        let function = FunctionRef {
            semantic,
            node: entry.node,
        };
        let scope = Scope::of(function, &[]).map_err(Absence::Encode)?;
        let order = self.postorder(root)?;
        // Each dimension is renamed to the index of the argument it measures, so the text depends only on the
        // function and the derivation, never on the order the analysis numbered its dimensions in.
        let mut renamed = HashMap::new();
        let mut dimensions = Vec::new();

        for derivation in order.iter().flat_map(|id| arena.get(*id)) {
            let costs = derivation.facts.iter().filter_map(|fact| match fact {
                Fact::Cost(cost) => Some(cost),
                _ => None,
            });

            for cost in std::iter::once(&derivation.cost).chain(costs) {
                for id in cost.dimension_ids() {
                    if let std::collections::hash_map::Entry::Vacant(slot) = renamed.entry(id) {
                        let argument = self.argument(entry, id)?;

                        slot.insert(argument as u64);

                        if !dimensions
                            .iter()
                            .any(|known: &Dimension| known.id == argument as u64)
                        {
                            dimensions.push(Dimension {
                                id: argument as u64,
                                measure: Measure::Arg(argument),
                            });
                        }
                    }
                }
            }
        }

        let entry_text = scope.entry(&dimensions).map_err(Absence::Encode)?;
        let mut terms = Terms {
            scope: &scope,
            entry,
            renamed: &renamed,
            sites: HashMap::new(),
            texts: HashMap::new(),
            uses_entry: false,
        };

        for id in &order {
            let derivation = arena.get(*id).ok_or(Absence::Missing)?;
            let text = terms.term(self.analysis, derivation)?;

            if text.len() > MAXIMUM_TEXT {
                return Err(Absence::Size);
            }

            terms.texts.insert(*id, text);
        }

        let root_derivation = arena.get(root).ok_or(Absence::Missing)?;
        let site = terms.site(root_derivation.syntax)?;
        let cert = terms.texts.remove(&root).ok_or(Absence::Missing)?;
        let derivation = match terms.uses_entry {
            true => format!("(let e : Olint.Model.Entry := {entry_text}; {cert})"),
            false => cert,
        };
        let encoding = scope.encode(&dimensions).map_err(Absence::Encode)?;
        let node = format!("⟨{entry_text}, {site}⟩");
        let bound = terms.cost(&root_derivation.cost);
        let mut hasher = Sha256::new();

        for text in [&encoding.program, &node, &derivation, &bound] {
            hasher.update(text.as_bytes());
            hasher.update(b"\n");
        }

        let sha256 = hasher
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();

        Ok(CertificateRecord {
            sha256,
            program: encoding.program,
            node,
            derivation,
            bound,
        })
    }

    /// The derivations under `root`, each after its premises.
    fn postorder(&self, root: DerivationId) -> Result<Vec<DerivationId>, Absence> {
        let arena = &self.analysis.traces.derivations;
        let mut order = Vec::new();
        let mut seen = HashSet::new();
        let mut pending = vec![(root, false)];

        while let Some((id, expanded)) = pending.pop() {
            if expanded {
                order.push(id);

                continue;
            }

            if !seen.insert(id) {
                continue;
            }

            let derivation = arena.get(id).ok_or(Absence::Missing)?;

            pending.push((id, true));
            pending.extend(
                derivation
                    .premises
                    .iter()
                    .rev()
                    .filter(|premise| !seen.contains(*premise))
                    .map(|premise| (*premise, false)),
            );
        }

        Ok(order)
    }

    /// The argument whose length a size dimension measures: the entry's `k`-th, when the dimension measures the value
    /// of a plain parameter of the entry.
    fn argument(&self, entry: FunctionId, id: u64) -> Result<usize, Absence> {
        let (value, quantity) = self
            .dimensions
            .get(&id)
            .copied()
            .ok_or(Absence::Dimension(id))?;
        let origin = self.analysis.values.origin_of_value(value);
        let parameters = match quantity {
            SizeQuantity::Value => parameters_of(self.analysis.function_at(entry)),
            SizeQuantity::Length | SizeQuantity::Keys => None,
        };
        let argument = parameters.and_then(|parameters| {
            parameters
                .items
                .iter()
                .position(|parameter| match &parameter.pattern {
                    BindingPattern::BindingIdentifier(identifier) => {
                        Some(self.analysis.source_span(entry.file, identifier.span)) == origin
                    }
                    _ => false,
                })
        });

        argument.ok_or(Absence::Dimension(id))
    }
}

/// The terms of one certificate: each derivation's `Olint.Cert` term, and the sites of the syntax it concerns.
struct Terms<'s, 'e, 'a> {
    scope: &'e Scope<'s, 'a>,
    entry: FunctionId,
    /// Each dimension's id in the certificate.
    renamed: &'e HashMap<u64, u64>,
    sites: HashMap<SourceSpan, String>,
    texts: HashMap<DerivationId, String>,
    /// Whether a term names a premise node, whose entry the derivation binds as `e`.
    uses_entry: bool,
}

impl Terms<'_, '_, '_> {
    fn cost(&self, cost: &crate::cost::Cost) -> String {
        cost.lean_with(&|id| self.renamed.get(&id).copied().unwrap_or(id))
    }

    fn site(&mut self, syntax: SourceSpan) -> Result<String, Absence> {
        if let Some(site) = self.sites.get(&syntax) {
            return Ok(site.clone());
        }

        if syntax.file != self.entry.file {
            return Err(Absence::Site(syntax));
        }

        let site = self
            .scope
            .site(Span::new(syntax.start, syntax.end))
            .map_err(Absence::Encode)?
            .ok_or(Absence::Site(syntax))?;

        self.sites.insert(syntax, site.clone());

        Ok(site)
    }

    fn premise(&self, id: DerivationId) -> Result<&str, Absence> {
        self.texts
            .get(&id)
            .map(String::as_str)
            .ok_or(Absence::Missing)
    }

    fn term(
        &mut self,
        analysis: &Analysis<'_, '_>,
        derivation: &crate::derivation::Derivation,
    ) -> Result<String, Absence> {
        let rule = derivation.rule;
        let arena = &analysis.traces.derivations;

        if UNCONSTRUCTED.contains(&rule) {
            return Err(Absence::Unconstructed(rule));
        }

        match rule {
            "seq-max"
                if derivation.premises.is_empty()
                    && derivation.facts.is_empty()
                    && derivation.cost.is_one() =>
            {
                return Ok(".seqUnit".to_string());
            }
            "channel-total"
                if derivation.facts.is_empty()
                    && derivation.premises.iter().all(|premise| {
                        arena
                            .get(*premise)
                            .is_some_and(|premise| premise.syntax == derivation.syntax)
                    }) =>
            {
                let parts = derivation
                    .premises
                    .iter()
                    .map(|premise| {
                        Ok(format!(
                            "([.normal, .ret, .brk, .cont], {})",
                            self.premise(*premise)?
                        ))
                    })
                    .collect::<Result<Vec<_>, Absence>>()?;

                return Ok(format!("(.channelTotal [{}])", parts.join(", ")));
            }
            rule if SHAPED.contains(&rule) => return Err(Absence::Unshaped(rule)),
            _ => {}
        }

        let mut premises = Vec::with_capacity(derivation.premises.len());

        for premise in &derivation.premises {
            let syntax = arena.get(*premise).ok_or(Absence::Missing)?.syntax;
            let site = self.site(syntax)?;

            premises.push(format!("(⟨e, {site}⟩, {})", self.premise(*premise)?));
        }

        self.uses_entry |= !premises.is_empty();

        let mut facts = Vec::with_capacity(derivation.facts.len());

        for fact in &derivation.facts {
            facts.push(match fact {
                Fact::Cost(cost) => format!(".cost ({})", self.cost(cost)),
                Fact::Nat(value) => format!(".nat {value}"),
                Fact::Name(name) => format!(".name {}", string(name)),
                Fact::Site(syntax) => format!(".site ({})", self.site(*syntax)?),
                Fact::Flag(flag) => format!(".flag {flag}"),
                Fact::Declared { .. } => return Err(Absence::Declared),
            });
        }

        Ok(format!(
            "(.{} [{}] [{}] ({}))",
            constructor_of(rule),
            premises.join(", "),
            facts.join(", "),
            self.cost(&derivation.cost)
        ))
    }
}

#[cfg(test)]
#[path = "certificate.test.rs"]
mod tests;

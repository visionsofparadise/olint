//! Certificates: a node's derivation as an `Olint.Cert` term over the `lean_syntax` encoding of its function, the
//! record `olint-corpus certify` turns into a theorem the proof record checks (spec §6.4).
//!
//! A certificate is emitted only where every rule application in the derivation has a counterpart in `Olint.Cert`
//! (`proofs/Olint/Certificate.lean`). A rule without a constructor, or one whose constructor fixes a shape the
//! recorded application does not have, leaves the node without a certificate ([`Absence`]) instead of emitting a
//! term the rule's constructor does not mean. The generic constructors of the rules pending their soundness proofs
//! carry the recorded premises at their nodes, the facts and the bound; `check` rejects them until action 5.3 lands
//! their proofs.
//!
//! olint joins parts pairwise (`Part::max`), recording each join as `max-dominance` or `max-normalise` at its first
//! part's syntax, and a reading's channels by `channel-total`. A join of parts at different nodes is no rule
//! application at a node of its own, so a certificate holds the parts it joins in its place ([`leaves`]): a
//! `seq-max` or `branch-join` at a node is `seqMax` or `branchJoin` over one certificate per child site
//! (`Olint.Rules.seqSites`, `Olint.Rules.branchSites`), each joined part at its child's site and `seqUnit` at every
//! child without one, concluded at the node's cost by `maxNormalise` or `maxDominance`; a generic constructor's
//! premises are the joined parts at their own nodes. Every term concludes its derivation's cost.

use std::collections::{HashMap, HashSet, VecDeque};

use oxc_ast::ast::BindingPattern;
use oxc_span::Span;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::analysis::Analysis;
use crate::cost::Cost;
use crate::declarations::{parameters_of, FunctionId};
use crate::derivation::{Derivation, DerivationArena, DerivationId, Fact};
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
/// (`maxDominance`, `maxNormalise`, `productNormalise`, `exprValidity`). `seq-max` without premises is `seqUnit`, or
/// one `seqUnit` per child at the entry or a branch; `seq-max` and `branch-join` over premises are `seqMax` and
/// `branchJoin` over the parts their joins combine, where those parts lie at the node's children; `channel-total`
/// over parts at its own node is `channelTotal`; `max-dominance`, `max-normalise` and `channel-total` over parts at
/// other nodes are joins a certificate holds the parts of. Every other application of these rules is
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
        let mut terms = Terms {
            arena,
            scope: &scope,
            entry,
            renamed: HashMap::new(),
            sites: HashMap::new(),
            shapes: HashMap::new(),
            texts: HashMap::new(),
            uses_entry: false,
        };
        let order = terms.postorder(root)?;
        // Each dimension is renamed to the index of the argument it measures, so the text depends only on the
        // function and the derivation, never on the order the analysis numbered its dimensions in.
        let mut dimensions = Vec::new();

        for derivation in order.iter().flat_map(|id| arena.get(*id)) {
            let costs = derivation.facts.iter().filter_map(|fact| match fact {
                Fact::Cost(cost) => Some(cost),
                _ => None,
            });

            for cost in std::iter::once(&derivation.cost).chain(costs) {
                for id in cost.dimension_ids() {
                    if let std::collections::hash_map::Entry::Vacant(slot) = terms.renamed.entry(id)
                    {
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

        for id in &order {
            let text = terms.term(*id)?;

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

/// How a derivation's term reads its premises.
enum Shape {
    /// `seqUnit`: `seq-max` without premises at a unit cost.
    Unit,
    /// `seqMax` or `branchJoin`: one certificate per child site, the premises' join leaves at their children's sites
    /// and `seqUnit` at every other child, concluded at the derivation's cost.
    Composed { branch: bool, sites: Vec<String> },
    /// The term of the one premise, a bound at the node by the derivation's cost: `seq-max` or `branch-join` passing a
    /// part derived at the node itself through unchanged.
    Same,
    /// `channelTotal`: the premises at the node, each bounding every channel, concluded at the derivation's cost.
    Total,
    /// A rule pending its soundness proof: the premises' join leaves at their nodes, the facts and the bound.
    Generic,
}

/// The terms of one certificate: each derivation's `Olint.Cert` term, and the sites of the syntax it concerns.
struct Terms<'s, 'e, 'a> {
    arena: &'e DerivationArena,
    scope: &'e Scope<'s, 'a>,
    entry: FunctionId,
    /// Each dimension's id in the certificate.
    renamed: HashMap<u64, u64>,
    sites: HashMap<SourceSpan, String>,
    /// Each derivation's shape and the derivations its term holds the terms of.
    shapes: HashMap<DerivationId, (Shape, Vec<DerivationId>)>,
    texts: HashMap<DerivationId, String>,
    /// Whether a term names a premise node, whose entry the derivation binds as `e`.
    uses_entry: bool,
}

impl Terms<'_, '_, '_> {
    fn cost(&self, cost: &Cost) -> String {
        cost.lean_with(&|id| self.renamed.get(&id).copied().unwrap_or(id))
    }

    fn derivation(&self, id: DerivationId) -> Result<&Derivation, Absence> {
        self.arena.get(id).ok_or(Absence::Missing)
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

    /// The derivations whose terms the certificate holds, each after those its term holds, with their shapes.
    fn postorder(&mut self, root: DerivationId) -> Result<Vec<DerivationId>, Absence> {
        let mut order = Vec::new();
        let mut pending = vec![(root, false)];

        while let Some((id, expanded)) = pending.pop() {
            if expanded {
                order.push(id);

                continue;
            }

            if self.shapes.contains_key(&id) {
                continue;
            }

            let shaped = self.shape(id)?;
            let held = shaped.1.clone();

            self.shapes.insert(id, shaped);
            pending.push((id, true));
            pending.extend(
                held.into_iter()
                    .rev()
                    .filter(|premise| !self.shapes.contains_key(premise))
                    .map(|premise| (premise, false)),
            );
        }

        Ok(order)
    }

    /// A derivation's shape and the derivations its term holds the terms of.
    fn shape(&mut self, id: DerivationId) -> Result<(Shape, Vec<DerivationId>), Absence> {
        let derivation = self.derivation(id)?;
        let rule = derivation.rule;

        if UNCONSTRUCTED.contains(&rule) {
            return Err(Absence::Unconstructed(rule));
        }

        if is_join(self.arena, derivation) {
            return Err(Absence::Unshaped(rule));
        }

        match rule {
            "seq-max"
                if derivation.premises.is_empty()
                    && derivation.facts.is_empty()
                    && derivation.cost.is_one() =>
            {
                // `seqUnit` holds at statements alone; at the entry or a branch, the unit base is one `seqUnit` per child.
                let syntax = derivation.syntax;
                let children = match syntax.file == self.entry.file {
                    true => self
                        .scope
                        .children(Span::new(syntax.start, syntax.end))
                        .map_err(Absence::Encode)?
                        .filter(|children| children.branch || children.body.is_some()),
                    false => None,
                };

                Ok(match children {
                    Some(children) => (
                        Shape::Composed {
                            branch: children.branch,
                            sites: children.sites,
                        },
                        Vec::new(),
                    ),
                    None => (Shape::Unit, Vec::new()),
                })
            }
            "seq-max" | "branch-join"
                if derivation.facts.is_empty()
                    && matches!(derivation.premises.as_slice(), [premise] if self
                        .arena
                        .get(*premise)
                        .is_some_and(|premise| premise.syntax == derivation.syntax && premise.cost == derivation.cost)) =>
            {
                Ok((Shape::Same, derivation.premises.clone()))
            }
            "seq-max" | "branch-join" if derivation.facts.is_empty() => {
                let syntax = derivation.syntax;
                let premises = derivation.premises.clone();

                if syntax.file != self.entry.file {
                    return Err(Absence::Site(syntax));
                }

                let children = self
                    .scope
                    .children(Span::new(syntax.start, syntax.end))
                    .map_err(Absence::Encode)?
                    .filter(|children| children.branch == (rule == "branch-join"))
                    .ok_or(Absence::Unshaped(rule))?;
                let body = children.body.map(|body| SourceSpan {
                    file: syntax.file,
                    start: body.start,
                    end: body.end,
                });
                let leaves = leaves(self.arena, &premises, body)?;

                Ok((
                    Shape::Composed {
                        branch: children.branch,
                        sites: children.sites,
                    },
                    leaves,
                ))
            }
            // `channel-total` over parts at other nodes is a join (`is_join`).
            "channel-total" if derivation.facts.is_empty() => {
                Ok((Shape::Total, derivation.premises.clone()))
            }
            rule if SHAPED.contains(&rule) => Err(Absence::Unshaped(rule)),
            _ => Ok((
                Shape::Generic,
                leaves(self.arena, &derivation.premises, None)?,
            )),
        }
    }

    /// The term of a derivation whose held terms are in `texts`.
    fn term(&mut self, id: DerivationId) -> Result<String, Absence> {
        let arena = self.arena;
        let get = |id: DerivationId| arena.get(id).ok_or(Absence::Missing);
        let derivation = get(id)?;
        let (shape, held) = self.shapes.remove(&id).ok_or(Absence::Missing)?;

        match shape {
            Shape::Unit => Ok(".seqUnit".to_string()),
            Shape::Same => Ok(self.held(held[0])?.to_string()),
            Shape::Composed { branch, sites } => {
                // Each leaf fills the first unfilled child of its site: children with equal sites are one structural
                // site, which the leaf bounds whichever of them it concerns.
                let mut filled: Vec<Option<DerivationId>> = vec![None; sites.len()];
                let mut unfilled: HashMap<&str, VecDeque<usize>> = HashMap::new();

                for (index, site) in sites.iter().enumerate() {
                    unfilled.entry(site.as_str()).or_default().push_back(index);
                }

                for leaf in &held {
                    let site = self.site(get(*leaf)?.syntax)?;
                    let slot = unfilled
                        .get_mut(site.as_str())
                        .and_then(|slots| slots.pop_front())
                        .ok_or(Absence::Unshaped(derivation.rule))?;

                    filled[slot] = Some(*leaf);
                }

                let mut children = Vec::with_capacity(filled.len());
                let mut costs = Vec::with_capacity(filled.len());

                for slot in filled {
                    match slot {
                        Some(leaf) => {
                            children.push(self.held(leaf)?.to_string());
                            costs.push(get(leaf)?.cost.clone());
                        }
                        None => {
                            children.push(".seqUnit".to_string());
                            costs.push(Cost::ONE);
                        }
                    }
                }

                let constructor = match branch {
                    true => "branchJoin",
                    false => "seqMax",
                };
                let term = format!("(.{constructor} [{}])", children.join(", "));

                Ok(self.concluded(term, &costs, &derivation.cost))
            }
            Shape::Total => {
                let mut parts = Vec::with_capacity(held.len());
                let mut costs = Vec::with_capacity(held.len());

                for premise in &held {
                    parts.push(format!(
                        "([.normal, .ret, .brk, .cont], {})",
                        self.held(*premise)?
                    ));
                    costs.push(get(*premise)?.cost.clone());
                }

                let term = format!("(.channelTotal [{}])", parts.join(", "));

                Ok(self.concluded(term, &costs, &derivation.cost))
            }
            Shape::Generic => {
                let mut premises = Vec::with_capacity(held.len());

                for premise in &held {
                    let site = self.site(get(*premise)?.syntax)?;

                    premises.push(format!("(⟨e, {site}⟩, {})", self.held(*premise)?));
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
                    constructor_of(derivation.rule),
                    premises.join(", "),
                    facts.join(", "),
                    self.cost(&derivation.cost)
                ))
            }
        }
    }

    fn held(&self, id: DerivationId) -> Result<&str, Absence> {
        self.texts
            .get(&id)
            .map(String::as_str)
            .ok_or(Absence::Missing)
    }

    /// `term`, which concludes the maximum of `costs`, concluding `target` instead: by `max-normalise` when every
    /// flattened term of that maximum is `0` or at most a flattened term of `target` (`Olint.Rules.maxCovers`), else by
    /// `max-dominance`, which drops the terms `O` of a kept one (`Olint.Rules.dominated`).
    fn concluded(&self, term: String, costs: &[Cost], target: &Cost) -> String {
        let maximum = format!(
            ".maximum [{}]",
            costs
                .iter()
                .map(|cost| self.cost(cost))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let target_text = self.cost(target);

        if maximum == target_text {
            return term;
        }

        let targets: Vec<(String, Option<u64>)> = target
            .maximum_terms()
            .iter()
            .map(|term| (self.cost(term), term.constant_of()))
            .collect();
        let covers = costs.iter().flat_map(Cost::maximum_terms).all(|term| {
            let (text, constant) = (self.cost(&term), term.constant_of());

            constant == Some(0) || targets.iter().any(|(target, bound)| {
                *target == text
                    || matches!((constant, bound), (Some(value), Some(bound)) if value <= *bound)
            })
        });
        let rule = match covers {
            true => "maxNormalise",
            false => "maxDominance",
        };

        format!("(.{rule} {term} ({target_text}))")
    }
}

/// Whether a derivation is a join of parts at other nodes rather than a rule application at its own: `max-dominance`
/// and `max-normalise` (`Part::max`), which record their first part's syntax, and `channel-total` over parts at
/// different nodes.
fn is_join(arena: &DerivationArena, derivation: &Derivation) -> bool {
    derivation.facts.is_empty()
        && match derivation.rule {
            "max-dominance" | "max-normalise" => true,
            "channel-total" => !derivation.premises.iter().all(|premise| {
                arena
                    .get(*premise)
                    .is_some_and(|premise| premise.syntax == derivation.syntax)
            }),
            _ => false,
        }
}

/// The parts the joins under `premises` combine, each once, in order: a premise that is a join (`is_join`) stands for
/// its own premises' parts, as does `seq-max` at `body`, the entry's function body.
fn leaves(
    arena: &DerivationArena,
    premises: &[DerivationId],
    body: Option<SourceSpan>,
) -> Result<Vec<DerivationId>, Absence> {
    let mut leaves = Vec::new();
    let mut seen = HashSet::new();
    let mut pending: Vec<DerivationId> = premises.iter().rev().copied().collect();

    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }

        let derivation = arena.get(id).ok_or(Absence::Missing)?;
        let transparent = is_join(arena, derivation)
            || (derivation.rule == "seq-max"
                && derivation.facts.is_empty()
                && Some(derivation.syntax) == body);

        match transparent {
            true => pending.extend(derivation.premises.iter().rev()),
            false => leaves.push(id),
        }
    }

    Ok(leaves)
}

#[cfg(test)]
#[path = "certificate.test.rs"]
mod tests;

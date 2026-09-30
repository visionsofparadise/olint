import Olint.Rules.Algebra

/-!
# Certificates

A certificate is a derivation in olint's proof rules: one `Cert` constructor per bound-producing
rule of the Phase 2 ledger (`corpus/ledger.json`, families A to J), carrying its premises, its
side-condition facts, and, through the node it is checked at, the syntax it concerns. Families
K, L and M (knownness, declared types and resolution) provide facts other rules consume, not
bounds, so they have no constructor: their conclusions enter certificates as `Fact`s, which the
consuming rule's soundness theorem justifies (`Fact.holds`).

`check p n xs c` is a structural recursion over `c` using only `Bool`, `ℕ` and structural
recursions over `Cost` and the syntax, so `decide` evaluates it by kernel reduction on a
concrete certificate. Cost comparisons inside `check` never touch `ℝ`: they are the decidable
orders of `Olint.Rules.Algebra` (`Cost.beq`, `valid`, `within`, `maxCovers`, `prodMatches`),
each proven sound there with respect to `Cost.eval` on every admitted instance of the entry.
`check` rejects:

* an entry that is not well formed (`Olint.Model.Entry.wf`): a dimension measuring an argument
  outside the parameters or of a type without a measured length, a dimension over a variable
  outside the entry's scope, two dimensions with one id or one measured quantity, a scope
  naming a variable twice or naming a program definition, or an object type naming a field
  twice. Every well-formed entry admits an instance at every valuation of its dimensions
  (`Olint.Model.Admitted.exists`), so no accepted certificate's bound holds vacuously;
* a concluded bound that mentions a dimension the entry does not measure, the legacy envelope
  `N`, `log N` or `N log N`, or an unbound name (`measured`);
* a derivation relying on an intrinsic outside `xs` (`Cert.reliance`).

A composing rule (`seqMax`, `branchJoin`) carries one child certificate per child of its node,
in syntax order; each child is checked at the child node, whose site `check` computes from the
parent's syntax, so a child certificate concerns exactly the syntax it bounds.

`check_sound` turns a checked certificate into the bound `costOf c` in every world `W` whose
analysed program modifies none of the intrinsics `xs` (`NoReplacement W xs`, §2.2). That premise
is part of every certificate theorem's statement; olint discharges it with its
intrinsic-replacement scan (family G, `intrinsic-replacement-scan`, certified in Phase 5). The
theorem quantifies over the world's spec-internal step costs `W.ops` too, so it rests on no G52
draft; a family whose soundness needs the drafts adds the premise `W.ops = SpecOps.draft`, which
`scripts/axioms.lean` reports as pending Matt's signature (§2.1, §6.3). A generated certificate
theorem passes the derivation explicitly, since `costOf` does not determine it:

```lean
theorem c_<sha256> (W : World) (hW : NoReplacement W <xs>) : Bound W <program> <node> <bound> :=
  check_sound W <xs> _ _ <derivation> hW (by decide)
```

Family A: `seq-max` (with its unit base), `branch-join`, `channel-total`, `max-dominance`,
`max-normalise`, `product-normalise` and `expr-validity` are checked and proven; `seq-max`,
`branch-join` and `channel-total` compose their child certificates. `limit-compare` is a
comparison, not a bound producer: `Olint.Rules.limitCompare_sound` and
`Olint.Rules.Bound.of_within` state it. `nest-product`, `partial-bind-known` and
`preference-rank` are pending their soundness proofs. Every rule without a proof, in family A
and in families B to J, is declared with generic fields (premises at their nodes, facts, bound)
and `check` rejects it until its soundness proof lands (action 5.3), so its `check_sound` case
is unreachable.
-/

namespace Olint

open Olint.Model Olint.Rules

/-- A side-condition fact a rule records. Families B to J refine these as their soundness
proofs land. -/
inductive Fact where
  /-- A cost the side condition names. -/
  | cost (c : Cost)
  /-- A count, index, depth or dimension id. -/
  | nat (k : ℕ)
  /-- A variable, property or function name. -/
  | name (x : Name)
  /-- A syntax site. -/
  | site (s : Site)
  /-- A decided condition. -/
  | flag (b : Bool)
  /-- A declared-type fact (ledger gap G51): the variable `x`, wherever the node's entry reads
  it, holds a value conforming to `τ`. `Fact.holds` justifies it from the encoded syntax by
  name resolution recomputed in Lean (`bindingTypes`): every binding of `x` the entry's runs
  can create is declared `τ`, so every read of `x` that completes returns a value conforming
  to `τ`: §2.5 is checked at every variable read (`Olint.Model.readVar`), and a read of a
  non-conforming value aborts the run. A rule that consumes the fact proves that consequence
  with its soundness theorem. -/
  | declared (x : Name) (τ : Ty)

/-- A derivation in olint's proof rules, concerning the node it is checked at. -/
inductive Cert where
  /-- `seq-max`, unit base (walker.rs:497, walker.rs:675): the node's statement lies in the
  state-independent fragment `unitStmt`, or the node is a literal, so its cost is `1`. -/
  | seqUnit
  /-- `seq-max` (cost.rs:2032-2056, walker.rs:675-737): the node runs its children in sequence,
  each at most once (`Olint.Rules.seqSites`: an entry's body, a block's statements, the
  expression of an expression statement, initialised declaration or `return`); from one
  certificate per child, a bound by the maximum of the children's bounds. -/
  | seqMax (children : List Cert)
  /-- `channel-total` (cost.rs:2101-2126): from bounds of the node on channel sets that cover
  every channel, each part's certificate bounding every channel of its set, a bound by the
  maximum of the parts' bounds. -/
  | channelTotal (parts : List (List Channel × Cert))
  /-- `branch-join` (walker.rs:497-566): the node is an `if` or a conditional expression
  (`Olint.Rules.branchSites`); from certificates for the test and each branch, in syntax order,
  a bound by their maximum. An absent `else` is the empty branch. -/
  | branchJoin (children : List Cert)
  /-- `max-dominance` (cost.rs:1824-1849): drop from a maximum the terms `within` a kept term. -/
  | maxDominance (premise : Cert) (target : Cost)
  /-- `max-normalise` (cost.rs:1004-1039): flatten nested maxima, fold constants, dedup. -/
  | maxNormalise (premise : Cert) (target : Cost)
  /-- `product-normalise` (cost.rs:278-381): flatten products, fold constants, group equal
  factors into powers, and reorder. -/
  | productNormalise (premise : Cert) (target : Cost)
  /-- `expr-validity` (cost.rs:383-475): the premise's cost is valid. -/
  | exprValidity (premise : Cert)
  /-- `nest-product` (family A, src/cost.rs:2150-2191); pending its soundness proof. -/
  | nestProduct (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `partial-bind-known` (family A, src/cost.rs:124-156); pending its soundness proof. -/
  | partialBindKnown (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `preference-rank` (family A, src/cost.rs:1788-1798); pending its soundness proof. -/
  | preferenceRank (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-additive` (family B, src/bounds.rs:934-1007); pending its soundness proof. -/
  | boundAdditive (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-best-of` (family B, src/bounds.rs:390-417); pending its soundness proof. -/
  | boundBestOf (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-bisection` (family B, src/bounds.rs:1688-1918); pending its soundness proof. -/
  | boundBisection (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-constant-collection` (family B, src/bounds.rs:314-315); pending its soundness proof. -/
  | boundConstantCollection (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-constant-distance` (family B, src/bounds.rs:997-1000); pending its soundness proof. -/
  | boundConstantDistance (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-directive` (family B, src/bounds.rs:271-275); pending its soundness proof. -/
  | boundDirective (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-exact-additive` (family B, src/bounds.rs:1009-1058); pending its soundness proof. -/
  | boundExactAdditive (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-false-condition` (family B, src/bounds.rs:396-398); pending its soundness proof. -/
  | boundFalseCondition (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-for-in` (family B, src/bounds.rs:325-333); pending its soundness proof. -/
  | boundForIn (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-for-of-native` (family B, src/bounds.rs:286-323); pending its soundness proof. -/
  | boundForOfNative (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-geometric` (family B, src/bounds.rs:851-932); pending its soundness proof. -/
  | boundGeometric (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-iterator-visits` (family B, src/bounds.rs:293-298); pending its soundness proof. -/
  | boundIteratorVisits (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-linear-default` (family B, src/bounds.rs:277-279); pending its soundness proof. -/
  | boundLinearDefault (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-live-visits` (family B, src/bounds.rs:300-312); pending its soundness proof. -/
  | boundLiveVisits (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-progression` (family B, src/bounds.rs:472-633); pending its soundness proof. -/
  | boundProgression (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-quantity` (family B, src/bounds.rs:1060-1501); pending its soundness proof. -/
  | boundQuantity (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-share` (family B, src/bounds.rs:316-317); pending its soundness proof. -/
  | boundShare (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `bound-single-iteration` (family B, src/bounds.rs:281-283); pending its soundness proof. -/
  | boundSingleIteration (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `for-of-produced-length` (family B, src/walker.rs:1393-1413); pending its soundness proof. -/
  | forOfProducedLength (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-effect-invalidation` (family B, src/effects.rs:808-866); pending its soundness proof. -/
  | loopEffectInvalidation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-nest` (family B, src/walker.rs:1622-1657); pending its soundness proof. -/
  | loopNest (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-phases` (family B, src/walker.rs:1336-1378); pending its soundness proof. -/
  | loopPhases (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-suspension` (family B, src/walker.rs:1444-1445); pending its soundness proof. -/
  | loopSuspension (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-unbounded` (family B, src/walker.rs:1577-1606); pending its soundness proof. -/
  | loopUnbounded (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `loop-unit` (family B, src/walker.rs:1608-1620); pending its soundness proof. -/
  | loopUnit (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `budget-cancel` (family C, src/walker.rs:1415-1420); pending its soundness proof. -/
  | budgetCancel (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `budget-collect` (family C, src/budgets.rs:337-450); pending its soundness proof. -/
  | budgetCollect (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `budget-share` (family C, src/walker.rs:1415-1435); pending its soundness proof. -/
  | budgetShare (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `hoisted-join` (family C, src/walker.rs:1489-1499); pending its soundness proof. -/
  | hoistedJoin (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `share-sized-operation` (family C, src/walker.rs:2071-2104); pending its soundness proof. -/
  | shareSizedOperation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `escape-absorb` (family D, src/walker.rs:896-925); pending its soundness proof. -/
  | escapeAbsorb (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `escape-depth-exhausted` (family D, src/walker.rs:1120-1124); pending its soundness proof. -/
  | escapeDepthExhausted (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `escape-lift` (family D, src/walker.rs:1255-1305); pending its soundness proof. -/
  | escapeLift (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `flow-completion` (family D, src/flow.rs:1284-1356); pending its soundness proof. -/
  | flowCompletion (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `flow-graph` (family D, src/flow.rs:123-169); pending its soundness proof. -/
  | flowGraph (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `async-assimilation` (family E, src/invocations.rs:2608-2739); pending its soundness proof. -/
  | asyncAssimilation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `await-continuation` (family E, src/walker.rs:689-757); pending its soundness proof. -/
  | awaitContinuation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-callback-parameter` (family E, src/summaries.rs:3292-3380); pending its soundness proof. -/
  | callCallbackParameter (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-effects-transfer` (family E, src/summaries.rs:4157-4304); pending its soundness proof. -/
  | callEffectsTransfer (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-fallback` (family E, src/summaries.rs:4345-4430); pending its soundness proof. -/
  | callFallback (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-lazy-phase` (family E, src/summaries.rs:3651-3689); pending its soundness proof. -/
  | callLazyPhase (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-open-remainder` (family E, src/walker.rs:2519-2544); pending its soundness proof. -/
  | callOpenRemainder (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-returned-function` (family E, src/walker.rs:2592-2635); pending its soundness proof. -/
  | callReturnedFunction (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `call-summary` (family E, src/summaries.rs:3691-3828); pending its soundness proof. -/
  | callSummary (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `construction-fields` (family E, src/summaries.rs:2526-2737); pending its soundness proof. -/
  | constructionFields (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `constructor-call` (family E, src/walker.rs:1967-2046); pending its soundness proof. -/
  | constructorCall (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `implicit-invocation` (family E, src/invocations.rs:246-321); pending its soundness proof. -/
  | implicitInvocation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `iterator-visits` (family E, src/invocations.rs:743-775); pending its soundness proof. -/
  | iteratorVisits (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `latent-production` (family E, src/summaries.rs:4854-4972); pending its soundness proof. -/
  | latentProduction (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `lazy-consume` (family E, src/summaries.rs:5519-5577); pending its soundness proof. -/
  | lazyConsume (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `returned-function-facts` (family E, src/summaries.rs:4053-4155); pending its soundness proof. -/
  | returnedFunctionFacts (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `size-substitution` (family E, src/summaries.rs:463-550); pending its soundness proof. -/
  | sizeSubstitution (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `target-resolution` (family E, src/value_targets.rs:593-683); pending its soundness proof. -/
  | targetResolution (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `tsc-callee-targets` (family E, src/types.rs:139-308); pending its soundness proof. -/
  | tscCalleeTargets (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-branching-decrement` (family F, src/recurrences.rs:313-404); pending its soundness proof. -/
  | recBranchingDecrement (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-chain-decrement` (family F, src/recurrences.rs:221-311); pending its soundness proof. -/
  | recChainDecrement (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-chain-division` (family F, src/recurrences.rs:267-311); pending its soundness proof. -/
  | recChainDivision (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-factorial` (family F, src/recurrences.rs:354-365); pending its soundness proof. -/
  | recFactorial (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-forget-multiplicity` (family F, src/recurrences.rs:442-449); pending its soundness proof. -/
  | recForgetMultiplicity (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-guard` (family F, src/recurrences.rs:145-170); pending its soundness proof. -/
  | recGuard (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-markers` (family F, src/summaries.rs:1979-2046); pending its soundness proof. -/
  | recMarkers (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-measure` (family F, src/recurrences.rs:407-440); pending its soundness proof. -/
  | recMeasure (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-reduced-measure-size` (family F, src/recurrences.rs:451-475); pending its soundness proof. -/
  | recReducedMeasureSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-relation` (family F, src/recurrences.rs:477-529); pending its soundness proof. -/
  | recRelation (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-relation-join` (family F, src/recurrences.rs:116-143); pending its soundness proof. -/
  | recRelationJoin (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rec-unsolved` (family F, src/recurrences.rs:227-265); pending its soundness proof. -/
  | recUnsolved (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `array-method` (family G, src/walker.rs:2704-2765); pending its soundness proof. -/
  | arrayMethod (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `intrinsic-replacement-scan` (family G, src/value_targets.rs:32); pending its soundness proof. -/
  | intrinsicReplacementScan (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `linear-constructor` (family G, src/walker.rs:2064-2105); pending its soundness proof. -/
  | linearConstructor (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `native-callback` (family G, src/native.rs:1450-1474); pending its soundness proof. -/
  | nativeCallback (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `native-charge-length` (family G, src/native.rs:1300-1341); pending its soundness proof. -/
  | nativeChargeLength (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `native-model` (family G, src/native.rs:185-551); pending its soundness proof. -/
  | nativeModel (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `native-visit-budget` (family G, src/native.rs:832-841); pending its soundness proof. -/
  | nativeVisitBudget (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `regex-cost` (family G, src/regex.rs:154-176); pending its soundness proof. -/
  | regexCost (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `regex-every-match` (family G, src/regex.rs:126-152); pending its soundness proof. -/
  | regexEveryMatch (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `regex-matched-once` (family G, src/regex.rs:99-124); pending its soundness proof. -/
  | regexMatchedOnce (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `set-map-linear` (family G, src/walker.rs:2767-2786); pending its soundness proof. -/
  | setMapLinear (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `unmodelled-native` (family G, src/walker.rs:2640-2667); pending its soundness proof. -/
  | unmodelledNative (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `argument-facts` (family H, src/summaries.rs:2787-3052); pending its soundness proof. -/
  | argumentFacts (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `array-method-size` (family H, src/values.rs:96-107); pending its soundness proof. -/
  | arrayMethodSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `constant-cardinality` (family H, src/value_sizes.rs:303-329); pending its soundness proof. -/
  | constantCardinality (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `count-of` (family H, src/values.rs:1225-1242); pending its soundness proof. -/
  | countOf (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `growth-sites` (family H, src/value_sizes.rs:680-783); pending its soundness proof. -/
  | growthSites (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `holder-stability` (family H, src/value_sizes.rs:813-835); pending its soundness proof. -/
  | holderStability (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `input-size-envelope` (family H, src/values.rs:142-150); pending its soundness proof. -/
  | inputSizeEnvelope (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `iterable-size` (family H, src/values.rs:973-997); pending its soundness proof. -/
  | iterableSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `parameter-size` (family H, src/values.rs:1305-1319); pending its soundness proof. -/
  | parameterSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `produced-size` (family H, src/values.rs:999-1013); pending its soundness proof. -/
  | producedSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `rest-copy` (family H, src/walker.rs:1785-1882); pending its soundness proof. -/
  | restCopy (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `result-size` (family H, src/values.rs:1244-1303); pending its soundness proof. -/
  | resultSize (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `size-algebra` (family H, src/values.rs:86-92); pending its soundness proof. -/
  | sizeAlgebra (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `size-dimension` (family H, src/values.rs:326-340); pending its soundness proof. -/
  | sizeDimension (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `size-labels` (family H, src/values.rs:342-380); pending its soundness proof. -/
  | sizeLabels (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `spread-copy` (family H, src/walker.rs:1785-1882); pending its soundness proof. -/
  | spreadCopy (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `tsc-type-kind` (family H, src/types.rs:78-101); pending its soundness proof. -/
  | tscTypeKind (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `value-identity` (family H, src/values.rs:382-475); pending its soundness proof. -/
  | valueIdentity (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-bounded-stmt` (family I, src/walker.rs:433-439); pending its soundness proof. -/
  | dirBoundedStmt (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-cost` (family I, src/summaries.rs:2387-2443); pending its soundness proof. -/
  | dirCost (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-function-mark` (family I, src/summaries.rs:3441-3473); pending its soundness proof. -/
  | dirFunctionMark (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-hot-cold` (family I, src/cost.rs:1788-1863); pending its soundness proof. -/
  | dirHotCold (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-ignore` (family I, src/walker.rs:385-391); pending its soundness proof. -/
  | dirIgnore (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `dir-ignore-function` (family I, src/summaries.rs:2376-2385); pending its soundness proof. -/
  | dirIgnoreFunction (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-config-graph` (family J, src/tsconfig.rs:101-106); pending its soundness proof. -/
  | resourceConfigGraph (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-effect-scheduling-depth` (family J, src/effects.rs:1525-1581); pending its soundness proof. -/
  | resourceEffectSchedulingDepth (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-exhaustion` (family J, src/summaries.rs:1022-1032); pending its soundness proof. -/
  | resourceExhaustion (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-flow-limit` (family J, src/project.rs:88-112); pending its soundness proof. -/
  | resourceFlowLimit (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-implementation-files` (family J, src/project.rs:187-194); pending its soundness proof. -/
  | resourceImplementationFiles (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-public-surface` (family J, src/public_surface.rs:79); pending its soundness proof. -/
  | resourcePublicSurface (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-regex-limits` (family J, src/regex.rs:56-77); pending its soundness proof. -/
  | resourceRegexLimits (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-scheduler-budget` (family J, src/summaries.rs:263-280); pending its soundness proof. -/
  | resourceSchedulerBudget (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-specialization-cap` (family J, src/summaries.rs:277); pending its soundness proof. -/
  | resourceSpecializationCap (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `resource-trace-arena` (family J, src/trace.rs:37-55); pending its soundness proof. -/
  | resourceTraceArena (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)
  /-- `tsc-candidate-cap` (family J, src/tsc_sidecar.mjs:6); pending its soundness proof. -/
  | tscCandidateCap (premises : List (Node × Cert)) (facts : List Fact) (bound : Cost)

mutual

/-- The bound a certificate concludes. -/
def costOf : Cert → Cost
  | .seqUnit => .constant 1
  | .seqMax children => .maximum (costsOf children)
  | .channelTotal parts => .maximum (partCosts parts)
  | .branchJoin children => .maximum (costsOf children)
  | .maxDominance _ target => target
  | .maxNormalise _ target => target
  | .productNormalise _ target => target
  | .exprValidity premise => costOf premise
  | .nestProduct _ _ b => b
  | .partialBindKnown _ _ b => b
  | .preferenceRank _ _ b => b
  | .boundAdditive _ _ b => b
  | .boundBestOf _ _ b => b
  | .boundBisection _ _ b => b
  | .boundConstantCollection _ _ b => b
  | .boundConstantDistance _ _ b => b
  | .boundDirective _ _ b => b
  | .boundExactAdditive _ _ b => b
  | .boundFalseCondition _ _ b => b
  | .boundForIn _ _ b => b
  | .boundForOfNative _ _ b => b
  | .boundGeometric _ _ b => b
  | .boundIteratorVisits _ _ b => b
  | .boundLinearDefault _ _ b => b
  | .boundLiveVisits _ _ b => b
  | .boundProgression _ _ b => b
  | .boundQuantity _ _ b => b
  | .boundShare _ _ b => b
  | .boundSingleIteration _ _ b => b
  | .forOfProducedLength _ _ b => b
  | .loopEffectInvalidation _ _ b => b
  | .loopNest _ _ b => b
  | .loopPhases _ _ b => b
  | .loopSuspension _ _ b => b
  | .loopUnbounded _ _ b => b
  | .loopUnit _ _ b => b
  | .budgetCancel _ _ b => b
  | .budgetCollect _ _ b => b
  | .budgetShare _ _ b => b
  | .hoistedJoin _ _ b => b
  | .shareSizedOperation _ _ b => b
  | .escapeAbsorb _ _ b => b
  | .escapeDepthExhausted _ _ b => b
  | .escapeLift _ _ b => b
  | .flowCompletion _ _ b => b
  | .flowGraph _ _ b => b
  | .asyncAssimilation _ _ b => b
  | .awaitContinuation _ _ b => b
  | .callCallbackParameter _ _ b => b
  | .callEffectsTransfer _ _ b => b
  | .callFallback _ _ b => b
  | .callLazyPhase _ _ b => b
  | .callOpenRemainder _ _ b => b
  | .callReturnedFunction _ _ b => b
  | .callSummary _ _ b => b
  | .constructionFields _ _ b => b
  | .constructorCall _ _ b => b
  | .implicitInvocation _ _ b => b
  | .iteratorVisits _ _ b => b
  | .latentProduction _ _ b => b
  | .lazyConsume _ _ b => b
  | .returnedFunctionFacts _ _ b => b
  | .sizeSubstitution _ _ b => b
  | .targetResolution _ _ b => b
  | .tscCalleeTargets _ _ b => b
  | .recBranchingDecrement _ _ b => b
  | .recChainDecrement _ _ b => b
  | .recChainDivision _ _ b => b
  | .recFactorial _ _ b => b
  | .recForgetMultiplicity _ _ b => b
  | .recGuard _ _ b => b
  | .recMarkers _ _ b => b
  | .recMeasure _ _ b => b
  | .recReducedMeasureSize _ _ b => b
  | .recRelation _ _ b => b
  | .recRelationJoin _ _ b => b
  | .recUnsolved _ _ b => b
  | .arrayMethod _ _ b => b
  | .intrinsicReplacementScan _ _ b => b
  | .linearConstructor _ _ b => b
  | .nativeCallback _ _ b => b
  | .nativeChargeLength _ _ b => b
  | .nativeModel _ _ b => b
  | .nativeVisitBudget _ _ b => b
  | .regexCost _ _ b => b
  | .regexEveryMatch _ _ b => b
  | .regexMatchedOnce _ _ b => b
  | .setMapLinear _ _ b => b
  | .unmodelledNative _ _ b => b
  | .argumentFacts _ _ b => b
  | .arrayMethodSize _ _ b => b
  | .constantCardinality _ _ b => b
  | .countOf _ _ b => b
  | .growthSites _ _ b => b
  | .holderStability _ _ b => b
  | .inputSizeEnvelope _ _ b => b
  | .iterableSize _ _ b => b
  | .parameterSize _ _ b => b
  | .producedSize _ _ b => b
  | .restCopy _ _ b => b
  | .resultSize _ _ b => b
  | .sizeAlgebra _ _ b => b
  | .sizeDimension _ _ b => b
  | .sizeLabels _ _ b => b
  | .spreadCopy _ _ b => b
  | .tscTypeKind _ _ b => b
  | .valueIdentity _ _ b => b
  | .dirBoundedStmt _ _ b => b
  | .dirCost _ _ b => b
  | .dirFunctionMark _ _ b => b
  | .dirHotCold _ _ b => b
  | .dirIgnore _ _ b => b
  | .dirIgnoreFunction _ _ b => b
  | .resourceConfigGraph _ _ b => b
  | .resourceEffectSchedulingDepth _ _ b => b
  | .resourceExhaustion _ _ b => b
  | .resourceFlowLimit _ _ b => b
  | .resourceImplementationFiles _ _ b => b
  | .resourcePublicSurface _ _ b => b
  | .resourceRegexLimits _ _ b => b
  | .resourceSchedulerBudget _ _ b => b
  | .resourceSpecializationCap _ _ b => b
  | .resourceTraceArena _ _ b => b
  | .tscCandidateCap _ _ b => b

/-- The bounds a list of certificates concludes. -/
def costsOf : List Cert → List Cost
  | [] => []
  | c :: cs => costOf c :: costsOf cs

/-- The bounds the parts of a `channel-total` conclude. -/
def partCosts : List (List Channel × Cert) → List Cost
  | [] => []
  | (_, c) :: ps => costOf c :: partCosts ps

end

/-! ## Declared-type facts and name resolution -/

mutual

/-- Structural equality of declared types. -/
def Ty.beq : Ty → Ty → Bool
  | .any, .any | .undefined, .undefined | .null, .null | .boolean, .boolean
  | .number, .number | .string, .string | .func, .func => true
  | .array a, .array b => Ty.beq a b
  | .map a b, .map c d => Ty.beq a c && Ty.beq b d
  | .set a, .set b => Ty.beq a b
  | .object fs, .object gs => Ty.beqFields fs gs
  | _, _ => false

/-- Structural equality of object type fields. -/
def Ty.beqFields : List (Name × Ty) → List (Name × Ty) → Bool
  | [], [] => true
  | (x, a) :: fs, (y, b) :: gs => x == y && Ty.beq a b && Ty.beqFields fs gs
  | _, _ => false

end

mutual

/-- The declared types of the bindings of `x` an expression's functions and classes create. -/
def exprBindings (x : Name) : Expr → List Ty
  | .lit _ | .ident _ | .«this» | .regex _ _ | .update _ _ _ => []
  | .unary _ a | .assign _ a | .assignOp _ _ a | .member a _ => exprBindings x a
  | .binary _ a b | .index a b | .updateIndex _ _ a b => exprBindings x a ++ exprBindings x b
  | .cond a b c | .assignIndex a b c | .assignOpIndex _ a b c =>
    exprBindings x a ++ exprBindings x b ++ exprBindings x c
  | .call f args | .new f args => exprBindings x f ++ exprsBindings x args
  | .func f => funcBindings x f
  | .klass c => classBindings x c
  | .array es => exprsBindings x es
  | .object ps => propsBindings x ps

/-- `exprBindings` over a list. -/
def exprsBindings (x : Name) : List Expr → List Ty
  | [] => []
  | e :: es => exprBindings x e ++ exprsBindings x es

/-- `exprBindings` over object literal properties. -/
def propsBindings (x : Name) : List (Name × Expr) → List Ty
  | [] => []
  | (_, e) :: ps => exprBindings x e ++ propsBindings x ps

/-- `exprBindings` over an optional expression. -/
def optBindings (x : Name) : Option Expr → List Ty
  | none => []
  | some e => exprBindings x e

/-- The declared types of the bindings of `x` a statement creates, directly or in its
functions and classes; a loop variable, a function or class name and `this` are `any`. -/
def stmtBindings (x : Name) : Stmt → List Ty
  | .expr e => exprBindings x e
  | .decl _ y τ init => (if y == x then [τ] else []) ++ optBindings x init
  | .block ss => stmtsBindings x ss
  | .ite c t e => exprBindings x c ++ stmtBindings x t ++ optStmtBindings x e
  | .forLoop init test update body =>
    optStmtBindings x init ++ optBindings x test ++ optBindings x update ++ stmtBindings x body
  | .forOf y e body | .forIn y e body =>
    (if y == x then [.any] else []) ++ exprBindings x e ++ stmtBindings x body
  | .«while» c body | .doWhile body c => exprBindings x c ++ stmtBindings x body
  | .ret e => optBindings x e
  | .brk | .cont => []
  | .funDecl y f => (if y == x then [.any] else []) ++ funcBindings x f
  | .classDecl y c => (if y == x then [.any] else []) ++ classBindings x c

/-- `stmtBindings` over a list. -/
def stmtsBindings (x : Name) : List Stmt → List Ty
  | [] => []
  | s :: ss => stmtBindings x s ++ stmtsBindings x ss

/-- `stmtBindings` over an optional statement. -/
def optStmtBindings (x : Name) : Option Stmt → List Ty
  | none => []
  | some s => stmtBindings x s

/-- The bindings of `x` a function creates when called: `this` for a non-arrow function, its
parameters with their declared types, and its body's. -/
def funcBindings (x : Name) : Func → List Ty
  | .mk params body arrow =>
    (if !arrow && x == "this" then [.any] else []) ++
      (params.filter (·.1 == x)).map (·.2) ++ stmtsBindings x body

/-- The bindings of `x` a class's constructor and methods create. -/
def classBindings (x : Name) : Class → List Ty
  | .mk ctor methods => optFuncBindings x ctor ++ methodsBindings x methods

/-- `funcBindings` over an optional constructor. -/
def optFuncBindings (x : Name) : Option Func → List Ty
  | none => []
  | some f => funcBindings x f

/-- `funcBindings` over class methods. -/
def methodsBindings (x : Name) : List (Name × Func) → List Ty
  | [] => []
  | (_, f) :: ms => funcBindings x f ++ methodsBindings x ms

end

/-- Name resolution recomputed from the encoded syntax: the declared types of every binding of
`x` the runs of an entry can create or find, namely the entry's free variables (§2.5 admits
their cells with these types), the program's definitions, and every binding in the entry and
the definitions. -/
def bindingTypes (p : Program) (e : Entry) (x : Name) : List Ty :=
  (e.scope.filter (·.1 == x)).map (·.2) ++ (if p.defs.any (·.1 == x) then [.any] else []) ++
    funcBindings x e.fn ++ p.defs.foldr (fun d acc => funcBindings x d.2 ++ acc) []

/-- A fact holds at a node. A declared-type fact holds when some binding of the variable
exists and every binding is declared with the fact's type; the other facts are decided by the
rule that records them. -/
def Fact.holds (p : Program) (n : Node) : Fact → Bool
  | .declared x τ =>
    let tys := bindingTypes p n.entry x
    !tys.isEmpty && tys.all (Ty.beq · τ)
  | _ => true

/-! ## Checking -/

mutual

/-- Every dimension a cost mentions is one of `dims`, and the cost mentions neither the legacy
envelope nor a name: a cost over an unmeasured dimension is unconstrained by the instance, and
§2 fixes no envelope. -/
def measured (dims : List ℕ) : Cost → Bool
  | .constant _ => true
  | .legacyN | .legacyLog | .legacyNLog | .name _ => false
  | .dimension j _ => dims.contains j
  | .sum cs | .product cs | .maximum cs => measuredList dims cs
  | .log c | .factorial c => measured dims c
  | .power a b | .ratio a b => measured dims a && measured dims b

/-- `measured` over a list. -/
def measuredList (dims : List ℕ) : List Cost → Bool
  | [] => true
  | c :: cs => measured dims c && measuredList dims cs

end

mutual

/-- Check a certificate at node `n` of program `p`. Decidable by kernel reduction. -/
def checkCert (p : Program) (n : Node) : Cert → Bool
  | .seqUnit =>
    match n.site with
    | .stmt s => unitStmt s
    | .expr (.lit _) => true
    | _ => false
  | .seqMax children =>
    match seqSites n.entry n.site with
    | some sites => checkChildren p n.entry sites children
    | none => false
  | .branchJoin children =>
    match branchSites n.site with
    | some sites => checkChildren p n.entry sites children
    | none => false
  | .channelTotal parts =>
    checkParts p n parts && allChannels.all fun k => parts.any fun x => x.1.contains k
  | .maxDominance premise target =>
    checkCert p n premise && valid (costOf premise) && valid target &&
      dominated (maxView (costOf premise)) (maxView target)
  | .maxNormalise premise target =>
    checkCert p n premise && valid (costOf premise) && valid target &&
      maxCovers (flatMax (costOf premise)) (flatMax target)
  | .productNormalise premise target =>
    checkCert p n premise && prodMatches (costOf premise) target
  | .exprValidity premise => checkCert p n premise && valid (costOf premise)
  | _ => false

/-- Check one certificate per child site, in order, each at its child node. -/
def checkChildren (p : Program) (e : Entry) : List Site → List Cert → Bool
  | [], [] => true
  | s :: ss, c :: cs => checkCert p ⟨e, s⟩ c && checkChildren p e ss cs
  | _, _ => false

/-- Check every part of a `channel-total` at the node. -/
def checkParts (p : Program) (n : Node) : List (List Channel × Cert) → Bool
  | [] => true
  | (_, c) :: ps => checkCert p n c && checkParts p n ps

end

/-- The intrinsics a derivation relies on: those whose modification by the analysed program
would change the work its rules reason about (§2.2). The family A rules reason about the
program's syntax and the costs alone and consult no intrinsic; families B to J extend this as
their rules land. -/
def Cert.reliance (_ : Cert) : List Intrinsic := []

/-- Check a certificate at node `n` of program `p` under the no-replacement facts `xs`: the
node's entry is well formed, the derivation checks, its bound is `measured` over the entry's
dimensions, and every intrinsic it relies on is among `xs`. Decidable by kernel reduction. -/
def check (p : Program) (n : Node) (xs : List Intrinsic) (c : Cert) : Bool :=
  n.entry.wf p && checkCert p n c && measured (n.entry.dims.map Prod.fst) (costOf c) &&
    c.reliance.all xs.contains

theorem partCosts_eq : ∀ parts : List (List Channel × Cert),
    partCosts parts = (parts.map fun x => (x.1, costOf x.2)).map Prod.snd
  | [] => rfl
  | (_, c) :: ps => by simp [partCosts, partCosts_eq ps]

mutual

/-- A checked certificate proves its bound. -/
theorem checkCert_sound (W : World) : ∀ (p : Program) (n : Node) (c : Cert),
    n.entry.wf p = true → checkCert p n c = true → Bound W p n (costOf c)
  | p, n, .seqUnit, hwf, h => by
    simp only [checkCert] at h
    split at h
    · rename_i s hs
      exact unit_bound hwf hs h
    · rename_i l hs
      exact lit_bound hwf hs
    · exact absurd h Bool.false_ne_true
  | p, n, .seqMax children, hwf, h => by
    simp only [checkCert] at h
    split at h
    · rename_i sites hs
      obtain ⟨hl, hb⟩ := checkChildren_sound W p n.entry sites children hwf h
      exact seqMax_sound hwf hs hl hb
    · exact absurd h Bool.false_ne_true
  | p, n, .branchJoin children, hwf, h => by
    simp only [checkCert] at h
    split at h
    · rename_i sites hs
      obtain ⟨hl, hb⟩ := checkChildren_sound W p n.entry sites children hwf h
      exact branchJoin_sound hwf hs hl hb
    · exact absurd h Bool.false_ne_true
  | p, n, .channelTotal parts, hwf, h => by
    simp only [checkCert, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
    obtain ⟨hp, hcov⟩ := h
    show Bound W p n (.maximum (partCosts parts))
    rw [partCosts_eq]
    refine channelTotal_sound hwf (fun x hx => ?_) (fun k => ?_)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (checkParts_sound W p n parts hwf hp y hy).restrict fun k _ => mem_allChannels k
    · obtain ⟨y, hy, hk⟩ := hcov k (mem_allChannels k)
      exact ⟨(y.1, costOf y.2), List.mem_map.2 ⟨y, hy, rfl⟩, List.contains_iff_mem.1 hk⟩
  | p, n, .maxDominance premise target, hwf, h => by
    simp only [checkCert, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hs⟩, ht⟩, hd⟩ := h
    exact maxDominance_sound (checkCert_sound W p n premise hwf hc) hs ht hd
  | p, n, .maxNormalise premise target, hwf, h => by
    simp only [checkCert, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hs⟩, ht⟩, hm⟩ := h
    exact maxNormalise_sound (checkCert_sound W p n premise hwf hc) hs ht hm
  | p, n, .productNormalise premise target, hwf, h => by
    simp only [checkCert, Bool.and_eq_true] at h
    exact productNormalise_sound (checkCert_sound W p n premise hwf h.1) h.2
  | p, n, .exprValidity premise, hwf, h => by
    simp only [checkCert, Bool.and_eq_true] at h
    exact checkCert_sound W p n premise hwf h.1
  | _, _, .nestProduct _ _ _, _, h
  | _, _, .partialBindKnown _ _ _, _, h
  | _, _, .preferenceRank _ _ _, _, h
  | _, _, .boundAdditive _ _ _, _, h
  | _, _, .boundBestOf _ _ _, _, h
  | _, _, .boundBisection _ _ _, _, h
  | _, _, .boundConstantCollection _ _ _, _, h
  | _, _, .boundConstantDistance _ _ _, _, h
  | _, _, .boundDirective _ _ _, _, h
  | _, _, .boundExactAdditive _ _ _, _, h
  | _, _, .boundFalseCondition _ _ _, _, h
  | _, _, .boundForIn _ _ _, _, h
  | _, _, .boundForOfNative _ _ _, _, h
  | _, _, .boundGeometric _ _ _, _, h
  | _, _, .boundIteratorVisits _ _ _, _, h
  | _, _, .boundLinearDefault _ _ _, _, h
  | _, _, .boundLiveVisits _ _ _, _, h
  | _, _, .boundProgression _ _ _, _, h
  | _, _, .boundQuantity _ _ _, _, h
  | _, _, .boundShare _ _ _, _, h
  | _, _, .boundSingleIteration _ _ _, _, h
  | _, _, .forOfProducedLength _ _ _, _, h
  | _, _, .loopEffectInvalidation _ _ _, _, h
  | _, _, .loopNest _ _ _, _, h
  | _, _, .loopPhases _ _ _, _, h
  | _, _, .loopSuspension _ _ _, _, h
  | _, _, .loopUnbounded _ _ _, _, h
  | _, _, .loopUnit _ _ _, _, h
  | _, _, .budgetCancel _ _ _, _, h
  | _, _, .budgetCollect _ _ _, _, h
  | _, _, .budgetShare _ _ _, _, h
  | _, _, .hoistedJoin _ _ _, _, h
  | _, _, .shareSizedOperation _ _ _, _, h
  | _, _, .escapeAbsorb _ _ _, _, h
  | _, _, .escapeDepthExhausted _ _ _, _, h
  | _, _, .escapeLift _ _ _, _, h
  | _, _, .flowCompletion _ _ _, _, h
  | _, _, .flowGraph _ _ _, _, h
  | _, _, .asyncAssimilation _ _ _, _, h
  | _, _, .awaitContinuation _ _ _, _, h
  | _, _, .callCallbackParameter _ _ _, _, h
  | _, _, .callEffectsTransfer _ _ _, _, h
  | _, _, .callFallback _ _ _, _, h
  | _, _, .callLazyPhase _ _ _, _, h
  | _, _, .callOpenRemainder _ _ _, _, h
  | _, _, .callReturnedFunction _ _ _, _, h
  | _, _, .callSummary _ _ _, _, h
  | _, _, .constructionFields _ _ _, _, h
  | _, _, .constructorCall _ _ _, _, h
  | _, _, .implicitInvocation _ _ _, _, h
  | _, _, .iteratorVisits _ _ _, _, h
  | _, _, .latentProduction _ _ _, _, h
  | _, _, .lazyConsume _ _ _, _, h
  | _, _, .returnedFunctionFacts _ _ _, _, h
  | _, _, .sizeSubstitution _ _ _, _, h
  | _, _, .targetResolution _ _ _, _, h
  | _, _, .tscCalleeTargets _ _ _, _, h
  | _, _, .recBranchingDecrement _ _ _, _, h
  | _, _, .recChainDecrement _ _ _, _, h
  | _, _, .recChainDivision _ _ _, _, h
  | _, _, .recFactorial _ _ _, _, h
  | _, _, .recForgetMultiplicity _ _ _, _, h
  | _, _, .recGuard _ _ _, _, h
  | _, _, .recMarkers _ _ _, _, h
  | _, _, .recMeasure _ _ _, _, h
  | _, _, .recReducedMeasureSize _ _ _, _, h
  | _, _, .recRelation _ _ _, _, h
  | _, _, .recRelationJoin _ _ _, _, h
  | _, _, .recUnsolved _ _ _, _, h
  | _, _, .arrayMethod _ _ _, _, h
  | _, _, .intrinsicReplacementScan _ _ _, _, h
  | _, _, .linearConstructor _ _ _, _, h
  | _, _, .nativeCallback _ _ _, _, h
  | _, _, .nativeChargeLength _ _ _, _, h
  | _, _, .nativeModel _ _ _, _, h
  | _, _, .nativeVisitBudget _ _ _, _, h
  | _, _, .regexCost _ _ _, _, h
  | _, _, .regexEveryMatch _ _ _, _, h
  | _, _, .regexMatchedOnce _ _ _, _, h
  | _, _, .setMapLinear _ _ _, _, h
  | _, _, .unmodelledNative _ _ _, _, h
  | _, _, .argumentFacts _ _ _, _, h
  | _, _, .arrayMethodSize _ _ _, _, h
  | _, _, .constantCardinality _ _ _, _, h
  | _, _, .countOf _ _ _, _, h
  | _, _, .growthSites _ _ _, _, h
  | _, _, .holderStability _ _ _, _, h
  | _, _, .inputSizeEnvelope _ _ _, _, h
  | _, _, .iterableSize _ _ _, _, h
  | _, _, .parameterSize _ _ _, _, h
  | _, _, .producedSize _ _ _, _, h
  | _, _, .restCopy _ _ _, _, h
  | _, _, .resultSize _ _ _, _, h
  | _, _, .sizeAlgebra _ _ _, _, h
  | _, _, .sizeDimension _ _ _, _, h
  | _, _, .sizeLabels _ _ _, _, h
  | _, _, .spreadCopy _ _ _, _, h
  | _, _, .tscTypeKind _ _ _, _, h
  | _, _, .valueIdentity _ _ _, _, h
  | _, _, .dirBoundedStmt _ _ _, _, h
  | _, _, .dirCost _ _ _, _, h
  | _, _, .dirFunctionMark _ _ _, _, h
  | _, _, .dirHotCold _ _ _, _, h
  | _, _, .dirIgnore _ _ _, _, h
  | _, _, .dirIgnoreFunction _ _ _, _, h
  | _, _, .resourceConfigGraph _ _ _, _, h
  | _, _, .resourceEffectSchedulingDepth _ _ _, _, h
  | _, _, .resourceExhaustion _ _ _, _, h
  | _, _, .resourceFlowLimit _ _ _, _, h
  | _, _, .resourceImplementationFiles _ _ _, _, h
  | _, _, .resourcePublicSurface _ _ _, _, h
  | _, _, .resourceRegexLimits _ _ _, _, h
  | _, _, .resourceSchedulerBudget _ _ _, _, h
  | _, _, .resourceSpecializationCap _ _ _, _, h
  | _, _, .resourceTraceArena _ _ _, _, h
  | _, _, .tscCandidateCap _ _ _, _, h => nomatch h

/-- Checked child certificates bound their child nodes. -/
theorem checkChildren_sound (W : World) : ∀ (p : Program) (e : Entry) (sites : List Site)
    (cs : List Cert), e.wf p = true → checkChildren p e sites cs = true →
      sites.length = (costsOf cs).length ∧ ∀ x ∈ sites.zip (costsOf cs), Bound W p ⟨e, x.1⟩ x.2
  | _, _, [], [], _, _ => ⟨rfl, by simp [costsOf]⟩
  | p, e, s :: ss, c :: cs, hwf, h => by
    simp only [checkChildren, Bool.and_eq_true] at h
    obtain ⟨hl, hb⟩ := checkChildren_sound W p e ss cs hwf h.2
    refine ⟨by simp [costsOf, hl], fun x hx => ?_⟩
    simp only [costsOf, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact checkCert_sound W p ⟨e, s⟩ c hwf h.1
    · exact hb x hx
  | _, _, [], _ :: _, _, h => by simp [checkChildren] at h
  | _, _, _ :: _, [], _, h => by simp [checkChildren] at h

/-- Checked parts bound the node. -/
theorem checkParts_sound (W : World) : ∀ (p : Program) (n : Node)
    (parts : List (List Channel × Cert)), n.entry.wf p = true → checkParts p n parts = true →
      ∀ x ∈ parts, Bound W p n (costOf x.2)
  | _, _, [], _, _ => by simp
  | p, n, (ks, c) :: ps, hwf, h => by
    simp only [checkParts, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact checkCert_sound W p n c hwf h.1
    · exact checkParts_sound W p n ps hwf h.2 x hx

end

/-- A checked certificate proves its bound in every world whose analysed program modifies none
of the intrinsics `xs` (§2.2), whatever the world's spec-internal step costs. -/
theorem check_sound (W : World) (xs : List Intrinsic) (p : Program) (n : Node) (c : Cert)
    (_hW : NoReplacement W xs) (h : check p n xs c = true) : Bound W p n (costOf c) := by
  simp only [check, Bool.and_eq_true] at h
  exact checkCert_sound W p n c h.1.1.1 h.1.1.2

end Olint

import Olint.Model.Admission
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Costs and bounds

`Cost` mirrors olint's cost `Expression` (`src/cost.rs`), and `Cost.eval` gives each cost its
value at a valuation of the input dimensions.

**Cost domain.** Every cost reads as `max(1, ·)` of its exact value `Cost.raw`, in which a
dimension reads as at least `1` and a logarithm as `log₂ (max x 2)`, so at least `1`. So a
dimension counts as at least `1`, `log 1` counts as `1`, and a product with a zero constant,
exactly `0`, reads as `1`, which makes olint's zero-product collapse sound (ledger gap G49).

**Bound.** `Bound W p n c` is the spec's bound (§1) in world `W`: the node's entry is well
formed (`Entry.wf`), and there is one constant `C` such that on every instance §2 admits for the
entry, every configuration the entry's run reaches at the node completes, and does at most
`C · c` work, measured against the entry's input dimensions. The constant is uniform over all
admitted instances, small ones included; since every cost and every dimension reads as at least
`1`, finitely many small instances cost only a larger constant, and a bound never ignores the
instances where some dimension stays small while others grow. A node's bound holds wherever the
node runs within its entry, so a parent's bound composes from its children's (`Olint.Rules`).
Completion is part of the bound: every reached run must complete, so a node whose run throws,
aborts or diverges on some admitted instance has no bound; runs that throw are excluded from
what a bound can cover. For the entry node itself the configurations are the root call alone,
and `Bound.work_isBigO` restates the bound over `Work`.

`BoundOn W p n ks c` is the bound on the runs that end in the channels `ks`, completion still
required of every run; `Bound` is `BoundOn` over every channel.

## Why no bound holds vacuously

A bound quantifies over the admitted instances, so it would say nothing if none existed. Three
facts exclude that:

* admission (`Olint.Model.Admitted`) constrains only the entry's inputs: the heap, the arguments,
  the free variables and the dimensions. §2.5 during the run is a check at every variable read
  (`Olint.Model.readVar`) that aborts the run on a non-conforming value, so a program that
  violates its declared types makes its runs abort, which no bound admits, instead of emptying
  admission;
* `Bound` requires the entry to be well formed (`Entry.wf`): every dimension measures an
  argument or a free variable of a measurable declared type, dimension ids and measured
  quantities are distinct, and object types name each field once;
* for a well-formed entry, every valuation of the dimensions has an admitted instance
  (`Olint.Model.Admitted.exists`), so a bound constrains the entry's runs at every size.

## Premises every certificate theorem carries

A certificate theorem holds in every world `W` satisfying `NoReplacement W xs` for the
intrinsics `xs` its derivation relies on (§2.2, olint's intrinsic-replacement scan, certified in
Phase 5). A derivation whose soundness needs the G52 draft step costs states `W.ops =
SpecOps.draft` as a further premise, and counts as pending Matt's signature until he signs the
drafts into §2 (§2.1, §6.3); `scripts/axioms.lean` reports it so.

## Ceilings need a separate reading

§2.3 reads a built-in's work as "at most" its worst-case step count, and the model charges
exactly that count, together with the step costs of `SpecOps`, which are upper readings too. A
work *upper* bound proven in this model is therefore an upper bound on real work. The same
charges read as a *lower* bound would overstate real work wherever an engine does less than the
worst-case steps, so a ceiling (Phase 7, §6.6), which claims work grows at least as fast as a
cost, must be proven against a separate lower-bound reading of the model, one that charges each
operation only the work every conforming implementation must do. No ceiling may be proven from
`Work` as defined here.
-/

-- TODO(7.2): define the lower-bound reading of the model of work (each built-in and each
-- spec-internal operation charged the least work every conforming implementation performs),
-- and prove ceilings against it, never against `Olint.Model.Work`.

namespace Olint

open Olint.Model Filter Asymptotics

/-- The domain of an input dimension (`Domain` in `src/cost.rs`). -/
inductive Domain where
  | positiveReal
  | size
  deriving DecidableEq, Repr

/-- A cost, constructor for constructor `Expression` in `src/cost.rs`. -/
inductive Cost where
  | constant (n : ℕ)
  /-- The legacy size envelope `N`. -/
  | legacyN
  /-- The legacy `log N`. -/
  | legacyLog
  /-- The legacy `N log N`. -/
  | legacyNLog
  /-- A named cost, resolved by binding before a bound is certified. -/
  | name (s : String)
  | dimension (id : ℕ) (domain : Domain)
  | sum (terms : List Cost)
  | product (terms : List Cost)
  | maximum (terms : List Cost)
  | log (c : Cost)
  | power (base exponent : Cost)
  | ratio (numerator denominator : Cost)
  | factorial (c : Cost)

/-- A valuation of the quantities a cost mentions. -/
structure Valuation where
  dim : ℕ → ℝ
  envelope : ℝ
  name : String → ℝ

/-- The valuation an instance induces. Names carry no value (`0`); the legacy envelope is the
instance's unconstrained `envelope`, as §2 sets no envelope. `Olint.check` rejects a bound that
mentions either. -/
def Model.Instance.valuation (i : Instance) : Valuation := ⟨i.dims, i.envelope, fun _ => 0⟩

/-- The logarithm of a cost: `log₂ (max x 2)`, which is at least `1`, as olint's costs are. -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 (max x 2)

mutual

/-- The exact value of a cost at a valuation, a dimension reading as at least `1`. -/
noncomputable def Cost.raw (v : Valuation) : Cost → ℝ
  | .constant n => n
  | .legacyN => v.envelope
  | .legacyLog => lg v.envelope
  | .legacyNLog => v.envelope * lg v.envelope
  | .name s => v.name s
  | .dimension id _ => max 1 (v.dim id)
  | .sum cs => Cost.rawSum v cs
  | .product cs => Cost.rawProduct v cs
  | .maximum cs => Cost.rawMaximum v cs
  | .log c => lg (c.raw v)
  | .power a b => a.raw v ^ b.raw v
  | .ratio a b => a.raw v / b.raw v
  | .factorial c => (Nat.factorial ⌈c.raw v⌉₊ : ℝ)

/-- The sum of a list of costs. -/
noncomputable def Cost.rawSum (v : Valuation) : List Cost → ℝ
  | [] => 0
  | c :: cs => c.raw v + Cost.rawSum v cs

/-- The product of a list of costs. -/
noncomputable def Cost.rawProduct (v : Valuation) : List Cost → ℝ
  | [] => 1
  | c :: cs => c.raw v * Cost.rawProduct v cs

/-- The maximum of a list of costs, `0` for the empty list. -/
noncomputable def Cost.rawMaximum (v : Valuation) : List Cost → ℝ
  | [] => 0
  | c :: cs => max (c.raw v) (Cost.rawMaximum v cs)

end

/-- The value of a cost: `max(1, ·)` of its exact value (ledger gap G49). -/
noncomputable def Cost.eval (v : Valuation) (c : Cost) : ℝ := max 1 (c.raw v)

theorem Cost.one_le_eval (v : Valuation) (c : Cost) : 1 ≤ c.eval v := le_max_left _ _

theorem Cost.eval_pos (v : Valuation) (c : Cost) : 0 < c.eval v :=
  lt_of_lt_of_le one_pos (c.one_le_eval v)

/-- The filter of the instances §2 admits for an entry, conformance of its inputs to their
declared types (§2.5) included: a property holds on it when it holds on every admitted
instance. -/
def Admits (e : Entry) : Filter Instance := 𝓟 {i | Admitted e i}

/-- In instance `i` and world `W`, every configuration the entry's run reaches at site `s`
completes with any fuel from `F` on, and does at most `b` work on a run ending in a channel of
`ks`. -/
def Holds (W : World) (p : Program) (e : Entry) (i : Instance) (s : Site) (ks : List Channel)
    (F : ℕ) (b : ℝ) : Prop :=
  ∀ c, Reach W p e i c → c.At p e i s →
    (∀ f, F ≤ f → ∃ o st', c.Runs W f o st') ∧
    ∀ f o st', c.Runs W f o st' → o.channel ∈ ks → (st'.work : ℝ) - c.st.work ≤ b

/-- `c` bounds node `n` of program `p` in world `W` on the channels `ks`: the node's entry is
well formed, and one constant `C` serves every admitted instance, where every configuration
reached at the node completes and does at most `C · c` work on the runs ending in `ks`. -/
def BoundOn (W : World) (p : Program) (n : Node) (ks : List Channel) (c : Cost) : Prop :=
  n.entry.wf p = true ∧
    ∃ C : ℝ, ∀ᶠ i in Admits n.entry, ∃ F, Holds W p n.entry i n.site ks F (C * c.eval i.valuation)

/-- `c` bounds node `n` of program `p` in world `W`: on every admitted instance of its
well-formed entry, every configuration the entry's run reaches at the node completes, and its
work is `O(c)`, one constant serving all of them. -/
def Bound (W : World) (p : Program) (n : Node) (c : Cost) : Prop := BoundOn W p n allChannels c

/-! ## Basic lemmas -/

@[simp] theorem Cost.raw_constant (v : Valuation) (k : ℕ) : (Cost.constant k).raw v = k := by
  simp [Cost.raw]

theorem lg_ge_one (x : ℝ) : 1 ≤ lg x := by
  unfold lg
  rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_right x 2)),
    Real.rpow_one]
  exact le_max_right x 2

theorem Holds.mono {W : World} {p : Program} {e : Entry} {i : Instance} {s : Site}
    {ks : List Channel} {F F' : ℕ} {b b' : ℝ} (h : Holds W p e i s ks F b) (hF : F ≤ F')
    (hb : b ≤ b') : Holds W p e i s ks F' b' := fun c hr ha =>
  ⟨fun f hf => (h c hr ha).1 f (le_trans hF hf),
    fun f o st' hc hk => le_trans ((h c hr ha).2 f o st' hc hk) hb⟩

/-- A bound's constant can be taken nonnegative. -/
theorem BoundOn.nonneg {W : World} {p : Program} {n : Node} {ks : List Channel} {c : Cost}
    (h : BoundOn W p n ks c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Admits n.entry, ∃ F,
      Holds W p n.entry i n.site ks F (C * c.eval i.valuation) := by
  obtain ⟨_, C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, hC.mono fun i ⟨F, hF⟩ => ⟨F, hF.mono le_rfl ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (c.eval_pos _))

/-- A bound is monotone in the cost: a bound by `c` is a bound by any `d` with `c = O(d)`. -/
theorem BoundOn.mono {W : World} {p : Program} {n : Node} {ks : List Channel} {c d : Cost}
    (h : BoundOn W p n ks c)
    (hcd : (fun i : Instance => c.eval i.valuation) =O[Admits n.entry]
      (fun i => d.eval i.valuation)) : BoundOn W p n ks d := by
  obtain ⟨C, hC0, hC⟩ := h.nonneg
  obtain ⟨K, hK⟩ := hcd.bound
  refine ⟨h.1, C * max K 0, (hC.and hK).mono fun i ⟨⟨F, hF⟩, hk⟩ => ⟨F, hF.mono le_rfl ?_⟩⟩
  have e1 : ‖c.eval i.valuation‖ = c.eval i.valuation := abs_of_pos (c.eval_pos _)
  have e2 : ‖d.eval i.valuation‖ = d.eval i.valuation := abs_of_pos (d.eval_pos _)
  rw [e1, e2] at hk
  have : c.eval i.valuation ≤ max K 0 * d.eval i.valuation :=
    le_trans hk (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (d.eval_pos _)))
  calc C * c.eval i.valuation ≤ C * (max K 0 * d.eval i.valuation) :=
        mul_le_mul_of_nonneg_left this hC0
    _ = C * max K 0 * d.eval i.valuation := by ring

theorem Bound.mono {W : World} {p : Program} {n : Node} {c d : Cost} (h : Bound W p n c)
    (hcd : (fun i : Instance => c.eval i.valuation) =O[Admits n.entry]
      (fun i => d.eval i.valuation)) : Bound W p n d :=
  BoundOn.mono h hcd

/-- A bound holds on every subset of its channels. -/
theorem BoundOn.restrict {W : World} {p : Program} {n : Node} {ks ks' : List Channel} {c : Cost}
    (h : BoundOn W p n ks c) (hk : ∀ k ∈ ks', k ∈ ks) : BoundOn W p n ks' c := by
  obtain ⟨hwf, C, hC⟩ := h
  exact ⟨hwf, C, hC.mono fun i ⟨F, hF⟩ => ⟨F, fun c hr ha =>
    ⟨(hF c hr ha).1, fun f o st' hc hk' => (hF c hr ha).2 f o st' hc (hk _ hk')⟩⟩⟩

/-- An entry's bound bounds its `Work`: on every admitted instance its run halts, and its work
is `O(c)`. -/
theorem Bound.work_isBigO {W : World} {p : Program} {n : Node} {c : Cost} (hn : n.site = .entry)
    (h : Bound W p n c) :
    (∀ᶠ i in Admits n.entry, Halts W p i n.entry) ∧
      (fun i => (Work W p i n.entry : ℝ)) =O[Admits n.entry] (fun i => c.eval i.valuation) := by
  obtain ⟨C, _, hC⟩ := BoundOn.nonneg h
  have key : ∀ᶠ i in Admits n.entry, Halts W p i n.entry ∧
      (Work W p i n.entry : ℝ) ≤ C * c.eval i.valuation := by
    refine hC.mono fun i ⟨F, hF⟩ => ?_
    have hr : Reach W p n.entry i (root p n.entry i) := Relation.ReflTransGen.refl
    have ha : (root p n.entry i).At p n.entry i n.site := by rw [hn]; rfl
    obtain ⟨hcomp, hwork⟩ := hF _ hr ha
    have h0 : (root p n.entry i).st.work = 0 := by
      unfold root
      split
      · rename_i env st hb
        obtain ⟨a, h', e⟩ := bindProgram_safe p i.env i.heap
        rw [e] at hb
        cases hb
        rfl
      · rfl
    have halts : Halts W p i n.entry := by
      obtain ⟨o, st', hc⟩ := hcomp F le_rfl
      refine ⟨F, ?_⟩
      simp only [HaltsWith, run]
      rw [show ((root p n.entry i).frame.run W F).run (root p n.entry i).st = .ok (o, st') from hc]
      rfl
    have atFuel : ∀ f, HaltsWith f W p i n.entry →
        (((run f W p i n.entry).toOption.getD 0 : ℕ) : ℝ) ≤ C * c.eval i.valuation := by
      intro f hf
      simp only [HaltsWith, run] at hf ⊢
      revert hf
      rcases hres : ((root p n.entry i).frame.run W f).run (root p n.entry i).st with
        err | ⟨o, st'⟩
      · intro hf; simp [Except.map, Except.toBool] at hf
      · intro _
        have hw := hwork f o st' hres (mem_allChannels _)
        rw [h0] at hw
        simpa [Except.map, Except.toOption] using hw
    refine ⟨halts, ?_⟩
    unfold Work
    split
    · exact atFuel _ (Nat.find_spec halts)
    · contradiction
  refine ⟨key.mono fun _ h => h.1, IsBigO.of_bound C (key.mono fun i h => ?_)⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_pos (c.eval_pos _)]
  exact h.2

end Olint

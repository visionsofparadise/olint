import Olint.Model.Cost
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

**Bound.** `Bound p n c` is the spec's bound (§1): there is one constant `C` such that on every
large instance §2 admits for the node's entry, every configuration the entry's run reaches at
the node completes, and does at most `C · c` work, measured against the entry's input
dimensions. A node's bound therefore holds wherever the node runs within its entry, so a
parent's bound composes from its children's (`Olint.Rules`). Completion is part of the bound:
every reached run must complete, so a node whose run throws, aborts or diverges on some large
admitted instance has no bound; runs that throw are excluded from what a bound can cover.
For the entry node itself the configurations are the root call alone, and `Bound.work_isBigO`
restates the bound over `Work`.

`BoundOn p n ks c` is the bound on the runs that end in the channels `ks`, completion still
required of every run; `Bound` is `BoundOn` over every channel.
-/

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

/-- The filter of large admitted instances of an entry: every dimension large (`atTop`),
restricted to the instances §2 admits for the entry, conformance to declared types (§2.5)
included. -/
def Admits (p : Program) (e : Entry) : Filter Instance := atTop ⊓ 𝓟 {i | Admitted p e i}

/-- In instance `i`, every configuration the entry's run reaches at site `s` completes with any
fuel from `F` on, and does at most `b` work on a run ending in a channel of `ks`. -/
def Holds (p : Program) (e : Entry) (i : Instance) (s : Site) (ks : List Channel) (F : ℕ)
    (b : ℝ) : Prop :=
  ∀ c, Reach p e i c → c.At p e i s →
    (∀ f, F ≤ f → ∃ o st', c.Runs f o st') ∧
    ∀ f o st', c.Runs f o st' → o.channel ∈ ks → (st'.work : ℝ) - c.st.work ≤ b

/-- `c` bounds node `n` of program `p` on the channels `ks`: one constant `C` serves every large
admitted instance, where every configuration reached at the node completes and does at most
`C · c` work on the runs ending in `ks`. -/
def BoundOn (p : Program) (n : Node) (ks : List Channel) (c : Cost) : Prop :=
  ∃ C : ℝ, ∀ᶠ i in Admits p n.entry, ∃ F, Holds p n.entry i n.site ks F (C * c.eval i.valuation)

/-- `c` bounds node `n` of program `p`: on every large admitted instance of its entry, every
configuration the entry's run reaches at the node completes, and its work is `O(c)`, one
constant serving all of them. -/
def Bound (p : Program) (n : Node) (c : Cost) : Prop := BoundOn p n allChannels c

/-! ## Basic lemmas -/

@[simp] theorem Cost.raw_constant (v : Valuation) (k : ℕ) : (Cost.constant k).raw v = k := by
  simp [Cost.raw]

theorem lg_ge_one (x : ℝ) : 1 ≤ lg x := by
  unfold lg
  rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_right x 2)),
    Real.rpow_one]
  exact le_max_right x 2

theorem Holds.mono {p : Program} {e : Entry} {i : Instance} {s : Site} {ks : List Channel}
    {F F' : ℕ} {b b' : ℝ} (h : Holds p e i s ks F b) (hF : F ≤ F') (hb : b ≤ b') :
    Holds p e i s ks F' b' := fun c hr ha =>
  ⟨fun f hf => (h c hr ha).1 f (le_trans hF hf),
    fun f o st' hc hk => le_trans ((h c hr ha).2 f o st' hc hk) hb⟩

/-- A bound's constant can be taken nonnegative. -/
theorem BoundOn.nonneg {p : Program} {n : Node} {ks : List Channel} {c : Cost}
    (h : BoundOn p n ks c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Admits p n.entry, ∃ F,
      Holds p n.entry i n.site ks F (C * c.eval i.valuation) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, hC.mono fun i ⟨F, hF⟩ => ⟨F, hF.mono le_rfl ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (c.eval_pos _))

/-- A bound is monotone in the cost: a bound by `c` is a bound by any `d` with `c = O(d)`. -/
theorem BoundOn.mono {p : Program} {n : Node} {ks : List Channel} {c d : Cost}
    (h : BoundOn p n ks c)
    (hcd : (fun i : Instance => c.eval i.valuation) =O[Admits p n.entry]
      (fun i => d.eval i.valuation)) : BoundOn p n ks d := by
  obtain ⟨C, hC0, hC⟩ := h.nonneg
  obtain ⟨K, hK⟩ := hcd.bound
  refine ⟨C * max K 0, (hC.and hK).mono fun i ⟨⟨F, hF⟩, hk⟩ => ⟨F, hF.mono le_rfl ?_⟩⟩
  have e1 : ‖c.eval i.valuation‖ = c.eval i.valuation := abs_of_pos (c.eval_pos _)
  have e2 : ‖d.eval i.valuation‖ = d.eval i.valuation := abs_of_pos (d.eval_pos _)
  rw [e1, e2] at hk
  have : c.eval i.valuation ≤ max K 0 * d.eval i.valuation :=
    le_trans hk (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (d.eval_pos _)))
  calc C * c.eval i.valuation ≤ C * (max K 0 * d.eval i.valuation) :=
        mul_le_mul_of_nonneg_left this hC0
    _ = C * max K 0 * d.eval i.valuation := by ring

theorem Bound.mono {p : Program} {n : Node} {c d : Cost} (h : Bound p n c)
    (hcd : (fun i : Instance => c.eval i.valuation) =O[Admits p n.entry]
      (fun i => d.eval i.valuation)) : Bound p n d :=
  BoundOn.mono h hcd

/-- A bound holds on every subset of its channels. -/
theorem BoundOn.restrict {p : Program} {n : Node} {ks ks' : List Channel} {c : Cost}
    (h : BoundOn p n ks c) (hk : ∀ k ∈ ks', k ∈ ks) : BoundOn p n ks' c := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, hC.mono fun i ⟨F, hF⟩ => ⟨F, fun c hr ha =>
    ⟨(hF c hr ha).1, fun f o st' hc hk' => (hF c hr ha).2 f o st' hc (hk _ hk')⟩⟩⟩

/-- An entry's bound bounds its `Work`: on large admitted instances its run halts, and its work
is `O(c)`. -/
theorem Bound.work_isBigO {p : Program} {n : Node} {c : Cost} (hn : n.site = .entry)
    (h : Bound p n c) :
    (∀ᶠ i in Admits p n.entry, Halts p i n.entry) ∧
      (fun i => (Work p i n.entry : ℝ)) =O[Admits p n.entry] (fun i => c.eval i.valuation) := by
  obtain ⟨C, _, hC⟩ := BoundOn.nonneg h
  have key : ∀ᶠ i in Admits p n.entry, Halts p i n.entry ∧
      (Work p i n.entry : ℝ) ≤ C * c.eval i.valuation := by
    refine hC.mono fun i ⟨F, hF⟩ => ?_
    have hr : Reach p n.entry i (root p n.entry i) := Relation.ReflTransGen.refl
    have ha : (root p n.entry i).At p n.entry i n.site := by rw [hn]; rfl
    obtain ⟨hcomp, hwork⟩ := hF _ hr ha
    have h0 : (root p n.entry i).st.work = 0 := by
      unfold root
      split
      · rename_i env st hb
        obtain ⟨a, h', e⟩ := (show ∃ a h', (bindProgram p i.env).run ⟨i.heap, 0⟩ =
            .ok (a, ⟨h', 0⟩) from bindProgram_safe p i.env i.heap)
        rw [e] at hb
        cases hb
        rfl
      · rfl
    have halts : Halts p i n.entry := by
      obtain ⟨o, st', hc⟩ := hcomp F le_rfl
      refine ⟨F, ?_⟩
      simp only [HaltsWith, run]
      rw [show ((root p n.entry i).frame.run F).run (root p n.entry i).st = .ok (o, st') from hc]
      rfl
    have atFuel : ∀ f, HaltsWith f p i n.entry →
        (((run f p i n.entry).toOption.getD 0 : ℕ) : ℝ) ≤ C * c.eval i.valuation := by
      intro f hf
      simp only [HaltsWith, run] at hf ⊢
      revert hf
      rcases hres : ((root p n.entry i).frame.run f).run (root p n.entry i).st with
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

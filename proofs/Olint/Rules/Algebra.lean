import Olint.Bound

/-!
# Family A: cost algebra and composition

Soundness lemmas for olint's family A rules (the Phase 2 rule inventory), and the decidable
side conditions `Olint.check` evaluates for them by kernel reduction.

The decidable side conditions are plain structural recursions over `Cost` and the syntax with
`ℕ` and `Bool` arithmetic only, so `decide` evaluates them; each has a soundness lemma here
stating what it establishes about `Cost.eval` on every admitted instance of an entry, with one
constant for all of them: every dimension reads as at least `1`, so the monomial comparison of
`within` holds uniformly, small dimensions included (`monoWithin_le`).

Every lemma holds in every world `W`, whatever its spec-internal step costs `W.ops` and the
intrinsics it modifies: the family A rules rest on none of the G52 drafts' values, only on the
shapes `SpecOps` fixes for them, and consult no intrinsic.

**Composition.** `seq-max`, `branch-join` and `channel-total` compose child certificates: a
child's bound holds at every configuration its entry's run reaches at the child
(`Olint.Bound`), so a parent's run, which is one unit of work followed by its children's runs,
each at most once, is bounded by the maximum of the children's bounds (`bound_compose`). The
composition lemmas unfold the interpreter one step (`execStmt_block`, `execStmt_ite`, …) into
run results continued on completion (`Res.bind`), so a child that throws or violates §2.5 ends
its parent the same way after the same work (`Ends.bind`, `Within.bind`), and use the `Sub`
edges from the parent to each child.

| Rule | olint | Decidable side condition | Soundness lemma |
| --- | --- | --- | --- |
| `seq-max` | cost.rs:2045/1800, walker.rs:675 | `seqSites` on the node, children checked | `seqMax_sound` |
| `seq-max` (unit base) | walker.rs:497, walker.rs:675 | `unitStmt` or `unitExpr` on the node | `unit_bound`, `unitExpr_bound` |
| `branch-join` | walker.rs:506-574 | `branchSites` on the node, children checked | `branchJoin_sound` |
| `channel-total` | cost.rs:2101 | parts checked, channels covered | `channelTotal_sound` |
| `max-dominance` | cost.rs:1826-1850, cost.rs:1009-1038 | `within` per dropped term | `maxDominance_sound` |
| `max-normalise` | cost.rs:288-380 (kind 2) | `maxCovers` over the flattened terms | `maxNormalise_sound` |
| `preference-rank` | cost.rs:1985-2068 | `within` per dropped term, as `max-dominance` | `maxDominance_sound` |
| `product-normalise` | cost.rs:288-380 (kind 1) | `prodMatches` over the expanded factors | `productNormalise_sound` |
| `expr-validity` | cost.rs:383-475 | `valid` | `valid_nonneg` |
| `limit-compare` | cost.rs:863-898, main.rs:290-316 | `within` | `limitCompare_sound` |

`preference-rank` keeps the part of higher preference rank and drops the other's cost whatever
its magnitude; its certificate is checked as `max-dominance`, so it is accepted exactly where
the dropped cost is `O` of the kept one, and the drop of a costlier part (ledger gap G1) is
rejected. The family A rules `nest-product` (cost.rs:2150-2191) and `partial-bind-known`
(cost.rs:124-156) are pending their soundness proofs; `Olint.check` rejects them until they
land.
-/

namespace Olint.Rules

open Olint Olint.Model Filter Asymptotics

variable {W : World}

/-! ## Syntactic equality of costs -/

mutual

/-- Structural equality of costs, a kernel-reducible stand-in for `DecidableEq`, which Lean
cannot derive for the nested `Cost`. -/
def Cost.beq : Cost → Cost → Bool
  | .constant a, .constant b => a == b
  | .legacyN, .legacyN => true
  | .legacyLog, .legacyLog => true
  | .legacyNLog, .legacyNLog => true
  | .name a, .name b => a == b
  | .dimension i d, .dimension j e => i == j && d == e
  | .sum as, .sum bs => Cost.beqList as bs
  | .product as, .product bs => Cost.beqList as bs
  | .maximum as, .maximum bs => Cost.beqList as bs
  | .log a, .log b => Cost.beq a b
  | .power a b, .power c d => Cost.beq a c && Cost.beq b d
  | .ratio a b, .ratio c d => Cost.beq a c && Cost.beq b d
  | .factorial a, .factorial b => Cost.beq a b
  | _, _ => false

/-- Structural equality of cost lists. -/
def Cost.beqList : List Cost → List Cost → Bool
  | [], [] => true
  | a :: as, b :: bs => Cost.beq a b && Cost.beqList as bs
  | _, _ => false

end

mutual

theorem Cost.eq_of_beq : ∀ (a b : Cost), Cost.beq a b = true → a = b
  | .constant a, .constant b, h => by simp_all [Cost.beq]
  | .legacyN, .legacyN, _ => rfl
  | .legacyLog, .legacyLog, _ => rfl
  | .legacyNLog, .legacyNLog, _ => rfl
  | .name a, .name b, h => by simp_all [Cost.beq]
  | .dimension i d, .dimension j e, h => by simp_all [Cost.beq]
  | .sum as, .sum bs, h => congrArg Cost.sum (Cost.eq_of_beqList as bs (by simpa [Cost.beq] using h))
  | .product as, .product bs, h =>
    congrArg Cost.product (Cost.eq_of_beqList as bs (by simpa [Cost.beq] using h))
  | .maximum as, .maximum bs, h =>
    congrArg Cost.maximum (Cost.eq_of_beqList as bs (by simpa [Cost.beq] using h))
  | .log a, .log b, h => congrArg Cost.log (Cost.eq_of_beq a b (by simpa [Cost.beq] using h))
  | .power a b, .power c d, h => by
    simp only [Cost.beq, Bool.and_eq_true] at h
    rw [Cost.eq_of_beq a c h.1, Cost.eq_of_beq b d h.2]
  | .ratio a b, .ratio c d, h => by
    simp only [Cost.beq, Bool.and_eq_true] at h
    rw [Cost.eq_of_beq a c h.1, Cost.eq_of_beq b d h.2]
  | .factorial a, .factorial b, h =>
    congrArg Cost.factorial (Cost.eq_of_beq a b (by simpa [Cost.beq] using h))
  | .constant _, .legacyN, h | .constant _, .legacyLog, h | .constant _, .legacyNLog, h
  | .constant _, .name _, h | .constant _, .dimension _ _, h | .constant _, .sum _, h
  | .constant _, .product _, h | .constant _, .maximum _, h | .constant _, .log _, h
  | .constant _, .power _ _, h | .constant _, .ratio _ _, h | .constant _, .factorial _, h
  | .legacyN, .constant _, h | .legacyN, .legacyLog, h | .legacyN, .legacyNLog, h
  | .legacyN, .name _, h | .legacyN, .dimension _ _, h | .legacyN, .sum _, h
  | .legacyN, .product _, h | .legacyN, .maximum _, h | .legacyN, .log _, h
  | .legacyN, .power _ _, h | .legacyN, .ratio _ _, h | .legacyN, .factorial _, h
  | .legacyLog, .constant _, h | .legacyLog, .legacyN, h | .legacyLog, .legacyNLog, h
  | .legacyLog, .name _, h | .legacyLog, .dimension _ _, h | .legacyLog, .sum _, h
  | .legacyLog, .product _, h | .legacyLog, .maximum _, h | .legacyLog, .log _, h
  | .legacyLog, .power _ _, h | .legacyLog, .ratio _ _, h | .legacyLog, .factorial _, h
  | .legacyNLog, .constant _, h | .legacyNLog, .legacyN, h | .legacyNLog, .legacyLog, h
  | .legacyNLog, .name _, h | .legacyNLog, .dimension _ _, h | .legacyNLog, .sum _, h
  | .legacyNLog, .product _, h | .legacyNLog, .maximum _, h | .legacyNLog, .log _, h
  | .legacyNLog, .power _ _, h | .legacyNLog, .ratio _ _, h | .legacyNLog, .factorial _, h
  | .name _, .constant _, h | .name _, .legacyN, h | .name _, .legacyLog, h
  | .name _, .legacyNLog, h | .name _, .dimension _ _, h | .name _, .sum _, h
  | .name _, .product _, h | .name _, .maximum _, h | .name _, .log _, h
  | .name _, .power _ _, h | .name _, .ratio _ _, h | .name _, .factorial _, h
  | .dimension _ _, .constant _, h | .dimension _ _, .legacyN, h
  | .dimension _ _, .legacyLog, h | .dimension _ _, .legacyNLog, h
  | .dimension _ _, .name _, h | .dimension _ _, .sum _, h | .dimension _ _, .product _, h
  | .dimension _ _, .maximum _, h | .dimension _ _, .log _, h | .dimension _ _, .power _ _, h
  | .dimension _ _, .ratio _ _, h | .dimension _ _, .factorial _, h
  | .sum _, .constant _, h | .sum _, .legacyN, h | .sum _, .legacyLog, h
  | .sum _, .legacyNLog, h | .sum _, .name _, h | .sum _, .dimension _ _, h
  | .sum _, .product _, h | .sum _, .maximum _, h | .sum _, .log _, h
  | .sum _, .power _ _, h | .sum _, .ratio _ _, h | .sum _, .factorial _, h
  | .product _, .constant _, h | .product _, .legacyN, h | .product _, .legacyLog, h
  | .product _, .legacyNLog, h | .product _, .name _, h | .product _, .dimension _ _, h
  | .product _, .sum _, h | .product _, .maximum _, h | .product _, .log _, h
  | .product _, .power _ _, h | .product _, .ratio _ _, h | .product _, .factorial _, h
  | .maximum _, .constant _, h | .maximum _, .legacyN, h | .maximum _, .legacyLog, h
  | .maximum _, .legacyNLog, h | .maximum _, .name _, h | .maximum _, .dimension _ _, h
  | .maximum _, .sum _, h | .maximum _, .product _, h | .maximum _, .log _, h
  | .maximum _, .power _ _, h | .maximum _, .ratio _ _, h | .maximum _, .factorial _, h
  | .log _, .constant _, h | .log _, .legacyN, h | .log _, .legacyLog, h
  | .log _, .legacyNLog, h | .log _, .name _, h | .log _, .dimension _ _, h
  | .log _, .sum _, h | .log _, .product _, h | .log _, .maximum _, h
  | .log _, .power _ _, h | .log _, .ratio _ _, h | .log _, .factorial _, h
  | .power _ _, .constant _, h | .power _ _, .legacyN, h | .power _ _, .legacyLog, h
  | .power _ _, .legacyNLog, h | .power _ _, .name _, h | .power _ _, .dimension _ _, h
  | .power _ _, .sum _, h | .power _ _, .product _, h | .power _ _, .maximum _, h
  | .power _ _, .log _, h | .power _ _, .ratio _ _, h | .power _ _, .factorial _, h
  | .ratio _ _, .constant _, h | .ratio _ _, .legacyN, h | .ratio _ _, .legacyLog, h
  | .ratio _ _, .legacyNLog, h | .ratio _ _, .name _, h | .ratio _ _, .dimension _ _, h
  | .ratio _ _, .sum _, h | .ratio _ _, .product _, h | .ratio _ _, .maximum _, h
  | .ratio _ _, .log _, h | .ratio _ _, .power _ _, h | .ratio _ _, .factorial _, h
  | .factorial _, .constant _, h | .factorial _, .legacyN, h | .factorial _, .legacyLog, h
  | .factorial _, .legacyNLog, h | .factorial _, .name _, h
  | .factorial _, .dimension _ _, h | .factorial _, .sum _, h | .factorial _, .product _, h
  | .factorial _, .maximum _, h | .factorial _, .log _, h | .factorial _, .power _ _, h
  | .factorial _, .ratio _ _, h => by simp [Cost.beq] at h

theorem Cost.eq_of_beqList : ∀ (a b : List Cost), Cost.beqList a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Cost.beqList, Bool.and_eq_true] at h
    rw [Cost.eq_of_beq a b h.1, Cost.eq_of_beqList as bs h.2]
  | [], _ :: _, h => by simp [Cost.beqList] at h
  | _ :: _, [], h => by simp [Cost.beqList] at h

end

/-! ## Run results

A run result completes (`.ok`) or stops, recording why and the work done so far. A composite
node's result continues its first child's result on completion (`Res.bind`): a child that
throws or violates §2.5 ends the node the same way, after the same work. -/

/-- Continue a run result with `k` on completion; a stop propagates unchanged. -/
def Res.bind {α β : Type} (r : Except (Abort × ℕ) (α × St))
    (k : α → St → Except (Abort × ℕ) (β × St)) : Except (Abort × ℕ) (β × St) :=
  match r with
  | .ok (a, st) => k a st
  | .error e => .error e

/-- Map a run result's value. -/
def Res.map {α β : Type} (g : α → β) (r : Except (Abort × ℕ) (α × St)) :
    Except (Abort × ℕ) (β × St) :=
  Res.bind r fun a st => .ok (g a, st)

@[simp] theorem Res.bind_ok {α β : Type} (a : α) (st : St)
    (k : α → St → Except (Abort × ℕ) (β × St)) : Res.bind (.ok (a, st)) k = k a st := rfl

@[simp] theorem Res.bind_error {α β : Type} (e : Abort × ℕ)
    (k : α → St → Except (Abort × ℕ) (β × St)) : Res.bind (.error e) k = .error e := rfl

theorem run_bind' {α β : Type} (x : M α) (g : α → M β) (st : St) :
    (x >>= g).run st = Res.bind (x.run st) fun a s => (g a).run s := by
  rw [run_bind]; rcases x.run st with e | ⟨a, s⟩ <;> rfl

theorem run_map' {α β : Type} (g : α → β) (x : M α) (st : St) :
    (g <$> x).run st = Res.map g (x.run st) := by
  rw [run_map]; rcases x.run st with e | ⟨a, s⟩ <;> rfl

theorem _root_.Olint.Ends.bind {α β : Type} {r : Except (Abort × ℕ) (α × St)}
    {k : α → St → Except (Abort × ℕ) (β × St)} (hr : Ends r)
    (hk : ∀ a st, r = .ok (a, st) → Ends (k a st)) : Ends (Res.bind r k) := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · exact hr
  · exact hk a st rfl

theorem _root_.Olint.Ends.map {α β : Type} {g : α → β} {r : Except (Abort × ℕ) (α × St)} (hr : Ends r) :
    Ends (Res.map g r) := hr.bind fun _ _ _ => trivial

theorem _root_.Olint.Ends.of_map {α β : Type} {g : α → β} {r : Except (Abort × ℕ) (α × St)}
    (h : Ends (Res.map g r)) : Ends r := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · exact h
  · trivial

theorem _root_.Olint.Within.error_fuel {α : Type} {P : α → Prop} {w0 w : ℕ} {b : ℝ} :
    Within P w0 b (.error (.fuel, w)) := fun h => by simp [Abort.thrown] at h

theorem _root_.Olint.Within.ok_of {α : Type} {P : α → Prop} {w0 : ℕ} {b : ℝ} {a : α} {st : St}
    (h : (st.work : ℝ) - w0 ≤ b) : Within P w0 b (.ok (a, st)) := fun _ => h

theorem _root_.Olint.Within.bind {α β : Type} {P : β → Prop} {w0 : ℕ} {b1 b2 : ℝ}
    {r : Except (Abort × ℕ) (α × St)} {k : α → St → Except (Abort × ℕ) (β × St)}
    (hr : Within (fun _ => True) w0 b1 r) (hb2 : 0 ≤ b2)
    (hk : ∀ a st, r = .ok (a, st) → Within P st.work b2 (k a st)) :
    Within P w0 (b1 + b2) (Res.bind r k) := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · intro he
    have := hr he
    linarith
  · have h1 : (st.work : ℝ) - w0 ≤ b1 := hr trivial
    have h2 := hk a st rfl
    show Within P w0 (b1 + b2) (k a st)
    revert h2
    rcases k a st with ⟨e, w⟩ | ⟨c, st'⟩
    · intro h2 he
      have := h2 he
      linarith
    · intro h2 hc
      have := h2 hc
      linarith

theorem _root_.Olint.Within.map {α β : Type} {P : β → Prop} {g : α → β} {w0 : ℕ} {b : ℝ}
    {r : Except (Abort × ℕ) (α × St)} (h : Within (fun a => P (g a)) w0 b r) :
    Within P w0 b (Res.map g r) := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · exact h
  · exact h

theorem _root_.Olint.Within.of_map {α β : Type} {P : β → Prop} {g : α → β} {w0 : ℕ} {b : ℝ}
    {r : Except (Abort × ℕ) (α × St)} (h : Within P w0 b (Res.map g r)) :
    Within (fun a => P (g a)) w0 b r := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · exact h
  · exact h

/-- A bound from a later start is a bound from an earlier one plus the work in between. -/
theorem _root_.Olint.Within.shift {α : Type} {P : α → Prop} {w0 w1 k : ℕ} {b : ℝ}
    {r : Except (Abort × ℕ) (α × St)} (h : Within P w1 b r) (hw : w1 ≤ w0 + k) :
    Within P w0 (k + b) r := by
  have hw' : (w1 : ℝ) ≤ w0 + k := by exact_mod_cast hw
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · intro he
    have := h he
    linarith
  · intro ha
    have := h ha
    linarith

/-- Starting one unit of work later costs one unit more from the earlier start. -/
theorem _root_.Olint.Within.tick {α : Type} {P : α → Prop} {st : St} {b : ℝ}
    {r : Except (Abort × ℕ) (α × St)} (h : Within P st.tick.work b r) :
    Within P st.work (1 + b) r := by
  have := h.shift (w0 := st.work) (k := 1) (by simp [St.tick])
  simpa using this

/-! ## Frame results -/

theorem result_expr {env : Env} {x : Expr} {st : St} {f : ℕ} :
    Cfg.result W ⟨.expr env x, st⟩ f = Res.map Outcome.val ((evalExpr W f env x).run st) :=
  run_map' _ _ _

theorem result_stmt {env : Env} {s : Stmt} {st : St} {f : ℕ} :
    Cfg.result W ⟨.stmt env s, st⟩ f =
      Res.map (fun r => Outcome.stmt r.1 r.2) ((execStmt W f env s).run st) :=
  run_map' _ _ _

theorem result_stmts {env : Env} {ss : List Stmt} {st : St} {f : ℕ} :
    Cfg.result W ⟨.stmts env ss, st⟩ f =
      Res.map (fun r => Outcome.stmt r.1 r.2) ((execStmts W f env ss).run st) :=
  run_map' _ _ _

theorem result_callFunc {fn : Func} {env : Env} {self : Value} {args : List Value} {st : St}
    {f : ℕ} :
    Cfg.result W ⟨.callFunc fn env self args, st⟩ f =
      Res.map Outcome.val ((callFunc W f fn env self args).run st) :=
  run_map' _ _ _

theorem runs_stmt {env : Env} {s : Stmt} {st : St} {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs W ⟨.stmt env s, st⟩ f o st' ↔
      ∃ r, (execStmt W f env s).run st = .ok (r, st') ∧ o = .stmt r.1 r.2 := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (execStmt W f env s).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

theorem runs_expr {env : Env} {x : Expr} {st : St} {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs W ⟨.expr env x, st⟩ f o st' ↔
      ∃ v, (evalExpr W f env x).run st = .ok (v, st') ∧ o = .val v := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (evalExpr W f env x).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

/-- A completed expression evaluation, as the `Ev` premise of a later `Sub` edge. -/
theorem ev_expr {env : Env} {x : Expr} {st st1 : St} {f : ℕ} {v : Value}
    (h : (evalExpr W f env x).run st = .ok (v, st1)) : Ev W (.expr env x) st (.val v) st1 :=
  ⟨f, runs_expr.2 ⟨v, h, rfl⟩⟩

/-- A completed statement execution, as the `Ev` premise of a later `Sub` edge. -/
theorem ev_stmt {env : Env} {s : Stmt} {st st1 : St} {f : ℕ} {r : Env × Completion}
    (h : (execStmt W f env s).run st = .ok (r, st1)) : Ev W (.stmt env s) st (.stmt r.1 r.2) st1 :=
  ⟨f, runs_stmt.2 ⟨r, h, rfl⟩⟩

/-- What a bound at an expression site gives about one reached evaluation of it. -/
theorem _root_.Olint.Holds.at_expr {p : Program} {e : Entry} {i : Instance} {x : Expr} {F : ℕ} {B : ℝ}
    {env : Env} {st : St} (h : Holds W p e i (.expr x) allChannels F B)
    (hr : Reach W p e i ⟨.expr env x, st⟩) :
    (∀ f, F ≤ f → Ends ((evalExpr W f env x).run st)) ∧
      ∀ f, Within (fun _ => True) st.work B ((evalExpr W f env x).run st) := by
  obtain ⟨he, hw⟩ := h _ hr ⟨env, rfl⟩
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · have := he f hf
    rw [result_expr] at this
    exact this.of_map
  · have := hw f
    rw [result_expr] at this
    exact this.of_map.restrict fun _ _ => mem_allChannels _

/-- What a bound at a statement site gives about one reached execution of it. -/
theorem _root_.Olint.Holds.at_stmt {p : Program} {e : Entry} {i : Instance} {s : Stmt} {F : ℕ} {B : ℝ}
    {env : Env} {st : St} (h : Holds W p e i (.stmt s) allChannels F B)
    (hr : Reach W p e i ⟨.stmt env s, st⟩) :
    (∀ f, F ≤ f → Ends ((execStmt W f env s).run st)) ∧
      ∀ f, Within (fun _ => True) st.work B ((execStmt W f env s).run st) := by
  obtain ⟨he, hw⟩ := h _ hr ⟨env, rfl⟩
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · have := he f hf
    rw [result_stmt] at this
    exact this.of_map
  · have := hw f
    rw [result_stmt] at this
    exact this.of_map.restrict fun _ _ => mem_allChannels _

/-- A bound at an expression site from bounds on its interpreter results. -/
theorem holds_expr_of {p : Program} {e : Entry} {i : Instance} {x : Expr} {F : ℕ} {B : ℝ}
    (h : ∀ env st, Reach W p e i ⟨.expr env x, st⟩ →
      (∀ f, F ≤ f → Ends ((evalExpr W f env x).run st)) ∧
        ∀ f, Within (fun _ => True) st.work B ((evalExpr W f env x).run st)) :
    Holds W p e i (.expr x) allChannels F B := by
  rintro ⟨fr, st⟩ hr ⟨env, hc⟩
  simp only at hc
  subst hc
  obtain ⟨he, hw⟩ := h env st hr
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · rw [result_expr]; exact (he f hf).map
  · rw [result_expr]; exact (hw f).map.restrict fun _ _ => trivial

/-- A bound at a statement site from bounds on its interpreter results. -/
theorem holds_stmt_of {p : Program} {e : Entry} {i : Instance} {s : Stmt} {F : ℕ} {B : ℝ}
    (h : ∀ env st, Reach W p e i ⟨.stmt env s, st⟩ →
      (∀ f, F ≤ f → Ends ((execStmt W f env s).run st)) ∧
        ∀ f, Within (fun _ => True) st.work B ((execStmt W f env s).run st)) :
    Holds W p e i (.stmt s) allChannels F B := by
  rintro ⟨fr, st⟩ hr ⟨env, hc⟩
  simp only at hc
  subst hc
  obtain ⟨he, hw⟩ := h env st hr
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · rw [result_stmt]; exact (he f hf).map
  · rw [result_stmt]; exact (hw f).map.restrict fun _ _ => trivial

/-! ## Unfolding the interpreter -/

theorem run_tick1 (st : St) : (tick 1).run st = .ok ((), st.tick) := rfl

theorem execStmt_zero (env : Env) (s : Stmt) (st : St) :
    (execStmt W 0 env s).run st = .error (.fuel, st.work) := by
  rw [execStmt]; rfl

theorem evalExpr_zero (env : Env) (x : Expr) (st : St) :
    (evalExpr W 0 env x).run st = .error (.fuel, st.work) := by
  rw [evalExpr]; rfl

theorem callFunc_zero (fn : Func) (env : Env) (self : Value) (args : List Value) (st : St) :
    (callFunc W 0 fn env self args).run st = .error (.fuel, st.work) := by
  rw [callFunc]; rfl

theorem execStmts_zero (env : Env) (ss : List Stmt) (st : St) :
    (execStmts W 0 env ss).run st = .error (.fuel, st.work) := by
  rw [execStmts]; rfl

theorem execStmts_nil (f : ℕ) (env : Env) (st : St) :
    (execStmts W (f + 1) env []).run st = .ok ((env, .normal), st) := by
  rw [execStmts]; rfl

theorem execStmts_cons (f : ℕ) (env : Env) (s : Stmt) (ss : List Stmt) (st : St) :
    (execStmts W (f + 1) env (s :: ss)).run st =
      Res.bind ((execStmt W f env s).run st) fun r st1 =>
        match r.2 with
        | .normal => (execStmts W f r.1 ss).run st1
        | c => .ok ((r.1, c), st1) := by
  simp only [execStmts, run_bind]
  rcases (execStmt W f env s).run st with e | ⟨⟨env', c⟩, st1⟩
  · rfl
  · cases c <;> rfl

theorem execStmt_block (f : ℕ) (env : Env) (ss : List Stmt) (st : St) :
    (execStmt W (f + 1) env (.block ss)).run st =
      Res.bind ((instantiate W env ss).run st.tick) fun env' st1 =>
        Res.map (fun r => (env, r.2)) ((execStmts W f env' ss).run st1) := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (instantiate W env ss).run st.tick with e | ⟨env', st1⟩
  · rfl
  · simp only [Res.bind_ok]
    rcases (execStmts W f env' ss).run st1 with e | ⟨⟨env'', c⟩, st2⟩ <;> rfl

theorem execStmt_expr (f : ℕ) (env : Env) (x : Expr) (st : St) :
    (execStmt W (f + 1) env (.expr x)).run st =
      Res.map (fun _ => (env, .normal)) ((evalExpr W f env x).run st.tick) := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr W f env x).run st.tick with e | ⟨v, st1⟩ <;> rfl

theorem execStmt_ret (f : ℕ) (env : Env) (x : Expr) (st : St) :
    (execStmt W (f + 1) env (.ret (some x))).run st =
      Res.map (fun v => (env, .ret v)) ((evalExpr W f env x).run st.tick) := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr W f env x).run st.tick with e | ⟨v, st1⟩ <;> rfl

theorem execStmt_decl (f : ℕ) (env : Env) (k : DeclKind) (y : Name) (τ : Ty) (x : Expr)
    (st : St) :
    (execStmt W (f + 1) env (.decl k y τ (some x))).run st =
      Res.bind ((evalExpr W f env x).run st.tick) fun v st1 =>
        Res.map (fun env' => (env', .normal)) ((initBinding env k y τ (some v)).run st1) := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr W f env x).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only [run_pure, Res.bind_ok]
    rcases (initBinding env k y τ (some v)).run st1 with e | ⟨env', st2⟩ <;> rfl

theorem execStmt_ite (f : ℕ) (env : Env) (c : Expr) (t : Stmt) (el : Option Stmt) (st : St) :
    (execStmt W (f + 1) env (.ite c t el)).run st =
      Res.bind ((evalExpr W f env c).run st.tick) fun v st1 =>
        if truthy v then Res.map (fun r => (env, r.2)) ((execStmt W f env t).run st1)
        else match el with
          | some g => Res.map (fun r => (env, r.2)) ((execStmt W f env g).run st1)
          | none => .ok ((env, .normal), st1) := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr W f env c).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only [Res.bind_ok]
    split
    · simp only [run_bind]
      rcases (execStmt W f env t).run st1 with e | ⟨⟨env', c'⟩, st2⟩ <;> rfl
    · cases el with
      | none => rfl
      | some g =>
        simp only [run_bind]
        rcases (execStmt W f env g).run st1 with e | ⟨⟨env', c'⟩, st2⟩ <;> rfl

theorem evalExpr_cond (f : ℕ) (env : Env) (c t g : Expr) (st : St) :
    (evalExpr W (f + 1) env (.cond c t g)).run st =
      Res.bind ((evalExpr W f env c).run st.tick) fun v st1 =>
        if truthy v then (evalExpr W f env t).run st1 else (evalExpr W f env g).run st1 := by
  simp only [evalExpr, run_bind, run_tick1]
  rcases (evalExpr W f env c).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only [Res.bind_ok]
    split <;> rfl

theorem evalExpr_lit (f : ℕ) (env : Env) (l : Lit) (st : St) :
    (evalExpr W (f + 1) env (.lit l)).run st = .ok (l.value, st.tick) := by
  simp only [evalExpr, run_bind, run_tick1]; rfl

theorem callFunc_succ (f : ℕ) (ps : List (Name × Ty)) (body : List Stmt) (ar : Bool) (env : Env)
    (self : Value) (args : List Value) (st : St) :
    (callFunc W (f + 1) (.mk ps body ar) env self args).run st =
      Res.bind ((enterFunc W (.mk ps body ar) env self args).run st) fun env' st1 =>
        Res.map (fun r => match r.2 with | .ret v => v | _ => .undef)
          ((execStmts W f env' body).run st1) := by
  simp only [callFunc, run_bind]
  rcases (enterFunc W (.mk ps body ar) env self args).run st with e | ⟨env', st1⟩
  · rfl
  · simp only [Res.bind_ok]
    rcases (execStmts W f env' body).run st1 with e | ⟨⟨env'', c⟩, st2⟩
    · rfl
    · cases c <;> rfl

/-- A computation that never aborts and performs at most `w` work completes, and the result
it continues is its continuation's. -/
theorem _root_.Olint.Model.SafeW.res {α β : Type} {x : M α} {w : ℕ} (hx : SafeW x w) (st : St)
    (k : α → St → Except (Abort × ℕ) (β × St)) :
    ∃ a st1, x.run st = .ok (a, st1) ∧ Res.bind (x.run st) k = k a st1 ∧
      st1.work ≤ st.work + w := by
  obtain ⟨a, h, n, hn, e⟩ := hx st
  exact ⟨a, ⟨h, st.work + n⟩, e, by rw [e]; rfl, by simp only; omega⟩

/-! ## Statement lists -/

theorem holds_stmts {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (ss0 : List Stmt) (h : ∀ s ∈ ss0, Holds W p e i (.stmt s) allChannels F B) :
    ∀ ss : List Stmt, (∀ s ∈ ss, s ∈ ss0) → ∀ env st, Reach W p e i ⟨.stmts env ss, st⟩ →
      (∀ f, F + ss.length + 1 ≤ f → Ends ((execStmts W f env ss).run st)) ∧
      ∀ f, Within (fun _ => True) st.work (ss.length * B) ((execStmts W f env ss).run st)
  | [], _, env, st, _ => by
    refine ⟨fun f hf => ?_, fun f => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      rw [execStmts_nil]; trivial
    · cases f with
      | zero => rw [execStmts_zero]; exact Within.error_fuel
      | succ f => rw [execStmts_nil]; exact Within.ok_of (by simp)
  | s :: ss, hss, env, st, hr => by
    have hs0 : s ∈ ss0 := hss s (by simp)
    have hhead : Reach W p e i ⟨.stmt env s, st⟩ := hr.tail Sub.stmtsHead
    obtain ⟨he, hw⟩ := (h s hs0).at_stmt hhead
    have tail := fun env' st1 (htail : Reach W p e i ⟨.stmts env' ss, st1⟩) =>
      holds_stmts hB ss0 h ss (fun s' hs' => hss s' (by simp [hs'])) env' st1 htail
    have hlB : (0 : ℝ) ≤ ss.length * B := mul_nonneg (Nat.cast_nonneg _) hB
    refine ⟨fun f hf => ?_, fun f => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      rw [execStmts_cons]
      refine (he f' (by simp at hf; omega)).bind fun r st1 hres => ?_
      obtain ⟨env', c⟩ := r
      cases c with
      | normal =>
        exact (tail env' st1 (hr.tail (Sub.stmtsTail (ev_stmt hres)))).1 f'
          (by simp at hf; omega)
      | _ => trivial
    · cases f with
      | zero => rw [execStmts_zero]; exact Within.error_fuel
      | succ f =>
        rw [execStmts_cons]
        have hlen : ((s :: ss).length : ℝ) * B = B + ss.length * B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
        rw [hlen]
        refine (hw f).bind hlB fun r st1 hres => ?_
        obtain ⟨env', c⟩ := r
        cases c with
        | normal => exact (tail env' st1 (hr.tail (Sub.stmtsTail (ev_stmt hres)))).2 f
        | _ => exact Within.ok_of (by simpa using hlB)

theorem root_eq (p : Program) (e : Entry) (i : Instance) :
    ∃ env h, root p e i = ⟨.callFunc e.fn env i.receiver i.args, ⟨h, 0⟩⟩ := by
  obtain ⟨env, h, hb⟩ := bindProgram_safe p i.env i.heap
  exact ⟨env, h, by unfold root; rw [hb]⟩

/-- The children a node runs in sequence, each at most once (`seq-max`): an entry's body
statements, a block's statements, and the expression of an expression statement, an
initialised declaration or a `return`. -/
def seqSites (e : Entry) : Site → Option (List Site)
  | .entry => match e.fn with
    | .mk _ body _ => some (body.map .stmt)
  | .stmt (.block ss) => some (ss.map .stmt)
  | .stmt (.expr x) => some [.expr x]
  | .stmt (.decl _ _ _ (some x)) => some [.expr x]
  | .stmt (.ret (some x)) => some [.expr x]
  | _ => none

/-- The children of a branch (`branch-join`): the test, then one of the branches. -/
def branchSites : Site → Option (List Site)
  | .stmt (.ite c t none) => some [.expr c, .stmt t]
  | .stmt (.ite c t (some g)) => some [.expr c, .stmt t, .stmt g]
  | .expr (.cond c t g) => some [.expr c, .expr t, .expr g]
  | _ => none

/-- A statement whose run is one unit of work, then its expression child, then a step with no
work that cannot stop: the statement ends one fuel unit after its child and does one more unit
of work. -/
theorem holds_stmt_single {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ}
    {s : Stmt} {x : Expr}
    (hsub : ∀ env st, Sub W ⟨.stmt env s, st⟩ ⟨.expr env x, st.tick⟩)
    (hunf : ∀ f env st, ∃ k : Value → St → Except (Abort × ℕ) ((Env × Completion) × St),
      (execStmt W (f + 1) env s).run st = Res.bind ((evalExpr W f env x).run st.tick) k ∧
        ∀ v st1, ∃ r h, k v st1 = .ok (r, ⟨h, st1.work⟩))
    (h : Holds W p e i (.expr x) allChannels F B) :
    Holds W p e i (.stmt s) allChannels (F + 1) (1 + B) := by
  refine holds_stmt_of fun env st hr => ?_
  obtain ⟨he, hw⟩ := h.at_expr (hr.tail (hsub env st))
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨k, hk, hsafe⟩ := hunf f' env st
    rw [hk]
    refine (he f' (by omega)).bind fun v st1 _ => ?_
    obtain ⟨r, h', e'⟩ := hsafe v st1
    rw [e']; trivial
  · cases f with
    | zero => rw [execStmt_zero]; exact Within.error_fuel
    | succ f =>
      obtain ⟨k, hk, hsafe⟩ := hunf f env st
      rw [hk]
      have := Within.tick (Within.bind (P := fun _ : Env × Completion => True) (k := k)
        (b2 := 0) (hw f) le_rfl fun v st1 _ => by
          obtain ⟨r, h', e'⟩ := hsafe v st1
          rw [e']
          exact Within.ok_of (by simp))
      exact this.mono (by linarith)

/-- The work a sequence node does besides its children's: one unit, and for a function body or
a block, the creation of the function objects its declaration instantiation hoists. -/
def seqK (W : World) (e : Entry) : Site → ℝ
  | .entry => match e.fn with
    | .mk _ body _ => 1 + ((funDecls body).length * W.ops.closureCreate : ℕ)
  | .stmt (.block ss) => 1 + ((funDecls ss).length * W.ops.closureCreate : ℕ)
  | _ => 1

theorem one_le_seqK (W : World) (e : Entry) (s : Site) : 1 ≤ seqK W e s := by
  unfold seqK
  split
  · split; simp only [le_add_iff_nonneg_right]; positivity
  · simp only [le_add_iff_nonneg_right]; positivity
  · exact le_rfl

theorem holds_seq {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} {s : Site}
    {sites : List Site} (hs : seqSites e s = some sites) (hB : 0 ≤ B)
    (h : ∀ x ∈ sites, Holds W p e i x allChannels F B) :
    Holds W p e i s allChannels (F + sites.length + 2) (seqK W e s + sites.length * B) := by
  have hlB : (0 : ℝ) ≤ sites.length * B := mul_nonneg (Nat.cast_nonneg _) hB
  cases s with
  | expr x => simp [seqSites] at hs
  | entry =>
    rcases hfn : e.fn with ⟨ps, body, ar⟩
    simp only [seqSites, hfn, Option.some.injEq] at hs
    subst hs
    have hbody : ∀ t ∈ body, Holds W p e i (.stmt t) allChannels F B := fun t ht =>
      h _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    intro c hr ha
    obtain ⟨env, h0, hroot⟩ := root_eq p e i
    simp only [Cfg.At] at ha
    subst ha
    rw [hroot] at hr ⊢
    rw [hfn] at hr ⊢
    have hsafe := SafeW.enterFunc W ps body ar env i.receiver i.args
    simp only [List.length_map, seqK, hfn] at hlB ⊢
    refine ⟨fun f hf => ?_, fun f => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [result_callFunc, callFunc_succ]
      obtain ⟨env', st1, hx, hb, _⟩ := hsafe.res ⟨h0, 0⟩ fun env' st1 =>
        Res.map (fun r => match r.2 with | .ret v => v | _ => .undef)
          ((execStmts W f' env' body).run st1)
      rw [hb]
      exact ((holds_stmts hB body hbody body (fun t ht => ht) env' st1
        (hr.tail (Sub.callFunc hx))).1 f' (by omega)).map.map
    · cases f with
      | zero => rw [result_callFunc, callFunc_zero]; exact Within.error_fuel
      | succ f =>
        rw [result_callFunc, callFunc_succ]
        obtain ⟨env', st1, hx, hb, hw1⟩ := hsafe.res ⟨h0, 0⟩ fun env' st1 =>
          Res.map (fun r => match r.2 with | .ret v => v | _ => .undef)
            ((execStmts W f env' body).run st1)
        rw [hb]
        have := ((holds_stmts hB body hbody body (fun t ht => ht) env' st1
          (hr.tail (Sub.callFunc hx))).2 f).map (g := fun r =>
            match r.2 with | .ret v => v | _ => .undef) |>.map (g := Outcome.val)
          |>.restrict (Q := fun o => o.channel ∈ allChannels) fun _ _ => trivial
        have := this.shift (w0 := 0) (k := (funDecls body).length * W.ops.closureCreate) hw1
        refine this.mono ?_
        push_cast
        linarith
  | stmt st0 =>
  cases st0 with
  | block ss =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have hss : ∀ t ∈ ss, Holds W p e i (.stmt t) allChannels F B := fun t ht =>
      h _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    have hsafe := fun env => SafeW.instantiate W env ss
    simp only [List.length_map, seqK] at hlB ⊢
    refine holds_stmt_of fun env st hr => ⟨fun f hf => ?_, fun f => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [execStmt_block]
      obtain ⟨env', st1, hx, hb, _⟩ := (hsafe env).res st.tick fun env' st1 =>
        Res.map (fun r => (env, r.2)) ((execStmts W f' env' ss).run st1)
      rw [hb]
      exact ((holds_stmts hB ss hss ss (fun t ht => ht) env' st1
        (hr.tail (Sub.block hx))).1 f' (by omega)).map
    · cases f with
      | zero => rw [execStmt_zero]; exact Within.error_fuel
      | succ f =>
        rw [execStmt_block]
        obtain ⟨env', st1, hx, hb, hw1⟩ := (hsafe env).res st.tick fun env' st1 =>
          Res.map (fun r => (env, r.2)) ((execStmts W f env' ss).run st1)
        rw [hb]
        have := ((holds_stmts hB ss hss ss (fun t ht => ht) env' st1
          (hr.tail (Sub.block hx))).2 f).map (g := fun r => (env, r.2))
          |>.restrict (Q := fun _ => True) fun _ _ => trivial
        have := (this.shift (k := (funDecls ss).length * W.ops.closureCreate) hw1).tick
        refine this.mono ?_
        push_cast
        linarith
  | expr x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .expr x) (x := x) (fun env st => Sub.exprStmt)
      (fun f env st => ⟨_, execStmt_expr f env x st, fun v st1 => ⟨_, st1.heap, rfl⟩⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp [seqK])
  | ret init =>
    cases init with
    | none => simp [seqSites] at hs
    | some x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .ret (some x)) (x := x) (fun env st => Sub.retExpr)
      (fun f env st => ⟨_, execStmt_ret f env x st, fun v st1 => ⟨_, st1.heap, rfl⟩⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp [seqK])
  | decl k y τ init =>
    cases init with
    | none => simp [seqSites] at hs
    | some x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .decl k y τ (some x)) (x := x) (fun env st => Sub.declInit)
      (fun f env st => ⟨_, execStmt_decl f env k y τ x st, fun v st1 => by
        obtain ⟨env', h3, hb⟩ := Safe.initBinding env k y τ (some v) st1
        exact ⟨(env', .normal), h3, by simp only [Res.map, hb]; rfl⟩⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp [seqK])
  | ite | forLoop | forOf | forIn | «while» | doWhile | brk | cont | funDecl | classDecl =>
    simp [seqSites] at hs

/-- A branch child's bound from the test's completion, at the `Sub` edge the test's value
selects. -/
theorem holds_branch {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} {s : Site}
    {sites : List Site} (hs : branchSites s = some sites) (hB : 0 ≤ B)
    (h : ∀ x ∈ sites, Holds W p e i x allChannels F B) :
    Holds W p e i s allChannels (F + sites.length + 2) (1 + sites.length * B) := by
  have hlen2 : (2 : ℝ) ≤ sites.length := by
    cases s with
    | entry => simp [branchSites] at hs
    | expr x =>
      cases x <;> simp [branchSites] at hs
      subst hs; norm_num
    | stmt s0 =>
      cases s0 <;> simp [branchSites] at hs
      split at hs <;> cases hs <;> norm_num
  have hF2 : 2 ≤ sites.length := by exact_mod_cast hlen2
  have hB2 : 1 + 2 * B ≤ 1 + sites.length * B := by nlinarith
  cases s with
  | entry => simp [branchSites] at hs
  | expr x =>
    cases x with
    | cond c t g =>
      simp only [branchSites, Option.some.injEq] at hs
      subst hs
      refine holds_expr_of fun env st hr => ?_
      obtain ⟨hce, hcw⟩ := (h (.expr c) (by simp)).at_expr (hr.tail Sub.condTest)
      have hbr : ∀ v st1 f0, (evalExpr W f0 env c).run st.tick = .ok (v, st1) →
          (∀ f, F ≤ f → Ends (if truthy v then (evalExpr W f env t).run st1
            else (evalExpr W f env g).run st1)) ∧
          ∀ f, Within (fun _ => True) st1.work B (if truthy v then (evalExpr W f env t).run st1
            else (evalExpr W f env g).run st1) := by
        intro v st1 f0 h0
        cases hv : truthy v
        · simpa using Holds.at_expr (h (.expr g) (by simp))
            (hr.tail (Sub.condElse (ev_expr h0) hv))
        · simpa using Holds.at_expr (h (.expr t) (by simp))
            (hr.tail (Sub.condThen (ev_expr h0) hv))
      refine ⟨fun f hf => ?_, fun f => ?_⟩
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [evalExpr_cond]
        exact Ends.bind (hce f' (by omega)) fun v st1 h1 => (hbr v st1 f' h1).1 f' (by omega)
      · cases f with
        | zero => rw [evalExpr_zero]; exact Within.error_fuel
        | succ f =>
          rw [evalExpr_cond]
          have := Within.tick (Within.bind (hcw f) hB fun v st1 h1 => (hbr v st1 f h1).2 f)
          refine this.mono ?_
          linarith
    | _ => simp [branchSites] at hs
  | stmt s0 =>
    cases s0 with
    | ite c t el =>
      have hsites : sites = [.expr c, .stmt t] ++ el.toList.map .stmt := by
        cases el <;> simp_all [branchSites]
      subst hsites
      refine holds_stmt_of fun env st hr => ?_
      obtain ⟨hce, hcw⟩ := (h (.expr c) (by simp)).at_expr (hr.tail Sub.iteTest)
      -- The continuation after the test, from its value.
      have hbr : ∀ v st1 f0, (evalExpr W f0 env c).run st.tick = .ok (v, st1) →
          (∀ f, F ≤ f → Ends (if truthy v then
            Res.map (fun r => (env, r.2)) ((execStmt W f env t).run st1)
            else match el with
              | some g => Res.map (fun r => (env, r.2)) ((execStmt W f env g).run st1)
              | none => .ok ((env, .normal), st1))) ∧
          ∀ f, Within (fun _ => True) st1.work B (if truthy v then
            Res.map (fun r => (env, r.2)) ((execStmt W f env t).run st1)
            else match el with
              | some g => Res.map (fun r => (env, r.2)) ((execStmt W f env g).run st1)
              | none => .ok ((env, .normal), st1)) := by
        intro v st1 f0 h0
        cases hv : truthy v
        · cases el with
          | none => exact ⟨fun _ _ => trivial, fun _ => Within.ok_of (by simpa using hB)⟩
          | some g =>
            obtain ⟨a, b⟩ := (h (.stmt g) (by simp)).at_stmt
              (hr.tail (Sub.iteElse (ev_expr h0) hv))
            exact ⟨fun f hf => (a f hf).map, fun f => (b f).map⟩
        · obtain ⟨a, b⟩ := (h (.stmt t) (by simp)).at_stmt
            (hr.tail (Sub.iteThen (ev_expr h0) hv))
          exact ⟨fun f hf => (a f hf).map, fun f => (b f).map⟩
      refine ⟨fun f hf => ?_, fun f => ?_⟩
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [execStmt_ite]
        exact (hce f' (by omega)).bind fun v st1 h1 => (hbr v st1 f' h1).1 f' (by omega)
      · cases f with
        | zero => rw [execStmt_zero]; exact Within.error_fuel
        | succ f =>
          rw [execStmt_ite]
          have := ((hcw f).bind hB fun v st1 h1 => (hbr v st1 f h1).2 f).tick
          refine this.mono ?_
          linarith
    | _ => simp [branchSites] at hs

/-! ## Unit bases

A unit base bounds a node by `1` from its syntax alone (`seq-max` without premises): from every
state, the node's run ends after a number of steps its syntax fixes, whatever values its
variables hold. The fragment is the syntax whose evaluation consults no value's kind beyond
`ToBoolean` and `typeof`: literals, variable reads (a name the model does not resolve to a
built-in global, whose read consults an intrinsic), `this`, `!`, `typeof`, the short-circuit
operators, conditionals, assignments to a variable and function expressions; and the statements
built from them, blocks, `if`, `return`, `break`, `continue` and function declarations. A read
of a binding ends by completing, by a ReferenceError in its temporal dead zone or of an
unresolvable name, or by a §2.5 violation (`Olint.Model.readVar`): each an end (`Ends`). Each
evaluation of the fragment costs its syntax's ticks (`unitTicksE`, `unitTicksS`), and runs out
of fuel only below its depth (`unitDepthE`, `unitDepthS`).

Operators whose work depends on the kind of their operands, arithmetic, comparisons, `+`,
property reads, compound assignments and updates, lie outside the fragment: on a String or an
object they run `ToNumber`, `ToString` or a property lookup whose work is not fixed by syntax,
or that the model leaves outside it. -/

/-- The value-kind-independent expression fragment. -/
def unitExpr : Expr → Bool
  | .lit _ => true
  | .ident x => (builtinGlobal x).isNone
  | .«this» => true
  | .unary .not a | .unary .typeof a => unitExpr a
  | .binary .and a b | .binary .or a b | .binary .nullish a b => unitExpr a && unitExpr b
  | .cond c t g => unitExpr c && unitExpr t && unitExpr g
  | .assign _ a => unitExpr a
  | .func _ => true
  | _ => false

/-- The work a fragment expression performs, at most. -/
def unitTicksE (W : World) : Expr → ℕ
  | .unary _ a => 1 + unitTicksE W a
  | .binary _ a b => 1 + unitTicksE W a + unitTicksE W b
  | .cond c t g => 1 + unitTicksE W c + unitTicksE W t + unitTicksE W g
  | .assign _ a => 1 + unitTicksE W a
  | .func _ => 1 + W.ops.closureCreate
  | _ => 1

/-- The fuel a fragment expression needs. -/
def unitDepthE : Expr → ℕ
  | .unary _ a => 1 + unitDepthE a
  | .binary _ a b => 1 + max (unitDepthE a) (unitDepthE b)
  | .cond c t g => 1 + max (unitDepthE c) (max (unitDepthE t) (unitDepthE g))
  | .assign _ a => 1 + unitDepthE a
  | _ => 1

mutual

/-- The value-kind-independent statement fragment. -/
def unitStmt : Stmt → Bool
  | .expr x => unitExpr x
  | .decl _ _ _ none => true
  | .decl _ _ _ (some x) => unitExpr x
  | .block ss => unitStmts ss
  | .ite c t el => unitExpr c && unitStmt t && unitOptStmt el
  | .ret none => true
  | .ret (some x) => unitExpr x
  | .brk | .cont => true
  | .funDecl _ _ => true
  | _ => false

/-- Every statement of the list lies in the fragment. -/
def unitStmts : List Stmt → Bool
  | [] => true
  | s :: ss => unitStmt s && unitStmts ss

/-- An absent statement, or one in the fragment. -/
def unitOptStmt : Option Stmt → Bool
  | none => true
  | some s => unitStmt s

end

mutual

/-- The work a fragment statement performs, at most. -/
def unitTicksS (W : World) : Stmt → ℕ
  | .expr x => 1 + unitTicksE W x
  | .decl _ _ _ none => 1
  | .decl _ _ _ (some x) => 1 + unitTicksE W x
  | .block ss => 1 + (funDecls ss).length * W.ops.closureCreate + unitTicksList W ss
  | .ite c t el => 1 + unitTicksE W c + unitTicksS W t + unitTicksOpt W el
  | .ret none => 1
  | .ret (some x) => 1 + unitTicksE W x
  | .brk | .cont => 1
  | .funDecl _ _ => 1 + W.ops.closureCreate
  | _ => 0

/-- The work a list of fragment statements performs, at most. -/
def unitTicksList (W : World) : List Stmt → ℕ
  | [] => 0
  | s :: ss => unitTicksS W s + unitTicksList W ss

/-- The work an optional fragment statement performs, at most. -/
def unitTicksOpt (W : World) : Option Stmt → ℕ
  | none => 0
  | some s => unitTicksS W s

end

mutual

/-- The fuel a fragment statement needs. -/
def unitDepthS : Stmt → ℕ
  | .expr x => 1 + unitDepthE x
  | .decl _ _ _ (some x) => 1 + unitDepthE x
  | .block ss => 1 + unitDepthList ss
  | .ite c t el => 1 + max (unitDepthE c) (max (unitDepthS t) (unitDepthOpt el))
  | .ret (some x) => 1 + unitDepthE x
  | _ => 1

/-- The fuel a list of fragment statements needs. -/
def unitDepthList : List Stmt → ℕ
  | [] => 1
  | s :: ss => 1 + max (unitDepthS s) (unitDepthList ss)

/-- The fuel an optional fragment statement needs. -/
def unitDepthOpt : Option Stmt → ℕ
  | none => 0
  | some s => unitDepthS s

end

/-- A unit run's result from work `w0`: it ends after at most `t` units, or runs out of fuel `f`
below the depth `d`. -/
def UnitR {α : Type} (r : Except (Abort × ℕ) (α × St)) (w0 t d f : ℕ) : Prop :=
  match r with
  | .ok (_, st') => st'.work ≤ w0 + t
  | .error (e, w) => (e = .fuel ∧ f < d) ∨ ((e.thrown = true ∨ e = .typeViolation) ∧ w ≤ w0 + t)

theorem UnitR.mono {α : Type} {r : Except (Abort × ℕ) (α × St)} {w0 t t' d d' f : ℕ}
    (h : UnitR r w0 t d f) (ht : t ≤ t') (hd : d ≤ d') : UnitR r w0 t' d' f := by
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · show st'.work ≤ w0 + t'
    have : st'.work ≤ w0 + t := h
    omega

theorem UnitR.bind {α β : Type} {r : Except (Abort × ℕ) (α × St)}
    {k : α → St → Except (Abort × ℕ) (β × St)} {w0 t1 t2 d f : ℕ} (hr : UnitR r w0 t1 d f)
    (hk : ∀ a st, r = .ok (a, st) → UnitR (k a st) st.work t2 d f) :
    UnitR (Res.bind r k) w0 (t1 + t2) d f := by
  rcases r with ⟨e, w⟩ | ⟨a, st⟩
  · rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, by omega⟩
  · have h1 : st.work ≤ w0 + t1 := hr
    have h2 := hk a st rfl
    show UnitR (k a st) w0 (t1 + t2) d f
    revert h2
    rcases k a st with ⟨e, w⟩ | ⟨c, st'⟩
    · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · exact Or.inl ⟨h3, h4⟩
      · exact Or.inr ⟨h3, by omega⟩
    · intro h2
      show st'.work ≤ w0 + (t1 + t2)
      have : st'.work ≤ st.work + t2 := h2
      omega

theorem UnitR.map {α β : Type} {g : α → β} {r : Except (Abort × ℕ) (α × St)} {w0 t d f : ℕ}
    (h : UnitR r w0 t d f) : UnitR (Res.map g r) w0 t d f := by
  have := UnitR.bind (k := fun a st => .ok (g a, st)) (t2 := 0) h fun a st _ =>
    (show st.work ≤ st.work + 0 by omega)
  simpa [Res.map] using this

theorem UnitR.tick {α : Type} {r : Except (Abort × ℕ) (α × St)} {st : St} {t d f : ℕ}
    (h : UnitR r st.tick.work t d f) : UnitR r st.work (1 + t) d f := by
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, by simp only [St.tick] at h2; omega⟩
  · show st'.work ≤ st.work + (1 + t)
    have : st'.work ≤ st.tick.work + t := h
    simp only [St.tick] at this
    omega

theorem UnitR.succ {α : Type} {r : Except (Abort × ℕ) (α × St)} {w0 t d f : ℕ}
    (h : UnitR r w0 t d f) : UnitR r w0 t (d + 1) (f + 1) := by
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, h2⟩
  · exact h

theorem UnitR.ends {α : Type} {r : Except (Abort × ℕ) (α × St)} {w0 t d f : ℕ}
    (h : UnitR r w0 t d f) (hf : d ≤ f) : Ends r := by
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · exact h1
  · trivial

theorem UnitR.within {α : Type} {P : α → Prop} {r : Except (Abort × ℕ) (α × St)} {w0 t d f : ℕ}
    (h : UnitR r w0 t d f) : Within P w0 t r := by
  rcases r with ⟨e, w⟩ | ⟨a, st'⟩
  · intro he
    rcases h with ⟨rfl, _⟩ | ⟨_, h2⟩
    · simp [Abort.thrown] at he
    · have : (w : ℝ) ≤ w0 + t := by exact_mod_cast h2
      linarith
  · intro _
    have : st'.work ≤ w0 + t := h
    have : (st'.work : ℝ) ≤ w0 + t := by exact_mod_cast this
    linarith

/-- A computation that ends with no work and never runs out of fuel: it completes, throws or
violates §2.5, at the work it started from. -/
def Plain {α : Type} (x : M α) : Prop := ∀ st f, UnitR (x.run st) st.work 0 0 f

theorem Plain.unitR {α : Type} {x : M α} (h : Plain x) (st : St) (t d f : ℕ) :
    UnitR (x.run st) st.work t d f := (h st f).mono (Nat.zero_le _) (Nat.zero_le _)

theorem Plain.pure {α : Type} (a : α) : Plain (pure a : M α) := fun st _ =>
  show st.work ≤ st.work + 0 by omega

theorem Plain.fail {α : Type} {e : Abort} (he : e.thrown = true ∨ e = .typeViolation) :
    Plain (fail e : M α) := fun st _ => Or.inr ⟨he, by simp⟩

theorem Plain.ofSafe {α : Type} {x : M α} (h : Safe x) : Plain x := fun st _ => by
  obtain ⟨a, h', e⟩ := h st
  rw [e]
  show st.work ≤ st.work + 0
  omega

theorem Plain.bind {α β : Type} {x : M α} {g : α → M β} (hx : Plain x) (hg : ∀ a, Plain (g a)) :
    Plain (x >>= g) := fun st f => by
  rw [run_bind']
  have := UnitR.bind (t2 := 0) (hx st f) fun a st1 _ => hg a st1 f
  simpa using this

theorem Plain.ofLoad (l : Loc) : Plain (load l) := by
  unfold Olint.Model.load
  refine Plain.bind (Plain.ofSafe Safe.get) fun s => ?_
  split
  · exact Plain.pure _
  · exact Plain.fail (Or.inl rfl)

theorem Plain.ofReadVarTy (l : Loc) : Plain (readVarTy l) := by
  unfold Olint.Model.readVarTy
  refine Plain.bind (Plain.ofLoad l) fun o => ?_
  split
  · refine Plain.bind (Plain.ofSafe Safe.get) fun s => ?_
    split
    · exact Plain.pure _
    · exact Plain.fail (Or.inr rfl)
  · exact Plain.fail (Or.inl rfl)
  · exact Plain.fail (Or.inl rfl)

theorem Plain.ofReadVar (l : Loc) : Plain (readVar l) := by
  unfold Olint.Model.readVar
  exact Plain.bind (Plain.ofReadVarTy l) fun _ => Plain.pure _

theorem Plain.ofCellType (l : Loc) : Plain (cellType l) := by
  unfold Olint.Model.cellType
  refine Plain.bind (Plain.ofLoad l) fun o => ?_
  split
  · exact Plain.pure _
  · exact Plain.fail (Or.inl rfl)
  · exact Plain.fail (Or.inl rfl)

theorem Plain.unop_not (v : Value) : Plain (unop .not v) := Plain.pure _

theorem Plain.unop_typeof (v : Value) : Plain (unop .typeof v) := by
  cases v with
  | ref l => exact Plain.bind (Plain.ofLoad l) fun _ => Plain.pure _
  | _ => exact Plain.pure _

theorem _root_.Olint.Model.SafeW.bindFuns (W : World) (env : Env) (fs : List (Name × Func)) :
    SafeW (bindFuns W env fs) (fs.length * W.ops.closureCreate) := by
  unfold Olint.Model.bindFuns
  refine (SafeW.bind (Safe.bindUninit _ _).safeW fun env' =>
    SafeW.bind (SafeW.storeFuns W env' _) fun _ => (Safe.pure _).safeW).mono ?_
  simp

/-- A computation that never aborts and performs at most `w` work is a unit run of `w`
ticks. -/
theorem _root_.Olint.Model.SafeW.unitR {α : Type} {x : M α} {w : ℕ} (h : SafeW x w) (st : St) (d f : ℕ) :
    UnitR (x.run st) st.work w d f := by
  obtain ⟨a, h', n, hn, e⟩ := h st
  rw [e]
  show st.work + n ≤ st.work + w
  omega

theorem unitE_run (f : ℕ) (ih : ∀ x env st, unitExpr x = true →
    UnitR ((evalExpr W f env x).run st) st.work (unitTicksE W x) (unitDepthE x) f) :
    ∀ x env st, unitExpr x = true →
      UnitR ((evalExpr W (f + 1) env x).run st) st.work (unitTicksE W x) (unitDepthE x) (f + 1)
  | .lit l, env, st, _ => by
    rw [evalExpr_lit]
    show st.tick.work ≤ st.work + 1
    simp [St.tick]
  | .ident x, env, st, hx => by
    simp only [unitExpr, Option.isNone_iff_eq_none] at hx
    simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
    refine (UnitR.tick (t := 0) ?_).mono (by simp only [unitTicksE]; omega) le_rfl
    split
    · exact (Plain.ofReadVar _).unitR _ _ _ _
    · rw [hx]; exact (Plain.fail (Or.inl rfl)).unitR _ _ _ _
  | .«this», env, st, _ => by
    simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
    refine (UnitR.tick (t := 0) ?_).mono (by simp only [unitTicksE]; omega) le_rfl
    split
    · exact (Plain.ofReadVar _).unitR _ _ _ _
    · exact (Plain.pure _).unitR _ _ _ _
  | .unary op a, env, st, hx => by
    have ha : unitExpr a = true ∧ (op = .not ∨ op = .typeof) := by
      cases op <;> simp_all [unitExpr]
    obtain ⟨ha, hop⟩ := ha
    rcases hop with rfl | rfl
    · simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
      refine (UnitR.tick (UnitR.bind (t2 := 0) ((ih a env st.tick ha).succ) fun v st1 _ =>
        (Plain.unop_not v).unitR st1 0 _ _)).mono (by simp only [unitTicksE]; omega)
        (by simp only [unitDepthE]; omega)
    · simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
      refine (UnitR.tick (UnitR.bind (t2 := 0) ((ih a env st.tick ha).succ) fun v st1 _ =>
        (Plain.unop_typeof v).unitR st1 0 _ _)).mono (by simp only [unitTicksE]; omega)
        (by simp only [unitDepthE]; omega)
  | .binary op a b, env, st, hx => by
    have hab : unitExpr a = true ∧ unitExpr b = true ∧
        (op = .and ∨ op = .or ∨ op = .nullish) := by
      cases op <;> simp_all [unitExpr]
    obtain ⟨ha, hb, hop⟩ := hab
    have hk : ∀ (o : BinOp) (v : Value) (st1 : St),
        UnitR ((if evaluatesRight o v then evalExpr W f env b else pure v).run st1) st1.work
          (unitTicksE W b) (1 + max (unitDepthE a) (unitDepthE b)) (f + 1) := by
      intro o v st1
      split
      · exact ((ih b env st1 hb).succ).mono le_rfl (by omega)
      · exact (Plain.pure _).unitR _ _ _ _
    have h1 := ((ih a env st.tick ha).succ).mono (t' := unitTicksE W a) le_rfl
      (show unitDepthE a + 1 ≤ 1 + max (unitDepthE a) (unitDepthE b) by omega)
    rcases hop with rfl | rfl | rfl <;>
    · simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
      refine (UnitR.tick (UnitR.bind h1 fun v st1 _ => hk _ v st1)).mono
        (by simp only [unitTicksE]; omega) (by simp only [unitDepthE]; omega)
  | .cond c t g, env, st, hx => by
    simp only [unitExpr, Bool.and_eq_true] at hx
    obtain ⟨⟨hc, ht⟩, hg⟩ := hx
    rw [evalExpr_cond]
    have hd : unitDepthE (.cond c t g) = 1 + max (unitDepthE c) (max (unitDepthE t) (unitDepthE g)) :=
      rfl
    have ht' : unitTicksE W (.cond c t g) = 1 + unitTicksE W c + unitTicksE W t + unitTicksE W g :=
      rfl
    rw [hd, ht']
    refine (UnitR.tick (UnitR.bind (t2 := unitTicksE W t + unitTicksE W g)
      (((ih c env st.tick hc).succ).mono (t' := unitTicksE W c)
        (d' := 1 + max (unitDepthE c) (max (unitDepthE t) (unitDepthE g))) le_rfl (by omega))
        fun v st1 _ => ?_)).mono (by omega) le_rfl
    split
    · exact ((ih t env st1 ht).succ).mono (by omega) (by omega)
    · exact ((ih g env st1 hg).succ).mono (by omega) (by omega)
  | .assign x a, env, st, hx => by
    simp only [unitExpr] at hx
    simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
    refine (UnitR.tick (UnitR.bind (t2 := 0) ((ih a env st.tick hx).succ) fun v st1 _ => ?_)).mono
      (by simp only [unitTicksE]; omega) (by simp only [unitDepthE]; omega)
    split
    · exact (Plain.bind (Plain.ofCellType _) fun _ =>
        Plain.bind (Plain.ofSafe (Safe.store _ _)) fun _ => Plain.pure _).unitR _ _ _ _
    · exact (Plain.fail (Or.inl rfl)).unitR _ _ _ _
  | .func fn, env, st, _ => by
    simp only [evalExpr, run_bind', run_tick1, Res.bind_ok]
    have := (SafeW.bind (SafeW.charge W (·.closureCreate)) fun _ =>
      SafeW.bind (Safe.allocate (.closure fn env)).safeW fun l =>
        (Safe.pure (Value.ref l)).safeW).unitR st.tick (unitDepthE (.func fn)) (f + 1)
    exact (UnitR.tick this).mono (by simp only [unitTicksE]; omega) le_rfl
  | .update _ _ _, _, _, hx | .updateIndex _ _ _ _, _, _, hx | .assignOp _ _ _, _, _, hx
  | .assignIndex _ _ _, _, _, hx | .assignOpIndex _ _ _ _, _, _, hx | .member _ _, _, _, hx
  | .index _ _, _, _, hx | .call _ _, _, _, hx | .new _ _, _, _, hx | .klass _, _, _, hx
  | .array _, _, _, hx | .object _, _, _, hx | .regex _ _, _, _, hx => by simp [unitExpr] at hx

theorem unitE_all : ∀ f x env st, unitExpr x = true →
    UnitR ((evalExpr W f env x).run st) st.work (unitTicksE W x) (unitDepthE x) f
  | 0, x, env, st, _ => by
    rw [evalExpr_zero]
    refine Or.inl ⟨rfl, ?_⟩
    cases x <;> simp only [unitDepthE] <;> omega
  | f + 1, x, env, st, hx => unitE_run f (unitE_all f) x env st hx

theorem unitDepthS_pos (s : Stmt) : 0 < unitDepthS s := by
  cases s with
  | decl _ _ _ init => cases init <;> simp [unitDepthS]
  | ret init => cases init <;> simp [unitDepthS]
  | _ => simp [unitDepthS]

theorem unitDepthList_pos (ss : List Stmt) : 0 < unitDepthList ss := by
  cases ss <;> simp only [unitDepthList] <;> omega

/-- Every fragment statement and statement list ends within its ticks from its depth on. -/
theorem unitS_all : ∀ f : ℕ,
    (∀ s env st, unitStmt s = true →
      UnitR ((execStmt W f env s).run st) st.work (unitTicksS W s) (unitDepthS s) f) ∧
    (∀ ss env st, unitStmts ss = true →
      UnitR ((execStmts W f env ss).run st) st.work (unitTicksList W ss) (unitDepthList ss) f)
  | 0 => ⟨fun s env st _ => by
        rw [execStmt_zero]; exact Or.inl ⟨rfl, unitDepthS_pos s⟩,
      fun ss env st _ => by rw [execStmts_zero]; exact Or.inl ⟨rfl, unitDepthList_pos ss⟩⟩
  | f + 1 => by
    obtain ⟨ihs, ihl⟩ := unitS_all f
    have ihe := unitE_all (W := W) f
    refine ⟨fun s env st hs => ?_, fun ss env st hs => ?_⟩
    · match s, hs with
      | .expr x, hs =>
        rw [execStmt_expr]
        exact (UnitR.tick ((ihe x env st.tick hs).succ.map)).mono
          (by simp only [unitTicksS]; omega) (by simp only [unitDepthS]; omega)
      | .decl k y τ none, _ =>
        simp only [execStmt]
        rw [run_bind', run_tick1, Res.bind_ok]
        have := (Plain.bind (Plain.pure (none : Option Value)) fun v =>
          Plain.bind (Plain.ofSafe (Safe.initBinding env k y τ v)) fun env' =>
            Plain.pure ((env', Completion.normal) : Env × Completion)).unitR st.tick 0 1 (f + 1)
        exact (UnitR.tick this).mono (show 1 + 0 ≤ 1 by omega) (show 1 ≤ 1 by omega)
      | .decl k y τ (some x), hs =>
        simp only [unitStmt] at hs
        rw [execStmt_decl]
        exact (UnitR.tick (UnitR.bind (t2 := 0) (ihe x env st.tick hs).succ fun v st1 _ =>
          ((Plain.ofSafe (Safe.initBinding env k y τ (some v))).unitR st1 0 _ _).map)).mono
          (by simp only [unitTicksS]; omega) (by simp only [unitDepthS]; omega)
      | .block ss, hs =>
        simp only [unitStmt] at hs
        rw [execStmt_block]
        exact (UnitR.tick (UnitR.bind (t2 := unitTicksList W ss)
          ((SafeW.instantiate W env ss).unitR st.tick (unitDepthList ss + 1) (f + 1))
          fun env' st1 _ => ((ihl ss env' st1 hs).succ).map)).mono
          (by simp only [unitTicksS]; omega) (by simp only [unitDepthS]; omega)
      | .ite c t el, hs =>
        simp only [unitStmt, Bool.and_eq_true] at hs
        obtain ⟨⟨hc, ht⟩, hel⟩ := hs
        rw [execStmt_ite]
        have hd : unitDepthS (.ite c t el) =
            1 + max (unitDepthE c) (max (unitDepthS t) (unitDepthOpt el)) := rfl
        have ht' : unitTicksS W (.ite c t el) =
            1 + unitTicksE W c + unitTicksS W t + unitTicksOpt W el := rfl
        rw [hd, ht']
        refine (UnitR.tick (UnitR.bind (t2 := unitTicksS W t + unitTicksOpt W el)
          (((ihe c env st.tick hc).succ).mono (t' := unitTicksE W c)
            (d' := 1 + max (unitDepthE c) (max (unitDepthS t) (unitDepthOpt el))) le_rfl
            (by omega)) fun v st1 _ => ?_)).mono (by omega) le_rfl
        split
        · exact (((ihs t env st1 ht).succ).mono
            (t' := unitTicksS W t + unitTicksOpt W el) (by omega) (by omega)).map
        · cases el with
          | none => show st1.work ≤ st1.work + _; omega
          | some g =>
            simp only [unitOptStmt] at hel
            have h1 : unitTicksOpt W (some g) = unitTicksS W g := rfl
            have h2 : unitDepthOpt (some g) = unitDepthS g := rfl
            rw [h1, h2]
            exact (((ihs g env st1 hel).succ).mono
              (t' := unitTicksS W t + unitTicksS W g) (by omega) (by omega)).map
      | .ret none, _ =>
        simp only [execStmt, run_bind', run_tick1, Res.bind_ok]
        exact (UnitR.tick ((Plain.pure _).unitR _ 0 _ _)).mono
          (by simp only [unitTicksS]; omega) le_rfl
      | .ret (some x), hs =>
        simp only [unitStmt] at hs
        rw [execStmt_ret]
        exact (UnitR.tick ((ihe x env st.tick hs).succ.map)).mono
          (by simp only [unitTicksS]; omega) (by simp only [unitDepthS]; omega)
      | .brk, _ =>
        simp only [execStmt, run_bind', run_tick1, Res.bind_ok]
        exact (UnitR.tick ((Plain.pure _).unitR _ 0 _ _)).mono
          (by simp only [unitTicksS]; omega) le_rfl
      | .cont, _ =>
        simp only [execStmt, run_bind', run_tick1, Res.bind_ok]
        exact (UnitR.tick ((Plain.pure _).unitR _ 0 _ _)).mono
          (by simp only [unitTicksS]; omega) le_rfl
      | .funDecl x fn, _ =>
        simp only [execStmt, run_bind', run_tick1, Res.bind_ok]
        refine (UnitR.tick (t := W.ops.closureCreate) ?_).mono
          (by simp only [unitTicksS]; omega) le_rfl
        split
        · exact (Plain.pure _).unitR _ _ _ _
        · have := (SafeW.bind (SafeW.bindFuns W env [(x, fn)]) fun env' =>
            (Safe.pure ((env', Completion.normal) : Env × Completion)).safeW).unitR st.tick
              (unitDepthS (.funDecl x fn)) (f + 1)
          exact this.mono (by simp) le_rfl
    · match ss, hs with
      | [], _ =>
        rw [execStmts_nil]
        show st.work ≤ st.work + _; omega
      | s :: ss, hs =>
        simp only [unitStmts, Bool.and_eq_true] at hs
        rw [execStmts_cons]
        refine (UnitR.bind (t2 := unitTicksList W ss)
          (((ihs s env st hs.1).succ).mono le_rfl (show unitDepthS s + 1 ≤
            1 + max (unitDepthS s) (unitDepthList ss) by omega)) fun r st1 _ => ?_).mono
          (by simp only [unitTicksList]; omega) (by simp only [unitDepthList]; omega)
        obtain ⟨env', c⟩ := r
        cases c with
        | normal =>
          exact ((ihl ss env' st1 hs.2).succ).mono le_rfl (by omega)
        | ret v => show st1.work ≤ st1.work + _; omega
        | brk => show st1.work ≤ st1.work + _; omega
        | cont => show st1.work ≤ st1.work + _; omega

/-- `seq-max`, unit base: a fragment statement ends from its depth on, within its ticks. -/
theorem holds_unit {p : Program} {e : Entry} {i : Instance} {s : Stmt} (hu : unitStmt s = true) :
    Holds W p e i (.stmt s) allChannels (unitDepthS s) (unitTicksS W s) :=
  holds_stmt_of fun env st _ =>
    ⟨fun f hf => ((unitS_all f).1 s env st hu).ends hf,
      fun f => ((unitS_all f).1 s env st hu).within⟩

/-- A fragment expression ends from its depth on, within its ticks. -/
theorem holds_unitExpr {p : Program} {e : Entry} {i : Instance} {x : Expr}
    (hu : unitExpr x = true) :
    Holds W p e i (.expr x) allChannels (unitDepthE x) (unitTicksE W x) :=
  holds_expr_of fun env st _ =>
    ⟨fun f hf => (unitE_all f x env st hu).ends hf, fun f => (unitE_all f x env st hu).within⟩

/-- A bound of every configuration by a fixed work from fixed fuel is a bound by the constant
`1`. -/
theorem bound_of_holds {p : Program} {n : Node} {F : ℕ} {w : ℝ} (hwf : n.entry.wf p = true)
    (h : ∀ i, Holds W p n.entry i n.site allChannels F w) : Bound W p n (.constant 1) :=
  ⟨hwf, w, Eventually.of_forall fun i => ⟨F, (h i).mono le_rfl (by
    simp [Cost.eval, Cost.raw])⟩⟩

/-! ## Combining children's bounds -/

theorem eval_le_maximum (v : Valuation) :
    ∀ (cs : List Cost) (c : Cost), c ∈ cs → c.eval v ≤ (Cost.maximum cs).eval v := by
  intro cs c hc
  unfold Cost.eval
  refine max_le_max le_rfl ?_
  simp only [Cost.raw]
  induction cs with
  | nil => simp at hc
  | cons d cs ih =>
    simp only [Cost.rawMaximum]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih hc)

theorem mem_zip_left {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length →
    ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, a, h => absurd h (by simp)
  | a :: as, [], h, _, _ => absurd h (by simp)
  | a :: as, b :: bs, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨b', hb'⟩ := mem_zip_left as bs (by simpa using h) x hx
      exact ⟨b', by simp [hb']⟩

/-- Finitely many bounds at nodes of one entry, each by a cost at most `M`, hold together with
one constant and one fuel. -/
theorem combine {p : Program} {e : Entry} {M : Cost} :
    ∀ l : List (Site × List Channel × Cost),
      (∀ x ∈ l, BoundOn W p ⟨e, x.1⟩ x.2.1 x.2.2) → (∀ x ∈ l, ∀ v, x.2.2.eval v ≤ M.eval v) →
      ∃ C, 0 ≤ C ∧ ∀ᶠ i in Admits e, ∃ F, ∀ x ∈ l,
        Holds W p e i x.1 x.2.1 F (C * M.eval i.valuation)
  | [], _, _ => ⟨0, le_rfl, Eventually.of_forall fun _ => ⟨0, fun x hx => absurd hx (by simp)⟩⟩
  | x :: l, hb, hle => by
    obtain ⟨C1, hC1, h1⟩ := (hb x (by simp)).nonneg
    obtain ⟨C2, hC2, h2⟩ := combine l (fun y hy => hb y (by simp [hy]))
      (fun y hy => hle y (by simp [hy]))
    refine ⟨max C1 C2, le_max_of_le_left hC1,
      (h1.and h2).mono fun i ⟨⟨F1, hF1⟩, ⟨F2, hF2⟩⟩ => ⟨max F1 F2, fun y hy => ?_⟩⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · refine hF1.mono (le_max_left _ _) ?_
      have := hle y (by simp) i.valuation
      calc C1 * y.2.2.eval i.valuation ≤ max C1 C2 * y.2.2.eval i.valuation :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (Cost.eval_pos _ _))
        _ ≤ max C1 C2 * M.eval i.valuation :=
            mul_le_mul_of_nonneg_left this (le_max_of_le_left hC1)
    · exact (hF2 y hy).mono (le_max_right _ _)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Cost.eval_pos _ _)))

/-- A node whose run is its children's runs, each at most once, after a fixed amount `K` of
work, is bounded by the maximum of the children's bounds. -/
theorem bound_compose {p : Program} {n : Node} {sites : List Site} {cs : List Cost} {K : ℝ}
    (hwf : n.entry.wf p = true) (hK : 0 ≤ K) (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound W p ⟨n.entry, x.1⟩ x.2)
    (hcomp : ∀ i F B, 0 ≤ B → (∀ s ∈ sites, Holds W p n.entry i s allChannels F B) →
      Holds W p n.entry i n.site allChannels (F + sites.length + 2) (K + sites.length * B)) :
    Bound W p n (.maximum cs) := by
  obtain ⟨C, hC, h⟩ := combine (e := n.entry) (M := .maximum cs)
    ((sites.zip cs).map fun x => (x.1, allChannels, x.2))
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact hchild x hx)
    (fun y hy v => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact eval_le_maximum v cs x.2 (List.of_mem_zip hx).2)
  refine ⟨hwf, K + sites.length * C, h.mono fun i ⟨F, hF⟩ => ⟨F + sites.length + 2, ?_⟩⟩
  have hM := Cost.one_le_eval i.valuation (.maximum cs)
  refine (hcomp i F _ (mul_nonneg hC (by linarith)) fun s hs => ?_).mono le_rfl ?_
  · obtain ⟨c, hc⟩ := mem_zip_left sites cs hlen s hs
    exact hF (s, allChannels, c) (List.mem_map.2 ⟨(s, c), hc, rfl⟩)
  · have : (0 : ℝ) ≤ sites.length * C := mul_nonneg (Nat.cast_nonneg _) hC
    nlinarith

/-- `channel-total`: bounds of one node on channel sets that cover every channel compose into a
bound by their maximum. -/
theorem channelTotal_sound {p : Program} {n : Node} {parts : List (List Channel × Cost)}
    (hwf : n.entry.wf p = true) (hparts : ∀ x ∈ parts, BoundOn W p n x.1 x.2)
    (hcover : ∀ k, ∃ x ∈ parts, k ∈ x.1) :
    Bound W p n (.maximum (parts.map Prod.snd)) := by
  obtain ⟨C, _, h⟩ := combine (e := n.entry) (M := .maximum (parts.map Prod.snd))
    (parts.map fun x => (n.site, x.1, x.2))
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact hparts x hx)
    (fun y hy v => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact eval_le_maximum v _ x.2 (List.mem_map.2 ⟨x, hx, rfl⟩))
  refine ⟨hwf, C, h.mono fun i ⟨F, hF⟩ => ⟨F, fun c hr ha => ⟨?_, fun f => ?_⟩⟩⟩
  · obtain ⟨x, hx, _⟩ := hcover .normal
    exact (hF (n.site, x.1, x.2) (List.mem_map.2 ⟨x, hx, rfl⟩) c hr ha).1
  · -- A completion in channel `k` is bounded by a part covering `k`; a throw, by any part.
    obtain ⟨x0, hx0, _⟩ := hcover .normal
    have hall := fun x (hx : x ∈ parts) =>
      (hF (n.site, x.1, x.2) (List.mem_map.2 ⟨x, hx, rfl⟩) c hr ha).2 f
    revert hall
    rcases c.result W f with ⟨e', w⟩ | ⟨o, st'⟩
    · intro hall he
      exact hall x0 hx0 he
    · intro hall hk
      obtain ⟨x, hx, hk'⟩ := hcover o.channel
      exact hall x hx hk' 

/-- `seq-max`: a sequence node is bounded by the maximum of its children's bounds. -/
theorem seqMax_sound {p : Program} {n : Node} {sites : List Site} {cs : List Cost}
    (hwf : n.entry.wf p = true) (hs : seqSites n.entry n.site = some sites)
    (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound W p ⟨n.entry, x.1⟩ x.2) : Bound W p n (.maximum cs) :=
  bound_compose hwf (le_trans zero_le_one (one_le_seqK W n.entry n.site)) hlen hchild
    fun _ _ _ hB h => holds_seq hs hB h

/-- `branch-join`: a branch node is bounded by the maximum of its test's and branches'
bounds. -/
theorem branchJoin_sound {p : Program} {n : Node} {sites : List Site} {cs : List Cost}
    (hwf : n.entry.wf p = true) (hs : branchSites n.site = some sites)
    (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound W p ⟨n.entry, x.1⟩ x.2) : Bound W p n (.maximum cs) :=
  bound_compose hwf zero_le_one hlen hchild fun _ _ _ hB h => holds_branch hs hB h

/-- `seq-max`, unit base, on bounds: a fragment statement. -/
theorem unit_bound {p : Program} {n : Node} {s : Stmt} (hwf : n.entry.wf p = true)
    (hn : n.site = .stmt s) (hu : unitStmt s = true) : Bound W p n (.constant 1) :=
  bound_of_holds (F := unitDepthS s) (w := (unitTicksS W s : ℝ)) hwf fun i => by
    rw [hn]; exact holds_unit hu

/-- `seq-max`, unit base, on bounds: a fragment expression. -/
theorem unitExpr_bound {p : Program} {n : Node} {x : Expr} (hwf : n.entry.wf p = true)
    (hn : n.site = .expr x) (hu : unitExpr x = true) : Bound W p n (.constant 1) :=
  bound_of_holds (F := unitDepthE x) (w := (unitTicksE W x : ℝ)) hwf fun i => by
    rw [hn]; exact holds_unitExpr hu

/-! ## `expr-validity`

olint's `valid` (cost.rs:383-475) rejects costs whose value is undefined. In the model every
cost has a value; the side condition that matters is that the exact value `Cost.raw` is
nonnegative, which fails only through the legacy envelope `N`, since §2 sets no envelope. -/

mutual

/-- A cost free of the legacy envelope, hence of nonnegative exact value. -/
def valid : Cost → Bool
  | .legacyN => false
  | .legacyNLog => false
  | .constant _ => true
  | .legacyLog => true
  | .name _ => true
  | .dimension _ _ => true
  | .sum cs => validList cs
  | .product cs => validList cs
  | .maximum cs => validList cs
  | .log c => valid c
  | .factorial c => valid c
  | .power a b => valid a && valid b
  | .ratio a b => valid a && valid b

/-- Every cost of the list is valid. -/
def validList : List Cost → Bool
  | [] => true
  | c :: cs => valid c && validList cs

end

/-- A valuation with nonnegative names. -/
def NonnegVal (v : Valuation) : Prop := ∀ s, 0 ≤ v.name s

theorem instance_nonnegVal (i : Instance) : NonnegVal i.valuation := fun _ => le_rfl

theorem rawMaximum_nonneg (v : Valuation) : ∀ cs : List Cost, 0 ≤ Cost.rawMaximum v cs
  | [] => le_refl _
  | _ :: cs => le_max_of_le_right (rawMaximum_nonneg v cs)

theorem rawSum_nonneg (v : Valuation) :
    ∀ cs : List Cost, (∀ c ∈ cs, 0 ≤ c.raw v) → 0 ≤ Cost.rawSum v cs
  | [], _ => le_refl _
  | c :: cs, h => by
    simp only [Cost.rawSum]
    exact add_nonneg (h c (by simp)) (rawSum_nonneg v cs fun d hd => h d (by simp [hd]))

theorem rawProduct_nonneg (v : Valuation) :
    ∀ cs : List Cost, (∀ c ∈ cs, 0 ≤ c.raw v) → 0 ≤ Cost.rawProduct v cs
  | [], _ => zero_le_one
  | c :: cs, h => by
    simp only [Cost.rawProduct]
    exact mul_nonneg (h c (by simp)) (rawProduct_nonneg v cs fun d hd => h d (by simp [hd]))

theorem lg_nonneg (x : ℝ) : 0 ≤ lg x := le_trans zero_le_one (lg_ge_one x)

mutual

/-- `expr-validity`: a valid cost has a nonnegative exact value. -/
theorem valid_nonneg (v : Valuation) (hv : NonnegVal v) :
    ∀ c : Cost, valid c = true → 0 ≤ c.raw v
  | .constant k, _ => by simp [Cost.raw]
  | .legacyLog, _ => by simp only [Cost.raw]; exact lg_nonneg _
  | .name s, _ => by simp only [Cost.raw]; exact hv s
  | .dimension j _, _ => by simp only [Cost.raw]; exact le_trans zero_le_one (le_max_left _ _)
  | .sum cs, h => by
    simp only [Cost.raw]
    exact rawSum_nonneg v cs (validList_nonneg v hv cs (by simpa [valid] using h))
  | .product cs, h => by
    simp only [Cost.raw]
    exact rawProduct_nonneg v cs (validList_nonneg v hv cs (by simpa [valid] using h))
  | .maximum cs, _ => by simp only [Cost.raw]; exact rawMaximum_nonneg v cs
  | .log c, _ => by simp only [Cost.raw]; exact lg_nonneg _
  | .factorial c, _ => by simp only [Cost.raw]; positivity
  | .power a b, h => by
    simp only [valid, Bool.and_eq_true] at h
    simp only [Cost.raw]
    exact Real.rpow_nonneg (valid_nonneg v hv a h.1) _
  | .ratio a b, h => by
    simp only [valid, Bool.and_eq_true] at h
    simp only [Cost.raw]
    exact div_nonneg (valid_nonneg v hv a h.1) (valid_nonneg v hv b h.2)
  | .legacyN, h => by simp [valid] at h
  | .legacyNLog, h => by simp [valid] at h

theorem validList_nonneg (v : Valuation) (hv : NonnegVal v) :
    ∀ cs : List Cost, validList cs = true → ∀ c ∈ cs, 0 ≤ c.raw v
  | [], _ => by simp
  | c :: cs, h => by
    simp only [validList, Bool.and_eq_true] at h
    intro d hd
    rcases List.mem_cons.1 hd with hdc | hd
    · rw [hdc]; exact valid_nonneg v hv c h.1
    · exact validList_nonneg v hv cs h.2 d hd

end

theorem eval_isBigO {l : Filter Instance} {c d : Cost}
    (h : (fun i : Instance => c.raw i.valuation) =O[l] (fun i => d.raw i.valuation))
    (hd : ∀ᶠ i in l, 0 ≤ d.raw i.valuation) :
    (fun i : Instance => c.eval i.valuation) =O[l] (fun i => d.eval i.valuation) := by
  obtain ⟨K, hK⟩ := h.bound
  refine IsBigO.of_bound (1 + max K 0) ((hK.and hd).mono fun i ⟨hk, hd⟩ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (c.eval_pos _), abs_of_pos (d.eval_pos _)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hd] at hk
  have h1 : c.eval i.valuation ≤ 1 + |c.raw i.valuation| :=
    max_le (by linarith [abs_nonneg (c.raw i.valuation)])
      (by linarith [le_abs_self (c.raw i.valuation)])
  have h2 : d.raw i.valuation ≤ d.eval i.valuation := le_max_right _ _
  have h3 : 1 ≤ d.eval i.valuation := Cost.one_le_eval _ _
  have h4 : K * d.raw i.valuation ≤ max K 0 * d.raw i.valuation :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hd
  have h5 : max K 0 * d.raw i.valuation ≤ max K 0 * d.eval i.valuation :=
    mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  have h6 : (1 + max K 0) * d.eval i.valuation = d.eval i.valuation + max K 0 * d.eval i.valuation :=
    by ring
  linarith

theorem eval_le_of_raw_le {v : Valuation} {c d : Cost} (h : c.raw v ≤ d.raw v) :
    c.eval v ≤ d.eval v := max_le_max le_rfl h

/-- A pointwise comparison of exact values is a comparison of values. -/
theorem isBigO_of_raw_le {l : Filter Instance} {c d : Cost}
    (h : ∀ᶠ i in l, c.raw i.valuation ≤ d.raw i.valuation) :
    (fun i : Instance => c.eval i.valuation) =O[l] (fun i => d.eval i.valuation) :=
  IsBigO.of_bound 1 (h.mono fun i hi => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (c.eval_pos _), abs_of_pos (d.eval_pos _),
      one_mul]
    exact eval_le_of_raw_le hi)

/-! ## Monomials and the decidable dominance order

`mono` reads a cost as a monomial `a · ∏ xⱼ^p · lg(xⱼ)^q` over dimensions `xⱼ` (each read as
at least `1`), as olint's `monomial` (cost.rs) does for natural exponents. `within c d` decides
`c = O(d)`: by syntactic equality, or by comparing the monomials' per-dimension exponents
lexicographically, power first then log power, as olint's `monomial_within` does. -/

/-- A monomial: its coefficient and its factors `(dimension, power, log power)`. -/
abbrev Mono := ℕ × List (ℕ × ℕ × ℕ)

mutual

/-- The monomial a cost denotes, if it is one. -/
def mono : Cost → Option Mono
  | .constant k => some (k, [])
  | .dimension j _ => some (1, [(j, 1, 0)])
  | .log (.dimension j _) => some (1, [(j, 0, 1)])
  | .product cs => monoList cs
  | .power b (.constant k) =>
    (mono b).map fun r => (r.1 ^ k, r.2.map fun e => (e.1, e.2.1 * k, e.2.2 * k))
  | _ => none

/-- The monomial a product of costs denotes. -/
def monoList : List Cost → Option Mono
  | [] => some (1, [])
  | c :: cs =>
    match mono c, monoList cs with
    | some r, some r' => some (r.1 * r'.1, r.2 ++ r'.2)
    | _, _ => none

end

/-- A dimension's value, read as at least `1`. -/
def dimVal (v : Valuation) (j : ℕ) : ℝ := max 1 (v.dim j)

/-- The value of one monomial factor. -/
noncomputable def factorVal (v : Valuation) (e : ℕ × ℕ × ℕ) : ℝ :=
  dimVal v e.1 ^ e.2.1 * lg (dimVal v e.1) ^ e.2.2

/-- The value of a monomial. -/
noncomputable def monoVal (v : Valuation) (r : Mono) : ℝ :=
  (r.1 : ℝ) * (r.2.map (factorVal v)).prod

theorem monoVal_nonneg (v : Valuation) (r : Mono) : 0 ≤ monoVal v r := by
  unfold monoVal
  refine mul_nonneg (Nat.cast_nonneg _) (List.prod_nonneg fun x hx => ?_)
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
  unfold factorVal dimVal
  exact mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    (pow_nonneg (lg_nonneg _) _)

/-- The total power of dimension `j` in a monomial. -/
def powSum (j : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | e :: m => (if e.1 = j then e.2.1 else 0) + powSum j m

/-- The total log power of dimension `j` in a monomial. -/
def logSum (j : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | e :: m => (if e.1 = j then e.2.2 else 0) + logSum j m

/-- The lexicographic order on (power, log power). -/
def lexLe (p q p' q' : ℕ) : Bool := Nat.blt p p' || (p == p' && Nat.ble q q')

/-- The monomial `r` is `O` of the monomial `r'`. -/
def monoWithin (r r' : Mono) : Bool :=
  Nat.blt 0 r'.1 &&
    (r.2.map (·.1) ++ r'.2.map (·.1)).all fun j =>
      lexLe (powSum j r.2) (logSum j r.2) (powSum j r'.2) (logSum j r'.2)

/-- The decidable dominance order: `within c d` establishes `c = O(d)` (`limitCompare_sound`). -/
def within (c d : Cost) : Bool :=
  Cost.beq c d ||
    match mono c, mono d with
    | some r, some r' => monoWithin r r'
    | _, _ => false

theorem prod_map_pow (v : Valuation) (k : ℕ) : ∀ m : List (ℕ × ℕ × ℕ),
    (m.map (factorVal v)).prod ^ k =
      ((m.map fun e => (e.1, e.2.1 * k, e.2.2 * k)).map (factorVal v)).prod
  | [] => by simp
  | e :: m => by
    simp only [List.map_cons, List.prod_cons, mul_pow, prod_map_pow v k m, factorVal, pow_mul]

theorem rawProduct_eq_prod (v : Valuation) :
    ∀ cs : List Cost, Cost.rawProduct v cs = (cs.map (Cost.raw v)).prod
  | [] => rfl
  | c :: cs => by simp [Cost.rawProduct, rawProduct_eq_prod v cs]

mutual

theorem mono_eval (v : Valuation) :
    ∀ (c : Cost) (r : Mono), mono c = some r → c.raw v = monoVal v r
  | .constant k, r, h => by
    simp only [mono, Option.some.injEq] at h; subst h; simp [monoVal, Cost.raw]
  | .dimension j _, r, h => by
    simp only [mono, Option.some.injEq] at h; subst h
    simp [monoVal, factorVal, dimVal, Cost.raw]
  | .log (.dimension j _), r, h => by
    simp only [mono, Option.some.injEq] at h; subst h
    simp [monoVal, factorVal, dimVal, Cost.raw]
  | .product cs, r, h => by
    simp only [mono] at h
    simp only [Cost.raw]
    exact monoList_eval v cs r h
  | .power b (.constant k), r, h => by
    simp only [mono, Option.map_eq_some_iff] at h
    obtain ⟨r0, h0, rfl⟩ := h
    simp only [Cost.raw, Real.rpow_natCast, mono_eval v b r0 h0, monoVal,
      mul_pow, Nat.cast_pow, prod_map_pow]
  | .legacyN, _, h | .legacyLog, _, h | .legacyNLog, _, h | .name _, _, h | .sum _, _, h
  | .maximum _, _, h | .factorial _, _, h | .ratio _ _, _, h => by simp [mono] at h
  | .log (.constant _), _, h | .log .legacyN, _, h | .log .legacyLog, _, h
  | .log .legacyNLog, _, h | .log (.name _), _, h | .log (.sum _), _, h
  | .log (.product _), _, h | .log (.maximum _), _, h | .log (.log _), _, h
  | .log (.power _ _), _, h | .log (.ratio _ _), _, h | .log (.factorial _), _, h => by
    simp [mono] at h
  | .power _ .legacyN, _, h | .power _ .legacyLog, _, h | .power _ .legacyNLog, _, h
  | .power _ (.name _), _, h | .power _ (.dimension _ _), _, h | .power _ (.sum _), _, h
  | .power _ (.product _), _, h | .power _ (.maximum _), _, h | .power _ (.log _), _, h
  | .power _ (.power _ _), _, h | .power _ (.ratio _ _), _, h
  | .power _ (.factorial _), _, h => by
    simp [mono] at h

theorem monoList_eval (v : Valuation) :
    ∀ (cs : List Cost) (r : Mono), monoList cs = some r → Cost.rawProduct v cs = monoVal v r
  | [], r, h => by
    simp only [monoList, Option.some.injEq] at h; subst h; simp [monoVal, Cost.rawProduct]
  | c :: cs, r, h => by
    simp only [monoList] at h
    split at h
    · rename_i r1 r2 h1 h2
      simp only [Option.some.injEq] at h
      subst h
      simp only [Cost.rawProduct, mono_eval v c r1 h1, monoList_eval v cs r2 h2, monoVal,
        Nat.cast_mul, List.map_append, List.prod_append]
      ring
    · simp at h

end

/-- A monomial's factors regrouped per dimension over a covering set of dimensions. -/
theorem prod_regroup (v : Valuation) (S : Finset ℕ) :
    ∀ m : List (ℕ × ℕ × ℕ), (∀ e ∈ m, e.1 ∈ S) →
      (m.map (factorVal v)).prod =
        ∏ j ∈ S, dimVal v j ^ powSum j m * lg (dimVal v j) ^ logSum j m
  | [], _ => by simp [powSum, logSum]
  | e :: m, hS => by
    have ih := prod_regroup v S m fun e' he' => hS e' (by simp [he'])
    have he : e.1 ∈ S := hS e (by simp)
    simp only [List.map_cons, List.prod_cons, ih, powSum, logSum, pow_add]
    have : ∏ j ∈ S, dimVal v j ^ (if e.1 = j then e.2.1 else 0) *
        lg (dimVal v j) ^ (if e.1 = j then e.2.2 else 0) = factorVal v e := by
      rw [Finset.prod_eq_single_of_mem e.1 he]
      · simp [factorVal]
      · intro j _ hj
        simp [Ne.symm hj]
    rw [← this, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

/-- The per-dimension comparison on the reals. -/
theorem lexLe_isBigO {p q p' q' : ℕ} (h : lexLe p q p' q' = true) :
    (fun x : ℝ => x ^ p * lg x ^ q) =O[atTop] (fun x => x ^ p' * lg x ^ q') := by
  simp only [lexLe, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  rcases h with hp | ⟨rfl, hq⟩
  · have hlog : (fun x : ℝ => lg x ^ q) =O[atTop] (fun x => x) := by
      have h1 : (fun x : ℝ => lg x ^ q) =ᶠ[atTop]
          (fun x => (Real.log 2)⁻¹ ^ q * Real.log x ^ q) := by
        filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
        rw [lg, max_eq_left hx, ← Real.log_div_log, div_eq_inv_mul, mul_pow]
      exact h1.trans_isBigO ((Real.isLittleO_pow_log_id_atTop.isBigO).const_mul_left _)
    have h2 : (fun x : ℝ => x ^ p * lg x ^ q) =O[atTop] (fun x => x ^ p * x) :=
      (isBigO_refl _ _).mul hlog
    refine h2.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hl : 1 ≤ lg x ^ q' := one_le_pow₀ (lg_ge_one x)
    have hl0 : 0 ≤ lg x := lg_nonneg x
    have hpow : x ^ p * x ≤ x ^ p' := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hx hp
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    calc x ^ p * x ≤ x ^ p' := hpow
      _ = x ^ p' * 1 := (mul_one _).symm
      _ ≤ x ^ p' * lg x ^ q' := mul_le_mul_of_nonneg_left hl (by positivity)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hl0 : 0 ≤ lg x := lg_nonneg x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (lg_ge_one x) hq) (by positivity)

theorem monoWithin_spec {r r' : Mono} (h : monoWithin r r' = true) :
    0 < r'.1 ∧ ∀ j ∈ (r.2.map (·.1) ++ r'.2.map (·.1)).toFinset,
      lexLe (powSum j r.2) (logSum j r.2) (powSum j r'.2) (logSum j r'.2) = true := by
  simp only [monoWithin, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  exact ⟨h.1, fun j hj => h.2 j (List.mem_toFinset.1 hj)⟩

/-- `lg` is monotone. -/
theorem lg_mono {x y : ℝ} (h : x ≤ y) : lg x ≤ lg y := by
  unfold lg
  exact Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le two_pos (le_max_right _ _))
    (max_le_max h le_rfl)

/-- A monotone nonnegative function on `[1, ∞)` that is `O(g)` at infinity, where `g ≥ 1`, is
at most a constant times `g` on all of `[1, ∞)`. -/
theorem uniform_of_isBigO {f g : ℝ → ℝ} (hf : ∀ x y, 1 ≤ x → x ≤ y → f x ≤ f y)
    (hf0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hg : ∀ x, 1 ≤ x → 1 ≤ g x) (h : f =O[atTop] g) :
    ∃ K, 0 ≤ K ∧ ∀ x, 1 ≤ x → f x ≤ K * g x := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨X, hX⟩ := eventually_atTop.1 hc
  have hY1 : (1 : ℝ) ≤ max X 1 := le_max_right _ _
  have hfY := hf0 _ hY1
  refine ⟨max c 0 + f (max X 1), add_nonneg (le_max_right _ _) hfY, fun x hx => ?_⟩
  have hgx := hg x hx
  by_cases hxY : max X 1 ≤ x
  · have hb := hX x (le_trans (le_max_left _ _) hxY)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 x hx),
      abs_of_nonneg (by linarith)] at hb
    have : f x ≤ max c 0 * g x :=
      le_trans hb (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    nlinarith
  · have hfx : f x ≤ f (max X 1) := hf x _ hx (le_of_lt (not_le.1 hxY))
    nlinarith [le_max_right c 0]

/-- The per-dimension comparison, uniformly on `[1, ∞)`. -/
theorem lexLe_uniform {p q p' q' : ℕ} (h : lexLe p q p' q' = true) :
    ∃ K, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → x ^ p * lg x ^ q ≤ K * (x ^ p' * lg x ^ q') := by
  refine uniform_of_isBigO (fun x y hx hxy => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (lexLe_isBigO h)
  · have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    exact mul_le_mul (pow_le_pow_left₀ hx0 hxy p) (pow_le_pow_left₀ (lg_nonneg x) (lg_mono hxy) q)
      (pow_nonneg (lg_nonneg x) q) (pow_nonneg (le_trans hx0 hxy) p)
  · exact mul_nonneg (pow_nonneg (le_trans zero_le_one hx) p) (pow_nonneg (lg_nonneg x) q)
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) (one_le_pow₀ (lg_ge_one x))

/-- `monoWithin` bounds one monomial's value by a constant times the other's, at every
valuation: every dimension reads as at least `1`, so the comparison holds uniformly. -/
theorem monoWithin_le {r r' : Mono} (h : monoWithin r r' = true) :
    ∃ K : ℝ, ∀ v : Valuation, monoVal v r ≤ K * monoVal v r' := by
  obtain ⟨hpos, hlex⟩ := monoWithin_spec h
  set S := (r.2.map (·.1) ++ r'.2.map (·.1)).toFinset
  have hS : ∀ e ∈ r.2, e.1 ∈ S := fun e he => by
    simp only [S, List.mem_toFinset, List.mem_append, List.mem_map]; exact Or.inl ⟨e, he, rfl⟩
  have hS' : ∀ e ∈ r'.2, e.1 ∈ S := fun e he => by
    simp only [S, List.mem_toFinset, List.mem_append, List.mem_map]; exact Or.inr ⟨e, he, rfl⟩
  have hK : ∀ j ∈ S, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      x ^ powSum j r.2 * lg x ^ logSum j r.2 ≤ K * (x ^ powSum j r'.2 * lg x ^ logSum j r'.2) :=
    fun j hj => lexLe_uniform (hlex j hj)
  choose! K hK0 hKle using hK
  refine ⟨r.1 * ∏ j ∈ S, K j, fun v => ?_⟩
  have hd : ∀ j, (1 : ℝ) ≤ dimVal v j := fun j => le_max_left _ _
  have hprod : ∏ j ∈ S, dimVal v j ^ powSum j r.2 * lg (dimVal v j) ^ logSum j r.2 ≤
      (∏ j ∈ S, K j) * ∏ j ∈ S, dimVal v j ^ powSum j r'.2 * lg (dimVal v j) ^ logSum j r'.2 :=
    (Finset.prod_le_prod₀ (fun j _ => mul_nonneg (pow_nonneg (le_trans zero_le_one (hd j)) _)
      (pow_nonneg (lg_nonneg _) _)) fun j hj => hKle j hj _ (hd j)).trans_eq
      Finset.prod_mul_distrib
  have hP : 0 ≤ ∏ j ∈ S, dimVal v j ^ powSum j r'.2 * lg (dimVal v j) ^ logSum j r'.2 :=
    Finset.prod_nonneg fun j _ => mul_nonneg (pow_nonneg (le_trans zero_le_one (hd j)) _)
      (pow_nonneg (lg_nonneg _) _)
  have hK0' : 0 ≤ ∏ j ∈ S, K j := Finset.prod_nonneg fun j hj => hK0 j hj
  have h1 : (1 : ℝ) ≤ r'.1 := by exact_mod_cast hpos
  rw [monoVal, prod_regroup _ S r.2 hS, monoVal, prod_regroup _ S r'.2 hS']
  calc (r.1 : ℝ) * ∏ j ∈ S, dimVal v j ^ powSum j r.2 * lg (dimVal v j) ^ logSum j r.2
      ≤ r.1 * ((∏ j ∈ S, K j) *
          ∏ j ∈ S, dimVal v j ^ powSum j r'.2 * lg (dimVal v j) ^ logSum j r'.2) :=
        mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = (r.1 * ∏ j ∈ S, K j) *
          ∏ j ∈ S, dimVal v j ^ powSum j r'.2 * lg (dimVal v j) ^ logSum j r'.2 := by ring
    _ ≤ (r.1 * ∏ j ∈ S, K j) *
          (r'.1 * ∏ j ∈ S, dimVal v j ^ powSum j r'.2 * lg (dimVal v j) ^ logSum j r'.2) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hP h1)
          (mul_nonneg (Nat.cast_nonneg _) hK0')

/-- `limit-compare`: the decidable comparison `within c d` establishes `c = O(d)` uniformly, so
on every filter of instances, the admitted instances of any entry included. olint's `Within`
verdict (cost.rs:863-898) rests on it. -/
theorem limitCompare_sound (l : Filter Instance) {c d : Cost} (h : within c d = true) :
    (fun i : Instance => c.eval i.valuation) =O[l] (fun i => d.eval i.valuation) := by
  simp only [within, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain rfl := Cost.eq_of_beq c d h; exact isBigO_refl _ _
  · split at h
    · rename_i r r' hc hd
      refine eval_isBigO ?_ (Eventually.of_forall fun i => ?_)
      · obtain ⟨K, hK⟩ := monoWithin_le h
        refine IsBigO.of_bound K (Eventually.of_forall fun i => ?_)
        rw [mono_eval _ c r hc, mono_eval _ d r' hd, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (monoVal_nonneg _ _), abs_of_nonneg (monoVal_nonneg _ _)]
        exact hK _
      · rw [mono_eval _ d r' hd]; exact monoVal_nonneg _ _
    · simp at h

/-- A verdict: a bound within a limit is a bound by the limit. -/
theorem Bound.of_within {p : Program} {n : Node} {c d : Cost} (h : Bound W p n c)
    (hw : within c d = true) : Bound W p n d :=
  h.mono (limitCompare_sound _ hw)

/-! ## `max-dominance` and `max-normalise` -/

theorem validList_valid : ∀ cs : List Cost, validList cs = true → ∀ c ∈ cs, valid c = true
  | [], _, c, h => by simp at h
  | d :: cs, h, c, hc => by
    simp only [validList, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact validList_valid cs h.2 c hc

/-- The terms of a cost read as a maximum. -/
def maxView : Cost → List Cost
  | .maximum cs => cs
  | c => [c]

mutual

/-- The terms of a cost read as a maximum, nested maxima flattened. -/
def flatMax : Cost → List Cost
  | .maximum cs => flatMaxList cs
  | c => [c]

/-- The terms of a list of maximum terms, nested maxima flattened. -/
def flatMaxList : List Cost → List Cost
  | [] => []
  | c :: cs => flatMax c ++ flatMaxList cs

end

/-- Every term of `cs` is `O` of some term of `ds`, by `within`. -/
def dominated (cs ds : List Cost) : Bool := cs.all fun c => ds.any fun d => within c d

/-- One maximum term is at most another at every valuation: equal, or constants in order. -/
def termLe : Cost → Cost → Bool
  | .constant a, .constant b => Nat.ble a b
  | c, d => Cost.beq c d

/-- Every term of `cs` is at most some term of `ds`, or the constant `0`. -/
def maxCovers (cs ds : List Cost) : Bool :=
  cs.all fun c => Cost.beq c (.constant 0) || ds.any fun d => termLe c d

theorem le_rawMaximum (v : Valuation) :
    ∀ (cs : List Cost) (c : Cost), c ∈ cs → c.raw v ≤ Cost.rawMaximum v cs
  | [], _, h => by simp at h
  | d :: cs, c, h => by
    simp only [Cost.rawMaximum]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_rawMaximum v cs c h)

theorem rawMaximum_le (v : Valuation) (b : ℝ) (hb : 0 ≤ b) :
    ∀ cs : List Cost, (∀ c ∈ cs, c.raw v ≤ b) → Cost.rawMaximum v cs ≤ b
  | [], _ => hb
  | c :: cs, h => by
    simp only [Cost.rawMaximum]
    exact max_le (h c (by simp)) (rawMaximum_le v b hb cs fun d hd => h d (by simp [hd]))

theorem rawMaximum_append (v : Valuation) :
    ∀ as bs : List Cost, Cost.rawMaximum v (as ++ bs) =
      max (Cost.rawMaximum v as) (Cost.rawMaximum v bs)
  | [], bs => by simp [Cost.rawMaximum, max_eq_right (rawMaximum_nonneg v bs)]
  | a :: as, bs => by simp [Cost.rawMaximum, rawMaximum_append v as bs, max_assoc]

mutual

theorem flatMax_eval (v : Valuation) :
    ∀ c : Cost, Cost.rawMaximum v (flatMax c) = Cost.rawMaximum v [c]
  | .maximum cs => by
    simp only [flatMax, flatMaxList_eval v cs, Cost.rawMaximum, Cost.raw]
    exact (max_eq_left (rawMaximum_nonneg v cs)).symm
  | .constant _ | .legacyN | .legacyLog | .legacyNLog | .name _ | .dimension _ _ | .sum _
  | .product _ | .log _ | .power _ _ | .ratio _ _ | .factorial _ => by simp [flatMax]

theorem flatMaxList_eval (v : Valuation) :
    ∀ cs : List Cost, Cost.rawMaximum v (flatMaxList cs) = Cost.rawMaximum v cs
  | [] => rfl
  | c :: cs => by
    rw [flatMaxList, rawMaximum_append, flatMax_eval v c, flatMaxList_eval v cs]
    simp only [Cost.rawMaximum]
    rw [max_assoc, max_eq_right (rawMaximum_nonneg v cs)]

end

/-- A valid cost is the maximum of its maximum view. -/
theorem maxView_eval (v : Valuation) (hv : NonnegVal v) (c : Cost) (hc : valid c = true) :
    Cost.rawMaximum v (maxView c) = c.raw v := by
  cases c with
  | maximum cs => rfl
  | _ => simp [maxView, Cost.rawMaximum, max_eq_left (valid_nonneg v hv _ hc)]

/-- A valid cost is the maximum of its flattened terms. -/
theorem flatMax_eval_valid (v : Valuation) (hv : NonnegVal v) (c : Cost) (hc : valid c = true) :
    Cost.rawMaximum v (flatMax c) = c.raw v := by
  rw [flatMax_eval, Cost.rawMaximum, Cost.rawMaximum, max_eq_left (valid_nonneg v hv c hc)]

theorem rawMaximum_le_sum (v : Valuation) :
    ∀ cs : List Cost, Cost.rawMaximum v cs ≤ (cs.map fun c => c.eval v).sum
  | [] => by simp [Cost.rawMaximum]
  | c :: cs => by
    have ih := rawMaximum_le_sum v cs
    have hs : 0 ≤ (cs.map fun c => c.eval v).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx; exact le_of_lt (d.eval_pos v)
    have hc : c.raw v ≤ c.eval v := le_max_right _ _
    simp only [Cost.rawMaximum, List.map_cons, List.sum_cons]
    exact max_le (by linarith) (by linarith [c.eval_pos v])

theorem sum_isBigO {l : Filter Instance} {g : Instance → ℝ} :
    ∀ cs : List Cost, (∀ c ∈ cs, (fun i : Instance => c.eval i.valuation) =O[l] g) →
      (fun i : Instance => (cs.map fun c => c.eval i.valuation).sum) =O[l] g
  | [], _ => by simp only [List.map_nil, List.sum_nil]; exact isBigO_zero _ _
  | c :: cs, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h c (by simp)).add (sum_isBigO cs fun d hd => h d (by simp [hd]))

/-- `max-dominance`: dropping from a maximum terms `O` of a remaining term keeps a bound. Both
sides must be valid, so each is the maximum of its terms. -/
theorem maxDominance_isBigO (e : Entry) {s t : Cost} (hs : valid s = true)
    (ht : valid t = true) (hd : dominated (maxView s) (maxView t) = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits e] (fun i => t.eval i.valuation) := by
  have hle : ∀ d ∈ maxView t, ∀ i : Instance, d.eval i.valuation ≤ t.eval i.valuation :=
    fun d hdm i => eval_le_of_raw_le (by
      rw [← maxView_eval _ (instance_nonnegVal i) t ht]
      exact le_rawMaximum _ _ d hdm)
  have hterms : ∀ c ∈ maxView s, (fun i : Instance => c.eval i.valuation) =O[Admits e]
      (fun i => t.eval i.valuation) := fun c hc => by
    simp only [dominated, List.all_eq_true, List.any_eq_true] at hd
    obtain ⟨d, hdm, hw⟩ := hd c hc
    refine (limitCompare_sound _ hw).trans (IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (d.eval_pos _),
      abs_of_pos (t.eval_pos _), one_mul]
    exact hle d hdm i
  have hone : (fun _ : Instance => (1 : ℝ)) =O[Admits e] (fun i => t.eval i.valuation) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun i => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos one_pos, abs_of_pos (t.eval_pos _),
        one_mul]
      exact t.one_le_eval _)
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_)).trans
    (hone.add (sum_isBigO _ hterms))
  have hsum : 0 ≤ ((maxView s).map fun c => c.eval i.valuation).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx; exact le_of_lt (d.eval_pos _)
  have hraw := rawMaximum_le_sum i.valuation (maxView s)
  rw [maxView_eval _ (instance_nonnegVal i) s hs] at hraw
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s.eval_pos _),
    abs_of_nonneg (by linarith), one_mul]
  exact max_le (by linarith) (by linarith)

theorem termLe_raw (v : Valuation) {c d : Cost} (h : termLe c d = true) : c.raw v ≤ d.raw v := by
  unfold termLe at h
  split at h
  · simp only [Nat.ble_eq] at h; simp only [Cost.raw]; exact_mod_cast h
  · obtain rfl := Cost.eq_of_beq _ _ h; exact le_refl _

/-- `maxCovers` compares maxima pointwise. -/
theorem maxCovers_le (v : Valuation) {cs ds : List Cost} (h : maxCovers cs ds = true) :
    Cost.rawMaximum v cs ≤ Cost.rawMaximum v ds := by
  refine rawMaximum_le v _ (rawMaximum_nonneg v ds) cs fun c hc => ?_
  simp only [maxCovers, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  rcases h c hc with h0 | ⟨d, hd, hle⟩
  · obtain rfl := Cost.eq_of_beq _ _ h0; simpa [Cost.raw] using rawMaximum_nonneg v ds
  · exact le_trans (termLe_raw v hle) (le_rawMaximum v ds d hd)

/-- `max-normalise`: flattening nested maxima, folding constants and removing duplicates keeps a
bound; `maxCovers` checks the normalised terms cover the original ones. -/
theorem maxNormalise_isBigO (e : Entry) {s t : Cost} (hs : valid s = true)
    (ht : valid t = true) (hc : maxCovers (flatMax s) (flatMax t) = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits e] (fun i => t.eval i.valuation) :=
  isBigO_of_raw_le (Eventually.of_forall fun i => by
    rw [← flatMax_eval_valid _ (instance_nonnegVal i) s hs,
      ← flatMax_eval_valid _ (instance_nonnegVal i) t ht]
    exact maxCovers_le _ hc)

/-! ## `product-normalise` -/

mutual

/-- The factors of a cost read as a product: nested products flattened, a power by a constant
`k` expanded into `k` factors, and the legacy `N log N` split into `N` and `log N`. -/
def factors : Cost → List Cost
  | .product cs => factorsList cs
  | .power b (.constant k) => List.replicate k b
  | .legacyNLog => [.legacyN, .legacyLog]
  | .constant k => [.constant k]
  | .legacyN => [.legacyN]
  | .legacyLog => [.legacyLog]
  | .name s => [.name s]
  | .dimension j d => [.dimension j d]
  | .sum cs => [.sum cs]
  | .maximum cs => [.maximum cs]
  | .log c => [.log c]
  | .power b e => [.power b e]
  | .ratio a b => [.ratio a b]
  | .factorial c => [.factorial c]

/-- The factors of a list of product terms. -/
def factorsList : List Cost → List Cost
  | [] => []
  | c :: cs => factors c ++ factorsList cs

end

/-- The product of the constant factors. -/
def constProd : List Cost → ℕ
  | [] => 1
  | .constant k :: cs => k * constProd cs
  | _ :: cs => constProd cs

/-- The non-constant factors. -/
def nonConst : List Cost → List Cost
  | [] => []
  | .constant _ :: cs => nonConst cs
  | c :: cs => c :: nonConst cs

/-- Remove the first factor equal to `x`, if any. -/
def eraseFirst (x : Cost) : List Cost → Option (List Cost)
  | [] => none
  | y :: ys => if Cost.beq x y then some ys else (eraseFirst x ys).map (y :: ·)

/-- The two lists are permutations of each other. -/
def permCheck : List Cost → List Cost → Bool
  | [], ys => ys.isEmpty
  | x :: xs, ys =>
    match eraseFirst x ys with
    | some ys' => permCheck xs ys'
    | none => false

/-- The product `s` normalises to `t`: `s` is `0` by a zero constant factor, or both have the
same constant and the same non-constant factors up to order. -/
def prodMatches (s t : Cost) : Bool :=
  constProd (factors s) == 0 ||
    (constProd (factors s) == constProd (factors t) &&
      permCheck (nonConst (factors s)) (nonConst (factors t)))

theorem rawProduct_append (v : Valuation) :
    ∀ as bs : List Cost, Cost.rawProduct v (as ++ bs) =
      Cost.rawProduct v as * Cost.rawProduct v bs
  | [], bs => by simp [Cost.rawProduct]
  | a :: as, bs => by simp [Cost.rawProduct, rawProduct_append v as bs, mul_assoc]

theorem rawProduct_replicate (v : Valuation) (b : Cost) :
    ∀ k : ℕ, Cost.rawProduct v (List.replicate k b) = b.raw v ^ k
  | 0 => rfl
  | k + 1 => by
    simp [List.replicate_succ, Cost.rawProduct, rawProduct_replicate v b k, pow_succ, mul_comm]

mutual

theorem factors_eval (v : Valuation) :
    ∀ c : Cost, Cost.rawProduct v (factors c) = c.raw v
  | .product cs => by simp only [factors, factorsList_eval v cs, Cost.raw]
  | .power b (.constant k) => by
    simp [factors, rawProduct_replicate, Cost.raw, Real.rpow_natCast]
  | .legacyNLog => by simp [factors, Cost.rawProduct, Cost.raw]
  | .constant _ | .legacyN | .legacyLog | .name _ | .dimension _ _ | .sum _ | .maximum _
  | .log _ | .ratio _ _ | .factorial _ => by simp [factors, Cost.rawProduct]
  | .power _ .legacyN | .power _ .legacyLog | .power _ .legacyNLog | .power _ (.name _)
  | .power _ (.dimension _ _) | .power _ (.sum _) | .power _ (.product _)
  | .power _ (.maximum _) | .power _ (.log _) | .power _ (.power _ _) | .power _ (.ratio _ _)
  | .power _ (.factorial _) => by simp [factors, Cost.rawProduct]

theorem factorsList_eval (v : Valuation) :
    ∀ cs : List Cost, Cost.rawProduct v (factorsList cs) = Cost.rawProduct v cs
  | [] => rfl
  | c :: cs => by
    rw [factorsList, rawProduct_append, factors_eval v c, factorsList_eval v cs]
    rfl

end

theorem rawProduct_split (v : Valuation) :
    ∀ cs : List Cost, Cost.rawProduct v cs = (constProd cs : ℝ) * Cost.rawProduct v (nonConst cs)
  | [] => by simp [Cost.rawProduct, constProd, nonConst]
  | .constant k :: cs => by
    simp only [Cost.rawProduct, constProd, nonConst, rawProduct_split v cs, Cost.raw,
      Nat.cast_mul]
    ring
  | .legacyN :: cs | .legacyLog :: cs | .legacyNLog :: cs | .name _ :: cs
  | .dimension _ _ :: cs | .sum _ :: cs | .product _ :: cs | .maximum _ :: cs | .log _ :: cs
  | .power _ _ :: cs | .ratio _ _ :: cs | .factorial _ :: cs => by
    simp only [Cost.rawProduct, constProd, nonConst, rawProduct_split v cs]
    ring

theorem eraseFirst_perm (x : Cost) :
    ∀ ys ys' : List Cost, eraseFirst x ys = some ys' → ys.Perm (x :: ys')
  | [], _, h => by simp [eraseFirst] at h
  | y :: ys, ys', h => by
    unfold eraseFirst at h
    split at h
    · rename_i hb
      obtain rfl := Cost.eq_of_beq _ _ hb
      simp only [Option.some.injEq] at h
      subst h
      exact List.Perm.refl _
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨zs, hz, rfl⟩ := h
      exact ((eraseFirst_perm x ys zs hz).cons y).trans (List.Perm.swap x y zs)

theorem permCheck_perm : ∀ xs ys : List Cost, permCheck xs ys = true → xs.Perm ys
  | [], ys, h => by
    simp only [permCheck, List.isEmpty_iff] at h; subst h; exact List.Perm.refl _
  | x :: xs, ys, h => by
    unfold permCheck at h
    split at h
    · rename_i ys' he
      exact ((permCheck_perm xs ys' h).cons x).trans (eraseFirst_perm x ys ys' he).symm
    · simp at h

/-- `product-normalise`: at every valuation the normalised product has the original's exact
value, or the original is exactly `0`. -/
theorem prodMatches_eval (v : Valuation) {s t : Cost} (h : prodMatches s t = true) :
    s.raw v = 0 ∨ s.raw v = t.raw v := by
  simp only [prodMatches, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rw [← factors_eval v s, ← factors_eval v t, rawProduct_split v (factors s),
    rawProduct_split v (factors t)]
  rcases h with h | ⟨hk, hp⟩
  · left; simp [h]
  · right
    rw [hk, rawProduct_eq_prod, rawProduct_eq_prod,
      ((permCheck_perm _ _ hp).map (Cost.raw v)).prod_eq]

/-- `product-normalise` keeps a bound: a zero product reads as `1`, the least value, so the
collapse to `0` is sound. -/
theorem productNormalise_isBigO (e : Entry) {s t : Cost}
    (h : prodMatches s t = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits e] (fun i => t.eval i.valuation) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s.eval_pos _), abs_of_pos (t.eval_pos _),
    one_mul]
  rcases prodMatches_eval i.valuation h with h0 | he
  · unfold Cost.eval; rw [h0, max_eq_left zero_le_one]; exact t.one_le_eval _
  · unfold Cost.eval; rw [he]

/-! ## Bound transformers -/

/-- `max-dominance` on bounds. -/
theorem maxDominance_sound {p : Program} {n : Node} {s t : Cost} (h : Bound W p n s)
    (hs : valid s = true) (ht : valid t = true) (hd : dominated (maxView s) (maxView t) = true) :
    Bound W p n t :=
  h.mono (maxDominance_isBigO n.entry hs ht hd)

/-- `max-normalise` on bounds. -/
theorem maxNormalise_sound {p : Program} {n : Node} {s t : Cost} (h : Bound W p n s)
    (hs : valid s = true) (ht : valid t = true) (hc : maxCovers (flatMax s) (flatMax t) = true) :
    Bound W p n t :=
  h.mono (maxNormalise_isBigO n.entry hs ht hc)

/-- `product-normalise` on bounds. -/
theorem productNormalise_sound {p : Program} {n : Node} {s t : Cost} (h : Bound W p n s)
    (hm : prodMatches s t = true) : Bound W p n t :=
  h.mono (productNormalise_isBigO n.entry hm)

end Olint.Rules

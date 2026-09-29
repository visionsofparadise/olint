import Olint.Bound

/-!
# Family A: cost algebra and composition

Soundness lemmas for olint's family A rules (the Phase 2 rule inventory), and the decidable
side conditions `Olint.check` evaluates for them by kernel reduction.

The decidable side conditions are plain structural recursions over `Cost` and the syntax with
`ℕ` and `Bool` arithmetic only, so `decide` evaluates them; each has a soundness lemma here
stating what it establishes about `Cost.eval` on the large admitted instances of an entry.

**Composition.** `seq-max`, `branch-join` and `channel-total` compose child certificates: a
child's bound holds at every configuration its entry's run reaches at the child
(`Olint.Bound`), so a parent's run, which is one unit of work followed by its children's runs,
each at most once, is bounded by the maximum of the children's bounds (`bound_compose`). The
composition lemmas unfold the interpreter one step (`execStmt_block`, `execStmt_ite`, …) and
use the `Sub` edges from the parent to each child.

| Rule | olint | Decidable side condition | Soundness lemma |
| --- | --- | --- | --- |
| `seq-max` | cost.rs:2045/1800, walker.rs:675 | `seqSites` on the node, children checked | `seqMax_sound` |
| `seq-max` (unit base) | walker.rs:497, walker.rs:675 | `unitStmt` or a literal on the node | `unit_bound`, `lit_bound` |
| `branch-join` | walker.rs:506-574 | `branchSites` on the node, children checked | `branchJoin_sound` |
| `channel-total` | cost.rs:2101 | parts checked, channels covered | `channelTotal_sound` |
| `max-dominance` | cost.rs:1826-1850, cost.rs:1009-1038 | `within` per dropped term | `maxDominance_sound` |
| `max-normalise` | cost.rs:288-380 (kind 2) | `maxCovers` over the flattened terms | `maxNormalise_sound` |
| `product-normalise` | cost.rs:288-380 (kind 1) | `prodMatches` over the expanded factors | `productNormalise_sound` |
| `expr-validity` | cost.rs:383-475 | `valid` | `valid_nonneg` |
| `limit-compare` | cost.rs:863-898, main.rs:290-316 | `within` | `limitCompare_sound` |
-/

namespace Olint.Rules

open Olint Olint.Model Filter Asymptotics

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

/-! ## Unfolding frames -/

theorem runs_stmt {env : Env} {s : Stmt} {st : St} {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs ⟨.stmt env s, st⟩ f o st' ↔
      ∃ r, (execStmt f env s).run st = .ok (r, st') ∧ o = .stmt r.1 r.2 := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (execStmt f env s).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

theorem runs_stmts {env : Env} {ss : List Stmt} {st : St} {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs ⟨.stmts env ss, st⟩ f o st' ↔
      ∃ r, (execStmts f env ss).run st = .ok (r, st') ∧ o = .stmt r.1 r.2 := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (execStmts f env ss).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

theorem runs_expr {env : Env} {x : Expr} {st : St} {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs ⟨.expr env x, st⟩ f o st' ↔
      ∃ v, (evalExpr f env x).run st = .ok (v, st') ∧ o = .val v := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (evalExpr f env x).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

theorem runs_callFunc {fn : Func} {env : Env} {self : Value} {args : List Value} {st : St}
    {f : ℕ} {o : Outcome} {st' : St} :
    Cfg.Runs ⟨.callFunc fn env self args, st⟩ f o st' ↔
      ∃ v, (callFunc f fn env self args).run st = .ok (v, st') ∧ o = .val v := by
  simp only [Cfg.Runs, Frame.run, run_map]
  rcases (callFunc f fn env self args).run st with e | ⟨r, st1⟩
  · simp
  · constructor
    · intro h; cases h; exact ⟨r, rfl, rfl⟩
    · rintro ⟨r', h1, rfl⟩; cases h1; rfl

/-! ## Statement lists -/

theorem execStmts_zero (env : Env) (ss : List Stmt) (st : St) :
    (execStmts 0 env ss).run st = .error .fuel := by
  rw [execStmts]; rfl

theorem execStmts_nil (f : ℕ) (env : Env) (st : St) :
    (execStmts (f + 1) env []).run st = .ok ((env, .normal), st) := by
  rw [execStmts]; rfl

theorem execStmts_cons (f : ℕ) (env : Env) (s : Stmt) (ss : List Stmt) (st : St) :
    (execStmts (f + 1) env (s :: ss)).run st =
      match (execStmt f env s).run st with
      | .ok ((env', .normal), st1) => (execStmts f env' ss).run st1
      | .ok ((env', c), st1) => .ok ((env', c), st1)
      | .error e => .error e := by
  simp only [execStmts, run_bind]
  rcases (execStmt f env s).run st with e | ⟨⟨env', c⟩, st1⟩
  · rfl
  · cases c <;> rfl

theorem holds_stmts {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (ss0 : List Stmt) (h : ∀ s ∈ ss0, Holds p e i (.stmt s) allChannels F B) :
    ∀ ss : List Stmt, (∀ s ∈ ss, s ∈ ss0) → ∀ env st, Reach p e i ⟨.stmts env ss, st⟩ →
      (∀ f, F + ss.length + 1 ≤ f → ∃ o st', Cfg.Runs ⟨.stmts env ss, st⟩ f o st') ∧
      (∀ f o st', Cfg.Runs ⟨.stmts env ss, st⟩ f o st' → (st'.work : ℝ) - st.work ≤ ss.length * B)
  | [], _, env, st, _ => by
    refine ⟨fun f hf => ?_, fun f o st' hc => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      exact ⟨_, _, runs_stmts.2 ⟨(env, .normal), execStmts_nil _ _ _, rfl⟩⟩
    · obtain ⟨r, hr, _⟩ := runs_stmts.1 hc
      cases f with
      | zero => rw [execStmts_zero] at hr; cases hr
      | succ f =>
        rw [execStmts_nil] at hr
        cases hr; simp
  | s :: ss, hss, env, st, hr => by
    have hs0 : s ∈ ss0 := hss s (by simp)
    have hhead : Reach p e i ⟨.stmt env s, st⟩ := hr.tail Sub.stmtsHead
    obtain ⟨hcomp, hwork⟩ := h s hs0 _ hhead ⟨env, rfl⟩
    refine ⟨fun f hf => ?_, fun f o st' hc => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      obtain ⟨o1, st1, h1⟩ := hcomp f' (by simp at hf; omega)
      obtain ⟨⟨env', c⟩, h1', rfl⟩ := runs_stmt.1 h1
      cases c with
      | normal =>
        have htail : Reach p e i ⟨.stmts env' ss, st1⟩ :=
          hr.tail (Sub.stmtsTail ⟨f', h1⟩)
        obtain ⟨o2, st2, h2⟩ := (holds_stmts hB ss0 h ss (fun s' hs' => hss s' (by simp [hs']))
          env' st1 htail).1 f' (by simp at hf; omega)
        obtain ⟨r2, h2', rfl⟩ := runs_stmts.1 h2
        exact ⟨_, _, runs_stmts.2 ⟨r2, by rw [execStmts_cons, h1']; exact h2', rfl⟩⟩
      | ret v => exact ⟨_, _, runs_stmts.2 ⟨_, by rw [execStmts_cons, h1'], rfl⟩⟩
      | brk => exact ⟨_, _, runs_stmts.2 ⟨_, by rw [execStmts_cons, h1'], rfl⟩⟩
      | cont => exact ⟨_, _, runs_stmts.2 ⟨_, by rw [execStmts_cons, h1'], rfl⟩⟩
    · obtain ⟨r, hr', _⟩ := runs_stmts.1 hc
      cases f with
      | zero => rw [execStmts_zero] at hr'; cases hr'
      | succ f =>
        rw [execStmts_cons] at hr'
        have hlen : ((s :: ss).length : ℝ) * B = B + ss.length * B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
        rw [hlen]
        rcases h1 : (execStmt f env s).run st with err | ⟨⟨env', c⟩, st1⟩
        · rw [h1] at hr'; cases hr'
        · rw [h1] at hr'
          have w1 := hwork f _ st1 (runs_stmt.2 ⟨_, h1, rfl⟩) (mem_allChannels _)
          have hlB : (0 : ℝ) ≤ ss.length * B := mul_nonneg (Nat.cast_nonneg _) hB
          cases c with
          | normal =>
            have htail : Reach p e i ⟨.stmts env' ss, st1⟩ :=
              hr.tail (Sub.stmtsTail ⟨f, runs_stmt.2 ⟨_, h1, rfl⟩⟩)
            have w2 := (holds_stmts hB ss0 h ss (fun s' hs' => hss s' (by simp [hs']))
              env' st1 htail).2 f _ st' (runs_stmts.2 ⟨r, hr', rfl⟩)
            linarith
          | ret v => cases hr'; linarith
          | brk => cases hr'; linarith
          | cont => cases hr'; linarith

/-! ## Unfolding statements and expressions -/

theorem run_tick1 (st : St) : (tick 1).run st = .ok ((), st.tick) := rfl

theorem execStmt_zero (env : Env) (s : Stmt) (st : St) :
    (execStmt 0 env s).run st = .error .fuel := by
  rw [execStmt]; rfl

theorem evalExpr_zero (env : Env) (x : Expr) (st : St) :
    (evalExpr 0 env x).run st = .error .fuel := by
  rw [evalExpr]; rfl

theorem callFunc_zero (fn : Func) (env : Env) (self : Value) (args : List Value) (st : St) :
    (callFunc 0 fn env self args).run st = .error .fuel := by
  rw [callFunc]; rfl

theorem execStmt_block (f : ℕ) (env : Env) (ss : List Stmt) (st : St) :
    (execStmt (f + 1) env (.block ss)).run st =
      match (execStmts f env ss).run st.tick with
      | .ok ((_, c), st1) => .ok ((env, c), st1)
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (execStmts f env ss).run st.tick with e | ⟨⟨env', c⟩, st1⟩ <;> rfl

theorem execStmt_expr (f : ℕ) (env : Env) (x : Expr) (st : St) :
    (execStmt (f + 1) env (.expr x)).run st =
      match (evalExpr f env x).run st.tick with
      | .ok (_, st1) => .ok ((env, .normal), st1)
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr f env x).run st.tick with e | ⟨v, st1⟩ <;> rfl

theorem execStmt_ret (f : ℕ) (env : Env) (x : Expr) (st : St) :
    (execStmt (f + 1) env (.ret (some x))).run st =
      match (evalExpr f env x).run st.tick with
      | .ok (v, st1) => .ok ((env, .ret v), st1)
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr f env x).run st.tick with e | ⟨v, st1⟩ <;> rfl

theorem execStmt_decl (f : ℕ) (env : Env) (k : DeclKind) (y : Name) (τ : Ty) (x : Expr)
    (st : St) :
    (execStmt (f + 1) env (.decl k y τ (some x))).run st =
      match (evalExpr f env x).run st.tick with
      | .ok (v, st1) => match (bindCell env y v τ).run st1 with
        | .ok (env', st2) => .ok ((env', .normal), st2)
        | .error e => .error e
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr f env x).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only
    rcases (bindCell env y v τ).run st1 with e | ⟨env', st2⟩ <;> rfl

theorem execStmt_ite (f : ℕ) (env : Env) (c : Expr) (t : Stmt) (el : Option Stmt) (st : St) :
    (execStmt (f + 1) env (.ite c t el)).run st =
      match (evalExpr f env c).run st.tick with
      | .ok (v, st1) =>
        if truthy v then
          match (execStmt f env t).run st1 with
          | .ok ((_, c'), st2) => .ok ((env, c'), st2)
          | .error e => .error e
        else match el with
          | some g => match (execStmt f env g).run st1 with
            | .ok ((_, c'), st2) => .ok ((env, c'), st2)
            | .error e => .error e
          | none => .ok ((env, .normal), st1)
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1]
  rcases (evalExpr f env c).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only
    split
    · simp only [run_bind]
      rcases (execStmt f env t).run st1 with e | ⟨⟨env', c'⟩, st2⟩ <;> rfl
    · cases el with
      | none => rfl
      | some g =>
        simp only [run_bind]
        rcases (execStmt f env g).run st1 with e | ⟨⟨env', c'⟩, st2⟩ <;> rfl

theorem evalExpr_cond (f : ℕ) (env : Env) (c t g : Expr) (st : St) :
    (evalExpr (f + 1) env (.cond c t g)).run st =
      match (evalExpr f env c).run st.tick with
      | .ok (v, st1) => if truthy v then (evalExpr f env t).run st1 else (evalExpr f env g).run st1
      | .error e => .error e := by
  simp only [evalExpr, run_bind, run_tick1]
  rcases (evalExpr f env c).run st.tick with e | ⟨v, st1⟩
  · rfl
  · simp only
    split <;> rfl

theorem evalExpr_lit (f : ℕ) (env : Env) (l : Lit) (st : St) :
    (evalExpr (f + 1) env (.lit l)).run st = .ok (l.value, st.tick) := by
  simp only [evalExpr, run_bind, run_tick1]; rfl

theorem callFunc_succ (f : ℕ) (ps : List (Name × Ty)) (body : List Stmt) (ar : Bool) (env : Env)
    (self : Value) (args : List Value) (st : St) :
    (callFunc (f + 1) (.mk ps body ar) env self args).run st =
      match (enterFunc (.mk ps body ar) env self args).run st with
      | .ok (env', st1) => match (execStmts f env' body).run st1 with
        | .ok ((_, c), st2) => .ok ((match c with | .ret v => v | _ => .undef), st2)
        | .error e => .error e
      | .error e => .error e := by
  simp only [callFunc, run_bind]
  rcases (enterFunc (.mk ps body ar) env self args).run st with e | ⟨env', st1⟩
  · rfl
  · simp only
    rcases (execStmts f env' body).run st1 with e | ⟨⟨env'', c⟩, st2⟩
    · rfl
    · cases c <;> rfl

theorem root_eq (p : Program) (e : Entry) (i : Instance) :
    ∃ env st, root p e i = ⟨.callFunc e.fn env .undef i.args, st⟩ := by
  obtain ⟨env, h, hb⟩ := bindProgram_safe p i.env i.heap
  exact ⟨env, ⟨h, 0⟩, by unfold root; rw [hb]⟩

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
work that cannot abort: the statement completes one fuel unit after its child and does one
more unit of work. -/
theorem holds_stmt_single {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ}
    {s : Stmt} {x : Expr}
    (hsub : ∀ env st, Sub ⟨.stmt env s, st⟩ ⟨.expr env x, st.tick⟩)
    (hdec : ∀ f env st o st', (execStmt (f + 1) env s).run st = .ok (o, st') →
      ∃ v st1, (evalExpr f env x).run st.tick = .ok (v, st1) ∧ st'.work = st1.work)
    (henc : ∀ f env st v st1, (evalExpr f env x).run st.tick = .ok (v, st1) →
      ∃ o st', (execStmt (f + 1) env s).run st = .ok (o, st'))
    (h : Holds p e i (.expr x) allChannels F B) :
    Holds p e i (.stmt s) allChannels (F + 1) (1 + B) := by
  rintro ⟨fr, st⟩ hr ⟨env, hc⟩
  simp only at hc
  subst hc
  obtain ⟨hcomp, hw⟩ := h _ (hr.tail (hsub env st)) ⟨env, rfl⟩
  refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨o2, st2, h2⟩ := hcomp f' (by omega)
    obtain ⟨v, h2', rfl⟩ := runs_expr.1 h2
    obtain ⟨o, st', h3⟩ := henc f' env st v st2 h2'
    exact ⟨_, _, runs_stmt.2 ⟨_, h3, rfl⟩⟩
  · obtain ⟨r, hv, _⟩ := runs_stmt.1 hrun
    cases f with
    | zero => rw [execStmt_zero] at hv; cases hv
    | succ f =>
      obtain ⟨v, st1, h1, hw1⟩ := hdec f env st r st' hv
      have := hw f _ st1 (runs_expr.2 ⟨_, h1, rfl⟩) (mem_allChannels _)
      simp only [St.tick, Nat.cast_add, Nat.cast_one] at this ⊢
      rw [hw1]
      linarith

theorem holds_seq {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} {s : Site}
    {sites : List Site} (hs : seqSites e s = some sites) (hB : 0 ≤ B)
    (h : ∀ x ∈ sites, Holds p e i x allChannels F B) :
    Holds p e i s allChannels (F + sites.length + 2) (1 + sites.length * B) := by
  have hlB : (0 : ℝ) ≤ sites.length * B := mul_nonneg (Nat.cast_nonneg _) hB
  cases s with
  | expr x => simp [seqSites] at hs
  | entry =>
    rcases hfn : e.fn with ⟨ps, body, ar⟩
    simp only [seqSites, hfn, Option.some.injEq] at hs
    subst hs
    have hbody : ∀ t ∈ body, Holds p e i (.stmt t) allChannels F B := fun t ht =>
      h _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    intro c hr ha
    obtain ⟨env, st, hroot⟩ := root_eq p e i
    simp only [Cfg.At] at ha
    subst ha
    rw [hroot] at hr ⊢
    rw [hfn] at hr ⊢
    obtain ⟨env', h1, hsafe⟩ := Safe.enterFunc (.mk ps body ar) env .undef i.args st
    have hstmts : Reach p e i ⟨.stmts env' body, ⟨h1, st.work⟩⟩ :=
      hr.tail (Sub.callFunc hsafe)
    obtain ⟨hc, hw⟩ := holds_stmts hB body hbody body (fun t ht => ht) env' _ hstmts
    simp only [List.length_map] at hlB ⊢
    refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨o2, st2, h2⟩ := hc f' (by omega)
      obtain ⟨⟨env2, c2⟩, h2', rfl⟩ := runs_stmts.1 h2
      exact ⟨_, _, runs_callFunc.2 ⟨_, by rw [callFunc_succ, hsafe]; simp only; rw [h2'], rfl⟩⟩
    · obtain ⟨v, hv, _⟩ := runs_callFunc.1 hrun
      cases f with
      | zero => rw [callFunc_zero] at hv; cases hv
      | succ f =>
        rw [callFunc_succ, hsafe] at hv
        simp only at hv
        rcases h2 : (execStmts f env' body).run ⟨h1, st.work⟩ with err | ⟨⟨env2, c2⟩, st2⟩
        · rw [h2] at hv; cases hv
        · rw [h2] at hv
          simp only [Except.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨_, rfl⟩ := hv
          have := hw f _ st2 (runs_stmts.2 ⟨_, h2, rfl⟩)
          simp only at this ⊢
          linarith
  | stmt st0 =>
  cases st0 with
  | block ss =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have hss : ∀ t ∈ ss, Holds p e i (.stmt t) allChannels F B := fun t ht =>
      h _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    rintro ⟨fr, st⟩ hr ⟨env, hc⟩
    simp only at hc
    subst hc
    have hstmts : Reach p e i ⟨.stmts env ss, st.tick⟩ := hr.tail Sub.block
    obtain ⟨hcomp, hw⟩ := holds_stmts hB ss hss ss (fun t ht => ht) env _ hstmts
    simp only [List.length_map] at hlB ⊢
    refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨o2, st2, h2⟩ := hcomp f' (by omega)
      obtain ⟨⟨env2, c2⟩, h2', rfl⟩ := runs_stmts.1 h2
      exact ⟨_, _, runs_stmt.2 ⟨_, by rw [execStmt_block, h2'], rfl⟩⟩
    · obtain ⟨r, hv, _⟩ := runs_stmt.1 hrun
      cases f with
      | zero => rw [execStmt_zero] at hv; cases hv
      | succ f =>
        rw [execStmt_block] at hv
        rcases h2 : (execStmts f env ss).run st.tick with err | ⟨⟨env2, c2⟩, st2⟩
        · rw [h2] at hv; cases hv
        · rw [h2] at hv
          simp only [Except.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨_, rfl⟩ := hv
          have := hw f _ st2 (runs_stmts.2 ⟨_, h2, rfl⟩)
          simp only [St.tick, Nat.cast_add, Nat.cast_one] at this ⊢
          linarith
  | expr x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .expr x) (x := x) (fun env st => Sub.exprStmt)
      (fun f env st o st' hv => by
        rw [execStmt_expr] at hv
        rcases h1 : (evalExpr f env x).run st.tick with err | ⟨v, st1⟩
        · rw [h1] at hv; cases hv
        · rw [h1] at hv; cases hv; exact ⟨v, _, rfl, rfl⟩)
      (fun f env st v st1 h1 => ⟨_, _, by rw [execStmt_expr, h1]⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp)
  | ret init =>
    cases init with
    | none => simp [seqSites] at hs
    | some x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .ret (some x)) (x := x) (fun env st => Sub.retExpr)
      (fun f env st o st' hv => by
        rw [execStmt_ret] at hv
        rcases h1 : (evalExpr f env x).run st.tick with err | ⟨v, st1⟩
        · rw [h1] at hv; cases hv
        · rw [h1] at hv; cases hv; exact ⟨v, _, rfl, rfl⟩)
      (fun f env st v st1 h1 => ⟨_, _, by rw [execStmt_ret, h1]⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp)
  | decl k y τ init =>
    cases init with
    | none => simp [seqSites] at hs
    | some x =>
    simp only [seqSites, Option.some.injEq] at hs
    subst hs
    have := holds_stmt_single (s := .decl k y τ (some x)) (x := x) (fun env st => Sub.declInit)
      (fun f env st o st' hv => by
        rw [execStmt_decl] at hv
        rcases h1 : (evalExpr f env x).run st.tick with err | ⟨v, st1⟩
        · rw [h1] at hv; cases hv
        · rw [h1] at hv
          obtain ⟨env', h3, hb⟩ := Safe.bindCell env y v τ st1
          simp only [hb] at hv
          cases hv
          exact ⟨v, st1, rfl, rfl⟩)
      (fun f env st v st1 h1 => by
        obtain ⟨env', h3, hb⟩ := Safe.bindCell env y v τ st1
        exact ⟨(env', .normal), ⟨h3, st1.work⟩, by rw [execStmt_decl, h1]; simp only [hb]⟩)
      (h (.expr x) (by simp))
    refine this.mono (by simp) (by simp)
  | ite | forLoop | forOf | forIn | «while» | doWhile | brk | cont | funDecl | classDecl =>
    simp [seqSites] at hs

theorem holds_branch {p : Program} {e : Entry} {i : Instance} {F : ℕ} {B : ℝ} {s : Site}
    {sites : List Site} (hs : branchSites s = some sites) (hB : 0 ≤ B)
    (h : ∀ x ∈ sites, Holds p e i x allChannels F B) :
    Holds p e i s allChannels (F + sites.length + 2) (1 + sites.length * B) := by
  cases s with
  | entry => simp [branchSites] at hs
  | expr x =>
    cases x with
    | cond c t g =>
      simp only [branchSites, Option.some.injEq] at hs
      subst hs
      rintro ⟨fr, st⟩ hr ⟨env, hc⟩
      simp only at hc
      subst hc
      obtain ⟨hcc, hcw⟩ := h (.expr c) (by simp) _ (hr.tail Sub.condTest) ⟨env, rfl⟩
      have hbr : ∀ v st1, (evalExpr_run : ∃ f, (evalExpr f env c).run st.tick = .ok (v, st1)) →
          ∀ y, (truthy v = true ∧ y = t ∨ truthy v = false ∧ y = g) →
          (∀ f, F ≤ f → ∃ o st', Cfg.Runs ⟨.expr env y, st1⟩ f o st') ∧
          ∀ f o st', Cfg.Runs ⟨.expr env y, st1⟩ f o st' → (st'.work : ℝ) - st1.work ≤ B := by
        rintro v st1 ⟨f0, h0⟩ y hy
        have hev : Ev (.expr env c) st.tick (.val v) st1 := ⟨f0, runs_expr.2 ⟨v, h0, rfl⟩⟩
        rcases hy with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
        · obtain ⟨a, b⟩ := h (.expr y) (by simp) _ (hr.tail (Sub.condThen hev hv)) ⟨env, rfl⟩
          exact ⟨a, fun f o st' hc => b f o st' hc (mem_allChannels _)⟩
        · obtain ⟨a, b⟩ := h (.expr y) (by simp) _ (hr.tail (Sub.condElse hev hv)) ⟨env, rfl⟩
          exact ⟨a, fun f o st' hc => b f o st' hc (mem_allChannels _)⟩
      refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
        obtain ⟨o1, st1, h1⟩ := hcc f' (by simp at hf; omega)
        obtain ⟨v, h1', rfl⟩ := runs_expr.1 h1
        cases hv : truthy v
        · obtain ⟨o2, st2, h2⟩ := (hbr v st1 ⟨f', h1'⟩ g (Or.inr ⟨hv, rfl⟩)).1 f'
            (by simp at hf; omega)
          obtain ⟨w, h2', rfl⟩ := runs_expr.1 h2
          exact ⟨_, _, runs_expr.2 ⟨w, by rw [evalExpr_cond, h1']; simp only [hv, Bool.false_eq_true, ↓reduceIte]; exact h2', rfl⟩⟩
        · obtain ⟨o2, st2, h2⟩ := (hbr v st1 ⟨f', h1'⟩ t (Or.inl ⟨hv, rfl⟩)).1 f'
            (by simp at hf; omega)
          obtain ⟨w, h2', rfl⟩ := runs_expr.1 h2
          exact ⟨_, _, runs_expr.2 ⟨w, by rw [evalExpr_cond, h1']; simp only [hv, ↓reduceIte]; exact h2', rfl⟩⟩
      · obtain ⟨w, hv', _⟩ := runs_expr.1 hrun
        cases f with
        | zero => rw [evalExpr_zero] at hv'; cases hv'
        | succ f =>
          rw [evalExpr_cond] at hv'
          rcases h1 : (evalExpr f env c).run st.tick with err | ⟨v, st1⟩
          · rw [h1] at hv'; cases hv'
          · rw [h1] at hv'
            have w1 := hcw f _ st1 (runs_expr.2 ⟨_, h1, rfl⟩) (mem_allChannels _)
            simp only [List.length_cons, List.length_nil] at w1 ⊢
            simp only [St.tick, Nat.cast_add, Nat.cast_one] at w1
            cases hv : truthy v
            · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hv'
              have w2 := (hbr v st1 ⟨f, h1⟩ g (Or.inr ⟨hv, rfl⟩)).2 f _ st'
                (runs_expr.2 ⟨_, hv', rfl⟩)
              push_cast
              linarith
            · simp only [hv, ↓reduceIte] at hv'
              have w2 := (hbr v st1 ⟨f, h1⟩ t (Or.inl ⟨hv, rfl⟩)).2 f _ st'
                (runs_expr.2 ⟨_, hv', rfl⟩)
              push_cast
              linarith
    | _ => simp [branchSites] at hs
  | stmt s0 =>
    cases s0 with
    | ite c t el =>
      have hsites : sites = [.expr c, .stmt t] ++ el.toList.map .stmt := by
        cases el <;> simp_all [branchSites]
      rw [hsites] at h ⊢
      rintro ⟨fr, st⟩ hr ⟨env, hc⟩
      simp only at hc
      subst hc
      obtain ⟨hcc, hcw⟩ := h (.expr c) (by simp) _ (hr.tail Sub.iteTest) ⟨env, rfl⟩
      have hthen : ∀ v st1, (∃ f, (evalExpr f env c).run st.tick = .ok (v, st1)) →
          truthy v = true →
          (∀ f, F ≤ f → ∃ o st', Cfg.Runs ⟨.stmt env t, st1⟩ f o st') ∧
          ∀ f o st', Cfg.Runs ⟨.stmt env t, st1⟩ f o st' → (st'.work : ℝ) - st1.work ≤ B := by
        rintro v st1 ⟨f0, h0⟩ hv
        have hev : Ev (.expr env c) st.tick (.val v) st1 := ⟨f0, runs_expr.2 ⟨v, h0, rfl⟩⟩
        obtain ⟨a, b⟩ := h (.stmt t) (by simp) _ (hr.tail (Sub.iteThen hev hv)) ⟨env, rfl⟩
        exact ⟨a, fun f o st' hc => b f o st' hc (mem_allChannels _)⟩
      have helse : ∀ g v st1, el = some g → (∃ f, (evalExpr f env c).run st.tick = .ok (v, st1)) →
          truthy v = false →
          (∀ f, F ≤ f → ∃ o st', Cfg.Runs ⟨.stmt env g, st1⟩ f o st') ∧
          ∀ f o st', Cfg.Runs ⟨.stmt env g, st1⟩ f o st' → (st'.work : ℝ) - st1.work ≤ B := by
        rintro g v st1 rfl ⟨f0, h0⟩ hv
        have hev : Ev (.expr env c) st.tick (.val v) st1 := ⟨f0, runs_expr.2 ⟨v, h0, rfl⟩⟩
        obtain ⟨a, b⟩ := h (.stmt g) (by simp) _ (hr.tail (Sub.iteElse hev hv)) ⟨env, rfl⟩
        exact ⟨a, fun f o st' hc => b f o st' hc (mem_allChannels _)⟩
      have hlen : (2 : ℝ) ≤ (([Site.expr c, .stmt t] ++ el.toList.map Site.stmt).length : ℕ) := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
        push_cast
        have : (0 : ℝ) ≤ (el.toList.length : ℝ) := Nat.cast_nonneg _
        linarith
      refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
        obtain ⟨o1, st1, h1⟩ := hcc f' (by simp at hf; omega)
        obtain ⟨v, h1', rfl⟩ := runs_expr.1 h1
        cases hv : truthy v
        · cases el with
          | none =>
            exact ⟨_, _, runs_stmt.2 ⟨_, by rw [execStmt_ite, h1']; simp only [hv, Bool.false_eq_true, ↓reduceIte]; try rfl, rfl⟩⟩
          | some g =>
            obtain ⟨o2, st2, h2⟩ := (helse g v st1 rfl ⟨f', h1'⟩ hv).1 f' (by simp at hf; omega)
            obtain ⟨⟨env2, c2⟩, h2', rfl⟩ := runs_stmt.1 h2
            exact ⟨_, _, runs_stmt.2 ⟨_, by rw [execStmt_ite, h1']; simp only [hv, h2', Bool.false_eq_true, ↓reduceIte]; try rfl, rfl⟩⟩
        · obtain ⟨o2, st2, h2⟩ := (hthen v st1 ⟨f', h1'⟩ hv).1 f' (by simp at hf; omega)
          obtain ⟨⟨env2, c2⟩, h2', rfl⟩ := runs_stmt.1 h2
          exact ⟨_, _, runs_stmt.2 ⟨_, by rw [execStmt_ite, h1']; simp only [hv, h2', ↓reduceIte]; try rfl, rfl⟩⟩
      · obtain ⟨r, hv', _⟩ := runs_stmt.1 hrun
        have hB2 : 1 + 2 * B ≤ 1 + (([Site.expr c, .stmt t] ++ el.toList.map Site.stmt).length : ℕ) * B := by
          nlinarith
        refine le_trans ?_ hB2
        cases f with
        | zero => rw [execStmt_zero] at hv'; cases hv'
        | succ f =>
          rw [execStmt_ite] at hv'
          rcases h1 : (evalExpr f env c).run st.tick with err | ⟨v, st1⟩
          · rw [h1] at hv'; cases hv'
          · rw [h1] at hv'
            have w1 := hcw f _ st1 (runs_expr.2 ⟨_, h1, rfl⟩) (mem_allChannels _)
            simp only [St.tick, Nat.cast_add, Nat.cast_one] at w1
            cases hv : truthy v
            · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hv'
              cases el with
              | none =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hv'
                obtain ⟨_, rfl⟩ := hv'
                linarith
              | some g =>
                simp only at hv'
                rcases h2 : (execStmt f env g).run st1 with err | ⟨⟨env2, c2⟩, st2⟩
                · rw [h2] at hv'; cases hv'
                · rw [h2] at hv'
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hv'
                  obtain ⟨_, rfl⟩ := hv'
                  have w2 := (helse g v st1 rfl ⟨f, h1⟩ hv).2 f _ st2 (runs_stmt.2 ⟨_, h2, rfl⟩)
                  linarith
            · simp only [hv, ↓reduceIte] at hv'
              rcases h2 : (execStmt f env t).run st1 with err | ⟨⟨env2, c2⟩, st2⟩
              · rw [h2] at hv'; cases hv'
              · rw [h2] at hv'
                simp only [Except.ok.injEq, Prod.mk.injEq] at hv'
                obtain ⟨_, rfl⟩ := hv'
                have w2 := (hthen v st1 ⟨f, h1⟩ hv).2 f _ st2 (runs_stmt.2 ⟨_, h2, rfl⟩)
                linarith
    | _ => simp [branchSites] at hs

/-! ## Unit bases -/

mutual

/-- The state-independent statement fragment. -/
def unitStmt : Stmt → Bool
  | .expr (.lit _) => true
  | .decl _ _ _ none => true
  | .decl _ _ _ (some (.lit _)) => true
  | .block ss => unitStmts ss
  | _ => false

/-- Every statement of the list lies in the fragment. -/
def unitStmts : List Stmt → Bool
  | [] => true
  | s :: ss => unitStmt s && unitStmts ss

end

mutual

/-- The work a fragment statement performs. -/
def unitTicks : Stmt → ℕ
  | .expr _ => 2
  | .decl _ _ _ none => 1
  | .decl _ _ _ (some _) => 2
  | .block ss => 1 + unitTicksList ss
  | _ => 0

/-- The work a list of fragment statements performs. -/
def unitTicksList : List Stmt → ℕ
  | [] => 0
  | s :: ss => unitTicks s + unitTicksList ss

end

mutual

/-- The fuel a fragment statement needs. -/
def unitDepth : Stmt → ℕ
  | .expr _ => 2
  | .decl _ _ _ none => 1
  | .decl _ _ _ (some _) => 2
  | .block ss => 1 + unitDepthList ss
  | _ => 1

/-- The fuel a list of fragment statements needs. -/
def unitDepthList : List Stmt → ℕ
  | [] => 1
  | s :: ss => 1 + max (unitDepth s) (unitDepthList ss)

end

/-- The outcome of running a fragment statement from work `w`: it completes normally after
exactly `t` further units, or it runs out of fuel `f` below its depth `d`. -/
def UnitRun (r : Except Abort ((Env × Completion) × St)) (w t d f : ℕ) : Prop :=
  match r with
  | .ok ((_, .normal), st') => st'.work = w + t
  | .ok _ => False
  | .error .fuel => f < d
  | .error _ => False

theorem unitDepth_pos (s : Stmt) : 0 < unitDepth s := by
  cases s with
  | decl k x τ init => cases init <;> simp [unitDepth]
  | _ => simp [unitDepth]

theorem unitDepthList_pos (ss : List Stmt) : 0 < unitDepthList ss := by
  cases ss <;> simp [unitDepthList]

theorem execStmt_decl_none (f : ℕ) (env : Env) (k : DeclKind) (y : Name) (τ : Ty) (st : St) :
    (execStmt (f + 1) env (.decl k y τ none)).run st =
      match (bindCell env y .undef τ).run st.tick with
      | .ok (env', st2) => .ok ((env', .normal), st2)
      | .error e => .error e := by
  simp only [execStmt, run_bind, run_tick1, run_pure]
  rcases (bindCell env y .undef τ).run st.tick with e | ⟨env', st2⟩ <;> rfl

theorem unit_run : ∀ f : ℕ,
    (∀ s env st, unitStmt s = true →
      UnitRun ((execStmt f env s).run st) st.work (unitTicks s) (unitDepth s) f) ∧
    (∀ ss env st, unitStmts ss = true →
      UnitRun ((execStmts f env ss).run st) st.work (unitTicksList ss) (unitDepthList ss) f)
  | 0 => ⟨fun s env st _ => by rw [execStmt_zero]; exact unitDepth_pos s,
      fun ss env st _ => by rw [execStmts_zero]; exact unitDepthList_pos ss⟩
  | f + 1 => by
    have ih := unit_run f
    refine ⟨fun s env st hs => ?_, fun ss env st hs => ?_⟩
    · match s, hs with
      | .expr (.lit l), _ =>
        rw [execStmt_expr]
        cases f with
        | zero => rw [evalExpr_zero]; simp [UnitRun, unitDepth]
        | succ f => rw [evalExpr_lit]; simp [UnitRun, unitTicks, St.tick]
      | .decl k x τ none, _ =>
        rw [execStmt_decl_none]
        obtain ⟨env', h, hb⟩ := Safe.bindCell env x .undef τ st.tick
        rw [hb]
        simp [UnitRun, unitTicks, St.tick]
      | .decl k x τ (some (.lit l)), _ =>
        rw [execStmt_decl]
        cases f with
        | zero => rw [evalExpr_zero]; simp [UnitRun, unitDepth]
        | succ f =>
          rw [evalExpr_lit]
          obtain ⟨env', h, hb⟩ := Safe.bindCell env x l.value τ st.tick.tick
          simp only [hb]
          simp only [UnitRun, unitTicks, St.tick]
      | .block ss, hs =>
        rw [execStmt_block]
        have h := ih.2 ss env st.tick (by simpa [unitStmt] using hs)
        revert h
        rcases (execStmts f env ss).run st.tick with e | ⟨⟨env', c⟩, st'⟩
        · cases e <;> simp [UnitRun, unitDepth]; omega
        · cases c <;> simp [UnitRun, unitTicks, St.tick]; omega
    · match ss, hs with
      | [], _ =>
        rw [execStmts_nil]
        simp [UnitRun, unitTicksList]
      | s :: ss, hs =>
        simp only [unitStmts, Bool.and_eq_true] at hs
        rw [execStmts_cons]
        have h1 := ih.1 s env st hs.1
        revert h1
        rcases (execStmt f env s).run st with e | ⟨⟨env', c⟩, st'⟩
        · cases e <;> simp [UnitRun, unitDepthList]; omega
        · cases c with
          | normal =>
            intro h1
            have h2 := ih.2 ss env' st' hs.2
            simp only [UnitRun] at h1
            dsimp only
            revert h2
            rcases (execStmts f env' ss).run st' with e | ⟨⟨env'', c⟩, st''⟩
            · cases e <;> simp [UnitRun, unitDepthList]; omega
            · cases c <;> simp [UnitRun, unitTicksList]; omega
          | _ => simp [UnitRun]

/-- `seq-max`, unit base: a fragment statement completes from its depth on, doing exactly its
ticks of work, from every state. -/
theorem holds_unit {p : Program} {e : Entry} {i : Instance} {s : Stmt} (hu : unitStmt s = true) :
    Holds p e i (.stmt s) allChannels (unitDepth s) (unitTicks s) := by
  rintro ⟨fr, st⟩ _ ⟨env, hc⟩
  simp only at hc
  subst hc
  have hr := fun f => (unit_run f).1 s env st hu
  refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
  · have h := hr f
    revert h
    rcases hres : (execStmt f env s).run st with e | ⟨⟨env', c⟩, st'⟩
    · cases e with
      | fuel => simp [UnitRun]; omega
      | _ => simp [UnitRun]
    · intro _; exact ⟨_, _, runs_stmt.2 ⟨_, hres, rfl⟩⟩
  · obtain ⟨r, hv, _⟩ := runs_stmt.1 hrun
    have h := hr f
    rw [hv] at h
    obtain ⟨env', c⟩ := r
    cases c <;> simp only [UnitRun] at h
    simp only [h, Nat.cast_add]
    linarith

/-- A literal expression completes from fuel `1`, doing one unit of work, from every state. -/
theorem holds_lit {p : Program} {e : Entry} {i : Instance} {l : Lit} :
    Holds p e i (.expr (.lit l)) allChannels 1 1 := by
  rintro ⟨fr, st⟩ _ ⟨env, hc⟩
  simp only at hc
  subst hc
  refine ⟨fun f hf => ?_, fun f o st' hrun _ => ?_⟩
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨_, _, runs_expr.2 ⟨_, evalExpr_lit f' env l st, rfl⟩⟩
  · obtain ⟨v, hv, _⟩ := runs_expr.1 hrun
    cases f with
    | zero => rw [evalExpr_zero] at hv; cases hv
    | succ f =>
      rw [evalExpr_lit] at hv
      cases hv
      simp [St.tick]

/-- A bound of every configuration by a fixed work from fixed fuel is a bound by the constant
`1`. -/
theorem bound_of_holds {p : Program} {n : Node} {F : ℕ} {w : ℝ}
    (h : ∀ i, Holds p n.entry i n.site allChannels F w) : Bound p n (.constant 1) :=
  ⟨w, Eventually.of_forall fun i => ⟨F, (h i).mono le_rfl (by
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
      (∀ x ∈ l, BoundOn p ⟨e, x.1⟩ x.2.1 x.2.2) → (∀ x ∈ l, ∀ v, x.2.2.eval v ≤ M.eval v) →
      ∃ C, 0 ≤ C ∧ ∀ᶠ i in Admits p e, ∃ F, ∀ x ∈ l,
        Holds p e i x.1 x.2.1 F (C * M.eval i.valuation)
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

/-- A node whose run is its children's runs, each at most once, after one unit of work, is
bounded by the maximum of the children's bounds. -/
theorem bound_compose {p : Program} {n : Node} {sites : List Site} {cs : List Cost}
    (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound p ⟨n.entry, x.1⟩ x.2)
    (hcomp : ∀ i F B, 0 ≤ B → (∀ s ∈ sites, Holds p n.entry i s allChannels F B) →
      Holds p n.entry i n.site allChannels (F + sites.length + 2) (1 + sites.length * B)) :
    Bound p n (.maximum cs) := by
  obtain ⟨C, hC, h⟩ := combine (e := n.entry) (M := .maximum cs)
    ((sites.zip cs).map fun x => (x.1, allChannels, x.2))
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact hchild x hx)
    (fun y hy v => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact eval_le_maximum v cs x.2 (List.of_mem_zip hx).2)
  refine ⟨1 + sites.length * C, h.mono fun i ⟨F, hF⟩ => ⟨F + sites.length + 2, ?_⟩⟩
  have hM := Cost.one_le_eval i.valuation (.maximum cs)
  refine (hcomp i F _ (mul_nonneg hC (by linarith)) fun s hs => ?_).mono le_rfl ?_
  · obtain ⟨c, hc⟩ := mem_zip_left sites cs hlen s hs
    exact hF (s, allChannels, c) (List.mem_map.2 ⟨(s, c), hc, rfl⟩)
  · have : (0 : ℝ) ≤ sites.length * C := mul_nonneg (Nat.cast_nonneg _) hC
    nlinarith

/-- `channel-total`: bounds of one node on channel sets that cover every channel compose into a
bound by their maximum. -/
theorem channelTotal_sound {p : Program} {n : Node} {parts : List (List Channel × Cost)}
    (hparts : ∀ x ∈ parts, BoundOn p n x.1 x.2) (hcover : ∀ k, ∃ x ∈ parts, k ∈ x.1) :
    Bound p n (.maximum (parts.map Prod.snd)) := by
  obtain ⟨C, _, h⟩ := combine (e := n.entry) (M := .maximum (parts.map Prod.snd))
    (parts.map fun x => (n.site, x.1, x.2))
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact hparts x hx)
    (fun y hy v => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact eval_le_maximum v _ x.2 (List.mem_map.2 ⟨x, hx, rfl⟩))
  refine ⟨C, h.mono fun i ⟨F, hF⟩ => ⟨F, fun c hr ha => ⟨?_, fun f o st' hc _ => ?_⟩⟩⟩
  · obtain ⟨x, hx, _⟩ := hcover .normal
    exact (hF (n.site, x.1, x.2) (List.mem_map.2 ⟨x, hx, rfl⟩) c hr ha).1
  · obtain ⟨x, hx, hk⟩ := hcover o.channel
    exact (hF (n.site, x.1, x.2) (List.mem_map.2 ⟨x, hx, rfl⟩) c hr ha).2 f o st' hc hk

/-- `seq-max`: a sequence node is bounded by the maximum of its children's bounds. -/
theorem seqMax_sound {p : Program} {n : Node} {sites : List Site} {cs : List Cost}
    (hs : seqSites n.entry n.site = some sites) (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound p ⟨n.entry, x.1⟩ x.2) : Bound p n (.maximum cs) :=
  bound_compose hlen hchild fun _ _ _ hB h => holds_seq hs hB h

/-- `branch-join`: a branch node is bounded by the maximum of its test's and branches'
bounds. -/
theorem branchJoin_sound {p : Program} {n : Node} {sites : List Site} {cs : List Cost}
    (hs : branchSites n.site = some sites) (hlen : sites.length = cs.length)
    (hchild : ∀ x ∈ sites.zip cs, Bound p ⟨n.entry, x.1⟩ x.2) : Bound p n (.maximum cs) :=
  bound_compose hlen hchild fun _ _ _ hB h => holds_branch hs hB h

/-- `seq-max`, unit base, on bounds. -/
theorem unit_bound {p : Program} {n : Node} {s : Stmt} (hn : n.site = .stmt s)
    (hu : unitStmt s = true) : Bound p n (.constant 1) :=
  bound_of_holds (F := unitDepth s) (w := (unitTicks s : ℝ)) fun i => by
    rw [hn]; exact holds_unit hu

/-- A literal expression is bounded by the unit cost. -/
theorem lit_bound {p : Program} {n : Node} {l : Lit} (hn : n.site = .expr (.lit l)) :
    Bound p n (.constant 1) :=
  bound_of_holds (F := 1) (w := 1) fun i => by rw [hn]; exact holds_lit

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

/-- The least instance with every dimension at `b`. -/
def floorInstance (b : ℝ) : Instance := ⟨Heap.empty, [], [], fun _ => b, 0⟩

/-- On large instances every dimension is at least `b`. -/
theorem eventually_dims_ge (p : Program) (e : Entry) (b : ℝ) :
    ∀ᶠ i in Admits p e, ∀ j, b ≤ i.dims j :=
  ((eventually_ge_atTop (floorInstance b)).filter_mono inf_le_left).mono fun _ h j => h j

/-- Every dimension, read as at least `1`, grows without bound on large instances. -/
theorem tendsto_dim (p : Program) (e : Entry) (j : ℕ) :
    Tendsto (fun i : Instance => max 1 (i.dims j)) (Admits p e) atTop :=
  tendsto_atTop.2 fun b => (eventually_dims_ge p e b).mono fun _ h => le_max_of_le_right (h j)

/-- A comparison of exact values against a nonnegative cost is a comparison of values. -/
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

/-- `monoWithin` establishes `O` between monomial values on large instances. -/
theorem monoWithin_isBigO (p : Program) (e : Entry) {r r' : Mono} (h : monoWithin r r' = true) :
    (fun i : Instance => monoVal i.valuation r) =O[Admits p e]
      (fun i => monoVal i.valuation r') := by
  obtain ⟨hpos, hlex⟩ := monoWithin_spec h
  set S := (r.2.map (·.1) ++ r'.2.map (·.1)).toFinset
  have hS : ∀ e ∈ r.2, e.1 ∈ S := fun e he => by
    simp only [S, List.mem_toFinset, List.mem_append, List.mem_map]; exact Or.inl ⟨e, he, rfl⟩
  have hS' : ∀ e ∈ r'.2, e.1 ∈ S := fun e he => by
    simp only [S, List.mem_toFinset, List.mem_append, List.mem_map]; exact Or.inr ⟨e, he, rfl⟩
  have hprod : (fun i : Instance => ∏ j ∈ S,
      dimVal i.valuation j ^ powSum j r.2 * lg (dimVal i.valuation j) ^ logSum j r.2) =O[Admits p e]
      (fun i => ∏ j ∈ S,
        dimVal i.valuation j ^ powSum j r'.2 * lg (dimVal i.valuation j) ^ logSum j r'.2) :=
    IsBigO.finsetProd fun j hj => (lexLe_isBigO (hlex j hj)).comp_tendsto (tendsto_dim p e j)
  have e1 : (fun i : Instance => monoVal i.valuation r) = fun i => (r.1 : ℝ) * ∏ j ∈ S,
      dimVal i.valuation j ^ powSum j r.2 * lg (dimVal i.valuation j) ^ logSum j r.2 :=
    funext fun i => by rw [monoVal, prod_regroup _ S r.2 hS]
  have e2 : (fun i : Instance => monoVal i.valuation r') = fun i => (r'.1 : ℝ) * ∏ j ∈ S,
      dimVal i.valuation j ^ powSum j r'.2 * lg (dimVal i.valuation j) ^ logSum j r'.2 :=
    funext fun i => by rw [monoVal, prod_regroup _ S r'.2 hS']
  rw [e1, e2]
  exact (hprod.const_mul_left _).trans
    (isBigO_self_const_mul (by exact_mod_cast hpos.ne') _ _)

/-- `limit-compare`: the decidable comparison `within c d` establishes `c = O(d)` on the large
admitted instances of any entry. olint's `Within` verdict (cost.rs:863-898) rests on it. -/
theorem limitCompare_sound (p : Program) (e : Entry) {c d : Cost} (h : within c d = true) :
    (fun i : Instance => c.eval i.valuation) =O[Admits p e] (fun i => d.eval i.valuation) := by
  simp only [within, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain rfl := Cost.eq_of_beq c d h; exact isBigO_refl _ _
  · split at h
    · rename_i r r' hc hd
      refine eval_isBigO ?_ (Eventually.of_forall fun i => ?_)
      · have e1 : (fun i : Instance => c.raw i.valuation) = fun i => monoVal i.valuation r :=
          funext fun i => mono_eval _ c r hc
        have e2 : (fun i : Instance => d.raw i.valuation) = fun i => monoVal i.valuation r' :=
          funext fun i => mono_eval _ d r' hd
        rw [e1, e2]
        exact monoWithin_isBigO p e h
      · rw [mono_eval _ d r' hd]; exact monoVal_nonneg _ _
    · simp at h

/-- A verdict: a bound within a limit is a bound by the limit. -/
theorem Bound.of_within {p : Program} {n : Node} {c d : Cost} (h : Bound p n c)
    (hw : within c d = true) : Bound p n d :=
  h.mono (limitCompare_sound p n.entry hw)

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
theorem maxDominance_isBigO (p : Program) (e : Entry) {s t : Cost} (hs : valid s = true)
    (ht : valid t = true) (hd : dominated (maxView s) (maxView t) = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits p e] (fun i => t.eval i.valuation) := by
  have hle : ∀ d ∈ maxView t, ∀ i : Instance, d.eval i.valuation ≤ t.eval i.valuation :=
    fun d hdm i => eval_le_of_raw_le (by
      rw [← maxView_eval _ (instance_nonnegVal i) t ht]
      exact le_rawMaximum _ _ d hdm)
  have hterms : ∀ c ∈ maxView s, (fun i : Instance => c.eval i.valuation) =O[Admits p e]
      (fun i => t.eval i.valuation) := fun c hc => by
    simp only [dominated, List.all_eq_true, List.any_eq_true] at hd
    obtain ⟨d, hdm, hw⟩ := hd c hc
    refine (limitCompare_sound p e hw).trans (IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (d.eval_pos _),
      abs_of_pos (t.eval_pos _), one_mul]
    exact hle d hdm i
  have hone : (fun _ : Instance => (1 : ℝ)) =O[Admits p e] (fun i => t.eval i.valuation) :=
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
theorem maxNormalise_isBigO (p : Program) (e : Entry) {s t : Cost} (hs : valid s = true)
    (ht : valid t = true) (hc : maxCovers (flatMax s) (flatMax t) = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits p e] (fun i => t.eval i.valuation) :=
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
theorem productNormalise_isBigO (p : Program) (e : Entry) {s t : Cost}
    (h : prodMatches s t = true) :
    (fun i : Instance => s.eval i.valuation) =O[Admits p e] (fun i => t.eval i.valuation) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s.eval_pos _), abs_of_pos (t.eval_pos _),
    one_mul]
  rcases prodMatches_eval i.valuation h with h0 | he
  · unfold Cost.eval; rw [h0, max_eq_left zero_le_one]; exact t.one_le_eval _
  · unfold Cost.eval; rw [he]

/-! ## Bound transformers -/

/-- `max-dominance` on bounds. -/
theorem maxDominance_sound {p : Program} {n : Node} {s t : Cost} (h : Bound p n s)
    (hs : valid s = true) (ht : valid t = true) (hd : dominated (maxView s) (maxView t) = true) :
    Bound p n t :=
  h.mono (maxDominance_isBigO p n.entry hs ht hd)

/-- `max-normalise` on bounds. -/
theorem maxNormalise_sound {p : Program} {n : Node} {s t : Cost} (h : Bound p n s)
    (hs : valid s = true) (ht : valid t = true) (hc : maxCovers (flatMax s) (flatMax t) = true) :
    Bound p n t :=
  h.mono (maxNormalise_isBigO p n.entry hs ht hc)

/-- `product-normalise` on bounds. -/
theorem productNormalise_sound {p : Program} {n : Node} {s t : Cost} (h : Bound p n s)
    (hm : prodMatches s t = true) : Bound p n t :=
  h.mono (productNormalise_isBigO p n.entry hm)

end Olint.Rules

import Olint.Rules.Algebra

/-!
# Declared types (ledger gap G51)

A variable read returns a value conforming to the declared type of the binding it finds
(`Olint.Model.readVarTy`, §2.5), so a read's value has a known kind exactly when the binding
the environment resolves the name to was declared with a known type. This file proves that
every binding of a name a run creates or finds was declared with one of the types name
resolution collects for it from the syntax.

**Name resolution.** `bindingTypes p e x` collects, from the encoded syntax alone, the declared
types of every binding of `x` the runs of entry `e` of program `p` can create or find: the
entry's free variables, the program's definitions, and every binding the entry's and the
definitions' functions, classes, blocks and loops create (`funcBindings`, `stmtBindings`,
`exprBindings`).

**The invariant.** For a predicate `T : Name → Ty → Prop` on names and declared types, a
heap is `T`-typed under a naming `N : Loc → Name` of its locations (`HeapOk`): its free
locations are those at or past `next` (`Heap.WF`), every variable binding at a location `l`
is declared with a type `τ` satisfying `T (N l) τ`, and every closure and class holds an
environment whose every entry `(x, l)` is a binding location named `x` (`EnvOk`) and functions
whose bindings satisfy `T` (`FuncOk`). The naming records the name each binding location was
created for; it is existential, and a run extends it at each location it allocates (`Ext`).

**Preservation.** `keeps_all` proves, by induction on fuel over the interpreter's mutual
functions, that every run started from a `T`-typed heap, an environment satisfying `EnvOk` and
syntax whose bindings satisfy `T` ends, when it completes, in a `T`-typed heap under an
extended naming, a statement returning an environment satisfying `EnvOk`. The built-in steps
of `Olint.Model.step` enter as the hypothesis `StepData W`: a step changes only the data
objects of the heap (ordinary objects, Arrays, Maps, Sets and RegExps) and allocates only data
objects. `Inv T c` is the invariant on a configuration, and `Sub` preserves it
(`Inv.sub`), so every configuration reached from a configuration satisfying it satisfies it
(`Inv.reach`).

**The root.** The root configuration of an entry's run satisfies the invariant (`Inv.root`)
when the entry function's bindings satisfy `T`, every program definition's name admits `any`
and its function's bindings satisfy `T`, and the instance's heap and environment are
`T`-typed under some naming. The last hypothesis constrains the closures and classes an
instance's heap holds, which admission (`Olint.Model.Admitted`) leaves unconstrained:
`Inv.reached` takes it as a premise.

**Consequence.** In a configuration satisfying `Inv T`, a variable read of `x` that completes
returns a value conforming to a type `τ` with `T x τ` (`readVarTy_typed`, `Inv.ident`).
-/

namespace Olint

open Olint.Model

/-! ## Name resolution -/

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

end Olint

namespace Olint.Rules

open Olint Olint.Model

/-! ## Typed heaps -/

/-- The declared type of the variable binding a location holds. -/
def _root_.Olint.Model.Heap.bindTy (h : Heap) (l : Loc) : Option Ty :=
  match h.get l with
  | some (.cell _ τ) | some (.uninit τ) => some τ
  | _ => none

/-- A data object: one a property write or a built-in step may overwrite with another data
object. Variable bindings, closures and classes are never overwritten by one. -/
def _root_.Olint.Model.Obj.isData : Obj → Bool
  | .cell _ _ | .uninit _ | .closure _ _ | .klass _ _ _ _ => false
  | _ => true

/-- A naming of heap locations: the name each binding location was created for. -/
abbrev Naming := Loc → Name

/-- Every entry `(x, l)` of an environment is a binding location named `x`. -/
def EnvOk (N : Naming) (h : Heap) (env : Env) : Prop :=
  ∀ x l, (x, l) ∈ env → N l = x ∧ h.bindTy l ≠ none

/-- Every binding an expression's functions and classes create satisfies `T`. -/
def ExprOk (T : Name → Ty → Prop) (e : Expr) : Prop :=
  ∀ x τ, τ ∈ exprBindings x e → T x τ

/-- `ExprOk` over a list. -/
def ExprsOk (T : Name → Ty → Prop) (es : List Expr) : Prop :=
  ∀ x τ, τ ∈ exprsBindings x es → T x τ

/-- `ExprOk` over object literal properties. -/
def PropsOk (T : Name → Ty → Prop) (ps : List (Name × Expr)) : Prop :=
  ∀ x τ, τ ∈ propsBindings x ps → T x τ

/-- `ExprOk` over an optional expression. -/
def OptOk (T : Name → Ty → Prop) (e : Option Expr) : Prop :=
  ∀ x τ, τ ∈ optBindings x e → T x τ

/-- Every binding a statement creates satisfies `T`. -/
def StmtOk (T : Name → Ty → Prop) (s : Stmt) : Prop :=
  ∀ x τ, τ ∈ stmtBindings x s → T x τ

/-- `StmtOk` over a list. -/
def StmtsOk (T : Name → Ty → Prop) (ss : List Stmt) : Prop :=
  ∀ x τ, τ ∈ stmtsBindings x ss → T x τ

/-- Every binding a function's call creates satisfies `T`. -/
def FuncOk (T : Name → Ty → Prop) (f : Func) : Prop :=
  ∀ x τ, τ ∈ funcBindings x f → T x τ

/-- Every binding a class's constructor and methods create satisfies `T`. -/
def ClassOk (T : Name → Ty → Prop) (c : Class) : Prop :=
  ∀ x τ, τ ∈ classBindings x c → T x τ

/-- A heap is `T`-typed under naming `N`. -/
structure HeapOk (T : Name → Ty → Prop) (N : Naming) (h : Heap) : Prop where
  wf : h.WF
  bind : ∀ l τ, h.bindTy l = some τ → T (N l) τ
  clo : ∀ l f env, h.get l = some (.closure f env) → EnvOk N h env ∧ FuncOk T f
  cls : ∀ l ctor ms acc env, h.get l = some (.klass ctor ms acc env) →
    EnvOk N h env ∧ ∀ f, ctor = some f → FuncOk T f

/-- A heap and naming extend another: allocated locations stay allocated and keep their names,
and binding locations stay binding locations. -/
structure Ext (N : Naming) (h : Heap) (N' : Naming) (h' : Heap) : Prop where
  alloc : ∀ l, h.get l ≠ none → h'.get l ≠ none
  name : ∀ l, h.get l ≠ none → N' l = N l
  bind : ∀ l, h.bindTy l ≠ none → h'.bindTy l ≠ none

theorem Ext.refl (N : Naming) (h : Heap) : Ext N h N h :=
  ⟨fun _ hl => hl, fun _ _ => rfl, fun _ hl => hl⟩

theorem Ext.trans {N1 N2 N3 : Naming} {h1 h2 h3 : Heap} (a : Ext N1 h1 N2 h2)
    (b : Ext N2 h2 N3 h3) : Ext N1 h1 N3 h3 :=
  ⟨fun l hl => b.alloc l (a.alloc l hl),
    fun l hl => (b.name l (a.alloc l hl)).trans (a.name l hl),
    fun l hl => b.bind l (a.bind l hl)⟩

theorem get_ne_none_of_bindTy {h : Heap} {l : Loc} (hb : h.bindTy l ≠ none) :
    h.get l ≠ none := by
  intro h0
  apply hb
  simp [Heap.bindTy, h0]

theorem EnvOk.ext {N N' : Naming} {h h' : Heap} {env : Env} (he : EnvOk N h env)
    (hx : Ext N h N' h') : EnvOk N' h' env := fun x l hm => by
  obtain ⟨hn, hb⟩ := he x l hm
  exact ⟨(hx.name l (get_ne_none_of_bindTy hb)).trans hn, hx.bind l hb⟩

theorem mem_of_lookup {x : Name} {l : Loc} :
    ∀ {env : Env}, env.lookup x = some l → (x, l) ∈ env
  | [], h => by simp [List.lookup] at h
  | (y, l') :: env, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hy
      cases h
      simp only [beq_iff_eq] at hy
      subst hy
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem EnvOk.lookup {N : Naming} {h : Heap} {env : Env} (he : EnvOk N h env) {x : Name} {l : Loc}
    (hl : env.lookup x = some l) : N l = x ∧ h.bindTy l ≠ none :=
  he x l (mem_of_lookup hl)

theorem EnvOk.cons {N : Naming} {h : Heap} {env : Env} (he : EnvOk N h env) {x : Name} {l : Loc}
    (hn : N l = x) (hb : h.bindTy l ≠ none) : EnvOk N h ((x, l) :: env) := fun y l' hm => by
  rcases List.mem_cons.1 hm with heq | hm
  · cases heq; exact ⟨hn, hb⟩
  · exact he y l' hm

/-! ## Runs that keep a heap typed -/

/-- A run result from heap `h` under naming `N`: when it completes, its heap is `T`-typed under
an extension of the naming, and its value satisfies `Q`. -/
def KeepsR (T : Name → Ty → Prop) {α : Type} (N : Naming) (h : Heap)
    (r : Except (Abort × ℕ) (α × St)) (Q : Naming → Heap → α → Prop) : Prop :=
  match r with
  | .ok (a, st') => ∃ N', HeapOk T N' st'.heap ∧ Ext N h N' st'.heap ∧ Q N' st'.heap a
  | .error _ => True

variable {T : Name → Ty → Prop}

theorem KeepsR.bind {α β : Type} {N : Naming} {h : Heap} {r : Except (Abort × ℕ) (α × St)}
    {k : α → St → Except (Abort × ℕ) (β × St)} {Q1 : Naming → Heap → α → Prop}
    {Q2 : Naming → Heap → β → Prop} (hr : KeepsR T N h r Q1)
    (hk : ∀ a st N', r = .ok (a, st) → HeapOk T N' st.heap → Ext N h N' st.heap →
      Q1 N' st.heap a → KeepsR T N' st.heap (k a st) Q2) :
    KeepsR T N h (Res.bind r k) Q2 := by
  rcases r with e | ⟨a, st⟩
  · trivial
  · obtain ⟨N1, hok, hx, hq⟩ := hr
    have h2 := hk a st N1 rfl hok hx hq
    show KeepsR T N h (k a st) Q2
    revert h2
    rcases k a st with e | ⟨b, st'⟩
    · intro; trivial
    · rintro ⟨N2, hok2, hx2, hq2⟩
      exact ⟨N2, hok2, hx.trans hx2, hq2⟩

theorem KeepsR.map {α β : Type} {N : Naming} {h : Heap} {g : α → β}
    {r : Except (Abort × ℕ) (α × St)} {Q : Naming → Heap → β → Prop}
    (hr : KeepsR T N h r fun N' h' a => Q N' h' (g a)) : KeepsR T N h (Res.map g r) Q := by
  rcases r with e | ⟨a, st⟩
  · trivial
  · exact hr

theorem KeepsR.ok {α : Type} {N : Naming} {h : Heap} {a : α} {st : St}
    {Q : Naming → Heap → α → Prop} (hh : st.heap = h) (hok : HeapOk T N h) (hq : Q N h a) :
    KeepsR T N h (.ok (a, st)) Q := ⟨N, hh ▸ hok, hh ▸ Ext.refl N h, hh ▸ hq⟩

theorem KeepsR.mono {α : Type} {N : Naming} {h : Heap} {r : Except (Abort × ℕ) (α × St)}
    {Q Q' : Naming → Heap → α → Prop} (hr : KeepsR T N h r Q)
    (hq : ∀ N' h' a, Q N' h' a → Q' N' h' a) : KeepsR T N h r Q' := by
  rcases r with e | ⟨a, st⟩
  · trivial
  · obtain ⟨N1, hok, hx, h1⟩ := hr
    exact ⟨N1, hok, hx, hq _ _ _ h1⟩

/-! ## Data runs

A data run changes only data objects and allocates only data objects. -/

/-- `h'` differs from `h` in data objects only, and keeps its free locations past `next`. -/
structure DataExt (h h' : Heap) : Prop where
  wf : h'.WF
  alloc : ∀ l, h.get l ≠ none → h'.get l ≠ none
  keep : ∀ l o, h.get l = some o → o.isData = false → h'.get l = some o
  back : ∀ l o, h'.get l = some o → o.isData = false → h.get l = some o

theorem DataExt.refl {h : Heap} (hw : h.WF) : DataExt h h :=
  ⟨hw, fun _ hl => hl, fun _ _ hl _ => hl, fun _ _ hl _ => hl⟩

theorem DataExt.trans {h1 h2 h3 : Heap} (a : DataExt h1 h2) (b : DataExt h2 h3) : DataExt h1 h3 :=
  ⟨b.wf, fun l hl => b.alloc l (a.alloc l hl), fun l o hl hd => b.keep l o (a.keep l o hl hd) hd,
    fun l o hl hd => a.back l o (b.back l o hl hd) hd⟩

/-- A data run result. -/
def DataR {α : Type} (h : Heap) (r : Except (Abort × ℕ) (α × St)) : Prop :=
  match r with
  | .ok (_, st') => DataExt h st'.heap
  | .error _ => True

/-- A computation whose every run from a well-formed heap is a data run. -/
def Data {α : Type} (x : M α) : Prop := ∀ st : St, st.heap.WF → DataR st.heap (x.run st)

/-- Location `l` holds a data object. -/
def DataLoc (h : Heap) (l : Loc) : Prop := ∃ o, h.get l = some o ∧ o.isData = true

/-- A computation whose every run from a well-formed heap where `l` holds a data object is a
data run. -/
def DataAt {α : Type} (l : Loc) (x : M α) : Prop :=
  ∀ st : St, st.heap.WF → DataLoc st.heap l → DataR st.heap (x.run st)

theorem DataLoc.ext {h h' : Heap} {l : Loc} (hl : DataLoc h l) (hd : DataExt h h') :
    DataLoc h' l := by
  obtain ⟨o, ho, hdo⟩ := hl
  cases ho' : h'.get l with
  | none => exact absurd ho' (hd.alloc l (by simp [ho]))
  | some o' =>
    refine ⟨o', ho', ?_⟩
    cases hdo' : o'.isData
    · have := hd.back l o' ho' hdo'
      rw [ho] at this
      cases this
      rw [hdo] at hdo'
      cases hdo'
    · rfl

theorem HeapOk.data {N : Naming} {h h' : Heap} (hok : HeapOk T N h) (hd : DataExt h h') :
    HeapOk T N h' ∧ Ext N h N h' := by
  have hx : Ext N h N h' := by
    refine ⟨hd.alloc, fun _ _ => rfl, fun l hb => ?_⟩
    unfold Heap.bindTy at hb ⊢
    split at hb
    · rename_i v τ hl
      rw [hd.keep l _ hl rfl]
      simp
    · rename_i τ hl
      rw [hd.keep l _ hl rfl]
      simp
    · exact absurd rfl hb
  refine ⟨⟨hd.wf, fun l τ hb => ?_, fun l f env hl => ?_, fun l ctor ms acc env hl => ?_⟩,
    hx⟩
  · apply hok.bind l τ
    unfold Heap.bindTy at hb ⊢
    split at hb
    · rename_i v τ' hl
      rw [hd.back l _ hl rfl]
      exact hb
    · rename_i τ' hl
      rw [hd.back l _ hl rfl]
      exact hb
    · cases hb
  · obtain ⟨he, hf⟩ := hok.clo l f env (hd.back l _ hl rfl)
    exact ⟨he.ext hx, hf⟩
  · obtain ⟨he, hf⟩ := hok.cls l ctor ms acc env (hd.back l _ hl rfl)
    exact ⟨he.ext hx, hf⟩

theorem KeepsR.ofData {α : Type} {N : Naming} {h : Heap} {r : Except (Abort × ℕ) (α × St)}
    {Q : Naming → Heap → α → Prop} (hok : HeapOk T N h) (hd : DataR h r)
    (hq : ∀ a st', r = .ok (a, st') → Q N st'.heap a) : KeepsR T N h r Q := by
  rcases r with e | ⟨a, st'⟩
  · trivial
  · obtain ⟨hok', hx⟩ := hok.data hd
    exact ⟨N, hok', hx, hq a st' rfl⟩

/-- A data computation keeps every typed heap typed. -/
theorem Data.keeps {α : Type} {x : M α} (hx : Data x) {N : Naming} {st : St}
    (hok : HeapOk T N st.heap) : KeepsR T N st.heap (x.run st) fun _ _ _ => True :=
  KeepsR.ofData hok (hx st hok.wf) fun _ _ _ => trivial

theorem DataAt.keeps {α : Type} {l : Loc} {x : M α} (hx : DataAt l x) {N : Naming} {st : St}
    (hok : HeapOk T N st.heap) (hl : DataLoc st.heap l) :
    KeepsR T N st.heap (x.run st) fun _ _ _ => True :=
  KeepsR.ofData hok (hx st hok.wf hl) fun _ _ _ => trivial

theorem Data.dataAt {α : Type} {x : M α} (hx : Data x) (l : Loc) : DataAt l x :=
  fun st hw _ => hx st hw

theorem Data.bind {α β : Type} {x : M α} {f : α → M β} (hx : Data x)
    (hf : ∀ a, Data (f a)) : Data (x >>= f) := fun st hw => by
  rw [run_bind']
  have h1 := hx st hw
  revert h1
  rcases x.run st with e | ⟨a, st1⟩
  · intro; trivial
  · intro h1
    have h2 := hf a st1 h1.wf
    show DataR st.heap ((f a).run st1)
    revert h2
    rcases (f a).run st1 with e | ⟨b, st2⟩
    · intro; trivial
    · exact fun h2 => h1.trans h2

theorem DataAt.bind {α β : Type} {l : Loc} {x : M α} {f : α → M β} (hx : DataAt l x)
    (hf : ∀ a, DataAt l (f a)) : DataAt l (x >>= f) := fun st hw hl => by
  rw [run_bind']
  have h1 := hx st hw hl
  revert h1
  rcases x.run st with e | ⟨a, st1⟩
  · intro; trivial
  · intro h1
    have h2 := hf a st1 h1.wf (hl.ext h1)
    show DataR st.heap ((f a).run st1)
    revert h2
    rcases (f a).run st1 with e | ⟨b, st2⟩
    · intro; trivial
    · exact fun h2 => h1.trans h2

theorem Data.pure {α : Type} (a : α) : Data (pure a : M α) := fun _ hw => DataExt.refl hw

theorem Data.fail {α : Type} (e : Abort) : Data (fail e : M α) := fun _ _ => trivial

theorem Data.tick (n : ℕ) : Data (tick n) := fun _ hw => DataExt.refl hw

theorem Data.charge (W : World) (f : SpecOps → ℕ) : Data (charge W f) := fun _ hw =>
  DataExt.refl hw

theorem Data.get : Data (get : M St) := fun _ hw => DataExt.refl hw

theorem Data.consult (W : World) (x : Intrinsic) : Data (consult W x) := by
  unfold Olint.Model.consult
  split
  · exact Data.fail _
  · exact Data.pure _

theorem Data.load (l : Loc) : Data (load l) := by
  unfold Olint.Model.load
  refine Data.bind Data.get fun s => ?_
  split
  · exact Data.pure _
  · exact Data.fail _

theorem Data.allocate {o : Obj} (ho : o.isData = true) : Data (allocate o) := fun st hw => by
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l o' hl hd => ?_, fun l o' hl hd => ?_⟩
  · change st.heap.next + 1 ≤ l at hl
    show (if l = st.heap.next then some o else st.heap.get l) = none
    simp only [Nat.ne_of_gt hl, ↓reduceIte]
    exact hw l (Nat.le_of_succ_le hl)
  · show (if l = st.heap.next then some o else st.heap.get l) ≠ none
    split
    · simp
    · exact hl
  · show (if l = st.heap.next then some o else st.heap.get l) = some o'
    have hne : l ≠ st.heap.next := by
      rintro rfl
      rw [hw _ le_rfl] at hl
      cases hl
    simp only [hne, ↓reduceIte]
    exact hl
  · change (if l = st.heap.next then some o else st.heap.get l) = some o' at hl
    split at hl
    · cases hl
      rw [ho] at hd
      cases hd
    · exact hl

theorem Data.store {l : Loc} {o : Obj} (ho : o.isData = true) : DataAt l (store l o) :=
  fun st hw ⟨o0, hl0, hd0⟩ => by
  refine ⟨fun l' hl => ?_, fun l' hl => ?_, fun l' o' hl hd => ?_, fun l' o' hl hd => ?_⟩
  · show (if l' = l then some o else st.heap.get l') = none
    have hne : l' ≠ l := by
      rintro rfl
      rw [hw _ hl] at hl0
      cases hl0
    simp only [hne, ↓reduceIte]
    exact hw l' hl
  · show (if l' = l then some o else st.heap.get l') ≠ none
    split
    · simp
    · exact hl
  · show (if l' = l then some o else st.heap.get l') = some o'
    have hne : l' ≠ l := by
      rintro rfl
      rw [hl0] at hl
      cases hl
      rw [hd0] at hd
      cases hd
    simp only [hne, ↓reduceIte]
    exact hl
  · change (if l' = l then some o else st.heap.get l') = some o' at hl
    split at hl
    · cases hl
      rw [ho] at hd
      cases hd
    · exact hl


/-! ## Data helpers of the interpreter -/

theorem run_load (l : Loc) (st : St) : (load l).run st = match st.heap.get l with
    | some o => .ok (o, st)
    | none => .error (.typeError, st.work) := by
  unfold Olint.Model.load
  rw [run_bind']
  show Res.bind (.ok (st, st)) _ = _
  rw [Res.bind_ok]
  cases st.heap.get l <;> rfl

/-- A data computation closed by one lemma. -/
syntax "data_leaf" : tactic

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.pure _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.fail _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.tick _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.charge _ _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.consult _ _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.load _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.get)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.allocate rfl)

/-- Close a data goal by the data combinators. -/
macro "data_tac" : tactic => `(tactic| repeat' (first
  | data_leaf
  | (apply Data.bind <;> intros)
  | split))

theorem Data.toNumeric (v : Value) : Data (toNumeric v) := by
  cases v <;> first | exact Data.pure _ | exact Data.fail _

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.toNumeric _)

theorem Data.toStringPrim (W : World) (v : Value) : Data (toStringPrim W v) := by
  cases v <;> simp only [Olint.Model.toStringPrim] <;> data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.toStringPrim _ _)

theorem Data.binop (W : World) (op : BinOp) (a b : Value) : Data (binop W op a b) := by
  unfold Olint.Model.binop
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.binop _ _ _ _)

theorem Data.unop (op : UnOp) (v : Value) : Data (unop op v) := by
  unfold Olint.Model.unop
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.unop _ _)

theorem Data.objectProtoGet (W : World) (x : Name) : Data (objectProtoGet W x) := by
  unfold Olint.Model.objectProtoGet
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.objectProtoGet _ _)

theorem Data.protoGet (W : World) (cls : Option Loc) (x : Name) : Data (protoGet W cls x) := by
  unfold Olint.Model.protoGet
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.protoGet _ _ _)

theorem Data.consultProto (W : World) (o : Obj) : Data (consultProto W o) := by
  unfold Olint.Model.consultProto
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.consultProto _ _)

theorem Data.readProp (W : World) (o : Obj) (x : Name) : Data (readProp W o x) := by
  unfold Olint.Model.readProp
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.readProp _ _ _)

theorem Data.getProp (W : World) (v : Value) (x : Name) : Data (getProp W v x) := by
  unfold Olint.Model.getProp
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.getProp _ _ _)

theorem Data.arrayMiss (W : World) : Data (arrayMiss W) := by
  unfold Olint.Model.arrayMiss
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.arrayMiss _)

theorem Data.readElem (W : World) (elems : List Value) (i : ℕ) : Data (readElem W elems i) := by
  unfold Olint.Model.readElem
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.readElem _ _ _)

theorem Data.getIndex (W : World) (v k : Value) : Data (getIndex W v k) := by
  unfold Olint.Model.getIndex
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.getIndex _ _ _)

theorem Data.newObject (W : World) (cls : Loc) : Data (newObject W cls) := by
  unfold Olint.Model.newObject
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.newObject _ _)

theorem Data.iterStep (W : World) (o : Obj) (i : ℕ) : Data (iterStep W o i) := by
  unfold Olint.Model.iterStep
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.iterStep _ _ _)

theorem Data.forInKeys (W : World) (l : Loc) : Data (forInKeys W l) := by
  unfold Olint.Model.forInKeys
  data_tac

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.forInKeys _ _)

theorem DataAt.pure {α : Type} (l : Loc) (a : α) : DataAt l (pure a : M α) :=
  (Data.pure a).dataAt l

theorem DataAt.fail {α : Type} (l : Loc) (e : Abort) : DataAt l (fail e : M α) :=
  (Data.fail e).dataAt l

theorem DataAt.ite {α : Type} {l : Loc} {c : Prop} [Decidable c] {x y : M α} (hx : DataAt l x)
    (hy : DataAt l y) : DataAt l (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-- Close a data goal at a location holding a data object. -/
macro "dataAt_tac" : tactic => `(tactic| repeat' (first
  | exact Data.store rfl
  | exact DataAt.putElem _ _ _ _ _
  | exact DataAt.putProp _ _ _ _ _ _ _
  | (apply Data.dataAt; data_leaf)
  | (apply DataAt.bind <;> intros)
  | split
  | (dsimp only)))

theorem DataAt.putElem (W : World) (l : Loc) (elems : List Value) (i : ℕ) (v : Value) :
    DataAt l (putElem W l elems i v) := by
  unfold Olint.Model.putElem
  dataAt_tac

theorem DataAt.putProp (W : World) (l : Loc) (props : List (Name × Value)) (acc : List Name)
    (cls : Option Loc) (x : Name) (v : Value) : DataAt l (putProp W l props acc cls x v) := by
  unfold Olint.Model.putProp
  dataAt_tac

/-- A computation that loads `l` and continues as a data computation, with `l` holding a data
object when the loaded object is one. -/
theorem Data.bindLoad {α : Type} (l : Loc) {f : Obj → M α}
    (hd : ∀ o, o.isData = true → DataAt l (f o)) (hn : ∀ o, o.isData = false → Data (f o)) :
    Data (Olint.Model.load l >>= f) := fun st hw => by
  rw [run_bind', run_load]
  cases hl : st.heap.get l with
  | none => trivial
  | some o =>
    show DataR st.heap ((f o).run st)
    cases ho : o.isData
    · exact hn o ho st hw
    · exact hd o ho st hw ⟨o, hl, ho⟩

theorem Data.putIndex (W : World) (v k w : Value) : Data (putIndex W v k w) := by
  unfold Olint.Model.putIndex
  split
  · rename_i l
    refine Data.bindLoad l (fun o _ => ?_) (fun o hn => ?_)
    · split
      · refine DataAt.bind ((Data.charge _ _).dataAt l) fun _ => ?_
        split
        · exact DataAt.putElem _ _ _ _ _
        · exact DataAt.fail l _
      · split
        · exact DataAt.putElem _ _ _ _ _
        · exact DataAt.fail l _
      · exact DataAt.putProp _ _ _ _ _ _ _
      · refine DataAt.bind ((Data.charge _ _).dataAt l) fun _ => ?_
        split
        · exact DataAt.putProp _ _ _ _ _ _ _
        · exact DataAt.fail l _
      · exact DataAt.fail l _
    · split <;> first | exact Data.fail _ | simp [Obj.isData] at hn
  all_goals exact Data.fail _

/-- A built-in step changes only data objects and allocates only data objects. -/
def StepData (W : World) : Prop :=
  ∀ b isNew h self args v h' w, h.WF → step W.ops b isNew h self args = .ok v h' w →
    DataExt h h'

theorem Data.ofGet {α : Type} {f : St → M α}
    (hf : ∀ st : St, st.heap.WF → DataR st.heap ((f st).run st)) :
    Data ((MonadState.get : M St) >>= f) :=
  fun st hw => by
  rw [run_bind']
  exact hf st hw

theorem Data.runStep {W : World} (hW : StepData W) (b : Builtin) (isNew : Bool) (self : Value)
    (args : List Value) : Data (runStep W b isNew self args) := by
  unfold Olint.Model.runStep
  refine Data.bind ?_ fun _ => ?_
  · generalize stepIntrinsics b isNew = xs
    induction xs with
    | nil => exact Data.pure _
    | cons x xs ih =>
      exact Data.bind (Data.consult _ _) fun _ => ih
  · refine Data.ofGet fun st hw => ?_
    split
    · rename_i v h w hs
      exact hW _ _ _ _ _ _ _ _ hw hs
    · trivial
    · trivial
    · trivial

/-! ## Allocating and overwriting typed objects -/

/-- A new object at a fresh location named `y` keeps a typed heap typed: a binding declared
with a type `τ` satisfying `T y τ`, a closure or class over an environment satisfying `EnvOk`
with functions satisfying `FuncOk`, or a data object. -/
def ObjOk (T : Name → Ty → Prop) (N : Naming) (h : Heap) (y : Name) : Obj → Prop
  | .cell _ τ | .uninit τ => T y τ
  | .closure f env => EnvOk N h env ∧ FuncOk T f
  | .klass ctor _ _ env => EnvOk N h env ∧ ∀ f, ctor = some f → FuncOk T f
  | _ => True

theorem alloc_get (h : Heap) (o : Obj) (l : Loc) :
    (h.alloc o).2.get l = if l = h.next then some o else h.get l := rfl

theorem put_get (h : Heap) (l : Loc) (o : Obj) (l' : Loc) :
    (h.put l o).get l' = if l' = l then some o else h.get l' := rfl

/-- The declared type of a binding object. -/
def _root_.Olint.Model.Obj.bty : Obj → Option Ty
  | .cell _ τ | .uninit τ => some τ
  | _ => none

theorem bindTy_eq (h : Heap) (l : Loc) : h.bindTy l = (h.get l).bind Obj.bty := by
  unfold Heap.bindTy
  cases h.get l with
  | none => rfl
  | some o => cases o <;> rfl

theorem ite_no {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem ite_yes {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem KeepsR.pre {α : Type} {N N' : Naming} {h h' : Heap}
    {r : Except (Abort × ℕ) (α × St)} {Q : Naming → Heap → α → Prop}
    (hx : Ext N h N' h') (hr : KeepsR T N' h' r Q) : KeepsR T N h r Q := by
  rcases r with e | ⟨a, st⟩
  · trivial
  · obtain ⟨N1, hok, hx1, hq⟩ := hr
    exact ⟨N1, hok, hx.trans hx1, hq⟩

theorem bindTy_alloc (h : Heap) (o : Obj) (l : Loc) :
    (h.alloc o).2.bindTy l = if l = h.next then o.bty else h.bindTy l := by
  rw [bindTy_eq, bindTy_eq, alloc_get]
  split <;> rfl

theorem bindTy_put (h : Heap) (l : Loc) (o : Obj) (l' : Loc) :
    (h.put l o).bindTy l' = if l' = l then o.bty else h.bindTy l' := by
  rw [bindTy_eq, bindTy_eq, put_get]
  split <;> rfl

theorem ne_next_of_get {h : Heap} (hw : h.WF) {l : Loc} (hl : h.get l ≠ none) : l ≠ h.next := by
  rintro rfl
  exact hl (hw _ le_rfl)

theorem alloc_ok {N : Naming} {h : Heap} (hok : HeapOk T N h) (y : Name) (o : Obj)
    (ho : ObjOk T N h y o) :
    HeapOk T (Function.update N h.next y) (h.alloc o).2 ∧
      Ext N h (Function.update N h.next y) (h.alloc o).2 := by
  have hx : Ext N h (Function.update N h.next y) (h.alloc o).2 := by
    refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hb => ?_⟩
    · rw [alloc_get, ite_no (ne_next_of_get hok.wf hl)]
      exact hl
    · exact Function.update_of_ne (ne_next_of_get hok.wf hl) _ _
    · have hne := ne_next_of_get hok.wf (get_ne_none_of_bindTy hb)
      rw [bindTy_alloc, ite_no hne]
      exact hb
  refine ⟨⟨fun l hl => ?_, fun l τ hb => ?_, fun l f env hl => ?_,
    fun l ctor ms acc env hl => ?_⟩, hx⟩
  · change h.next + 1 ≤ l at hl
    rw [alloc_get, ite_no (Nat.ne_of_gt hl)]
    exact hok.wf l (Nat.le_of_succ_le hl)
  · rw [bindTy_alloc] at hb
    by_cases hl : l = h.next
    · subst hl
      rw [ite_yes rfl] at hb
      rw [Function.update_self]
      cases o <;> simp [Obj.bty] at hb <;> (subst hb; exact ho)
    · rw [ite_no hl] at hb
      rw [Function.update_of_ne hl]
      exact hok.bind l τ hb
  · rw [alloc_get] at hl
    split at hl
    · cases hl
      exact ⟨ho.1.ext hx, ho.2⟩
    · obtain ⟨he, hf⟩ := hok.clo l f env hl
      exact ⟨he.ext hx, hf⟩
  · rw [alloc_get] at hl
    split at hl
    · cases hl
      exact ⟨ho.1.ext hx, ho.2⟩
    · obtain ⟨he, hf⟩ := hok.cls l ctor ms acc env hl
      exact ⟨he.ext hx, hf⟩

theorem store_cell_ok {N : Naming} {h : Heap} (hok : HeapOk T N h) {l : Loc}
    (hb : h.bindTy l ≠ none) (v : Value) {τ : Ty} (hτ : T (N l) τ) :
    HeapOk T N (h.put l (.cell v τ)) ∧ Ext N h N (h.put l (.cell v τ)) := by
  have hl0 := get_ne_none_of_bindTy hb
  have hx : Ext N h N (h.put l (.cell v τ)) := by
    refine ⟨fun l' hl => ?_, fun _ _ => rfl, fun l' hb' => ?_⟩
    · rw [put_get]
      split
      · simp
      · exact hl
    · rw [bindTy_put]
      split
      · simp [Obj.bty]
      · exact hb'
  refine ⟨⟨fun l' hl => ?_, fun l' τ' hb' => ?_, fun l' f env hl => ?_,
    fun l' ctor ms acc env hl => ?_⟩, hx⟩
  · have hne : l' ≠ l := by
      rintro rfl
      exact hl0 (hok.wf _ hl)
    show (if l' = l then _ else h.get l') = none
    rw [ite_no hne]
    exact hok.wf l' hl
  · rw [bindTy_put] at hb'
    split at hb'
    · rename_i he
      subst he
      simp only [Obj.bty, Option.some.injEq] at hb'
      subst hb'
      exact hτ
    · exact hok.bind l' τ' hb'
  · rw [put_get] at hl
    split at hl
    · cases hl
    · obtain ⟨he, hf⟩ := hok.clo l' f env hl
      exact ⟨he.ext hx, hf⟩
  · rw [put_get] at hl
    split at hl
    · cases hl
    · obtain ⟨he, hf⟩ := hok.cls l' ctor ms acc env hl
      exact ⟨he.ext hx, hf⟩

/-! ## Variable reads and writes -/

theorem readVarTy_ok {l : Loc} {st st' : St} {v : Value} {τ : Ty}
    (h : (readVarTy l).run st = .ok ((v, τ), st')) :
    st' = st ∧ st.heap.bindTy l = some τ ∧ conforms st.heap v τ = true := by
  unfold readVarTy at h
  rw [run_bind', run_load] at h
  cases hl : st.heap.get l with
  | none => rw [hl] at h; cases h
  | some o =>
    rw [hl] at h
    simp only [Res.bind_ok] at h
    split at h
    · rename_i v' τ'
      rw [run_bind'] at h
      change Res.bind (.ok (st, st)) _ = _ at h
      rw [Res.bind_ok] at h
      split at h
      · cases h
        exact ⟨rfl, by simp [Heap.bindTy, hl], by assumption⟩
      · cases h
    · cases h
    · cases h

theorem cellType_ok {l : Loc} {st st' : St} {τ : Ty} (h : (cellType l).run st = .ok (τ, st')) :
    st' = st ∧ st.heap.bindTy l = some τ := by
  unfold cellType at h
  rw [run_bind', run_load] at h
  cases hl : st.heap.get l with
  | none => rw [hl] at h; cases h
  | some o =>
    rw [hl] at h
    simp only [Res.bind_ok] at h
    split at h
    · cases h
      exact ⟨rfl, by simp [Heap.bindTy, hl]⟩
    · cases h
    · cases h

theorem Data.readVarTy (l : Loc) : Data (readVarTy l) := fun st hw => by
  cases h : (Olint.Model.readVarTy l).run st with
  | error => trivial
  | ok r =>
    obtain ⟨⟨v, τ⟩, st'⟩ := r
    obtain ⟨rfl, -⟩ := readVarTy_ok h
    exact DataExt.refl hw

theorem Data.readVar (l : Loc) : Data (readVar l) := by
  unfold Olint.Model.readVar
  exact Data.bind (Data.readVarTy l) fun _ => Data.pure _

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.readVar _)

theorem Data.cellType (l : Loc) : Data (cellType l) := fun st hw => by
  cases h : (Olint.Model.cellType l).run st with
  | error => trivial
  | ok r =>
    obtain ⟨τ, st'⟩ := r
    obtain ⟨rfl, -⟩ := cellType_ok h
    exact DataExt.refl hw

/-! ## Binding helpers -/

theorem keeps_bindCell {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) (x : Name) (v : Value) {τ : Ty} (hτ : T x τ) :
    KeepsR T N st.heap ((bindCell env x v τ).run st) fun N' h' env' => EnvOk N' h' env' := by
  obtain ⟨hok', hx⟩ := alloc_ok hok x (.cell v τ) hτ
  refine ⟨_, hok', hx, (he.ext hx).cons (Function.update_self _ _ _) ?_⟩
  show Heap.bindTy _ _ ≠ none
  rw [bindTy_alloc, ite_yes rfl]
  simp [Obj.bty]

theorem keeps_bindParams : ∀ (ps : List (Name × Ty)) {N : Naming} {st : St} {env : Env}
    (args : List Value), HeapOk T N st.heap → EnvOk N st.heap env →
    (∀ p ∈ ps, T p.1 p.2) →
    KeepsR T N st.heap ((bindParams env ps args).run st) fun N' h' env' => EnvOk N' h' env'
  | [], _, st, env, _, hok, he, _ => KeepsR.ok rfl hok he
  | (x, τ) :: ps, N, st, env, args, hok, he, hps => by
    simp only [bindParams]
    rw [run_bind']
    exact KeepsR.bind (keeps_bindCell hok he x _ (hps _ List.mem_cons_self))
      fun env' st1 N1 _ hok1 _ he1 => keeps_bindParams ps _ hok1 he1
        fun p hp => hps p (List.mem_cons_of_mem _ hp)

theorem keeps_bindUninit : ∀ (bs : List (Name × Ty)) {N : Naming} {st : St} {env : Env},
    HeapOk T N st.heap → EnvOk N st.heap env → (∀ b ∈ bs, T b.1 b.2) →
    KeepsR T N st.heap ((bindUninit env bs).run st) fun N' h' env' => EnvOk N' h' env'
  | [], _, st, env, hok, he, _ => KeepsR.ok rfl hok he
  | (x, τ) :: bs, N, st, env, hok, he, hbs => by
    simp only [bindUninit]
    rw [run_bind']
    show KeepsR T N st.heap (Res.bind (.ok (st.heap.next, { st with heap := (st.heap.alloc
      (.uninit τ)).2 })) _) _
    rw [Res.bind_ok]
    obtain ⟨hok', hx⟩ := alloc_ok hok x (.uninit τ) (hbs _ List.mem_cons_self)
    refine KeepsR.pre hx <| keeps_bindUninit
      (st := { st with heap := (st.heap.alloc (.uninit τ)).2 }) bs hok'
      ((he.ext hx).cons (Function.update_self _ _ _) ?_)
      fun b hb => hbs b (List.mem_cons_of_mem _ hb)
    show Heap.bindTy _ _ ≠ none
    rw [bindTy_alloc, ite_yes rfl]
    simp [Obj.bty]

theorem keeps_hoistVars : ∀ (vs : List (Name × Ty)) {N : Naming} {st : St} {env : Env}
    (seen : List Name), HeapOk T N st.heap → EnvOk N st.heap env → (∀ b ∈ vs, T b.1 b.2) →
    KeepsR T N st.heap ((hoistVars env seen vs).run st) fun N' h' env' => EnvOk N' h' env'
  | [], _, st, env, _, hok, he, _ => KeepsR.ok rfl hok he
  | (x, τ) :: vs, N, st, env, seen, hok, he, hvs => by
    simp only [hoistVars]
    split
    · exact keeps_hoistVars vs seen hok he fun b hb => hvs b (List.mem_cons_of_mem _ hb)
    · rw [run_bind']
      exact KeepsR.bind (keeps_bindCell hok he x _ (hvs _ List.mem_cons_self))
        fun env' st1 N1 _ hok1 _ he1 => keeps_hoistVars vs _ hok1 he1
          fun b hb => hvs b (List.mem_cons_of_mem _ hb)

theorem keeps_storeFun {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) (x : Name) (f : Func) (hx : T x .any) (hf : FuncOk T f) :
    KeepsR T N st.heap ((storeFun env x f).run st) fun _ _ _ => True := by
  unfold storeFun
  split
  · rename_i l hl
    rw [run_bind']
    show KeepsR T N st.heap (Res.bind (.ok (st.heap.next, { st with heap := (st.heap.alloc
      (.closure f env)).2 })) _) _
    rw [Res.bind_ok]
    obtain ⟨hok1, hx1⟩ := alloc_ok hok "" (.closure f env) ⟨he, hf⟩
    obtain ⟨hn, hb⟩ := (he.ext hx1).lookup hl
    obtain ⟨hok2, hx2⟩ := store_cell_ok hok1 hb (.ref st.heap.next) (τ := .any) (hn ▸ hx)
    exact ⟨_, hok2, hx1.trans hx2, trivial⟩
  · exact KeepsR.ok rfl hok trivial

theorem keeps_storeFuns (W : World) {env : Env} :
    ∀ (fs : List (Name × Func)) {N : Naming} {st : St},
    HeapOk T N st.heap → EnvOk N st.heap env → (∀ d ∈ fs, T d.1 .any ∧ FuncOk T d.2) →
    KeepsR T N st.heap ((storeFuns W env fs).run st) fun _ _ _ => True
  | [], _, st, hok, _, _ => KeepsR.ok rfl hok trivial
  | (x, f) :: fs, N, st, hok, he, hfs => by
    simp only [storeFuns]
    rw [run_bind']
    refine KeepsR.bind ((Data.charge W _).keeps hok) fun _ st1 N1 _ hok1 hx1 _ => ?_
    rw [run_bind']
    obtain ⟨hxa, hf⟩ := hfs _ List.mem_cons_self
    refine KeepsR.bind (keeps_storeFun hok1 (he.ext hx1) x f hxa hf)
      fun _ st2 N2 _ hok2 hx2 _ => ?_
    exact keeps_storeFuns W fs hok2 ((he.ext hx1).ext hx2)
      fun d hd => hfs d (List.mem_cons_of_mem _ hd)

theorem keeps_bindFuns (W : World) {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) (fs : List (Name × Func))
    (hfs : ∀ d ∈ fs, T d.1 .any ∧ FuncOk T d.2) :
    KeepsR T N st.heap ((bindFuns W env fs).run st) fun N' h' env' => EnvOk N' h' env' := by
  unfold bindFuns
  rw [run_bind']
  refine KeepsR.bind (keeps_bindUninit _ hok he fun b hb => ?_) fun env1 st1 N1 _ hok1 _ he1 => ?_
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
    exact (hfs d hd).1
  · rw [run_bind']
    exact KeepsR.bind (keeps_storeFuns W fs hok1 he1 hfs) fun _ st2 N2 _ hok2 hx2 _ =>
      KeepsR.ok rfl hok2 (he1.ext hx2)

theorem keeps_allocate {N : Naming} {st : St} (hok : HeapOk T N st.heap) (y : Name) (o : Obj)
    (ho : ObjOk T N st.heap y o) :
    KeepsR T N st.heap ((allocate o).run st) fun _ h' l => h'.get l = some o := by
  obtain ⟨hok', hx⟩ := alloc_ok hok y o ho
  refine ⟨_, hok', hx, ?_⟩
  show (if st.heap.next = st.heap.next then _ else _) = _
  rw [ite_yes rfl]

/-! ## Name resolution covers every binding a run creates -/

theorem lexBindings_mem : ∀ (ss : List Stmt) (x : Name) (τ : Ty), (x, τ) ∈ lexBindings ss →
    τ ∈ stmtsBindings x ss
  | [], _, _, h => by simp [lexBindings] at h
  | s :: ss, x, τ, h => by
    have ih := lexBindings_mem ss x τ
    simp only [stmtsBindings, List.mem_append]
    match s, h with
    | .decl .«let» y σ init, h | .decl .«const» y σ init, h =>
      simp only [lexBindings, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · left; simp [stmtBindings]
      · exact Or.inr (ih h)
    | .decl .var y σ init, h => exact Or.inr (ih (by simpa [lexBindings] using h))
    | .classDecl y c, h =>
      simp only [lexBindings, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · left; simp [stmtBindings]
      · exact Or.inr (ih h)
    | .expr _, h | .block _, h | .ite _ _ _, h | .forLoop _ _ _ _, h | .forOf _ _ _, h
    | .forIn _ _ _, h | .«while» _ _, h | .doWhile _ _, h | .ret _, h | .brk, h | .cont, h
    | .funDecl _ _, h => exact Or.inr (ih (by simpa [lexBindings] using h))

theorem funDecls_mem : ∀ (ss : List Stmt) (y : Name) (f : Func), (y, f) ∈ funDecls ss →
    Ty.any ∈ stmtsBindings y ss ∧
      ∀ x τ, τ ∈ funcBindings x f → τ ∈ stmtsBindings x ss
  | [], _, _, h => by simp [funDecls] at h
  | s :: ss, y, f, h => by
    have ih := funDecls_mem ss y f
    simp only [stmtsBindings, List.mem_append]
    match s, h with
    | .funDecl z g, h =>
      simp only [funDecls, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨Or.inl (by simp [stmtBindings]),
          fun x τ hm => Or.inl (by simp [stmtBindings, hm])⟩
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨Or.inr h1, fun x τ hm => Or.inr (h2 x τ hm)⟩
    | .expr _, h | .decl _ _ _ _, h | .block _, h | .ite _ _ _, h | .forLoop _ _ _ _, h
    | .forOf _ _ _, h | .forIn _ _ _, h | .«while» _ _, h | .doWhile _ _, h | .ret _, h | .brk, h
    | .cont, h | .classDecl _ _, h =>
      obtain ⟨h1, h2⟩ := ih (by simpa [funDecls] using h)
      exact ⟨Or.inr h1, fun x τ hm => Or.inr (h2 x τ hm)⟩

mutual

theorem varDecls_mem : ∀ (s : Stmt) (x : Name) (τ : Ty), (x, τ) ∈ varDecls s →
    τ ∈ stmtBindings x s
  | .decl .var y σ init, x, τ, h => by
    simp only [varDecls, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [stmtBindings]
  | .block ss, x, τ, h => by
    simp only [varDecls] at h
    simpa [stmtBindings] using varDeclsList_mem ss x τ h
  | .ite c t e, x, τ, h => by
    simp only [varDecls, List.mem_append] at h
    simp only [stmtBindings, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inr (varDecls_mem t x τ h))
    · exact Or.inr (optVarDecls_mem e x τ h)
  | .forLoop init test update body, x, τ, h => by
    simp only [varDecls, List.mem_append] at h
    simp only [stmtBindings, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl (optVarDecls_mem init x τ h)))
    · exact Or.inr (varDecls_mem body x τ h)
  | .forOf y e body, x, τ, h => by
    simp only [varDecls] at h
    simp only [stmtBindings, List.mem_append]
    exact Or.inr (varDecls_mem body x τ h)
  | .forIn y e body, x, τ, h => by
    simp only [varDecls] at h
    simp only [stmtBindings, List.mem_append]
    exact Or.inr (varDecls_mem body x τ h)
  | .«while» c body, x, τ, h => by
    simp only [varDecls] at h
    simp only [stmtBindings, List.mem_append]
    exact Or.inr (varDecls_mem body x τ h)
  | .doWhile body c, x, τ, h => by
    simp only [varDecls] at h
    simp only [stmtBindings, List.mem_append]
    exact Or.inr (varDecls_mem body x τ h)
  | .decl .«let» _ _ _, _, _, h | .decl .«const» _ _ _, _, _, h | .expr _, _, _, h
  | .ret _, _, _, h | .brk, _, _, h | .cont, _, _, h | .funDecl _ _, _, _, h
  | .classDecl _ _, _, _, h => by simp [varDecls] at h

theorem varDeclsList_mem : ∀ (ss : List Stmt) (x : Name) (τ : Ty),
    (x, τ) ∈ varDeclsList ss → τ ∈ stmtsBindings x ss
  | [], _, _, h => by simp [varDeclsList] at h
  | s :: ss, x, τ, h => by
    simp only [varDeclsList, List.mem_append] at h
    simp only [stmtsBindings, List.mem_append]
    rcases h with h | h
    · exact Or.inl (varDecls_mem s x τ h)
    · exact Or.inr (varDeclsList_mem ss x τ h)

theorem optVarDecls_mem : ∀ (s : Option Stmt) (x : Name) (τ : Ty), (x, τ) ∈ optVarDecls s →
    τ ∈ optStmtBindings x s
  | none, _, _, h => by simp [optVarDecls] at h
  | some s, x, τ, h => by
    simp only [optVarDecls] at h
    simpa [optStmtBindings] using varDecls_mem s x τ h

end

theorem forScope_mem (init : Option Stmt) (x : Name) (τ : Ty) (h : (x, τ) ∈ forScope init) :
    τ ∈ optStmtBindings x init := by
  match init, h with
  | some (.decl .«let» y σ e), h | some (.decl .«const» y σ e), h =>
    simp only [forScope, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [optStmtBindings, stmtBindings]
  | none, h => simp [forScope] at h
  | some (.decl .var _ _ _), h | some (.expr _), h | some (.block _), h | some (.ite _ _ _), h
  | some (.forLoop _ _ _ _), h | some (.forOf _ _ _), h | some (.forIn _ _ _), h
  | some (.«while» _ _), h | some (.doWhile _ _), h | some (.ret _), h | some .brk, h
  | some .cont, h | some (.funDecl _ _), h | some (.classDecl _ _), h => simp [forScope] at h

theorem FuncOk.this {ps : List (Name × Ty)} {body : List Stmt}
    (hf : FuncOk T (.mk ps body false)) :
    T "this" .any := hf _ _ (by simp [funcBindings])

theorem FuncOk.param {ps : List (Name × Ty)} {body : List Stmt} {ar : Bool}
    (hf : FuncOk T (.mk ps body ar)) {p : Name × Ty} (hp : p ∈ ps) : T p.1 p.2 :=
  hf _ _ (by
    simp only [funcBindings, List.mem_append, List.mem_map, List.mem_filter]
    exact Or.inl (Or.inr ⟨p, ⟨hp, by simp⟩, rfl⟩))

theorem FuncOk.body {ps : List (Name × Ty)} {body : List Stmt} {ar : Bool}
    (hf : FuncOk T (.mk ps body ar)) : StmtsOk T body := fun x τ h =>
  hf x τ (by simp [funcBindings, h])

theorem ClassOk.ctor {ctor : Option Func} {ms : List (Name × Func)} (hc : ClassOk T (.mk ctor ms))
    (f : Func) (hf : ctor = some f) : FuncOk T f := fun x τ h =>
  hc x τ (by subst hf; simp [classBindings, optFuncBindings, h])

theorem methodsOk : ∀ {ms : List (Name × Func)},
    (∀ x τ, τ ∈ methodsBindings x ms → T x τ) → ∀ m ∈ ms, FuncOk T m.2
  | [], _, m, hm => by simp at hm
  | (y, f) :: ms, h, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact fun x τ hx => h x τ (by simp [methodsBindings, hx])
    · exact methodsOk (fun x τ hx => h x τ (by simp [methodsBindings, hx])) m hm

theorem ClassOk.methods {ctor : Option Func} {ms : List (Name × Func)}
    (hc : ClassOk T (.mk ctor ms)) : ∀ m ∈ ms, FuncOk T m.2 :=
  methodsOk fun x τ h => hc x τ (by simp [classBindings, h])

/-! ## Declaration instantiation -/

theorem keeps_instantiate (W : World) {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) {ss : List Stmt} (hss : StmtsOk T ss) :
    KeepsR T N st.heap ((instantiate W env ss).run st) fun N' h' env' => EnvOk N' h' env' := by
  unfold instantiate
  rw [run_bind']
  refine KeepsR.bind (keeps_bindUninit _ hok he fun b hb => hss _ _ (lexBindings_mem ss _ _ hb))
    fun env1 st1 N1 _ hok1 _ he1 => keeps_bindFuns W hok1 he1 _ fun d hd => ?_
  obtain ⟨h1, h2⟩ := funDecls_mem ss d.1 d.2 hd
  exact ⟨hss _ _ h1, fun x τ hx => hss _ _ (h2 x τ hx)⟩

theorem keeps_enterFunc (W : World) {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) {f : Func} (hf : FuncOk T f) (self : Value) (args : List Value) :
    KeepsR T N st.heap ((enterFunc W f env self args).run st)
      fun N' h' env' => EnvOk N' h' env' := by
  obtain ⟨ps, body, ar⟩ := f
  rw [enterFunc, run_bind']
  have hthis : KeepsR T N st.heap ((bindThis ar env self).run st)
      fun N' h' env' => EnvOk N' h' env' := by
    unfold bindThis
    split
    · exact KeepsR.ok rfl hok he
    · rename_i har
      simp only [Bool.not_eq_true] at har
      subst har
      exact keeps_bindCell hok he _ _ hf.this
  refine KeepsR.bind hthis fun env1 st1 N1 _ hok1 _ he1 => ?_
  rw [run_bind']
  refine KeepsR.bind (keeps_bindParams ps args hok1 he1 fun p hp => hf.param hp)
    fun env2 st2 N2 _ hok2 _ he2 => ?_
  rw [run_bind']
  refine KeepsR.bind (keeps_hoistVars _ _ hok2 he2 fun b hb =>
    hf.body _ _ (varDeclsList_mem body _ _ hb)) fun env3 st3 N3 _ hok3 _ he3 => ?_
  exact keeps_instantiate W hok3 he3 hf.body

theorem keeps_initBinding {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) (k : DeclKind) (x : Name) {τ : Ty} (hτ : T x τ)
    (v : Option Value) :
    KeepsR T N st.heap ((initBinding env k x τ v).run st) fun N' h' env' => EnvOk N' h' env' := by
  unfold initBinding
  split
  · rename_i l hl
    obtain ⟨hn, hb⟩ := he.lookup hl
    rw [run_bind']
    change KeepsR T N st.heap (Res.bind (.ok (st, st)) _) _
    rw [Res.bind_ok]
    split
    · obtain ⟨hok', hx⟩ := store_cell_ok hok hb (v.getD .undef) (hn ▸ hτ)
      exact ⟨N, hok', hx, he.ext hx⟩
    · obtain ⟨hok', hx⟩ := store_cell_ok hok hb (v.getD .undef) (hn ▸ hτ)
      exact ⟨N, hok', hx, he.ext hx⟩
    · rename_i old τ' hget
      have hτ' : T (N l) τ' := hok.bind l τ' (by simp [Heap.bindTy, hget])
      obtain ⟨hok', hx⟩ := store_cell_ok hok hb (v.getD old) hτ'
      exact ⟨N, hok', hx, he.ext hx⟩
    · exact keeps_bindCell hok he x _ hτ
  · exact keeps_bindCell hok he x _ hτ

theorem keeps_copyBindings : ∀ (names : List Name) {N : Naming} {st : St} {env : Env},
    HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((copyBindings env names).run st) fun N' h' env' => EnvOk N' h' env'
  | [], _, _, _, hok, he => KeepsR.ok rfl hok he
  | x :: xs, N, st, env, hok, he => by
    simp only [copyBindings]
    split
    · rename_i l hl
      obtain ⟨hn, _⟩ := he.lookup hl
      rw [run_bind', run_load]
      cases hget : st.heap.get l with
      | none => trivial
      | some o =>
        simp only [Res.bind_ok]
        split
        · rename_i v τ
          have hτ : T x τ := hn ▸ hok.bind l τ (by simp [Heap.bindTy, hget])
          rw [run_bind', run_tick1, Res.bind_ok, run_bind']
          exact KeepsR.bind (keeps_bindCell (st := st.tick) hok he x v hτ)
            fun env' st1 N1 _ hok1 _ he1 => keeps_copyBindings xs hok1 he1
        · trivial
        · trivial
    · exact keeps_copyBindings xs hok he

theorem keeps_makeMethods (W : World) {env : Env} : ∀ (ms : List (Name × Func)) {N : Naming}
    {st : St}, HeapOk T N st.heap → EnvOk N st.heap env → (∀ m ∈ ms, FuncOk T m.2) →
    KeepsR T N st.heap ((makeMethods W env ms).run st) fun _ _ _ => True
  | [], _, _, hok, _, _ => KeepsR.ok rfl hok trivial
  | (x, f) :: ms, N, st, hok, he, hms => by
    simp only [makeMethods]
    rw [run_bind']
    refine KeepsR.bind ((Data.charge W _).keeps hok) fun _ st1 N1 _ hok1 hx1 _ => ?_
    rw [run_bind']
    refine KeepsR.bind (keeps_allocate hok1 "" (.closure f env)
      ⟨he.ext hx1, hms _ List.mem_cons_self⟩) fun l st2 N2 _ hok2 hx2 _ => ?_
    rw [run_bind']
    refine KeepsR.bind (keeps_makeMethods W ms hok2 ((he.ext hx1).ext hx2)
      fun m hm => hms m (List.mem_cons_of_mem _ hm)) fun ls st3 N3 _ hok3 _ _ => ?_
    exact KeepsR.ok rfl hok3 trivial

theorem keeps_makeClass (W : World) {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env}
    (he : EnvOk N st.heap env) {c : Class} (hc : ClassOk T c) :
    KeepsR T N st.heap ((makeClass W env c).run st) fun _ _ _ => True := by
  obtain ⟨ctor, ms⟩ := c
  simp only [makeClass]
  rw [run_bind']
  refine KeepsR.bind (keeps_makeMethods W ms hok he hc.methods) fun ls st1 N1 _ hok1 hx1 _ => ?_
  rw [run_bind']
  refine KeepsR.bind ((Data.charge W _).keeps hok1) fun _ st2 N2 _ hok2 hx2 _ => ?_
  exact (keeps_allocate hok2 "" (.klass ctor ls [] env)
    ⟨(he.ext hx1).ext hx2, hc.ctor⟩).mono fun _ _ _ _ => trivial

/-! ## Variable access within runs -/

theorem keeps_cellType {N : Naming} {st : St} (hok : HeapOk T N st.heap) (l : Loc) :
    KeepsR T N st.heap ((cellType l).run st) fun _ h τ => h.bindTy l = some τ := by
  cases hc : (cellType l).run st with
  | error => trivial
  | ok r =>
    obtain ⟨τ, st'⟩ := r
    obtain ⟨rfl, hb⟩ := cellType_ok hc
    exact KeepsR.ok rfl hok hb

theorem keeps_readVarTy {N : Naming} {st : St} (hok : HeapOk T N st.heap) (l : Loc) :
    KeepsR T N st.heap ((readVarTy l).run st)
      fun _ h r => h.bindTy l = some r.2 ∧ conforms h r.1 r.2 = true := by
  cases hc : (readVarTy l).run st with
  | error => trivial
  | ok r =>
    obtain ⟨⟨v, τ⟩, st'⟩ := r
    obtain ⟨rfl, hb, hv⟩ := readVarTy_ok hc
    exact KeepsR.ok rfl hok ⟨hb, hv⟩

theorem typed_ext {N N' : Naming} {h h' : Heap} (hok : HeapOk T N h) {l : Loc} {τ : Ty}
    (hb : h.bindTy l = some τ) (hx : Ext N h N' h') : h'.bindTy l ≠ none ∧ T (N' l) τ := by
  have hne : h.bindTy l ≠ none := by rw [hb]; simp
  refine ⟨hx.bind l hne, ?_⟩
  rw [hx.name l (get_ne_none_of_bindTy hne)]
  exact hok.bind l τ hb

theorem keeps_storeCell {N : Naming} {st : St} (hok : HeapOk T N st.heap) {l : Loc}
    (hb : st.heap.bindTy l ≠ none) (v : Value) {τ : Ty} (hτ : T (N l) τ) :
    KeepsR T N st.heap ((store l (.cell v τ)).run st) fun _ _ _ => True := by
  obtain ⟨hok', hx⟩ := store_cell_ok hok hb v hτ
  exact ⟨N, hok', hx, trivial⟩

/-! ## Preservation by induction on fuel -/

/-- Every interpreter function, run with fuel `fuel` from a `T`-typed heap, an environment
satisfying `EnvOk` and syntax whose bindings satisfy `T`, keeps the heap typed, a statement
returning an environment satisfying `EnvOk`. -/
structure Good (W : World) (T : Name → Ty → Prop) (fuel : ℕ) : Prop where
  expr : ∀ env e N st, ExprOk T e → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((evalExpr W fuel env e).run st) fun _ _ _ => True
  args : ∀ env es N st, ExprsOk T es → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((evalArgs W fuel env es).run st) fun _ _ _ => True
  props : ∀ env ps N st, PropsOk T ps → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((evalProps W fuel env ps).run st) fun _ _ _ => True
  callValue : ∀ callee self args N st, HeapOk T N st.heap →
    KeepsR T N st.heap ((callValue W fuel callee self args).run st) fun _ _ _ => True
  construct : ∀ callee args N st, HeapOk T N st.heap →
    KeepsR T N st.heap ((construct W fuel callee args).run st) fun _ _ _ => True
  callFunc : ∀ f env self args N st, FuncOk T f → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((callFunc W fuel f env self args).run st) fun _ _ _ => True
  stmt : ∀ env s N st, StmtOk T s → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((execStmt W fuel env s).run st) fun N' h' r => EnvOk N' h' r.1
  stmts : ∀ env ss N st, StmtsOk T ss → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((execStmts W fuel env ss).run st) fun N' h' r => EnvOk N' h' r.1
  whileLoop : ∀ env c body N st, ExprOk T c → StmtOk T body → HeapOk T N st.heap →
    EnvOk N st.heap env →
    KeepsR T N st.heap ((whileLoop W fuel env c body).run st) fun _ _ _ => True
  forLoop : ∀ env names test update body N st, OptOk T test → OptOk T update →
    StmtOk T body → HeapOk T N st.heap → EnvOk N st.heap env →
    KeepsR T N st.heap ((forLoop W fuel env names test update body).run st) fun _ _ _ => True
  forOfLoop : ∀ env x l i body N st, T x .any → StmtOk T body → HeapOk T N st.heap →
    EnvOk N st.heap env →
    KeepsR T N st.heap ((forOfLoop W fuel env x l i body).run st) fun _ _ _ => True
  forEachValue : ∀ env x vs body N st, T x .any → StmtOk T body → HeapOk T N st.heap →
    EnvOk N st.heap env →
    KeepsR T N st.heap ((forEachValue W fuel env x vs body).run st) fun _ _ _ => True

theorem good_zero (W : World) : Good W T 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (rw [evalExpr]; trivial) | (rw [evalArgs]; trivial) | (rw [evalProps]; trivial)
    | (rw [Olint.Model.callValue]; trivial) | (rw [Olint.Model.construct]; trivial)
    | (rw [Olint.Model.callFunc]; trivial) | (rw [execStmt]; trivial) | (rw [execStmts]; trivial)
    | (rw [Olint.Model.whileLoop]; trivial) | (rw [Olint.Model.forLoop]; trivial)
    | (rw [Olint.Model.forOfLoop]; trivial) | (rw [Olint.Model.forEachValue]; trivial)

/-- Syntax decomposition: the bindings of a part are bindings of the whole. -/
macro "sub_ok" h:term : term => `(fun x τ hm => $h x τ (by
  first
  | (simp [exprBindings, exprsBindings, propsBindings, optBindings, stmtBindings, stmtsBindings,
      optStmtBindings, funcBindings, classBindings, hm]; done)
  | (simp [exprBindings, exprsBindings, propsBindings, optBindings, stmtBindings, stmtsBindings,
      optStmtBindings, funcBindings, classBindings] at hm; done)
  | (simp only [exprBindings, exprsBindings, propsBindings, optBindings, stmtBindings,
      stmtsBindings, optStmtBindings, funcBindings, classBindings, List.mem_append] at hm ⊢
     simp [hm])))

theorem KeepsR.tickThen {β : Type} {N : Naming} {st : St} {body : M β}
    {Q : Naming → Heap → β → Prop} (h : KeepsR T N st.heap (body.run st.tick) Q) :
    KeepsR T N st.heap ((tick >>= fun _ => body).run st) Q := by
  rw [run_bind', run_tick1, Res.bind_ok]
  exact h

theorem KeepsR.bindM {α β : Type} {N : Naming} {st : St} {x : M α} {f : α → M β}
    {Q1 : Naming → Heap → α → Prop} {Q2 : Naming → Heap → β → Prop}
    (hx : KeepsR T N st.heap (x.run st) Q1)
    (hf : ∀ a st' N', HeapOk T N' st'.heap → Ext N st.heap N' st'.heap → Q1 N' st'.heap a →
      KeepsR T N' st'.heap ((f a).run st') Q2) :
    KeepsR T N st.heap ((x >>= f).run st) Q2 := by
  rw [run_bind']
  exact KeepsR.bind hx fun a st' N' _ h1 h2 h3 => hf a st' N' h1 h2 h3

theorem KeepsR.fail {α : Type} {N : Naming} {st : St} {e : Abort}
    {Q : Naming → Heap → α → Prop} : KeepsR T N st.heap ((fail e : M α).run st) Q := trivial

theorem KeepsR.pure {α : Type} {N : Naming} {st : St} {a : α}
    {Q : Naming → Heap → α → Prop} (hok : HeapOk T N st.heap) (hq : Q N st.heap a) :
    KeepsR T N st.heap ((Pure.pure a : M α).run st) Q := KeepsR.ok rfl hok hq

macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.putIndex _ _ _ _)
macro_rules | `(tactic| data_leaf) => `(tactic| exact Data.readVarTy _)
macro_rules | `(tactic| data_leaf) => `(tactic| (dsimp only; done))

variable {W : World}

theorem keeps_expr_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env e N st, ExprOk T e → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((evalExpr W (fuel + 1) env e).run st) fun _ _ _ => True := by
  intro env e N st he hok henv
  cases e with
  | lit l =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.pure (st := st.tick) hok trivial)
  | ident x =>
    simp only [evalExpr]
    exact KeepsR.tickThen (Data.keeps (st := st.tick) (by data_tac) hok)
  | «this» =>
    simp only [evalExpr]
    exact KeepsR.tickThen (Data.keeps (st := st.tick) (by data_tac) hok)
  | unary op a =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.bindM (ih.expr env a N st.tick (sub_ok he) hok henv)
      fun v st1 N1 hok1 _ _ => Data.keeps (Data.unop op v) hok1)
  | binary op a b =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env a N st.tick (sub_ok he) hok henv)
      fun va st1 N1 hok1 hx1 _ => ?_)
    have hb := ih.expr env b N1 st1 (sub_ok he) hok1 (henv.ext hx1)
    split
    all_goals first
      | (split
         · exact hb
         · exact KeepsR.pure hok1 trivial)
      | exact KeepsR.bindM hb fun vb st2 N2 hok2 _ _ => Data.keeps (Data.binop W op va vb) hok2
  | cond c t f =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env c N st.tick (sub_ok he) hok henv)
      fun v st1 N1 hok1 hx1 _ => ?_)
    split
    · exact ih.expr env t N1 st1 (sub_ok he) hok1 (henv.ext hx1)
    · exact ih.expr env f N1 st1 (sub_ok he) hok1 (henv.ext hx1)
  | assign x a =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env a N st.tick (sub_ok he) hok henv)
      fun v st1 N1 hok1 _ _ => ?_)
    split
    · rename_i l _
      exact KeepsR.bindM (keeps_cellType hok1 l) fun τ st2 N2 hok2 _ hb =>
        KeepsR.bindM (keeps_storeCell hok2 (by rw [hb]; simp) v (hok2.bind l τ hb))
          fun _ st3 N3 hok3 _ _ => KeepsR.pure hok3 trivial
    · exact trivial
  | assignIndex o k a =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
      fun vo st1 N1 hok1 hx1 _ => ?_)
    refine KeepsR.bindM (ih.expr env k N1 st1 (sub_ok he) hok1 (henv.ext hx1))
      fun vk st2 N2 hok2 hx2 _ => ?_
    refine KeepsR.bindM (ih.expr env a N2 st2 (sub_ok he) hok2 ((henv.ext hx1).ext hx2))
      fun v st3 N3 hok3 _ _ => ?_
    exact Data.keeps (by data_tac) hok3
  | assignOp op x a =>
    simp only [evalExpr]
    refine KeepsR.tickThen ?_
    split
    · rename_i l _
      refine KeepsR.bindM (keeps_readVarTy (st := st.tick) hok l) fun r st1 N1 hok1 hx1 hr => ?_
      obtain ⟨lv, τ⟩ := r
      obtain ⟨hb, _⟩ := hr
      simp only []
      split
      · refine KeepsR.bindM (ih.expr env a N1 st1 (sub_ok he) hok1 (henv.ext hx1))
          fun rv st2 N2 hok2 hx2 _ => ?_
        split <;>
        · refine KeepsR.bindM (Data.keeps (by data_tac) hok2) fun r st3 N3 hok3 hx3 _ => ?_
          obtain ⟨hb3, hτ3⟩ := typed_ext hok1 hb (hx2.trans hx3)
          exact KeepsR.bindM (keeps_storeCell hok3 hb3 r hτ3) fun _ st4 N4 hok4 _ _ =>
            KeepsR.pure hok4 trivial
      · exact KeepsR.pure hok1 trivial
    · exact trivial
  | assignOpIndex op o k a =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
      fun vo st1 N1 hok1 hx1 _ => ?_)
    refine KeepsR.bindM (ih.expr env k N1 st1 (sub_ok he) hok1 (henv.ext hx1))
      fun vk st2 N2 hok2 hx2 _ => ?_
    refine KeepsR.bindM (Data.keeps (Data.getIndex W vo vk) hok2) fun lv st3 N3 hok3 hx3 _ => ?_
    split
    · refine KeepsR.bindM (ih.expr env a N3 st3 (sub_ok he) hok3
        (((henv.ext hx1).ext hx2).ext hx3)) fun rv st4 N4 hok4 _ _ => ?_
      exact Data.keeps (by data_tac) hok4
    · exact KeepsR.pure hok3 trivial
  | update inc pre x =>
    simp only [evalExpr]
    refine KeepsR.tickThen ?_
    split
    · rename_i l _
      refine KeepsR.bindM (keeps_readVarTy (st := st.tick) hok l) fun r st1 N1 hok1 hx1 hr => ?_
      obtain ⟨v, τ⟩ := r
      obtain ⟨hb, _⟩ := hr
      simp only []
      refine KeepsR.bindM (Data.keeps (Data.toNumeric v) hok1) fun old st2 N2 hok2 hx2 _ => ?_
      obtain ⟨hb2, hτ2⟩ := typed_ext hok1 hb hx2
      exact KeepsR.bindM (keeps_storeCell hok2 hb2 _ hτ2) fun _ st3 N3 hok3 _ _ =>
        KeepsR.pure hok3 trivial
    · exact trivial
  | updateIndex inc pre o k =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
      fun vo st1 N1 hok1 hx1 _ => ?_)
    refine KeepsR.bindM (ih.expr env k N1 st1 (sub_ok he) hok1 (henv.ext hx1))
      fun vk st2 N2 hok2 _ _ => ?_
    exact Data.keeps (by data_tac) hok2
  | member o x =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
      fun v st1 N1 hok1 _ _ => Data.keeps (Data.getProp W v x) hok1)
  | index o k =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
      fun vo st1 N1 hok1 hx1 _ => ?_)
    exact KeepsR.bindM (ih.expr env k N1 st1 (sub_ok he) hok1 (henv.ext hx1))
      fun vk st2 N2 hok2 _ _ => Data.keeps (Data.getIndex W vo vk) hok2
  | call f args =>
    cases f
    case member o x =>
      simp only [evalExpr]
      refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
        fun self st1 N1 hok1 hx1 _ => ?_)
      refine KeepsR.bindM (Data.keeps (Data.getProp W self x) hok1)
        fun callee st2 N2 hok2 hx2 _ => ?_
      exact KeepsR.bindM (ih.args env args N2 st2 (sub_ok he) hok2 ((henv.ext hx1).ext hx2))
        fun vs st3 N3 hok3 _ _ => ih.callValue callee self vs N3 st3 hok3
    case index o k =>
      simp only [evalExpr]
      refine KeepsR.tickThen (KeepsR.bindM (ih.expr env o N st.tick (sub_ok he) hok henv)
        fun self st1 N1 hok1 hx1 _ => ?_)
      refine KeepsR.bindM (ih.expr env k N1 st1 (sub_ok he) hok1 (henv.ext hx1))
        fun vk st2 N2 hok2 hx2 _ => ?_
      refine KeepsR.bindM (Data.keeps (Data.getIndex W self vk) hok2)
        fun callee st3 N3 hok3 hx3 _ => ?_
      exact KeepsR.bindM (ih.args env args N3 st3 (sub_ok he) hok3
        (((henv.ext hx1).ext hx2).ext hx3)) fun vs st4 N4 hok4 _ _ =>
          ih.callValue callee self vs N4 st4 hok4
    all_goals
      simp only [evalExpr]
      refine KeepsR.tickThen (KeepsR.bindM (ih.expr env _ N st.tick (sub_ok he) hok henv)
        fun callee st1 N1 hok1 hx1 _ => ?_)
      exact KeepsR.bindM (ih.args env args N1 st1 (sub_ok he) hok1 (henv.ext hx1))
        fun vs st2 N2 hok2 _ _ => ih.callValue callee .undef vs N2 st2 hok2
  | new f args =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env f N st.tick (sub_ok he) hok henv)
      fun callee st1 N1 hok1 hx1 _ => ?_)
    exact KeepsR.bindM (ih.args env args N1 st1 (sub_ok he) hok1 (henv.ext hx1))
      fun vs st2 N2 hok2 _ _ => ih.construct callee vs N2 st2 hok2
  | func f =>
    simp only [evalExpr]
    refine KeepsR.tickThen (KeepsR.bindM (Data.keeps (st := st.tick) (Data.charge W _) hok)
      fun _ st1 N1 hok1 hx1 _ => ?_)
    exact KeepsR.bindM (keeps_allocate hok1 "" (.closure f env) ⟨henv.ext hx1, sub_ok he⟩)
      fun l st2 N2 hok2 _ _ => KeepsR.pure hok2 trivial
  | klass c =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.bindM (keeps_makeClass W (st := st.tick) hok henv (sub_ok he))
      fun l st1 N1 hok1 _ _ => KeepsR.pure hok1 trivial)
  | array elems =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.bindM (ih.args env elems N st.tick (sub_ok he) hok henv)
      fun vs st1 N1 hok1 _ _ => Data.keeps (by data_tac) hok1)
  | object ps =>
    simp only [evalExpr]
    exact KeepsR.tickThen (KeepsR.bindM (ih.props env ps N st.tick (sub_ok he) hok henv)
      fun vs st1 N1 hok1 _ _ => Data.keeps (by data_tac) hok1)
  | regex pattern flags =>
    simp only [evalExpr]
    exact KeepsR.tickThen (Data.keeps (st := st.tick) (by data_tac) hok)

theorem keeps_load {N : Naming} {st : St} (hok : HeapOk T N st.heap) (l : Loc) :
    KeepsR T N st.heap ((load l).run st) fun _ h o => h.get l = some o := by
  rw [run_load]
  cases hl : st.heap.get l with
  | none => trivial
  | some o => exact KeepsR.ok rfl hok hl

theorem KeepsR.discard {α : Type} {N : Naming} {st : St} {x : M α}
    {Q : Naming → Heap → α → Prop} (h : KeepsR T N st.heap (x.run st) Q) :
    KeepsR T N st.heap ((discard x).run st) fun _ _ _ => True := by
  rw [run_discard]
  revert h
  rcases x.run st with e | ⟨a, st'⟩
  · intro; trivial
  · rintro ⟨N', hok, hx, _⟩
    exact ⟨N', hok, hx, trivial⟩

theorem keeps_args_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env es N st, ExprsOk T es → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((evalArgs W (fuel + 1) env es).run st) fun _ _ _ => True := by
  intro env es N st hes hok henv
  cases es with
  | nil => simp only [evalArgs]; exact KeepsR.pure hok trivial
  | cons e es =>
    simp only [evalArgs]
    exact KeepsR.bindM (ih.expr env e N st (sub_ok hes) hok henv) fun v st1 N1 hok1 hx1 _ =>
      KeepsR.bindM (ih.args env es N1 st1 (sub_ok hes) hok1 (henv.ext hx1))
        fun vs st2 N2 hok2 _ _ => KeepsR.pure hok2 trivial

theorem keeps_props_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env ps N st, PropsOk T ps → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((evalProps W (fuel + 1) env ps).run st) fun _ _ _ => True := by
  intro env ps N st hps hok henv
  match ps with
  | [] => simp only [evalProps]; exact KeepsR.pure hok trivial
  | (x, e) :: ps =>
    simp only [evalProps]
    exact KeepsR.bindM (ih.expr env e N st (sub_ok hps) hok henv) fun v st1 N1 hok1 hx1 _ =>
      KeepsR.bindM (ih.props env ps N1 st1 (sub_ok hps) hok1 (henv.ext hx1))
        fun vs st2 N2 hok2 _ _ => KeepsR.pure hok2 trivial

theorem keeps_callValue_step (hW : StepData W) {fuel : ℕ} (ih : Good W T fuel) :
    ∀ callee self args N st, HeapOk T N st.heap →
      KeepsR T N st.heap ((callValue W (fuel + 1) callee self args).run st)
        fun _ _ _ => True := by
  intro callee self args N st hok
  simp only [Olint.Model.callValue]
  refine KeepsR.tickThen ?_
  split
  · exact Data.keeps (st := st.tick) (Data.runStep hW _ _ _ _) hok
  · rename_i l
    refine KeepsR.bindM (keeps_load (st := st.tick) hok l) fun o st1 N1 hok1 _ hget => ?_
    split
    · rename_i f env
      obtain ⟨he, hf⟩ := hok1.clo l f env hget
      exact ih.callFunc f env self args N1 st1 hf hok1 he
    · exact trivial
  · exact trivial

theorem keeps_construct_step (hW : StepData W) {fuel : ℕ} (ih : Good W T fuel) :
    ∀ callee args N st, HeapOk T N st.heap →
      KeepsR T N st.heap ((construct W (fuel + 1) callee args).run st) fun _ _ _ => True := by
  intro callee args N st hok
  simp only [Olint.Model.construct]
  refine KeepsR.tickThen ?_
  split
  · exact Data.keeps (st := st.tick) (Data.runStep hW _ _ _ _) hok
  · rename_i l
    refine KeepsR.bindM (keeps_load (st := st.tick) hok l) fun o st1 N1 hok1 _ hget => ?_
    split
    · rename_i ctor ms acc env
      obtain ⟨he, hf⟩ := hok1.cls l ctor ms acc env hget
      refine KeepsR.bindM (Data.keeps (Data.newObject W l) hok1) fun l' st2 N2 hok2 hx2 _ => ?_
      try simp only []
      split
      · rename_i f
        exact KeepsR.bindM (ih.callFunc f env _ args N2 st2 (hf f rfl) hok2 (he.ext hx2))
          fun r st3 N3 hok3 _ _ => Data.keeps (by data_tac) hok3
      · exact KeepsR.pure hok2 trivial
    · exact trivial
  · exact trivial

theorem keeps_callFunc_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ f env self args N st, FuncOk T f → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((callFunc W (fuel + 1) f env self args).run st) fun _ _ _ => True := by
  intro f env self args N st hf hok henv
  obtain ⟨ps, body, ar⟩ := f
  simp only [Olint.Model.callFunc]
  exact KeepsR.bindM (keeps_enterFunc W hok henv hf self args) fun env' st1 N1 hok1 _ he1 =>
    KeepsR.bindM (ih.stmts env' body N1 st1 hf.body hok1 he1) fun r st2 N2 hok2 _ _ =>
      Data.keeps (by data_tac) hok2

theorem keeps_stmts_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env ss N st, StmtsOk T ss → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((execStmts W (fuel + 1) env ss).run st)
        fun N' h' r => EnvOk N' h' r.1 := by
  intro env ss N st hss hok henv
  cases ss with
  | nil => simp only [execStmts]; exact KeepsR.pure hok henv
  | cons s ss =>
    simp only [execStmts]
    refine KeepsR.bindM (ih.stmt env s N st (sub_ok hss) hok henv) fun r st1 N1 hok1 _ he1 => ?_
    obtain ⟨env', c⟩ := r
    try simp only []
    split
    · exact ih.stmts env' ss N1 st1 (sub_ok hss) hok1 he1
    · exact KeepsR.pure hok1 he1

theorem keeps_while_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env c body N st, ExprOk T c → StmtOk T body → HeapOk T N st.heap →
      EnvOk N st.heap env →
      KeepsR T N st.heap ((whileLoop W (fuel + 1) env c body).run st) fun _ _ _ => True := by
  intro env c body N st hc hb hok henv
  simp only [Olint.Model.whileLoop]
  refine KeepsR.bindM (ih.expr env c N st hc hok henv) fun v st1 N1 hok1 hx1 _ => ?_
  split
  · refine KeepsR.bindM (ih.stmt env body N1 st1 hb hok1 (henv.ext hx1))
      fun r st2 N2 hok2 hx2 _ => ?_
    try simp only []
    split
    · exact ih.whileLoop env c body N2 st2 hc hb hok2 ((henv.ext hx1).ext hx2)
    · exact Data.keeps (by data_tac) hok2
  · exact KeepsR.pure hok1 trivial

theorem keeps_forLoop_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env names test update body N st, OptOk T test → OptOk T update → StmtOk T body →
      HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((forLoop W (fuel + 1) env names test update body).run st)
        fun _ _ _ => True := by
  intro env names test update body N st ht hu hb hok henv
  simp only [Olint.Model.forLoop]
  split
  on_goal 1 =>
    rename_i t
    refine KeepsR.bindM (ih.expr env t N st (sub_ok ht) hok henv) fun v st0 N0 hok0 hx0 _ => ?_
    refine KeepsR.bindM (KeepsR.pure (Q := fun _ _ _ => True) hok0 trivial)
      fun go st1 N1 hok1 hx1 _ => ?_
    have he1 : EnvOk N1 st1.heap env := (henv.ext hx0).ext hx1
  on_goal 2 =>
    refine KeepsR.bindM (KeepsR.pure (Q := fun _ _ _ => True) hok trivial)
      fun go st1 N1 hok1 hx1 _ => ?_
    have he1 : EnvOk N1 st1.heap env := henv.ext hx1
  all_goals
    split
    · refine KeepsR.bindM (ih.stmt env body N1 st1 hb hok1 he1) fun r st2 N2 hok2 hx2 _ => ?_
      split
      · refine KeepsR.bindM (keeps_copyBindings names hok2 (he1.ext hx2))
          fun env' st3 N3 hok3 _ he3 => ?_
        split
        · rename_i u
          exact KeepsR.bindM (KeepsR.discard (ih.expr env' u N3 st3 (sub_ok hu) hok3 he3))
            fun _ st4 N4 hok4 hx4 _ =>
              ih.forLoop env' names _ _ body N4 st4 ht hu hb hok4 (he3.ext hx4)
        · exact ih.forLoop env' names _ _ body N3 st3 ht hu hb hok3 he3
      · exact Data.keeps (by data_tac) hok2
    · exact KeepsR.pure hok1 trivial

theorem keeps_forOfLoop_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env x l i body N st, T x .any → StmtOk T body → HeapOk T N st.heap →
      EnvOk N st.heap env →
      KeepsR T N st.heap ((forOfLoop W (fuel + 1) env x l i body).run st) fun _ _ _ => True := by
  intro env x l i body N st hx hb hok henv
  simp only [Olint.Model.forOfLoop]
  refine KeepsR.tickThen (KeepsR.bindM (Data.keeps (st := st.tick) (Data.load l) hok)
    fun o st1 N1 hok1 hx1 _ => KeepsR.bindM (Data.keeps (Data.iterStep W o i) hok1)
      fun r st2 N2 hok2 hx2 _ => ?_)
  have he2 : EnvOk N2 st2.heap env := (henv.ext hx1).ext hx2
  split
  · exact KeepsR.pure hok2 trivial
  · exact ih.forOfLoop env x l (i + 1) body N2 st2 hx hb hok2 he2
  · rename_i v
    refine KeepsR.bindM (keeps_bindCell hok2 he2 x v hx) fun env' st3 N3 hok3 hx3 he3 => ?_
    refine KeepsR.bindM (ih.stmt env' body N3 st3 hb hok3 he3) fun r st4 N4 hok4 hx4 _ => ?_
    split
    · exact ih.forOfLoop env x l (i + 1) body N4 st4 hx hb hok4 ((he2.ext hx3).ext hx4)
    · exact Data.keeps (by data_tac) hok4

theorem keeps_forEachValue_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env x vs body N st, T x .any → StmtOk T body → HeapOk T N st.heap →
      EnvOk N st.heap env →
      KeepsR T N st.heap ((forEachValue W (fuel + 1) env x vs body).run st)
        fun _ _ _ => True := by
  intro env x vs body N st hx hb hok henv
  cases vs with
  | nil => simp only [Olint.Model.forEachValue]; exact KeepsR.pure hok trivial
  | cons v vs =>
    simp only [Olint.Model.forEachValue]
    refine KeepsR.bindM (keeps_bindCell hok henv x v hx) fun env' st1 N1 hok1 hx1 he1 => ?_
    refine KeepsR.bindM (ih.stmt env' body N1 st1 hb hok1 he1) fun r st2 N2 hok2 hx2 _ => ?_
    try simp only []
    split
    · exact ih.forEachValue env x vs body N2 st2 hx hb hok2 ((henv.ext hx1).ext hx2)
    · exact Data.keeps (by data_tac) hok2

theorem keeps_stmt_step {fuel : ℕ} (ih : Good W T fuel) :
    ∀ env s N st, StmtOk T s → HeapOk T N st.heap → EnvOk N st.heap env →
      KeepsR T N st.heap ((execStmt W (fuel + 1) env s).run st)
        fun N' h' r => EnvOk N' h' r.1 := by
  intro env s N st hs hok henv
  cases s with
  | expr e =>
    simp only [execStmt]
    exact KeepsR.tickThen (KeepsR.bindM (ih.expr env e N st.tick (sub_ok hs) hok henv)
      fun _ st1 N1 hok1 hx1 _ => KeepsR.pure hok1 (henv.ext hx1))
  | decl k x τ init =>
    have hτ : T x τ := hs x τ (by simp [stmtBindings])
    simp only [execStmt]
    refine KeepsR.tickThen ?_
    split
    · rename_i e
      refine KeepsR.bindM (ih.expr env e N st.tick (sub_ok hs) hok henv)
        fun v st1 N1 hok1 hx1 _ => ?_
      refine KeepsR.bindM (KeepsR.pure (Q := fun _ _ _ => True) hok1 trivial)
        fun ov st2 N2 hok2 hx2 _ => ?_
      exact KeepsR.bindM (keeps_initBinding hok2 ((henv.ext hx1).ext hx2) k x hτ ov)
        fun env' st3 N3 hok3 _ he3 => KeepsR.pure hok3 he3
    · refine KeepsR.bindM (KeepsR.pure (st := st.tick) (Q := fun _ _ _ => True) hok trivial)
        fun ov st2 N2 hok2 hx2 _ => ?_
      exact KeepsR.bindM (keeps_initBinding hok2 (henv.ext hx2) k x hτ ov)
        fun env' st3 N3 hok3 _ he3 => KeepsR.pure hok3 he3
  | block ss =>
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (keeps_instantiate W (st := st.tick) hok henv
      (sub_ok hs)) fun env' st1 N1 hok1 hx1 he1 => ?_)
    exact KeepsR.bindM (ih.stmts env' ss N1 st1 (sub_ok hs) hok1 he1)
      fun _ st2 N2 hok2 hx2 _ => KeepsR.pure hok2 ((henv.ext hx1).ext hx2)
  | ite c t f =>
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env c N st.tick (sub_ok hs) hok henv)
      fun v st1 N1 hok1 hx1 _ => ?_)
    have he1 := henv.ext hx1
    split
    · exact KeepsR.bindM (ih.stmt env t N1 st1 (sub_ok hs) hok1 he1)
        fun _ st2 N2 hok2 hx2 _ => KeepsR.pure hok2 (he1.ext hx2)
    · split
      · rename_i g
        exact KeepsR.bindM (ih.stmt env g N1 st1 (sub_ok hs) hok1 he1)
          fun _ st2 N2 hok2 hx2 _ => KeepsR.pure hok2 (he1.ext hx2)
      · exact KeepsR.pure hok1 he1
  | forLoop init test update body =>
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (keeps_bindUninit (st := st.tick) _ hok henv
      fun b hb => hs _ _ (by simp [stmtBindings, forScope_mem init b.1 b.2 hb]))
      fun env1 st1 N1 hok1 hx1 he1 => ?_)
    split
    · rename_i i
      refine KeepsR.bindM (ih.stmt env1 i N1 st1 (sub_ok hs) hok1 he1)
        fun r st2 N2 hok2 hx2 he2 => ?_
      refine KeepsR.bindM (KeepsR.pure (Q := fun N h e => EnvOk N h e) hok2 he2)
        fun env2 st3 N3 hok3 hx3 he3 => ?_
      refine KeepsR.bindM (keeps_copyBindings _ hok3 he3) fun env3 st4 N4 hok4 hx4 he4 => ?_
      exact KeepsR.bindM (ih.forLoop env3 _ test update body N4 st4 (sub_ok hs) (sub_ok hs)
        (sub_ok hs) hok4 he4) fun _ st5 N5 hok5 hx5 _ =>
          KeepsR.pure hok5 (henv.ext (hx1.trans (hx2.trans (hx3.trans (hx4.trans hx5)))))
    · refine KeepsR.bindM (KeepsR.pure (Q := fun N h e => EnvOk N h e) hok1 he1)
        fun env2 st3 N3 hok3 hx3 he3 => ?_
      refine KeepsR.bindM (keeps_copyBindings _ hok3 he3) fun env3 st4 N4 hok4 hx4 he4 => ?_
      exact KeepsR.bindM (ih.forLoop env3 _ test update body N4 st4 (sub_ok hs) (sub_ok hs)
        (sub_ok hs) hok4 he4) fun _ st5 N5 hok5 hx5 _ =>
          KeepsR.pure hok5 (henv.ext (hx1.trans (hx3.trans (hx4.trans hx5))))
  | forOf x e body =>
    have hx : T x .any := hs x .any (by simp [stmtBindings])
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env e N st.tick (sub_ok hs) hok henv)
      fun v st1 N1 hok1 hx1 _ => ?_)
    have he1 := henv.ext hx1
    split
    · rename_i l
      exact KeepsR.bindM (ih.forOfLoop env x l 0 body N1 st1 hx (sub_ok hs) hok1 he1)
        fun _ st2 N2 hok2 hx2 _ => KeepsR.pure hok2 (he1.ext hx2)
    · exact trivial
  | forIn x e body =>
    have hx : T x .any := hs x .any (by simp [stmtBindings])
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (ih.expr env e N st.tick (sub_ok hs) hok henv)
      fun v st1 N1 hok1 hx1 _ => ?_)
    have he1 := henv.ext hx1
    split
    · rename_i l
      split
      · exact trivial
      · rename_i w _
        refine KeepsR.bindM (Data.keeps (Data.tick w) hok1) fun _ st2 N2 hok2 hx2 _ => ?_
        refine KeepsR.bindM (Data.keeps (Data.forInKeys W l) hok2) fun keys st3 N3 hok3 hx3 _ => ?_
        have he3 := (he1.ext hx2).ext hx3
        exact KeepsR.bindM (ih.forEachValue env x keys body N3 st3 hx (sub_ok hs) hok3 he3)
          fun _ st4 N4 hok4 hx4 _ => KeepsR.pure hok4 (he3.ext hx4)
    · exact KeepsR.pure hok1 he1
    · exact KeepsR.pure hok1 he1
    · exact trivial
  | «while» c body =>
    simp only [execStmt]
    exact KeepsR.tickThen (KeepsR.bindM (ih.whileLoop env c body N st.tick (sub_ok hs)
      (sub_ok hs) hok henv) fun _ st1 N1 hok1 hx1 _ => KeepsR.pure hok1 (henv.ext hx1))
  | doWhile body c =>
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (ih.stmt env body N st.tick (sub_ok hs) hok henv)
      fun r st1 N1 hok1 hx1 _ => ?_)
    have he1 := henv.ext hx1
    try simp only []
    split
    · exact KeepsR.bindM (ih.whileLoop env c body N1 st1 (sub_ok hs) (sub_ok hs) hok1 he1)
        fun _ st2 N2 hok2 hx2 _ => KeepsR.pure hok2 (he1.ext hx2)
    · split
      · exact KeepsR.pure hok1 he1
      · exact KeepsR.pure hok1 he1
  | ret e =>
    simp only [execStmt]
    refine KeepsR.tickThen ?_
    split
    · rename_i x
      exact KeepsR.bindM (ih.expr env x N st.tick (sub_ok hs) hok henv)
        fun _ st1 N1 hok1 hx1 _ => KeepsR.pure hok1 (henv.ext hx1)
    · exact KeepsR.pure (st := st.tick) hok henv
  | brk =>
    simp only [execStmt]
    exact KeepsR.tickThen (KeepsR.pure (st := st.tick) hok henv)
  | cont =>
    simp only [execStmt]
    exact KeepsR.tickThen (KeepsR.pure (st := st.tick) hok henv)
  | funDecl x f =>
    have hx : T x .any := hs x .any (by simp [stmtBindings])
    simp only [execStmt]
    refine KeepsR.tickThen ?_
    split
    · exact KeepsR.pure (st := st.tick) hok henv
    · refine KeepsR.bindM (keeps_bindFuns W (st := st.tick) hok henv [(x, f)] fun d hd => ?_)
        fun env' st1 N1 hok1 _ he1 => KeepsR.pure hok1 he1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨hx, sub_ok hs⟩
  | classDecl x c =>
    have hx : T x .any := hs x .any (by simp [stmtBindings])
    simp only [execStmt]
    refine KeepsR.tickThen (KeepsR.bindM (keeps_makeClass W (st := st.tick) hok henv (sub_ok hs))
      fun l st1 N1 hok1 hx1 _ => ?_)
    exact KeepsR.bindM (keeps_initBinding hok1 (henv.ext hx1) .«let» x hx _)
      fun env' st2 N2 hok2 _ he2 => KeepsR.pure hok2 he2

theorem good_succ (hW : StepData W) {fuel : ℕ} (ih : Good W T fuel) : Good W T (fuel + 1) :=
  ⟨keeps_expr_step ih, keeps_args_step ih, keeps_props_step ih, keeps_callValue_step hW ih,
    keeps_construct_step hW ih, keeps_callFunc_step ih, keeps_stmt_step ih, keeps_stmts_step ih,
    keeps_while_step ih, keeps_forLoop_step ih, keeps_forOfLoop_step ih,
    keeps_forEachValue_step ih⟩

/-- Every run of every interpreter function keeps a typed heap typed, given that the built-in
steps change only data objects. -/
theorem keeps_all (hW : StepData W) : ∀ fuel, Good W T fuel
  | 0 => good_zero W
  | fuel + 1 => good_succ hW (keeps_all hW fuel)

/-! ## The invariant on configurations -/

/-- A frame's environment satisfies `EnvOk` and the bindings its syntax creates satisfy `T`. -/
@[reducible] def FrameOk (T : Name → Ty → Prop) (N : Naming) (h : Heap) : Frame → Prop
  | .expr env e => EnvOk N h env ∧ ExprOk T e
  | .stmt env s => EnvOk N h env ∧ StmtOk T s
  | .stmts env ss => EnvOk N h env ∧ StmtsOk T ss
  | .args env es => EnvOk N h env ∧ ExprsOk T es
  | .props env ps => EnvOk N h env ∧ PropsOk T ps
  | .callValue _ _ _ | .construct _ _ => True
  | .callFunc f env _ _ => EnvOk N h env ∧ FuncOk T f
  | .whileLoop env c body => EnvOk N h env ∧ ExprOk T c ∧ StmtOk T body
  | .forLoop env _ test update body =>
    EnvOk N h env ∧ OptOk T test ∧ OptOk T update ∧ StmtOk T body
  | .forOfLoop env x _ _ body | .forEachValue env x _ body =>
    EnvOk N h env ∧ T x .any ∧ StmtOk T body

/-- A statement's outcome returns an environment satisfying `EnvOk`. -/
@[reducible] def OutOk (N : Naming) (h : Heap) : Outcome → Prop
  | .stmt env _ => EnvOk N h env
  | _ => True

/-- The declared-type invariant on a configuration: its heap is `T`-typed under some naming,
under which its frame satisfies `FrameOk`. -/
def Inv (T : Name → Ty → Prop) (c : Cfg) : Prop :=
  ∃ N, HeapOk T N c.st.heap ∧ FrameOk T N c.st.heap c.frame

theorem frame_keeps (hW : StepData W) (fuel : ℕ) : ∀ (fr : Frame) (N : Naming) (st : St),
    HeapOk T N st.heap → FrameOk T N st.heap fr →
    KeepsR T N st.heap ((fr.run W fuel).run st) fun N' h' o => OutOk N' h' o := by
  have g := keeps_all (T := T) hW fuel
  intro fr N st hok hf
  cases fr with
  | expr env e =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.expr env e N st hf.2 hok hf.1).mono fun _ _ _ _ => trivial)
  | stmt env s =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.stmt env s N st hf.2 hok hf.1).mono fun _ _ _ h => h)
  | stmts env ss =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.stmts env ss N st hf.2 hok hf.1).mono fun _ _ _ h => h)
  | args env es =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.args env es N st hf.2 hok hf.1).mono fun _ _ _ _ => trivial)
  | props env ps =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.props env ps N st hf.2 hok hf.1).mono fun _ _ _ _ => trivial)
  | callValue callee self args =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.callValue callee self args N st hok).mono fun _ _ _ _ => trivial)
  | construct callee args =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.construct callee args N st hok).mono fun _ _ _ _ => trivial)
  | callFunc f env self args =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.callFunc f env self args N st hf.2 hok hf.1).mono
      fun _ _ _ _ => trivial)
  | whileLoop env c body =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.whileLoop env c body N st hf.2.1 hf.2.2 hok hf.1).mono
      fun _ _ _ _ => trivial)
  | forLoop env names test update body =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.forLoop env names test update body N st hf.2.1 hf.2.2.1 hf.2.2.2 hok
      hf.1).mono fun _ _ _ _ => trivial)
  | forOfLoop env x l i body =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.forOfLoop env x l i body N st hf.2.1 hf.2.2 hok hf.1).mono
      fun _ _ _ _ => trivial)
  | forEachValue env x vs body =>
    simp only [Frame.run]; rw [run_map']
    exact KeepsR.map ((g.forEachValue env x vs body N st hf.2.1 hf.2.2 hok hf.1).mono
      fun _ _ _ _ => trivial)

/-- A completed run of a computation that keeps typed heaps typed ends in a typed heap. -/
theorem KeepsR.out {α : Type} {N : Naming} {st st' : St} {x : M α} {a : α}
    {Q : Naming → Heap → α → Prop} (hx : KeepsR T N st.heap (x.run st) Q)
    (h : Out x st a st') :
    ∃ N', HeapOk T N' st'.heap ∧ Ext N st.heap N' st'.heap ∧ Q N' st'.heap a := by
  unfold Out at h
  rw [h] at hx
  exact hx

/-- A completed run of a frame satisfying `FrameOk` from a typed heap ends in a typed heap. -/
theorem ev_keeps (hW : StepData W) {fr : Frame} {st st' : St} {o : Outcome} {N : Naming}
    (hev : Ev W fr st o st') (hok : HeapOk T N st.heap) (hf : FrameOk T N st.heap fr) :
    ∃ N', HeapOk T N' st'.heap ∧ Ext N st.heap N' st'.heap ∧ OutOk N' st'.heap o := by
  obtain ⟨fuel, hr⟩ := hev
  have := frame_keeps hW fuel fr N st hok hf
  unfold Cfg.Runs at hr
  rw [hr] at this
  exact this

theorem forGo_keeps (hW : StepData W) {env : Env} {test : Option Expr} {st st1 : St} {N : Naming}
    (hg : ForGo W env test st st1) (hok : HeapOk T N st.heap) (he : EnvOk N st.heap env)
    (ht : OptOk T test) : ∃ N', HeapOk T N' st1.heap ∧ Ext N st.heap N' st1.heap := by
  rcases hg with ⟨_, rfl⟩ | ⟨t, v, rfl, hev, _⟩
  · exact ⟨N, hok, Ext.refl N _⟩
  · obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨he, sub_ok ht⟩
    exact ⟨N1, hok1, hx1⟩

/-- Every call a configuration satisfying the invariant makes satisfies it. -/
theorem Inv.sub (hW : StepData W) {c c' : Cfg} (h : Sub W c c') (hi : Inv T c) : Inv T c' := by
  obtain ⟨N, hok, hf⟩ := hi
  cases h with
  | unary => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | binaryL => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | binaryR hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | condTest => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | condThen hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | condElse hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | assign => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | assignIndexO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | assignIndexK hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | assignIndexA hev1 hev2 =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    exact ⟨N2, hok2, (hf.1.ext hx1).ext hx2, sub_ok hf.2⟩
  | assignOp => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | assignOpIndexO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | assignOpIndexK hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | assignOpIndexA hev1 hev2 hout _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    obtain ⟨N3, hok3, hx3, _⟩ := (Data.keeps (Data.getIndex W _ _) hok2).out hout
    exact ⟨N3, hok3, ((hf.1.ext hx1).ext hx2).ext hx3, sub_ok hf.2⟩
  | updateIndexO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | updateIndexK hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | memberO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | indexO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | indexK hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | callMemberO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | callMemberArgs hev hout =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := (Data.keeps (Data.getProp W _ _) hok1).out hout
    exact ⟨N2, hok2, (hf.1.ext hx1).ext hx2, sub_ok hf.2⟩
  | callMemberCall hev hout hev2 =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := (Data.keeps (Data.getProp W _ _) hok1).out hout
    obtain ⟨N3, hok3, _, _⟩ := ev_keeps hW hev2 hok2 ⟨(hf.1.ext hx1).ext hx2, sub_ok hf.2⟩
    exact ⟨N3, hok3, trivial⟩
  | callIndexO => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | callIndexK hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | callIndexArgs hev1 hev2 hout =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    obtain ⟨N3, hok3, hx3, _⟩ := (Data.keeps (Data.getIndex W _ _) hok2).out hout
    exact ⟨N3, hok3, ((hf.1.ext hx1).ext hx2).ext hx3, sub_ok hf.2⟩
  | callIndexCall hev1 hev2 hout hev3 =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    obtain ⟨N3, hok3, hx3, _⟩ := (Data.keeps (Data.getIndex W _ _) hok2).out hout
    obtain ⟨N4, hok4, _, _⟩ := ev_keeps hW hev3 hok3
      ⟨((hf.1.ext hx1).ext hx2).ext hx3, sub_ok hf.2⟩
    exact ⟨N4, hok4, trivial⟩
  | callF => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | callArgs _ _ hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | callCall _ _ hev1 hev2 =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, _, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    exact ⟨N2, hok2, trivial⟩
  | newF => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | newArgs hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | newConstruct hev1 hev2 =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, _, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, sub_ok hf.2⟩
    exact ⟨N2, hok2, trivial⟩
  | arrayElems => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | objectProps => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | argsHead => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | argsTail hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | propsHead => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | propsTail hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | @callValue l self args st f env hget =>
    exact ⟨N, hok, hok.clo l f env hget⟩
  | @construct l args st f ms acc env l' st1 hget hout =>
    obtain ⟨he, hfn⟩ := hok.cls l (some f) ms acc env hget
    obtain ⟨N1, hok1, hx1, _⟩ := (Data.keeps (st := st.tick) (Data.newObject W l) hok).out hout
    exact ⟨N1, hok1, he.ext hx1, hfn f rfl⟩
  | callFunc hout =>
    obtain ⟨N1, hok1, _, he1⟩ := (keeps_enterFunc W hok hf.1 hf.2 _ _).out hout
    exact ⟨N1, hok1, he1, hf.2.body⟩
  | exprStmt => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | declInit => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | @block env ss st env' st1 hout =>
    obtain ⟨N1, hok1, _, he1⟩ :=
      (keeps_instantiate W (st := st.tick) (ss := ss) hok hf.1 (sub_ok hf.2)).out hout
    exact ⟨N1, hok1, he1, sub_ok hf.2⟩
  | iteTest => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | iteThen hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | iteElse hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2⟩
  | @forInit env i test update body st env1 st1 hout =>
    obtain ⟨N1, hok1, _, he1⟩ := (keeps_bindUninit (st := st.tick) _ hok hf.1
      fun b hb => hf.2 _ _ (by simp [stmtBindings, forScope_mem _ b.1 b.2 hb])).out hout
    exact ⟨N1, hok1, he1, sub_ok hf.2⟩
  | @forStart env i test update body st env1 st1 env2 c st2 env3 st3 hout1 hev hout2 =>
    obtain ⟨N1, hok1, _, he1⟩ := (keeps_bindUninit (st := st.tick) _ hok hf.1
      fun b hb => hf.2 _ _ (by simp [stmtBindings, forScope_mem _ b.1 b.2 hb])).out hout1
    obtain ⟨N2, hok2, _, he2⟩ := ev_keeps hW hev hok1 ⟨he1, sub_ok hf.2⟩
    obtain ⟨N3, hok3, _, he3⟩ := (keeps_copyBindings _ hok2 he2).out hout2
    exact ⟨N3, hok3, he3, sub_ok hf.2, sub_ok hf.2, sub_ok hf.2⟩
  | forStartBare => exact ⟨N, hok, hf.1, sub_ok hf.2, sub_ok hf.2, sub_ok hf.2⟩
  | forOfExpr => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | forOfStart hev =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, hf.2 _ _ (by simp [stmtBindings]), sub_ok hf.2⟩
  | forInExpr => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | @forInStart env x e body st l st1 w keys st2 hev _ hout =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    obtain ⟨N2, hok2, hx2, _⟩ :=
      (Data.keeps (st := { st1 with work := st1.work + w }) (Data.forInKeys W l) hok1).out hout
    exact ⟨N2, hok2, (hf.1.ext hx1).ext hx2, hf.2 _ _ (by simp [stmtBindings]), sub_ok hf.2⟩
  | whileStart => exact ⟨N, hok, hf.1, sub_ok hf.2, sub_ok hf.2⟩
  | doBody => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | doLoop hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, hf.1.ext hx1, sub_ok hf.2, sub_ok hf.2⟩
  | retExpr => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | stmtsHead => exact ⟨N, hok, hf.1, sub_ok hf.2⟩
  | stmtsTail hev =>
    obtain ⟨N1, hok1, _, he1⟩ := ev_keeps hW hev hok ⟨hf.1, sub_ok hf.2⟩
    exact ⟨N1, hok1, he1, sub_ok hf.2⟩
  | whileTest => exact ⟨N, hok, hf.1, hf.2.1⟩
  | whileBody hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev hok ⟨hf.1, hf.2.1⟩
    exact ⟨N1, hok1, hf.1.ext hx1, hf.2.2⟩
  | whileNext hev1 _ hev2 _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := ev_keeps hW hev1 hok ⟨hf.1, hf.2.1⟩
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev2 hok1 ⟨hf.1.ext hx1, hf.2.2⟩
    exact ⟨N2, hok2, (hf.1.ext hx1).ext hx2, hf.2.1, hf.2.2⟩
  | forTest => exact ⟨N, hok, hf.1, sub_ok hf.2.1⟩
  | forBody hg =>
    obtain ⟨N1, hok1, hx1⟩ := forGo_keeps hW hg hok hf.1 hf.2.1
    exact ⟨N1, hok1, hf.1.ext hx1, hf.2.2.2⟩
  | forUpdate hg hev _ hout =>
    obtain ⟨N1, hok1, hx1⟩ := forGo_keeps hW hg hok hf.1 hf.2.1
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev hok1 ⟨hf.1.ext hx1, hf.2.2.2⟩
    obtain ⟨N3, hok3, _, he3⟩ := (keeps_copyBindings _ hok2 ((hf.1.ext hx1).ext hx2)).out hout
    exact ⟨N3, hok3, he3, sub_ok hf.2.2.1⟩
  | forNext hg hev _ hout hu =>
    obtain ⟨N1, hok1, hx1⟩ := forGo_keeps hW hg hok hf.1 hf.2.1
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev hok1 ⟨hf.1.ext hx1, hf.2.2.2⟩
    obtain ⟨N3, hok3, _, he3⟩ := (keeps_copyBindings _ hok2 ((hf.1.ext hx1).ext hx2)).out hout
    rcases hu with ⟨_, rfl⟩ | ⟨u, v, hu, hev2⟩
    · exact ⟨N3, hok3, he3, hf.2⟩
    · subst hu
      obtain ⟨N4, hok4, hx4, _⟩ := ev_keeps hW hev2 hok3 ⟨he3, sub_ok hf.2.2.1⟩
      exact ⟨N4, hok4, he3.ext hx4, hf.2⟩
  | @forOfSkip env x l i body st st1 hout =>
    obtain ⟨N1, hok1, hx1, _⟩ := (Data.keeps (st := st.tick) (Data.bind (Data.load l)
      fun o => Data.iterStep W o i) hok).out hout
    exact ⟨N1, hok1, hf.1.ext hx1, hf.2⟩
  | @forOfBody env x l i body st v st1 env' st2 hout1 hout2 =>
    obtain ⟨N1, hok1, hx1, _⟩ := (Data.keeps (st := st.tick) (Data.bind (Data.load l)
      fun o => Data.iterStep W o i) hok).out hout1
    obtain ⟨N2, hok2, _, he2⟩ := (keeps_bindCell hok1 (hf.1.ext hx1) x v hf.2.1).out hout2
    exact ⟨N2, hok2, he2, hf.2.2⟩
  | @forOfNext env x l i body st v st1 env' st2 env'' c' st3 hout1 hout2 hev _ =>
    obtain ⟨N1, hok1, hx1, _⟩ := (Data.keeps (st := st.tick) (Data.bind (Data.load l)
      fun o => Data.iterStep W o i) hok).out hout1
    obtain ⟨N2, hok2, hx2, he2⟩ := (keeps_bindCell hok1 (hf.1.ext hx1) x v hf.2.1).out hout2
    obtain ⟨N3, hok3, hx3, _⟩ := ev_keeps hW hev hok2 ⟨he2, hf.2.2⟩
    exact ⟨N3, hok3, ((hf.1.ext hx1).ext hx2).ext hx3, hf.2⟩
  | @eachBody env x v vs body st env' st1 hout =>
    obtain ⟨N1, hok1, _, he1⟩ := (keeps_bindCell hok hf.1 x v hf.2.1).out hout
    exact ⟨N1, hok1, he1, hf.2.2⟩
  | @eachNext env x v vs body st env' st1 env'' c' st2 hout hev _ =>
    obtain ⟨N1, hok1, hx1, he1⟩ := (keeps_bindCell hok hf.1 x v hf.2.1).out hout
    obtain ⟨N2, hok2, hx2, _⟩ := ev_keeps hW hev hok1 ⟨he1, hf.2.2⟩
    exact ⟨N2, hok2, (hf.1.ext hx1).ext hx2, hf.2⟩

/-- Every configuration reached from a configuration satisfying the invariant satisfies it. -/
theorem Inv.reach (hW : StepData W) {c c' : Cfg} (h : Relation.ReflTransGen (Sub W) c c')
    (hi : Inv T c) : Inv T c' := by
  induction h with
  | refl => exact hi
  | tail _ hs ih => exact Inv.sub hW hs ih

/-! ## The root configuration -/

/-- The state a `for … in` step continues or stops with. -/
def stepVal {β : Type} : ForInStep β → β
  | .done b | .yield b => b

theorem keeps_forIn {α β : Type} (P : Naming → Heap → β → Prop)
    (f : α → β → M (ForInStep β)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b N (st : St), HeapOk T N st.heap → P N st.heap b →
      KeepsR T N st.heap ((f a b).run st) fun N' h' r => P N' h' (stepVal r)) →
    ∀ init N (st : St), HeapOk T N st.heap → P N st.heap init →
      KeepsR T N st.heap ((forIn l init f).run st) P
  | [], _, init, N, st, hok, hp => KeepsR.pure hok hp
  | a :: l, hf, init, N, st, hok, hp => by
    rw [List.forIn_cons]
    refine KeepsR.bindM (hf a List.mem_cons_self init N st hok hp) fun r st1 N1 hok1 _ hp1 => ?_
    cases r with
    | done b => exact KeepsR.pure hok1 hp1
    | yield b =>
      exact keeps_forIn P f l (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b N1 st1 hok1 hp1

theorem keeps_bindProgram (p : Program) (hdefs : ∀ d ∈ p.defs, T d.1 .any ∧ FuncOk T d.2)
    {N : Naming} {st : St} (hok : HeapOk T N st.heap) {env : Env} (he : EnvOk N st.heap env) :
    KeepsR T N st.heap ((bindProgram p env).run st) fun N' h' env' => EnvOk N' h' env' := by
  unfold bindProgram
  refine KeepsR.bindM (keeps_forIn (fun N h env => EnvOk N h env) _ p.defs ?_ env N st hok he)
    fun env1 st1 N1 hok1 _ he1 => ?_
  · intro d hd b N0 st0 hok0 hb
    obtain ⟨x, fn⟩ := d
    exact KeepsR.bindM (keeps_bindCell hok0 hb x .undef (hdefs _ hd).1)
      fun env' st' N' hok' _ he' => KeepsR.pure hok' he'
  · refine KeepsR.bindM (keeps_forIn (fun N h _ => EnvOk N h env1) _ p.defs ?_ _ N1 st1 hok1 he1)
      fun _ st2 N2 hok2 _ he2 => KeepsR.pure hok2 he2
    intro d hd b N0 st0 hok0 hb
    obtain ⟨x, fn⟩ := d
    obtain ⟨hx, hfn⟩ := hdefs _ hd
    simp only []
    split
    · rename_i l hl
      refine KeepsR.bindM (keeps_allocate hok0 "" (.closure fn env1) ⟨hb, hfn⟩)
        fun c st3 N3 hok3 hx3 _ => ?_
      obtain ⟨hn, hbl⟩ := (hb.ext hx3).lookup hl
      exact KeepsR.bindM (keeps_storeCell hok3 hbl _ (τ := .any) (hn ▸ hx))
        fun _ st4 N4 hok4 hx4 _ => KeepsR.pure hok4 ((hb.ext hx3).ext hx4)
    · exact KeepsR.pure hok0 hb

/-- The root configuration satisfies the invariant when the entry function and the program's
definitions create bindings satisfying `T`, the definitions' names admit `any`, and the
instance's heap and environment are `T`-typed under some naming. -/
theorem Inv.root (p : Program) (e : Entry) (i : Instance) (hfn : FuncOk T e.fn)
    (hdefs : ∀ d ∈ p.defs, T d.1 .any ∧ FuncOk T d.2)
    (hinst : ∃ N, HeapOk T N i.heap ∧ EnvOk N i.heap i.env) : Inv T (root p e i) := by
  obtain ⟨N, hok, he⟩ := hinst
  unfold Olint.Model.root
  have hk := keeps_bindProgram (st := ⟨i.heap, 0⟩) p hdefs hok he
  revert hk
  rcases (bindProgram p i.env).run ⟨i.heap, 0⟩ with _ | ⟨env, st⟩
  · intro
    exact ⟨N, hok, he, hfn⟩
  · rintro ⟨N', hok', _, he'⟩
    exact ⟨N', hok', he', hfn⟩

/-- Every configuration an entry's run reaches satisfies the invariant, under the hypotheses of
`Inv.root` and `StepData W`. -/
theorem Inv.reached (hW : StepData W) {p : Program} {e : Entry} {i : Instance}
    (hfn : FuncOk T e.fn) (hdefs : ∀ d ∈ p.defs, T d.1 .any ∧ FuncOk T d.2)
    (hinst : ∃ N, HeapOk T N i.heap ∧ EnvOk N i.heap i.env) {c : Cfg} (hr : Reach W p e i c) :
    Inv T c :=
  Inv.reach hW hr (Inv.root p e i hfn hdefs hinst)

/-! ## Consequence: typed variable reads -/

/-- A variable read through a typed environment that completes returns a value conforming to
a type `τ` with `T x τ`. -/
theorem readVarTy_typed {N : Naming} {st st' : St} {env : Env} {x : Name} {l : Loc} {v : Value}
    {τ : Ty} (hok : HeapOk T N st.heap) (he : EnvOk N st.heap env) (hl : env.lookup x = some l)
    (h : (readVarTy l).run st = .ok ((v, τ), st')) :
    st' = st ∧ T x τ ∧ conforms st.heap v τ = true := by
  obtain ⟨rfl, hb, hv⟩ := readVarTy_ok h
  obtain ⟨hn, _⟩ := he.lookup hl
  exact ⟨rfl, hn ▸ hok.bind l τ hb, hv⟩

/-- In a configuration satisfying the invariant, an identifier the environment binds evaluates,
when it completes, to a value conforming to a type `τ` with `T x τ`, without changing the
heap. -/
theorem Inv.ident {env : Env} {x : Name} {st : St} (hi : Inv T ⟨.expr env (.ident x), st⟩)
    {fuel : ℕ} {v : Value} {st' : St}
    (h : (evalExpr W fuel env (.ident x)).run st = .ok (v, st')) :
    env.lookup x = none ∨
      st'.heap = st.heap ∧ ∃ τ, T x τ ∧ conforms st.heap v τ = true := by
  obtain ⟨N, hok, he, _⟩ := hi
  cases fuel with
  | zero => rw [evalExpr_zero] at h; cases h
  | succ fuel =>
    simp only [evalExpr] at h
    rw [run_bind', run_tick1, Res.bind_ok] at h
    split at h
    · rename_i l hl
      right
      unfold readVar at h
      rw [run_bind'] at h
      cases hr : (readVarTy l).run st.tick with
      | error => rw [hr] at h; cases h
      | ok r =>
        obtain ⟨⟨v', τ⟩, st1⟩ := r
        rw [hr, Res.bind_ok] at h
        cases h
        obtain ⟨rfl, hτ, hv⟩ := readVarTy_typed (st := st.tick) hok he hl hr
        exact ⟨rfl, τ, hτ, hv⟩
    · left
      assumption

end Olint.Rules

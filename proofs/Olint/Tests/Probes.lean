import Olint.Certificate

/-!
# Review probes

Regression tests for the Phase 3 review's probes. Each bogus bound the review derived is now
rejected: `check` returns `false` on it, by kernel `decide`, or the bound is refuted outright.
Each semantics probe runs the interpreter by kernel `decide` and gets the ECMAScript result, or
`.unmodelled` where the model stops short of ECMAScript (never a wrong value).
-/

namespace Olint.Tests.Probes

open Olint Olint.Model Filter

/-- A world on the draft step costs whose analysed program modifies no intrinsic. -/
def W0 : World := ⟨SpecOps.draft, fun _ => false⟩

/-- What a run returns: its value, or why it stopped. -/
def ret : Except Abort (Value × St) → Abort ⊕ Value
  | .ok (v, _) => .inr v
  | .error e => .inl e

/-- Evaluate an expression from the empty heap. -/
def evalIn (W : World) (e : Expr) : Abort ⊕ Value :=
  ret ((evalExpr W 50 [] e).run ⟨Heap.empty, 0⟩)

/-- Call a function body with no arguments from the empty heap. -/
def callIn (W : World) (body : List Stmt) : Abort ⊕ Value :=
  ret ((callFunc W 200 (.mk [] body false) [] .undef []).run ⟨Heap.empty, 0⟩)

/-- A Number literal. -/
def n (k : ℕ) : Expr := .lit (.num (Double.ofNat k))

/-! ## Vacuous bounds -/

/-- `while (true) {}` with a dimension over a free variable its empty scope does not hold, as
the encoder used to emit: the review proved `Bound … (.constant 1)` of it because no instance
was admitted. The entry is not well formed now, so no bound holds at it. -/
def loopEntry : Entry := ⟨.mk [] [.«while» (.lit (.bool true)) (.block [])] false, [], [(0, .var "xs")]⟩

example : loopEntry.wf ⟨[]⟩ = false := by decide

theorem vacuous_bound_refuted (W : World) : ¬ Bound W ⟨[]⟩ ⟨loopEntry, .entry⟩ (.constant 1) :=
  fun h => absurd h.1 (by decide)

/-- A certificate that checks at `function f(xs: number[]) { 1; }` over `|xs|`. -/
def unitCert : Cert := .maxNormalise (.seqMax [.seqUnit]) (.constant 1)

/-- The body `1;` under the given parameters and dimensions. -/
def unitEntry (params : List (Name × Ty)) (dims : List (ℕ × Measure)) : Entry :=
  ⟨.mk params [.expr (.lit (.num 1))] false, [], dims⟩

example : check ⟨[]⟩ ⟨unitEntry [("xs", .array .number)] [(0, .arg 0)], .entry⟩ [] unitCert =
    true := by decide

/-- The same certificate is rejected over a free variable outside the (empty) scope, … -/
example : check ⟨[]⟩ ⟨unitEntry [("xs", .array .number)] [(0, .var "xs")], .entry⟩ [] unitCert =
    false := by decide

/-- … over an argument past the parameters, … -/
example : check ⟨[]⟩ ⟨unitEntry [("xs", .array .number)] [(0, .arg 1)], .entry⟩ [] unitCert =
    false := by decide

/-- … over an argument whose declared type has no length, … -/
example : check ⟨[]⟩ ⟨unitEntry [("k", .number)] [(0, .arg 0)], .entry⟩ [] unitCert =
    false := by decide

/-- … with two dimensions under one id, … -/
example : check ⟨[]⟩
    ⟨unitEntry [("xs", .array .number), ("ys", .string)] [(0, .arg 0), (0, .arg 1)], .entry⟩
    [] unitCert = false := by decide

/-- … and with two dimensions measuring one quantity. -/
example : check ⟨[]⟩ ⟨unitEntry [("xs", .array .number)] [(0, .arg 0), (1, .arg 0)], .entry⟩
    [] unitCert = false := by decide

/-- A well-formed entry admits an instance at every valuation (`Admitted.exists`). -/
example : ∃ i, Admitted (unitEntry [("xs", .array .number)] [(0, .arg 0)]) i ∧
    ∀ j, i.dims j = ((0 : ℕ) : ℝ) :=
  Admitted.exists ⟨[]⟩ (unitEntry [("xs", .array .number)] [(0, .arg 0)]) (by decide) fun _ => 0

/-! ## Uniform constants -/

/-- The review's filter excluded every instance with a measured dimension below `2`, so a bound
could fail on all of them. Admission is a principal filter now, and the instance where `|xs|`
is `1` is admitted, so no property of large instances alone holds eventually. -/
theorem small_instances_count :
    ¬ ∀ᶠ i in Admits (unitEntry [("xs", .array .number)] [(0, .arg 0)]), 2 ≤ i.dims 0 := by
  intro h
  obtain ⟨i, hi, hd⟩ := Admitted.exists ⟨[]⟩ (unitEntry [("xs", .array .number)] [(0, .arg 0)])
    (by decide) fun _ => 1
  have h2 := (eventually_principal.1 h) i hi
  rw [hd] at h2
  norm_num at h2

/-! ## Prototype chains -/

/-- `({}).toString` is `%Object.prototype.toString%` in ECMAScript; the model does not run
`%Object.prototype%`'s members, so the read is `.unmodelled`, never `undefined`. -/
example : evalIn W0 (.member (.object []) "toString") = .inl .unmodelled := by decide

/-- `typeof ({}).toString` likewise stops short of `"function"`. -/
example : evalIn W0 (.unary .typeof (.member (.object []) "toString")) = .inl .unmodelled := by
  decide

/-- `typeof function () {}` is `"function"`: a closure implements `[[Call]]` (§13.5.3.1). -/
example : evalIn W0 (.unary .typeof (.func (.mk [] [] false))) = .inr (.str "function") := by
  decide

/-- `typeof class {}` is `"function"`: a class constructor implements `[[Call]]`. -/
example : evalIn W0 (.unary .typeof (.klass (.mk none []))) = .inr (.str "function") := by
  decide

/-- `typeof {}` and `typeof []` stay `"object"`. -/
example : evalIn W0 (.unary .typeof (.object [])) = .inr (.str "object") ∧
    evalIn W0 (.unary .typeof (.array [])) = .inr (.str "object") := by
  decide

/-- `({}).missing` is `undefined`: no object of the chain has it. -/
example : evalIn W0 (.member (.object []) "missing") = .inr .undef := by decide

/-- `new (class { m() { return 7; } })().m()` finds `m` on the class prototype: `7`. -/
example : evalIn W0 (.call (.member (.new (.klass (.mk none
    [("m", .mk [] [.ret (some (n 7))] false)])) []) "m") []) = .inr (.num 7) := by decide

/-- `({ __proto__: null }).x` sets the prototype (§13.2.5.5), which the model does not follow:
`.unmodelled`. -/
example : evalIn W0 (.member (.object [("__proto__", .lit .null)]) "x") = .inl .unmodelled := by
  decide

/-- `[].foo` reads `%Array.prototype%`, whose other members the model does not run. -/
example : evalIn W0 (.member (.array []) "foo") = .inl .unmodelled := by decide

/-! ## Hoisting -/

/-- `var n = 5; var n; return n;` is `5`: the second declaration keeps the hoisted binding. -/
example : callIn W0 [.decl .var "n" .any (some (n 5)), .decl .var "n" .any none,
    .ret (some (.ident "n"))] = .inr (.num 5) := by decide

/-- `return n; var n = 5;` reads the hoisted binding before its declaration: `undefined`. -/
example : callIn W0 [.ret (some (.ident "n")), .decl .var "n" .any (some (n 5))] = .inr .undef := by
  decide

/-- `return g(); function g() { return 3; }` calls the hoisted function: `3`. -/
example : callIn W0 [.ret (some (.call (.ident "g") [])),
    .funDecl "g" (.mk [] [.ret (some (n 3))] false)] = .inr (.num 3) := by decide

/-- `return x; let x = 1;` reads `x` in its temporal dead zone: a ReferenceError. -/
example : callIn W0 [.ret (some (.ident "x")), .decl .«let» "x" .any (some (n 1))] =
    .inl .referenceError := by decide

/-! ## Per-iteration bindings -/

/-- `const xs = [1, 2, 3]; const fs = [];
for (let i = xs.length; i > 0; i = i - 1) { fs.push(() => i); } return fs[0]();` is `3`: each
iteration's closure keeps that iteration's `i` (§14.7.4.4). -/
example : callIn W0 [
    .decl .«const» "xs" .any (some (.array [n 1, n 2, n 3])),
    .decl .«const» "fs" .any (some (.array [])),
    .forLoop (some (.decl .«let» "i" .any (some (.member (.ident "xs") "length"))))
      (some (.binary .gt (.ident "i") (n 0)))
      (some (.assign "i" (.binary .sub (.ident "i") (n 1))))
      (.block [.expr (.call (.member (.ident "fs") "push")
        [.func (.mk [] [.ret (some (.ident "i"))] true)])]),
    .ret (some (.call (.index (.ident "fs") (n 0)) []))] = .inr (.num 3) := by decide +kernel

/-! ## `fromIndex` -/

/-- `[1, 2].indexOf(2)` is `1`. -/
example : evalIn W0 (.call (.member (.array [n 1, n 2]) "indexOf") [n 2]) = .inr (.num 1) := by
  decide

/-- `[1, 2, 1].indexOf(1, 1)` is `2` in ECMAScript; the model does not follow `fromIndex`:
`.unmodelled`. -/
example : evalIn W0 (.call (.member (.array [n 1, n 2, n 1]) "indexOf") [n 1, n 1]) =
    .inl .unmodelled := by decide

/-- `[1, 2].includes(1, 1)` is `false` in ECMAScript; `.unmodelled` in the model. -/
example : evalIn W0 (.call (.member (.array [n 1, n 2]) "includes") [n 1, n 1]) =
    .inl .unmodelled := by decide

/-! ## §2.2 replacement -/

/-- A world whose analysed program replaced the global `Map`. -/
def replacedMap : World := ⟨SpecOps.draft, fun x => x == .globalMap⟩

/-- `new Map()` consults the global `Map`, so in that world the run stops on it. -/
example : evalIn replacedMap (.new (.ident "Map") []) = .inl (.modified .globalMap) := by decide

/-- In a world with no replacement it constructs a Map. -/
example : (match evalIn W0 (.new (.ident "Map") []) with | .inr (.ref _) => true | _ => false) =
    true := by decide

/-- The replacement premise of a certificate theorem excludes that world. -/
example : ¬ NoReplacement replacedMap [.globalMap] := fun h => absurd (h .globalMap (by simp)) (by decide)

/-! ## Structural conformance (§2.5) -/

/-- A heap holding one object at location `0`. -/
def one (o : Obj) : Heap := (Heap.empty.alloc o).2

/-- `{length: number}` admits a String … -/
example : conforms Heap.empty (.str "ab") (.object [("length", .number)]) = true := by decide

/-- … and an Array. -/
example : conforms (one (.array [])) (.ref 0) (.object [("length", .number)]) = true := by decide

/-- `{}` admits a Number and a Boolean, but not `null` or `undefined`. -/
example : conforms Heap.empty (.num 1) (.object []) = true := by decide
example : conforms Heap.empty (.bool true) (.object []) = true := by decide
example : conforms Heap.empty .null (.object []) = false := by decide
example : conforms Heap.empty .undef (.object []) = false := by decide

/-- `Set<number>` admits an ordinary object carrying `Set`'s members. -/
example : conforms (one (.ordinary ((setInterface.map fun x => (x, .undef))) [] none)) (.ref 0)
    (.set .number) = true := by decide

/-- A class getter satisfies a field. -/
example : conforms
    ⟨2, fun l => if l = 0 then some (.klass none [] ["size"] []) else
      if l = 1 then some (.ordinary [] [] (some 0)) else none⟩
    (.ref 1) (.object [("size", .number)]) = true := by decide

/-! ## Draft step costs -/

/-- Evaluating `/ab/g` costs one unit plus the draft RegExp parse cost `2 + 1 + 1`. It rests on
the G52 draft (`W.ops = SpecOps.draft`), so `scripts/axioms.lean` reports it as pending Matt's
signature. -/
theorem regex_literal_work_draft (W : World) (hops : W.ops = SpecOps.draft) :
    ((evalExpr W 1 [] (.regex "ab" "g")).run ⟨Heap.empty, 0⟩).toOption.map (·.2.work) =
      some 5 := by
  obtain ⟨ops, m⟩ := W
  cases hops
  rfl

end Olint.Tests.Probes

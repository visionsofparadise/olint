import Lean

/-!
# Axiom audit (§6.3)

Run from `proofs/` with `lake env lean scripts/axioms.lean` after `lake build` (and after the
corpus generator has written `Olint/Corpus/`, when it has).

It imports every module under `Olint/` and prints the axioms of every theorem those modules
declare, as `#print axioms` does, skipping only the equation lemmas Lean generates for
definitions (`f.eq_1`, `f.eq_def`, `f.eq_unfold`). It fails, so `lean` exits non-zero, when:

* any audited theorem depends on an axiom outside `propext`, `Classical.choice` and
  `Quot.sound`;
* any source file (`Olint.lean`, `Olint/**`, `lakefile.toml`) mentions the kernel-check bypass
  option `debug.skipKernelTC`;
* a generated certificate theorem (`Olint.Corpus.*`, and the `c_…` theorems of
  `Olint.Tests.Certificate`, which follow the generator's shape) states anything but
  `∀ W : World, NoReplacement W xs → Bound W <program> <node> <bound>`, optionally with the
  draft premise `W.ops = SpecOps.draft` before `Bound`.

A theorem whose statement or proof reaches `Olint.Model.SpecOps.draft` rests on the G52 step
cost drafts, which are not yet signed into §2. So does a theorem that reaches a `SpecOps` field
whose type fixes a draft's shape: property lookup, List append, number-to-key conversion, object
creation and function object creation, each a constant, and List membership, a function of the
List's length alone. A theorem stated for every `SpecOps` still rests on those shapes. The audit
lists each such theorem as pending Matt's signature (§2.1), naming what it rests on, and a
certificate resting on a draft does not count as accepted until he signs.
-/

open Lean System

namespace OlintAxioms

/-- The axioms §6.3 admits. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The G52 draft step costs, tracked like an axiom so the audit can report what rests on
them. -/
def draft : Name := `Olint.Model.SpecOps.draft

/-- The `SpecOps` fields whose types fix the shape of a G52 draft, the constant costs and List
membership's cost in the List's length alone, tracked like `draft`: a theorem that reads one
rests on that shape whatever the field's value. -/
def shapes : Array Name := #[`Olint.Model.SpecOps.propertyLookup, `Olint.Model.SpecOps.listAppend,
  `Olint.Model.SpecOps.listContains, `Olint.Model.SpecOps.numberToKey,
  `Olint.Model.SpecOps.objectCreate, `Olint.Model.SpecOps.closureCreate]

/-- Everything tracked as unsigned: the drafts' values and the shapes. -/
def unsigned : Array Name := #[draft] ++ shapes

/-- The `.lean` files under a directory, recursively; none when it does not exist. -/
partial def leanFiles (dir : FilePath) : IO (Array FilePath) := do
  if !(← dir.isDir) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then
      out := out.push e.path
  return out

/-- The module name of a source path relative to `proofs/`. -/
def moduleOf (p : FilePath) : Name :=
  (p.withExtension "").components.foldl
    (fun n c => if c == "." || c.isEmpty then n else Name.str n c) .anonymous

/-- The axioms, and the unsigned drafts, a constant depends on, memoised across constants,
following the same edges as `#print axioms` (`Lean.collectAxioms`): types, values, and an
inductive's constructors. -/
partial def axiomsOf (env : Environment) (c : Name) : StateM (NameMap (Array Name)) (Array Name) := do
  if let some r := (← get).find? c then return r
  modify (·.insert c #[])
  let r ← match env.find? c with
    | some (.axiomInfo _) => pure #[c]
    | some info => do
      let mut deps := info.type.getUsedConstants
      if let some v := info.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
      if let .inductInfo i := info then deps := deps ++ i.ctors.toArray
      let mut acc : Array Name := if unsigned.contains c then #[c] else #[]
      for d in deps do
        for a in ← axiomsOf env d do
          if !acc.contains a then acc := acc.push a
      pure acc
    | none => pure #[]
  modify (·.insert c r)
  return r

/-- An equation lemma Lean generates for a definition: `eq_<n>`, `eq_def` or `eq_unfold`. -/
def isEquationLemma (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "eq_def" || s == "eq_unfold" ||
      (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit)
  | _ => false

/-- `e` is `∀ W : World, NoReplacement W xs → [W.ops = SpecOps.draft →] Bound W p n c` with closed
`xs`, `p`, `n` and `c`. -/
def isCertificateStatement (e : Expr) : Bool :=
  match e with
  | .forallE _ (.const `Olint.Model.World []) (.forallE _ hyp body _) _ =>
    let noReplacement := hyp.isAppOfArity `Olint.Model.NoReplacement 2 &&
      hyp.appFn!.appArg! == .bvar 0 && !hyp.appArg!.hasLooseBVars
    let bound (b : Expr) (w : Nat) : Bool :=
      b.isAppOfArity `Olint.Bound 4 && b.getAppArgs[0]! == .bvar w &&
        (b.getAppArgs.extract 1 4).all (!·.hasLooseBVars)
    let isDraft (d : Expr) : Bool :=
      d.isAppOfArity `Eq 3 && d.appArg!.isConstOf draft &&
        d.appFn!.appArg! == mkApp (.const `Olint.Model.World.ops []) (.bvar 1)
    noReplacement && (bound body 1 || match body with
      | .forallE _ d b _ => isDraft d && bound b 2
      | _ => false)
  | _ => false

/-- A generated certificate theorem: one in `Olint.Corpus`, or a `c_…` theorem of
`Olint.Tests.Certificate`. -/
def isCertificate (m n : Name) : Bool :=
  (`Olint.Corpus).isPrefixOf m ||
    (m == `Olint.Tests.Certificate && match n with
      | .str _ s => s.startsWith "c_"
      | _ => false)

/-- The source files the kernel-check bypass must not appear in. -/
def sources : IO (Array FilePath) := do
  return (#["Olint.lean", "lakefile.toml"] : Array FilePath) ++ (← leanFiles "Olint")

/-- The audit. -/
def audit : IO Unit := do
  let needle := "skipKernel" ++ "TC"
  let mut bypass : Array FilePath := #[]
  for f in ← sources do
    if (← f.pathExists) && ((← IO.FS.readFile f).splitOn needle).length > 1 then
      bypass := bypass.push f
  initSearchPath (← findSysroot)
  let mods := (← leanFiles "Olint").map moduleOf
  let imports := mods.map fun m => ({ module := m } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut targets : Array (Name × Name) := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | throw <| IO.userError s!"module {m} not imported"
    for n in env.header.moduleData[idx.toNat]!.constNames do
      if let some (.thmInfo _) := env.find? n then
        if !isEquationLemma n then targets := targets.push (n, m)
  let sorted := targets.qsort (fun a b => Name.lt a.1 b.1)
  let mut memo : NameMap (Array Name) := {}
  let mut bad : Array (Name × Array Name) := #[]
  let mut pending : Array (Name × Array Name) := #[]
  let mut shapes : Array Name := #[]
  let mut certificates := 0
  for (n, m) in sorted do
    let (deps, memo') := (axiomsOf env n).run memo
    memo := memo'
    let axs := (deps.filter (!unsigned.contains ·)).qsort Name.lt
    IO.println s!"'{n}' depends on axioms: {axs.toList}"
    let extra := axs.filter fun a => !allowed.contains a
    if !extra.isEmpty then bad := bad.push (n, extra)
    let drafts := (deps.filter unsigned.contains).qsort Name.lt
    if !drafts.isEmpty then pending := pending.push (n, drafts)
    if isCertificate m n then
      certificates := certificates + 1
      if let some (.thmInfo info) := env.find? n then
        if !isCertificateStatement info.type then shapes := shapes.push n
  IO.println s!"audited {sorted.size} theorems in {mods.size} modules"
  IO.println s!"checked the statement of {certificates} certificate theorems"
  for (n, drafts) in pending do
    IO.println s!"pending signature (rests on the G52 drafts {drafts.toList}): '{n}'"
  IO.println s!"{pending.size} theorems pending signature"
  let mut errors : Array String := #[]
  if !bypass.isEmpty then
    errors := errors.push s!"kernel-check bypass `debug.{needle}` in {bypass.toList}"
  if !bad.isEmpty then
    errors := errors.push s!"axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"
  if !shapes.isEmpty then
    errors := errors.push
      s!"certificate theorems not stating `∀ W, NoReplacement W xs → Bound W p n c`: {shapes.toList}"
  if !errors.isEmpty then
    throw <| IO.userError ("; ".intercalate errors.toList)

end OlintAxioms

#eval OlintAxioms.audit

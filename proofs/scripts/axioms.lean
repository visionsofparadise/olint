import Lean

/-!
# Axiom audit (§6.3)

Run from `proofs/` with `lake env lean scripts/axioms.lean` after `lake build` (and after the
corpus generator has written `Olint/Corpus/`, when it has).

It imports `Olint.Certificate` and every module under `Olint/Rules/`, `Olint/Corpus/` and
`Olint/Tests/`, then prints the axioms of `Olint.check_sound` and of every theorem those
modules declare, as `#print axioms` does. It fails, so `lean` exits non-zero, when any axiom
lies outside `propext`, `Classical.choice` and `Quot.sound`.
-/

open Lean System

namespace OlintAxioms

/-- The axioms §6.3 admits. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The directories whose modules' theorems are audited. -/
def auditedDirs : Array FilePath := #["Olint/Rules", "Olint/Corpus", "Olint/Tests"]

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

/-- The axioms a constant depends on, memoised across constants, following the same edges as
`#print axioms` (`Lean.collectAxioms`): types, values, and an inductive's constructors. -/
partial def axiomsOf (env : Environment) (c : Name) : StateM (NameMap (Array Name)) (Array Name) := do
  if let some r := (← get).find? c then return r
  modify (·.insert c #[])
  let r ← match env.find? c with
    | some (.axiomInfo _) => pure #[c]
    | some info => do
      let mut deps := info.type.getUsedConstants
      if let some v := info.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
      if let .inductInfo i := info then deps := deps ++ i.ctors.toArray
      let mut acc : Array Name := #[]
      for d in deps do
        for a in ← axiomsOf env d do
          if !acc.contains a then acc := acc.push a
      pure acc
    | none => pure #[]
  modify (·.insert c r)
  return r

/-- A theorem declared in the source, not an equation lemma Lean generates for a definition. -/
def isDeclared (n : Name) : Bool :=
  match n with
  | .str _ s => !(s.startsWith "eq_" || s.startsWith "_") && !n.isInternalDetail
  | _ => false

/-- The audit: print every audited theorem's axioms and fail on any outside `allowed`. -/
def audit : IO Unit := do
  initSearchPath (← findSysroot)
  let mut mods : Array Name := #[]
  for dir in auditedDirs do
    for f in ← leanFiles dir do
      mods := mods.push (moduleOf f)
  let imports := (#[`Olint.Certificate] ++ mods).map fun m => ({ module := m } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut targets : Array Name := #[`Olint.check_sound]
  for m in mods do
    let some idx := env.getModuleIdx? m | throw <| IO.userError s!"module {m} not imported"
    for n in env.header.moduleData[idx.toNat]!.constNames do
      if let some (.thmInfo _) := env.find? n then
        if isDeclared n then targets := targets.push n
  let sorted := targets.qsort Name.lt
  let mut memo : NameMap (Array Name) := {}
  let mut bad : Array (Name × Array Name) := #[]
  for n in sorted do
    let (axs, memo') := (axiomsOf env n).run memo
    memo := memo'
    let axs := axs.qsort Name.lt
    IO.println s!"'{n}' depends on axioms: {axs.toList}"
    let extra := axs.filter fun a => !allowed.contains a
    if !extra.isEmpty then bad := bad.push (n, extra)
  IO.println s!"audited {sorted.size} theorems in {mods.size + 1} modules"
  if !bad.isEmpty then
    throw <| IO.userError s!"axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"

end OlintAxioms

#eval OlintAxioms.audit

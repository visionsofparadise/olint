import Olint.Model.Value

/-!
# The encoding of §2

Each clause of spec §2 is encoded here, and nowhere else:

* **§2.1** Proven results rest on this file's definitions, the model in `Olint.Model`, and Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The file declares no `axiom`.
* **§2.2** Built-ins are the fixed definitions `builtinGlobal`, `builtinMethod`, `builtinGetter`
  and `step`. The work semantics consults them only after the program's own bindings, own
  properties and class methods, so only program definitions shadow them. The syntax has no
  form that modifies a built-in.
* **§2.3** `step` and `builtinGetter` follow each built-in's ECMA-262 algorithm steps and charge
  their worst-case step count; each docstring cites the clause of ECMA-262, 17th edition
  (ECMAScript 2026).
* **§2.4** A built-in whose work ECMA-262 leaves implementation-defined steps to
  `Step.implementationDefined`, which carries no work, so evaluation through it never halts and
  no bound through it is provable. A spec-internal operation with no work definition
  (`ownPropertyKeysWork`) aborts the run the same way.
* **§2.5** `Conforms` is the judgement that a value conforms to its declared type; admission of
  an instance (`Olint.Model.Admitted`) requires it of every variable cell in every state the
  run reaches, so it is a hypothesis of every bound.
* **Spec-internal operations.** The ECMA-262 steps use operations on Lists, Strings, BigInts
  and ordinary objects whose work the steps themselves do not define. Their step costs are the
  §2 axiom drafts of the section *Spec-internal operations* below, each pending Matt's
  signature (ledger gap G52).
-/

namespace Olint.Model

/-! ## Spec-internal operations

The step costs of the operations the ECMA-262 algorithm steps perform without spelling out
their own steps. Each is a definition, not a Lean `axiom`, and each is a draft of a §2 axiom
awaiting Matt's signature. -/

/-- -- §2 axiom draft (G52), pending Matt's signature

Looking up a property of an ordinary object (`OrdinaryGetOwnProperty`, ECMA-262 §10.1.5.1, as
`[[Get]]` and `[[Set]]` reach it) costs `O(1)`: one unit. -/
def propertyLookupWork : ℕ := 1

/-- -- §2 axiom draft (G52), pending Matt's signature

Appending an element to a List (§6.2.2, "append … to the List") costs `O(1)`: one unit. -/
def listAppendWork : ℕ := 1

/-- -- §2 axiom draft (G52), pending Matt's signature

Deciding whether a List of `len` elements contains a value (§6.2.2, "is an element of") costs
`O(len)`: `len + 1` units. -/
def listContainsWork (len : ℕ) : ℕ := len + 1

/-- -- §2 axiom draft (G52), pending Matt's signature

Concatenating two Strings (§6.1.4, "the string-concatenation of") costs `O(length)`: the
UTF-16 length of the result plus one. -/
def stringConcatWork (a b : String) : ℕ := utf16Length a + utf16Length b + 1

/-- -- §2 axiom draft (G52), pending Matt's signature

Comparing two Strings for equality (`SameValueNonNumber`, §7.2.12, as `IsStrictlyEqual` and
`SameValueZero` reach it) costs `O(length)`: the shorter UTF-16 length plus one, the code
units compared before the first difference at worst. -/
def stringEqWork (a b : String) : ℕ := min (utf16Length a) (utf16Length b) + 1

/-- -- §2 axiom draft (G52), pending Matt's signature

Comparing two BigInts of at most `digits` digits for equality (`BigInt::equal`, §6.1.6.2.13)
costs `O(digits)`: `digits + 1` units. The model has no BigInt values yet; the cost is fixed
here so the axiom set is complete. -/
def bigIntEqWork (digits : ℕ) : ℕ := digits + 1

/-- -- §2 axiom draft (G52), pending Matt's signature

`OrdinaryOwnPropertyKeys` (§10.1.11.1) has no work definition: its ordering of the keys is not
given by steps whose work §2 fixes, so it is an unknown contribution (§2.4) and a run that
reaches it aborts (`Abort.undefinedWork`). -/
def ownPropertyKeysWork : Option ℕ := none

/-- The work of comparing two values with `IsStrictlyEqual` or `SameValueZero`: `stringEqWork`
for two Strings, one unit otherwise. -/
def valueEqWork : Value → Value → ℕ
  | .str a, .str b => stringEqWork a b
  | _, _ => 1

/-! ## §2.2 Resolution of built-ins -/

/-- The global bindings of built-ins, consulted after every program binding (§2.2). -/
def builtinGlobal : Name → Option Builtin
  | "Map" => some .mapCtor
  | "Set" => some .setCtor
  | _ => none

/-- The built-in prototype methods of an object, consulted after its own properties and class
methods (§2.2). -/
def builtinMethod : Obj → Name → Option Builtin
  | .map _, "get" => some .mapGet
  | .map _, "has" => some .mapHas
  | .map _, "set" => some .mapSet
  | .map _, "delete" => some .mapDelete
  | .map _, "clear" => some .mapClear
  | .set _, "has" => some .setHas
  | .set _, "add" => some .setAdd
  | .set _, "delete" => some .setDelete
  | .set _, "clear" => some .setClear
  | .array _, "push" => some .arrayPush
  | .array _, "indexOf" => some .arrayIndexOf
  | .array _, "includes" => some .arrayIncludes
  | .array _, "sort" => some .arraySort
  | .array _, "toSorted" => some .arrayToSorted
  | _, _ => none

/-! ## §2.3 Keyed-collection data operations

`[[MapData]]` and `[[SetData]]` are Lists whose deleted entries are `none` (ECMA-262's `empty`).
Every keyed operation below scans that List, as the ECMA-262 steps do; the specification rejects
amortized keyed access. -/

/-- `-0` as a key reads as `+0` (§24.1.3.11 step 4, §24.2.4.1 step 3). -/
def normKey : Value → Value
  | .num (.fin true 0 _) => .num Double.posZero
  | v => v

/-- The work of scanning every record of a `[[MapData]]` or `[[SetData]]` List for a key, as
the keyed operations do: each live record costs one `SameValueZero` comparison
(`valueEqWork`), each deleted record one unit, plus one. -/
def scanWork (k : Value) : List (Option Value) → ℕ
  | [] => 1
  | some k' :: rest => valueEqWork k' k + scanWork k rest
  | none :: rest => 1 + scanWork k rest

/-- The keys of a `[[MapData]]` List, deleted records kept as `none`. -/
def mapKeys (data : List (Option (Value × Value))) : List (Option Value) :=
  data.map (Option.map Prod.fst)

/-- The value of the first live record with key `k`. -/
def mapFind (k : Value) : List (Option (Value × Value)) → Option Value
  | [] => none
  | some (k', v) :: rest => if sameValueZero k' k then some v else mapFind k rest
  | none :: rest => mapFind k rest

/-- Overwrite the first live record with key `k`, else append a record. -/
def mapPut (k v : Value) : List (Option (Value × Value)) → List (Option (Value × Value))
  | [] => [some (normKey k, v)]
  | some (k', v') :: rest =>
    if sameValueZero k' k then some (k', v) :: rest else some (k', v') :: mapPut k v rest
  | none :: rest => none :: mapPut k v rest

/-- Empty the first live record with key `k`, reporting whether one existed. -/
def mapErase (k : Value) : List (Option (Value × Value)) → List (Option (Value × Value)) × Bool
  | [] => ([], false)
  | some (k', v') :: rest =>
    if sameValueZero k' k then (none :: rest, true)
    else let (r, b) := mapErase k rest; (some (k', v') :: r, b)
  | none :: rest => let (r, b) := mapErase k rest; (none :: r, b)

/-- Whether a live element equals `v`. -/
def setFind (v : Value) : List (Option Value) → Bool
  | [] => false
  | some v' :: rest => sameValueZero v' v || setFind v rest
  | none :: rest => setFind v rest

/-- Append `v` unless a live element equals it. -/
def setPut (v : Value) (data : List (Option Value)) : List (Option Value) :=
  if setFind v data then data else data ++ [some (normKey v)]

/-- Empty the first live element equal to `v`, reporting whether one existed. -/
def setErase (v : Value) : List (Option Value) → List (Option Value) × Bool
  | [] => ([], false)
  | some v' :: rest =>
    if sameValueZero v' v then (none :: rest, true)
    else let (r, b) := setErase v rest; (some v' :: r, b)
  | none :: rest => let (r, b) := setErase v rest; (none :: r, b)

/-- The number of live entries. -/
def liveCount {α : Type} (data : List (Option α)) : ℕ := (data.filter Option.isSome).length

/-! ## §2.3 and §2.4 Built-in steps -/

/-- The outcome of one built-in operation. -/
inductive Step where
  /-- The operation returns `v`, leaving heap `h`, after `work` steps. -/
  | ok (v : Value) (h : Heap) (work : ℕ)
  /-- The operation throws a TypeError, which the model does not continue past. -/
  | typeError
  /-- The operation's work is implementation-defined (§2.4): it has no work definition. -/
  | implementationDefined
  /-- The operation is outside the modelled subset of its argument forms. -/
  | unmodelled

/-- The first argument, `undefined` when absent (ECMA-262 §10.3, missing arguments). -/
def arg0 : List Value → Value
  | v :: _ => v
  | [] => .undef

/-- Run `k` on the Map a receiver refers to, else throw a TypeError
(`RequireInternalSlot(M, [[MapData]])`). -/
def withMap (h : Heap) (self : Value) (k : Loc → List (Option (Value × Value)) → Step) : Step :=
  match self with
  | .ref l => match h.get l with
    | some (.map data) => k l data
    | _ => .typeError
  | _ => .typeError

/-- Run `k` on the Set a receiver refers to, else throw a TypeError
(`RequireInternalSlot(S, [[SetData]])`). -/
def withSet (h : Heap) (self : Value) (k : Loc → List (Option Value) → Step) : Step :=
  match self with
  | .ref l => match h.get l with
    | some (.set data) => k l data
    | _ => .typeError
  | _ => .typeError

/-- Run `k` on the Array a receiver refers to. -/
def withArray (h : Heap) (self : Value) (k : Loc → List Value → Step) : Step :=
  match self with
  | .ref l => match h.get l with
    | some (.array elems) => k l elems
    | _ => .unmodelled
  | _ => .unmodelled

/-- `AddEntriesFromIterable` over an Array of `[key, value]` Arrays, calling
`Map.prototype.set` per entry (ECMA-262 §24.1.1.2). Each step charges one iterator step plus
the `set` it performs. -/
def addEntries (h : Heap) :
    List Value → List (Option (Value × Value)) → ℕ → Option (List (Option (Value × Value)) × ℕ)
  | [], data, w => some (data, w)
  | .ref l :: rest, data, w => match h.get l with
    | some (.array (k :: v :: _)) =>
      addEntries h rest (mapPut k v data) (w + 1 + scanWork k (mapKeys data))
    | some (.array [k]) =>
      addEntries h rest (mapPut k .undef data) (w + 1 + scanWork k (mapKeys data))
    | some (.array []) =>
      addEntries h rest (mapPut .undef .undef data) (w + 1 + scanWork .undef (mapKeys data))
    | _ => none
  | _ :: _, _, _ => none

/-- The Set constructor's loop over an Array, calling `Set.prototype.add` per element
(ECMA-262 §24.2.2.1). Each step charges one iterator step plus the `add` it performs. -/
def addElements : List Value → List (Option Value) → ℕ → List (Option Value) × ℕ
  | [], data, w => (data, w)
  | v :: rest, data, w => addElements rest (setPut v data) (w + 1 + scanWork v data)

/-- The iterable argument of a keyed-collection constructor, as the Array elements it yields;
`some []` for an absent, `undefined` or `null` iterable. -/
def iterableElems (h : Heap) : List Value → Option (List Value)
  | [] | .undef :: _ | .null :: _ => some []
  | .ref l :: _ => match h.get l with
    | some (.array elems) => some elems
    | _ => none
  | _ :: _ => none

/-- One call of a built-in, as a constructor when `isNew`.

Work per built-in, each the worst-case step count of its ECMA-262 algorithm. `scan(D, k)` is
`scanWork`: one `SameValueZero` comparison per live record of the receiver's `[[MapData]]` or
`[[SetData]]` List `D` and one unit per deleted record, plus one, so every keyed call pays a
full scan of all `|D|` records, deleted records included; a comparison costs one unit, or the
`stringEqWork` of two Strings. `cmp(A, k)` is the same sum over an Array `A`'s elements.

| Built-in | ECMA-262 | Work |
| --- | --- | --- |
| `new Map(iterable)` | §24.1.1.1, §24.1.1.2 | `1` plus, per entry, `1 + scan(D, key)` |
| `Map.prototype.clear` | §24.1.3.1 | `|D| + 1` |
| `Map.prototype.delete` | §24.1.3.3 | `scan(D, key)` |
| `Map.prototype.get` | §24.1.3.6 | `scan(D, key)` |
| `Map.prototype.has` | §24.1.3.9 | `scan(D, key)` |
| `Map.prototype.set` | §24.1.3.11 | `scan(D, key) + listAppendWork` |
| `new Set(iterable)` | §24.2.2.1 | `1` plus, per element, `1 + scan(D, value)` |
| `Set.prototype.add` | §24.2.4.1 | `scan(D, value) + listAppendWork` |
| `Set.prototype.clear` | §24.2.4.2 | `|D| + 1` |
| `Set.prototype.delete` | §24.2.4.4 | `scan(D, value)` |
| `Set.prototype.has` | §24.2.4.8, §24.2.1.3, §24.2.1.4 | `scan(D, value)` |
| `Array.prototype.includes` | §23.1.3.16 | `cmp(A, searchElement)` |
| `Array.prototype.indexOf` | §23.1.3.17 | `cmp(A, searchElement)` |
| `Array.prototype.push` | §23.1.3.23 | `items · listAppendWork + 1` |
| `Array.prototype.sort` | §23.1.3.30 | none: implementation-defined (§2.4) |
| `Array.prototype.toSorted` | §23.1.3.34 | none: implementation-defined (§2.4) |

`sort` and `toSorted` reach `SortIndexedProperties` (§23.1.3.30.1), whose sequence of
`SortCompare` calls ECMA-262 leaves implementation-defined. -/
def step (b : Builtin) (isNew : Bool) (h : Heap) (self : Value) (args : List Value) : Step :=
  match b, isNew with
  /- §24.1.1.1 `Map ( [ iterable ] )`: throws without NewTarget; creates `[[MapData]]` and
  runs `AddEntriesFromIterable` (§24.1.1.2) with `Map.prototype.set` as adder. -/
  | .mapCtor, true => match iterableElems h args with
    | some elems => match addEntries h elems [] 1 with
      | some (data, w) => let (l, h') := h.alloc (.map data); .ok (.ref l) h' w
      | none => .unmodelled
    | none => .unmodelled
  /- §24.2.2.1 `Set ( [ iterable ] )`: throws without NewTarget; calls `Set.prototype.add` per
  element of the iterable. -/
  | .setCtor, true => match iterableElems h args with
    | some elems =>
      let (data, w) := addElements elems [] 1
      let (l, h') := h.alloc (.set data)
      .ok (.ref l) h' w
    | none => .unmodelled
  | .mapCtor, false | .setCtor, false => .typeError
  | _, true => .typeError
  /- §24.1.3.6 `Map.prototype.get ( key )`: scans every record of `[[MapData]]`. -/
  | .mapGet, false => withMap h self fun _ data =>
    .ok ((mapFind (arg0 args) data).getD .undef) h (scanWork (arg0 args) (mapKeys data))
  /- §24.1.3.9 `Map.prototype.has ( key )`: scans every record of `[[MapData]]`. -/
  | .mapHas, false => withMap h self fun _ data =>
    .ok (.bool (mapFind (arg0 args) data).isSome) h (scanWork (arg0 args) (mapKeys data))
  /- §24.1.3.11 `Map.prototype.set ( key, value )`: scans `[[MapData]]`, then overwrites or
  appends. -/
  | .mapSet, false => withMap h self fun l data =>
    .ok self (h.put l (.map (mapPut (arg0 args) (arg0 args.tail) data)))
      (scanWork (arg0 args) (mapKeys data) + listAppendWork)
  /- §24.1.3.3 `Map.prototype.delete ( key )`: scans `[[MapData]]` and empties the record. -/
  | .mapDelete, false => withMap h self fun l data =>
    let (data', found) := mapErase (arg0 args) data
    .ok (.bool found) (h.put l (.map data')) (scanWork (arg0 args) (mapKeys data))
  /- §24.1.3.1 `Map.prototype.clear ( )`: empties every record, keeping the List. -/
  | .mapClear, false => withMap h self fun l data =>
    .ok .undef (h.put l (.map (data.map fun _ => none))) (data.length + 1)
  /- §24.2.4.8 `Set.prototype.has ( value )`: `SetDataHas` (§24.2.1.3) via `SetDataIndex`
  (§24.2.1.4), which scans `[[SetData]]`. -/
  | .setHas, false => withSet h self fun _ data =>
    .ok (.bool (setFind (arg0 args) data)) h (scanWork (arg0 args) data)
  /- §24.2.4.1 `Set.prototype.add ( value )`: scans `[[SetData]]`, then appends. -/
  | .setAdd, false => withSet h self fun l data =>
    .ok self (h.put l (.set (setPut (arg0 args) data))) (scanWork (arg0 args) data + listAppendWork)
  /- §24.2.4.4 `Set.prototype.delete ( value )`: scans `[[SetData]]` and empties the element. -/
  | .setDelete, false => withSet h self fun l data =>
    let (data', found) := setErase (arg0 args) data
    .ok (.bool found) (h.put l (.set data')) (scanWork (arg0 args) data)
  /- §24.2.4.2 `Set.prototype.clear ( )`: empties every element, keeping the List. -/
  | .setClear, false => withSet h self fun l data =>
    .ok .undef (h.put l (.set (data.map fun _ => none))) (data.length + 1)
  /- §23.1.3.23 `Array.prototype.push ( ...items )`: one `Set` per item. -/
  | .arrayPush, false => withArray h self fun l elems =>
    let elems' := elems ++ args
    .ok (.num (Double.ofNat elems'.length)) (h.put l (.array elems'))
      (args.length * listAppendWork + 1)
  /- §23.1.3.17 `Array.prototype.indexOf ( searchElement [ , fromIndex ] )`: scans up to `len`
  indices with `IsStrictlyEqual`. -/
  | .arrayIndexOf, false => withArray h self fun _ elems =>
    let i := elems.findIdx (strictEquals · (arg0 args))
    .ok (.num (Double.ofInt (if i < elems.length then (i : ℤ) else -1))) h
      (scanWork (arg0 args) (elems.map some))
  /- §23.1.3.16 `Array.prototype.includes ( searchElement [ , fromIndex ] )`: scans up to `len`
  indices with `SameValueZero`. -/
  | .arrayIncludes, false => withArray h self fun _ elems =>
    .ok (.bool (elems.any (sameValueZero · (arg0 args)))) h
      (scanWork (arg0 args) (elems.map some))
  /- §23.1.3.30 and §23.1.3.34: the comparison sequence of `SortIndexedProperties` is
  implementation-defined (§2.4). -/
  | .arraySort, false | .arrayToSorted, false => .implementationDefined

/-- Built-in accessor and length reads, with their work (§2.2, §2.3).

* `get Map.prototype.size` (ECMA-262 §24.1.3.12) counts the live records of `[[MapData]]`:
  `|D| + 1`.
* `get Set.prototype.size` (§24.2.4.14) is `SetDataSize` (§24.2.1.5), which counts the live
  elements of `[[SetData]]`: `|D| + 1`.
* An Array's `length` is an own data property of an Array exotic object (§10.4.2): `1`. -/
def builtinGetter : Obj → Name → Option (Value × ℕ)
  | .map data, "size" => some (.num (Double.ofNat (liveCount data)), data.length + 1)
  | .set data, "size" => some (.num (Double.ofNat (liveCount data)), data.length + 1)
  | .array elems, "length" => some (.num (Double.ofNat elems.length), 1)
  | _, _ => none

/-- Evaluating a RegularExpressionLiteral (ECMA-262 §13.2.7.3) runs `RegExpCreate`
(§22.2.3.1), which parses the pattern: `|pattern| + |flags| + 1`. -/
def regexCreateWork (pattern flags : String) : ℕ := pattern.length + flags.length + 1

/-! ## §2.5 Conformance to declared types -/

/-- `Conforms h v τ`: value `v` conforms to declared type `τ` in heap `h` (§2.5). -/
inductive Conforms (h : Heap) : Value → Ty → Prop where
  | any (v : Value) : Conforms h v .any
  | undefined : Conforms h .undef .undefined
  | null : Conforms h .null .null
  | boolean (b : Bool) : Conforms h (.bool b) .boolean
  | number (n : Double) : Conforms h (.num n) .number
  | string (s : String) : Conforms h (.str s) .string
  | array (l : Loc) (elems : List Value) (τ : Ty) :
      h.get l = some (.array elems) → (∀ v ∈ elems, Conforms h v τ) →
      Conforms h (.ref l) (.array τ)
  | map (l : Loc) (data : List (Option (Value × Value))) (κ τ : Ty) :
      h.get l = some (.map data) →
      (∀ k v, some (k, v) ∈ data → Conforms h k κ) →
      (∀ k v, some (k, v) ∈ data → Conforms h v τ) →
      Conforms h (.ref l) (.map κ τ)
  | set (l : Loc) (data : List (Option Value)) (τ : Ty) :
      h.get l = some (.set data) → (∀ v, some v ∈ data → Conforms h v τ) →
      Conforms h (.ref l) (.set τ)
  | object (l : Loc) (props : List (Name × Value)) (cls : Option Loc)
      (fields : List (Name × Ty)) :
      h.get l = some (.ordinary props cls) →
      (∀ x τ, (x, τ) ∈ fields → (props.lookup x).isSome) →
      (∀ x τ v, (x, τ) ∈ fields → props.lookup x = some v → Conforms h v τ) →
      Conforms h (.ref l) (.object fields)
  | closure (l : Loc) (f : Func) (env : Env) :
      h.get l = some (.closure f env) → Conforms h (.ref l) .func
  | builtin (b : Builtin) : Conforms h (.builtin b) .func

end Olint.Model

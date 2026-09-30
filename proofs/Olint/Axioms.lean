import Olint.Model.Value

/-!
# The encoding of §2

Each clause of spec §2 is encoded here, and nowhere else:

* **§2.1** Proven results rest on this file's definitions, the model in `Olint.Model`, and Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The file declares no `axiom`.
  The step costs of spec-internal operations are §2 axiom drafts awaiting Matt's signature
  (ledger gap G52), so the model takes them as a parameter, `SpecOps`, and the drafts' values
  are one instance of it, `SpecOps.draft`. A theorem that holds for every `SpecOps` rests on
  none of those values, but it still rests on the shapes the fields' types fix, which are
  drafts too: property lookup, List append, number-to-key conversion, object creation and
  function object creation each cost a constant, and List membership costs a function of the
  List's length alone. `scripts/axioms.lean` reports as pending signature every theorem that
  reaches one of those fields, and every theorem that needs the drafts' values, which names
  `SpecOps.draft` in its statement (§2.1, §6.3).
* **§2.2** Built-ins are the fixed definitions `builtinGlobal`, `builtinMethod`, `builtinGetter`
  and `step`. The work semantics consults them only after the program's own bindings, own
  properties and class members, so the certificate's own code shadows them. The rest of the
  analysed program, which a certificate's program scope does not contain, may also replace or
  modify built-ins (§2.2). A `World` records which intrinsics it modified (`World.modified`),
  and the work semantics aborts wherever it would consult a modified intrinsic, since the
  modified behaviour is unknown. Every certificate theorem is stated for every world satisfying
  `NoReplacement W xs`, where `xs` lists the intrinsics its derivation relies on; olint
  discharges that premise by its intrinsic-replacement scan (family G,
  `intrinsic-replacement-scan`), whose soundness Phase 5 certifies.
* **§2.3** `step` and `builtinGetter` follow each built-in's ECMA-262 algorithm steps and charge
  their worst-case step count; each docstring cites the clause of ECMA-262, 17th edition
  (ECMAScript 2026).
* **§2.4** A built-in whose work ECMA-262 leaves implementation-defined steps to
  `Step.implementationDefined`, which carries no work, so evaluation through it never halts and
  no bound through it is provable. A spec-internal operation with no work definition
  (`SpecOps.ownPropertyKeys` in the draft) aborts the run the same way.
* **§2.5** `Conforms` is the judgement that a value conforms to its declared type, following
  TypeScript's structural assignability for the modelled types (`conforms`). Admission of an
  instance (`Olint.Model.Admitted`) requires it of the entry's inputs, and every read of a
  variable during the run checks it (`Olint.Model.readVar`), aborting on a value that does not
  conform: a run that would read a non-conforming value never completes, so no bound covers it
  and no bound holds vacuously because of it.
-/

namespace Olint.Model

/-! ## Spec-internal operations (G52 drafts)

The step costs of the operations the ECMA-262 algorithm steps perform without spelling out
their own steps. `SpecOps` is the parameter; `SpecOps.draft` holds the §2 axiom drafts, each
pending Matt's signature. -/

/-- The step costs of spec-internal operations. The model of work is parametric in them, so
a theorem that holds for every `SpecOps` depends on none of the drafts' values; the types of
`propertyLookup`, `listAppend`, `listContains`, `numberToKey`, `objectCreate` and
`closureCreate` still fix a draft's shape, on which such a theorem rests (§2.1). -/
structure SpecOps where
  /-- Looking up one property of one object (`OrdinaryGetOwnProperty`, ECMA-262 §10.1.5.1, as
  `[[Get]]`, `[[Set]]` and `[[DefineOwnProperty]]` reach it, once per object of the prototype
  chain they visit), including deciding whether a String key is an array index (§6.1.7). -/
  propertyLookup : ℕ
  /-- Appending an element to a List (§6.2.2, "append … to the List"), and the
  `CreateDataPropertyOrThrow` of one Array element. -/
  listAppend : ℕ
  /-- Deciding whether a List of the given length contains a value (§6.2.2, "is an element
  of"). -/
  listContains : ℕ → ℕ
  /-- Concatenating two Strings (§6.1.4, "the string-concatenation of"). -/
  stringConcat : String → String → ℕ
  /-- Comparing two Strings for equality (`SameValueNonNumber`, §7.2.12). -/
  stringEq : String → String → ℕ
  /-- Comparing two BigInts of at most the given number of digits (`BigInt::equal`,
  §6.1.6.2.13). The model has no BigInt values yet. -/
  bigIntEq : ℕ → ℕ
  /-- `OrdinaryOwnPropertyKeys` (§10.1.11.1); `none` when it has no work definition, which
  makes it an unknown contribution (§2.4). -/
  ownPropertyKeys : Option ℕ
  /-- Converting a Number to a property key (`ToPropertyKey`, §7.1.19, through
  `Number::toString`, §6.1.6.1.20). -/
  numberToKey : ℕ
  /-- Parsing a regular expression literal (`RegExpCreate`, §22.2.3.1, through
  `ParsePattern`, §22.2.3.4). -/
  regexCreate : String → String → ℕ
  /-- Creating an object (`OrdinaryObjectCreate`, §10.1.12, and `ArrayCreate`, §10.4.2.2). -/
  objectCreate : ℕ
  /-- Creating a function object (`OrdinaryFunctionCreate`, §10.2.3, as function and arrow
  expressions, hoisted function declarations and class definitions reach it). -/
  closureCreate : ℕ

/-- The length of a String in UTF-16 code units, as the drafts measure Strings. -/
abbrev strLen (s : String) : ℕ := utf16Length s

/-- -- §2 axiom drafts (G52), pending Matt's signature

* property lookup `O(1)`: one unit;
* List append `O(1)`: one unit;
* List membership `O(len)`: `len + 1` units;
* String concatenation `O(length)`: the UTF-16 length of the result plus one;
* String equality `O(length)`: the shorter UTF-16 length plus one, the code units compared
  before the first difference at worst;
* BigInt equality `O(digits)`: `digits + 1` units;
* `OrdinaryOwnPropertyKeys`: no work definition, since its ordering of the keys is not given by
  steps whose work §2 fixes, so a run that reaches it aborts (§2.4);
* Number to property key `O(1)`: one unit, a binary64 value having at most 25 characters;
* RegExp literal parse `O(length)`: `|pattern| + |flags| + 1`;
* object creation `O(1)`: one unit;
* function object creation `O(1)`: one unit. -/
def SpecOps.draft : SpecOps where
  propertyLookup := 1
  listAppend := 1
  listContains len := len + 1
  stringConcat a b := strLen a + strLen b + 1
  stringEq a b := min (strLen a) (strLen b) + 1
  bigIntEq digits := digits + 1
  ownPropertyKeys := none
  numberToKey := 1
  regexCreate pattern flags := pattern.length + flags.length + 1
  objectCreate := 1
  closureCreate := 1

/-- The work of comparing two values with `IsStrictlyEqual` or `SameValueZero`: the String
equality cost for two Strings, one unit otherwise. -/
def valueEqWork (ops : SpecOps) : Value → Value → ℕ
  | .str a, .str b => ops.stringEq a b
  | _, _ => 1

/-! ## §2.2 Intrinsics the rest of the program may modify -/

/-- The intrinsics whose behaviour the model fixes: the global bindings of the modelled
constructors, and the prototype objects the model's property lookups and iterations consult
(each with its iterator prototype, `%ArrayIteratorPrototype%`, `%MapIteratorPrototype%` and
`%SetIteratorPrototype%`). -/
inductive Intrinsic where
  | globalMap | globalSet
  | objectPrototype | arrayPrototype | mapPrototype | setPrototype | functionPrototype
  | regexpPrototype
  deriving DecidableEq, Repr

/-- The world a run happens in: the spec-internal step costs, and the intrinsics the analysed
program replaced or modified outside the certificate's program scope (§2.2). -/
structure World where
  ops : SpecOps
  modified : Intrinsic → Bool

/-- The analysed program modifies none of the intrinsics `xs` (§2.2). A certificate theorem
takes it as a premise over the intrinsics its derivation relies on. Its discharge is olint's
intrinsic-replacement scan (family G, `intrinsic-replacement-scan`), certified in Phase 5. -/
def NoReplacement (W : World) (xs : List Intrinsic) : Prop := ∀ x ∈ xs, W.modified x = false

/-! ## §2.2 Resolution of built-ins -/

/-- The global bindings of built-ins, consulted after every program binding, with the
intrinsic each rests on (§2.2). -/
def builtinGlobal : Name → Option (Builtin × Intrinsic)
  | "Map" => some (.mapCtor, .globalMap)
  | "Set" => some (.setCtor, .globalSet)
  | _ => none

/-- The prototype object a built-in object's property lookups reach after its own
properties. -/
def protoOf : Obj → Option Intrinsic
  | .array _ => some .arrayPrototype
  | .map _ => some .mapPrototype
  | .set _ => some .setPrototype
  | .closure _ _ | .klass _ _ _ _ => some .functionPrototype
  | .regexp _ _ => some .regexpPrototype
  | .ordinary _ _ _ => some .objectPrototype
  | .cell _ _ | .uninit _ => none

/-- The built-in prototype methods of an object, consulted after its own properties
(§2.2). -/
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

/-! ## Built-in prototype members

The names of the properties the built-in prototypes carry (ECMA-262 §20.1.3, §22.1.3, §23.1.3,
§24.1.3, §24.2.4, §20.2.3, §21.1.3, §20.3.3, §22.2.6, and Annex B.2), and the members of the
TypeScript interfaces `Array<T>`, `Map<K, V>` and `Set<T>` in their ES5 and ES2015 core
libraries, less the members every object inherits from `%Object.prototype%` and those keyed by
symbols, which the model's values cannot carry. -/

/-- `%Object.prototype%` (§20.1.3, Annex B.2.2). -/
def objectProtoMembers : List Name :=
  ["constructor", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString",
    "toString", "valueOf", "__proto__", "__defineGetter__", "__defineSetter__",
    "__lookupGetter__", "__lookupSetter__"]

/-- `%Array.prototype%` (§23.1.3). -/
def arrayProtoMembers : List Name :=
  ["at", "concat", "constructor", "copyWithin", "entries", "every", "fill", "filter", "find",
    "findIndex", "findLast", "findLastIndex", "flat", "flatMap", "forEach", "includes",
    "indexOf", "join", "keys", "lastIndexOf", "map", "pop", "push", "reduce", "reduceRight",
    "reverse", "shift", "slice", "some", "sort", "splice", "toLocaleString", "toReversed",
    "toSorted", "toSpliced", "toString", "unshift", "values", "with"]

/-- `%Map.prototype%` (§24.1.3). -/
def mapProtoMembers : List Name :=
  ["clear", "constructor", "delete", "entries", "forEach", "get", "getOrInsert",
    "getOrInsertComputed", "has", "keys", "set", "size", "values"]

/-- `%Set.prototype%` (§24.2.4). -/
def setProtoMembers : List Name :=
  ["add", "clear", "constructor", "delete", "difference", "entries", "forEach", "has",
    "intersection", "isDisjointFrom", "isSubsetOf", "isSupersetOf", "keys", "size",
    "symmetricDifference", "union", "values"]

/-- `%String.prototype%` (§22.1.3, Annex B.2.2). -/
def stringProtoMembers : List Name :=
  ["at", "charAt", "charCodeAt", "codePointAt", "concat", "constructor", "endsWith",
    "includes", "indexOf", "isWellFormed", "lastIndexOf", "localeCompare", "match", "matchAll",
    "normalize", "padEnd", "padStart", "repeat", "replace", "replaceAll", "search", "slice",
    "split", "startsWith", "substring", "toLocaleLowerCase", "toLocaleUpperCase",
    "toLowerCase", "toString", "toUpperCase", "toWellFormed", "trim", "trimEnd", "trimStart",
    "valueOf", "substr", "anchor", "big", "blink", "bold", "fixed", "fontcolor", "fontsize",
    "italics", "link", "small", "strike", "sub", "sup", "trimLeft", "trimRight"]

/-- `%Number.prototype%` (§21.1.3). -/
def numberProtoMembers : List Name :=
  ["constructor", "toExponential", "toFixed", "toLocaleString", "toPrecision", "toString",
    "valueOf"]

/-- `%Boolean.prototype%` (§20.3.3). -/
def booleanProtoMembers : List Name := ["constructor", "toString", "valueOf"]

/-- `%Function.prototype%` (§20.2.3) and the own properties of function objects. -/
def functionProtoMembers : List Name :=
  ["apply", "bind", "call", "constructor", "toString", "length", "name", "prototype", "caller",
    "arguments"]

/-- `%RegExp.prototype%` (§22.2.6, Annex B.2.4) and the own `lastIndex`. -/
def regexpProtoMembers : List Name :=
  ["compile", "constructor", "dotAll", "exec", "flags", "global", "hasIndices", "ignoreCase",
    "lastIndex", "multiline", "source", "sticky", "test", "toString", "unicode", "unicodeSets"]

/-- The string-keyed members of TypeScript's `Array<T>` (lib.es5), less `toString` and
`toLocaleString`, which `%Object.prototype%` supplies. -/
def arrayInterface : List Name :=
  ["length", "pop", "push", "concat", "join", "reverse", "shift", "slice", "sort", "splice",
    "unshift", "indexOf", "lastIndexOf", "every", "some", "forEach", "map", "filter", "reduce",
    "reduceRight"]

/-- The string-keyed members of TypeScript's `Map<K, V>` (lib.es2015.collection). -/
def mapInterface : List Name := ["clear", "delete", "forEach", "get", "has", "set", "size"]

/-- The string-keyed members of TypeScript's `Set<T>` (lib.es2015.collection). -/
def setInterface : List Name := ["add", "clear", "delete", "forEach", "has", "size"]

/-! ## §2.3 Keyed-collection data operations

`[[MapData]]` and `[[SetData]]` are Lists whose deleted entries are `none` (ECMA-262's `empty`).
Every keyed operation below scans that List, as the ECMA-262 steps do; the specification rejects
amortized keyed access.

**Size measure.** A deleted or cleared entry stays in the List, so the List's length `|D|`
counts every entry ever added, deleted ones included, and only grows. The input dimension of a
Map or Set (`Olint.Model.Heap.lengthOf`) measures `|D|`, not the live count `size` returns.
olint's size tracking agrees with it: by the G36 decision, any `delete` or `clear` on a
collection makes olint's size of it untracked, so a tracked size is always the number of
entries added, which is `|D|`. -/

/-- `-0` as a key reads as `+0` (§24.1.3.11 step 4, §24.2.4.1 step 3). -/
def normKey : Value → Value
  | .num (.fin true 0 _) => .num Double.posZero
  | v => v

/-- The work of scanning every record of a `[[MapData]]` or `[[SetData]]` List for a key, as
the keyed operations do: each live record costs one `SameValueZero` comparison
(`valueEqWork`), each deleted record one unit, plus one. -/
def scanWork (ops : SpecOps) (k : Value) : List (Option Value) → ℕ
  | [] => 1
  | some k' :: rest => valueEqWork ops k' k + scanWork ops k rest
  | none :: rest => 1 + scanWork ops k rest

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
def addEntries (ops : SpecOps) (h : Heap) :
    List Value → List (Option (Value × Value)) → ℕ → Option (List (Option (Value × Value)) × ℕ)
  | [], data, w => some (data, w)
  | .ref l :: rest, data, w => match h.get l with
    | some (.array (k :: v :: _)) =>
      addEntries ops h rest (mapPut k v data) (w + 1 + scanWork ops k (mapKeys data))
    | some (.array [k]) =>
      addEntries ops h rest (mapPut k .undef data) (w + 1 + scanWork ops k (mapKeys data))
    | some (.array []) =>
      addEntries ops h rest (mapPut .undef .undef data)
        (w + 1 + scanWork ops .undef (mapKeys data))
    | _ => none
  | _ :: _, _, _ => none

/-- The Set constructor's loop over an Array, calling `Set.prototype.add` per element
(ECMA-262 §24.2.2.1). Each step charges one iterator step plus the `add` it performs. -/
def addElements (ops : SpecOps) : List Value → List (Option Value) → ℕ → List (Option Value) × ℕ
  | [], data, w => (data, w)
  | v :: rest, data, w => addElements ops rest (setPut v data) (w + 1 + scanWork ops v data)

/-- The iterable argument of a keyed-collection constructor, as the Array elements it yields;
`some []` for an absent, `undefined` or `null` iterable. -/
def iterableElems (h : Heap) : List Value → Option (List Value)
  | [] | .undef :: _ | .null :: _ => some []
  | .ref l :: _ => match h.get l with
    | some (.array elems) => some elems
    | _ => none
  | _ :: _ => none

/-- The intrinsics a built-in call consults beyond the built-in itself: the keyed-collection
constructors look up their adder on the new collection's prototype and iterate their Array
argument (§24.1.1.2, §24.2.2.1). -/
def stepIntrinsics : Builtin → Bool → List Intrinsic
  | .mapCtor, true => [.mapPrototype, .arrayPrototype]
  | .setCtor, true => [.setPrototype, .arrayPrototype]
  | _, _ => []

/-- One call of a built-in, as a constructor when `isNew`.

Work per built-in, each the worst-case step count of its ECMA-262 algorithm. `scan(D, k)` is
`scanWork`: one `SameValueZero` comparison per live record of the receiver's `[[MapData]]` or
`[[SetData]]` List `D` and one unit per deleted record, plus one, so every keyed call pays a
full scan of all `|D|` records, deleted records included; a comparison costs one unit, or the
String equality cost of two Strings. `cmp(A, k)` is the same sum over an Array `A`'s elements.
`create`, `lookup` and `append` are the `SpecOps` costs of object creation, property lookup and
List append.

| Built-in | ECMA-262 | Work |
| --- | --- | --- |
| `new Map(iterable)` | §24.1.1.1, §24.1.1.2 | `create + lookup` plus, per entry, `1 + scan(D, key)` |
| `Map.prototype.clear` | §24.1.3.1 | `|D| + 1` |
| `Map.prototype.delete` | §24.1.3.3 | `scan(D, key)` |
| `Map.prototype.get` | §24.1.3.6 | `scan(D, key)` |
| `Map.prototype.has` | §24.1.3.9 | `scan(D, key)` |
| `Map.prototype.set` | §24.1.3.11 | `scan(D, key) + append` |
| `new Set(iterable)` | §24.2.2.1 | `create + lookup` plus, per element, `1 + scan(D, value)` |
| `Set.prototype.add` | §24.2.4.1 | `scan(D, value) + append` |
| `Set.prototype.clear` | §24.2.4.2 | `|D| + 1` |
| `Set.prototype.delete` | §24.2.4.4 | `scan(D, value)` |
| `Set.prototype.has` | §24.2.4.8, §24.2.1.3, §24.2.1.4 | `scan(D, value)` |
| `Array.prototype.includes` | §23.1.3.16 | `cmp(A, searchElement)`; with `fromIndex`, outside the model |
| `Array.prototype.indexOf` | §23.1.3.17 | `cmp(A, searchElement)`; with `fromIndex`, outside the model |
| `Array.prototype.push` | §23.1.3.23 | `items · append + 1` |
| `Array.prototype.sort` | §23.1.3.30 | none: implementation-defined (§2.4) |
| `Array.prototype.toSorted` | §23.1.3.34 | none: implementation-defined (§2.4) |

`sort` and `toSorted` reach `SortIndexedProperties` (§23.1.3.30.1), whose sequence of
`SortCompare` calls ECMA-262 leaves implementation-defined. A `fromIndex` argument runs
`ToIntegerOrInfinity` on it and starts the scan there (§23.1.3.16 steps 4-10, §23.1.3.17 steps
4-10), which the model does not follow, so a call passing one is outside the model. -/
def step (ops : SpecOps) (b : Builtin) (isNew : Bool) (h : Heap) (self : Value)
    (args : List Value) : Step :=
  match b, isNew with
  /- §24.1.1.1 `Map ( [ iterable ] )`: throws without NewTarget; creates `[[MapData]]` and
  runs `AddEntriesFromIterable` (§24.1.1.2) with `Map.prototype.set` as adder. -/
  | .mapCtor, true => match iterableElems h args with
    | some elems => match addEntries ops h elems [] (ops.objectCreate + ops.propertyLookup) with
      | some (data, w) => let (l, h') := h.alloc (.map data); .ok (.ref l) h' w
      | none => .unmodelled
    | none => .unmodelled
  /- §24.2.2.1 `Set ( [ iterable ] )`: throws without NewTarget; calls `Set.prototype.add` per
  element of the iterable. -/
  | .setCtor, true => match iterableElems h args with
    | some elems =>
      let (data, w) := addElements ops elems [] (ops.objectCreate + ops.propertyLookup)
      let (l, h') := h.alloc (.set data)
      .ok (.ref l) h' w
    | none => .unmodelled
  | .mapCtor, false | .setCtor, false => .typeError
  | _, true => .typeError
  /- §24.1.3.6 `Map.prototype.get ( key )`: scans every record of `[[MapData]]`. -/
  | .mapGet, false => withMap h self fun _ data =>
    .ok ((mapFind (arg0 args) data).getD .undef) h (scanWork ops (arg0 args) (mapKeys data))
  /- §24.1.3.9 `Map.prototype.has ( key )`: scans every record of `[[MapData]]`. -/
  | .mapHas, false => withMap h self fun _ data =>
    .ok (.bool (mapFind (arg0 args) data).isSome) h (scanWork ops (arg0 args) (mapKeys data))
  /- §24.1.3.11 `Map.prototype.set ( key, value )`: scans `[[MapData]]`, then overwrites or
  appends. -/
  | .mapSet, false => withMap h self fun l data =>
    .ok self (h.put l (.map (mapPut (arg0 args) (arg0 args.tail) data)))
      (scanWork ops (arg0 args) (mapKeys data) + ops.listAppend)
  /- §24.1.3.3 `Map.prototype.delete ( key )`: scans `[[MapData]]` and empties the record. -/
  | .mapDelete, false => withMap h self fun l data =>
    let (data', found) := mapErase (arg0 args) data
    .ok (.bool found) (h.put l (.map data')) (scanWork ops (arg0 args) (mapKeys data))
  /- §24.1.3.1 `Map.prototype.clear ( )`: empties every record, keeping the List. -/
  | .mapClear, false => withMap h self fun l data =>
    .ok .undef (h.put l (.map (data.map fun _ => none))) (data.length + 1)
  /- §24.2.4.8 `Set.prototype.has ( value )`: `SetDataHas` (§24.2.1.3) via `SetDataIndex`
  (§24.2.1.4), which scans `[[SetData]]`. -/
  | .setHas, false => withSet h self fun _ data =>
    .ok (.bool (setFind (arg0 args) data)) h (scanWork ops (arg0 args) data)
  /- §24.2.4.1 `Set.prototype.add ( value )`: scans `[[SetData]]`, then appends. -/
  | .setAdd, false => withSet h self fun l data =>
    .ok self (h.put l (.set (setPut (arg0 args) data)))
      (scanWork ops (arg0 args) data + ops.listAppend)
  /- §24.2.4.4 `Set.prototype.delete ( value )`: scans `[[SetData]]` and empties the element. -/
  | .setDelete, false => withSet h self fun l data =>
    let (data', found) := setErase (arg0 args) data
    .ok (.bool found) (h.put l (.set data')) (scanWork ops (arg0 args) data)
  /- §24.2.4.2 `Set.prototype.clear ( )`: empties every element, keeping the List. -/
  | .setClear, false => withSet h self fun l data =>
    .ok .undef (h.put l (.set (data.map fun _ => none))) (data.length + 1)
  /- §23.1.3.23 `Array.prototype.push ( ...items )`: one `Set` per item. -/
  | .arrayPush, false => withArray h self fun l elems =>
    let elems' := elems ++ args
    .ok (.num (Double.ofNat elems'.length)) (h.put l (.array elems'))
      (args.length * ops.listAppend + 1)
  /- §23.1.3.17 `Array.prototype.indexOf ( searchElement [ , fromIndex ] )`: scans up to `len`
  indices with `IsStrictlyEqual`; a `fromIndex` is outside the model. -/
  | .arrayIndexOf, false => withArray h self fun _ elems =>
    if 2 ≤ args.length then .unmodelled else
    let i := elems.findIdx (strictEquals · (arg0 args))
    .ok (.num (Double.ofInt (if i < elems.length then (i : ℤ) else -1))) h
      (scanWork ops (arg0 args) (elems.map some))
  /- §23.1.3.16 `Array.prototype.includes ( searchElement [ , fromIndex ] )`: scans up to `len`
  indices with `SameValueZero`; a `fromIndex` is outside the model. -/
  | .arrayIncludes, false => withArray h self fun _ elems =>
    if 2 ≤ args.length then .unmodelled else
    .ok (.bool (elems.any (sameValueZero · (arg0 args)))) h
      (scanWork ops (arg0 args) (elems.map some))
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

/-! ## §2.5 Conformance to declared types

TypeScript's assignability is structural: a value conforms to an object type when it has every
field, whatever its class, and a primitive has the members of its wrapper prototype. `conforms`
follows it for the modelled types, reading each strict-mode rule (`strictNullChecks`, under
which `null` and `undefined` conform only to their own types and `any`):

* `{}` admits every value but `null` and `undefined`; `{x: τ}` admits a value whose own data
  property `x` conforms to `τ`, or whose class has a method `x` conforming to `τ`, or which has
  an accessor `x` (own or on its class, a class getter satisfying a field), or whose built-in
  prototype chain has a member `x` (`{length: number}` admits Strings and Arrays);
* `T[]`, `Map<K, V>` and `Set<T>` admit the built-in collections whose elements conform, and
  every ordinary object carrying each string-keyed member of the TypeScript interface, since
  TypeScript admits a structurally compatible user object. Built-in methods are looked up on
  the value (`Olint.Model.readProp`), so a call on such an object runs its own functions, whose
  work is the program's;
* a function type admits every function object.

The members an interface or a prototype supplies are admitted without checking their types, and
symbol-keyed members, which the model's values cannot carry, are not required, so `conforms`
admits at least every value TypeScript assigns to the type.

Admission is narrower than §2.5 in one respect, pending Matt's reading of the axioms: a
dimension measures only a String or a built-in collection, an Array exotic object, a Map or a
Set (`Olint.Model.Heap.lengthOf`). An instance whose measured argument or free variable is an
ordinary object standing in for a collection conforms to its type but is not admitted, so a
bound over such a dimension covers the built-in collections only. -/

/-- How a value provides a property, for structural typing: the value to check against the
field's type, present with a type the model does not check, or absent. -/
inductive FieldView where
  | value (w : Value)
  | present
  | absent

/-- A property on a built-in prototype chain whose own prototype carries `names`. -/
def protoMember (names : List Name) (x : Name) : FieldView :=
  if objectProtoMembers.contains x || names.contains x then .present else .absent

/-- How value `v` provides property `x` in heap `h`, following its prototype chain. -/
def fieldView (h : Heap) (v : Value) (x : Name) : FieldView :=
  match v with
  | .undef | .null => .absent
  | .bool _ => protoMember booleanProtoMembers x
  | .num _ => protoMember numberProtoMembers x
  | .str s =>
    if x = "length" then .value (.num (Double.ofNat (utf16Length s)))
    else if (arrayIndexKey x).isSome then .present
    else protoMember stringProtoMembers x
  | .builtin _ => protoMember functionProtoMembers x
  | .ref l =>
    match h.get l with
    | some (.ordinary props acc cls) =>
      match props.lookup x with
      | some w => .value w
      | none =>
        if acc.contains x then .present
        else match cls with
          | some c => match h.get c with
            | some (.klass _ ms acc' _) =>
              match ms.lookup x with
              | some ml => .value (.ref ml)
              | none => if acc'.contains x then .present else protoMember [] x
            | _ => protoMember [] x
          | none => protoMember [] x
    | some (.array elems) =>
      if x = "length" then .value (.num (Double.ofNat elems.length))
      else match arrayIndexKey x with
        | some i => match elems[i]? with
          | some w => .value w
          | none => .present
        | none => protoMember arrayProtoMembers x
    | some (.map data) =>
      if x = "size" then .value (.num (Double.ofNat (liveCount data)))
      else protoMember mapProtoMembers x
    | some (.set data) =>
      if x = "size" then .value (.num (Double.ofNat (liveCount data)))
      else protoMember setProtoMembers x
    | some (.closure _ _) | some (.klass _ _ _ _) => protoMember functionProtoMembers x
    | some (.regexp _ _) => protoMember regexpProtoMembers x
    | some (.cell _ _) | some (.uninit _) | none => .absent

/-- The property is absent. -/
def FieldView.isAbsent : FieldView → Bool
  | .absent => true
  | _ => false

/-- An ordinary object carrying every member of an interface, as TypeScript admits for the
interface's type. -/
def impostor (h : Heap) (l : Loc) (names : List Name) : Bool :=
  match h.get l with
  | some (.ordinary _ _ _) => names.all fun x => !(fieldView h (.ref l) x).isAbsent
  | _ => false

mutual

/-- `conforms h v τ`: value `v` conforms to declared type `τ` in heap `h` (§2.5). -/
def conforms (h : Heap) : Value → Ty → Bool
  | _, .any => true
  | .undef, .undefined => true
  | .null, .null => true
  | .bool _, .boolean => true
  | .num _, .number => true
  | .str _, .string => true
  | .builtin _, .func => true
  | .ref l, .func =>
    match h.get l with
    | some (.closure _ _) | some (.klass _ _ _ _) => true
    | _ => false
  | .ref l, .array τ =>
    match h.get l with
    | some (.array elems) => elems.all fun w => conforms h w τ
    | _ => impostor h l arrayInterface
  | .ref l, .map κ τ =>
    match h.get l with
    | some (.map data) => data.all fun e => match e with
      | some (k, w) => conforms h k κ && conforms h w τ
      | none => true
    | _ => impostor h l mapInterface
  | .ref l, .set τ =>
    match h.get l with
    | some (.set data) => data.all fun e => match e with
      | some w => conforms h w τ
      | none => true
    | _ => impostor h l setInterface
  | .undef, .object _ | .null, .object _ => false
  | v, .object fields => conformsFields h v fields
  | _, _ => false

/-- `v` provides every field, each conforming to its type. -/
def conformsFields (h : Heap) (v : Value) : List (Name × Ty) → Bool
  | [] => true
  | (x, τ) :: fs =>
    (match fieldView h v x with
      | .value w => conforms h w τ
      | .present => true
      | .absent => false) && conformsFields h v fs

end

/-- `Conforms h v τ`: value `v` conforms to declared type `τ` in heap `h` (§2.5). -/
def Conforms (h : Heap) (v : Value) (τ : Ty) : Prop := conforms h v τ = true

/-- A type whose values have a length the model measures (`Olint.Model.Heap.lengthOf`):
Strings, Arrays, Maps and Sets, and `any`, which admits them. -/
def Ty.measurable : Ty → Bool
  | .any | .string | .array _ | .map _ _ | .set _ => true
  | _ => false

/-- No name occurs twice. -/
def distinctNames : List Name → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinctNames xs

mutual

/-- A well-formed type: an object type names each field once, as TypeScript requires, so every
well-formed type has a conforming value. -/
def Ty.wf : Ty → Bool
  | .array τ | .set τ => Ty.wf τ
  | .map κ τ => Ty.wf κ && Ty.wf τ
  | .object fields => distinctNames (fields.map Prod.fst) && Ty.wfFields fields
  | _ => true

/-- Every field type is well formed. -/
def Ty.wfFields : List (Name × Ty) → Bool
  | [] => true
  | (_, τ) :: fs => Ty.wf τ && Ty.wfFields fs

end

end Olint.Model

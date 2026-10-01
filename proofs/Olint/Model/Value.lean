import Olint.Model.Syntax

/-!
# Numbers, values and the heap

The runtime state the work semantics runs over. Every variable binding is a heap cell, so
closures share mutable bindings as ECMAScript scopes do. A cell records its binding's declared
type, the type §2.5 says its value conforms to.

Keyed collections keep their `[[MapData]]` and `[[SetData]]` Lists as ECMA-262 describes them
(§24.1.3, §24.2.4): a deleted or cleared entry becomes `none` (the specification's `empty`) and
stays in the List, so the List only grows.

Numbers are ECMAScript Numbers (`Olint.Model.Double`): IEEE-754 binary64 values with `NaN`,
signed zeros and infinities, computed exactly and rounded to nearest, ties to even, as
ECMA-262 §6.1.6.1 specifies. Every operation is a plain structural function over `ℕ` and `ℤ`.
-/

namespace Olint.Model

/-! ## Numbers (ECMA-262 §6.1.6.1) -/

namespace Double

/-- `+0`. -/
def posZero : Double := fin false 0 (-1074)

/-- The Number nearest to `(-1)^neg · (n / d) · 2^e`, rounding to nearest with ties to even,
overflowing to `±∞` and underflowing gradually through the subnormals to a zero of sign `neg`
(ECMA-262 §6.1.6.1: "the Number value for x", IEEE-754-2019 roundTiesToEven). -/
def round (neg : Bool) (n d : ℕ) (e : ℤ) : Double :=
  if n == 0 || d == 0 then fin neg 0 (-1074) else
  -- `n / d · 2^(e - k0)` lies in `(2^51, 2^53)`.
  let k0 : ℤ := e + (Nat.log2 n : ℤ) - (Nat.log2 d : ℤ) - 52
  let s0 := e - k0
  let atLeast : Bool :=
    if 0 ≤ s0 then Nat.ble (2 ^ 52 * d) (n <<< s0.toNat)
    else Nat.ble ((2 ^ 52 * d) <<< (-s0).toNat) n
  let k := max (if atLeast then k0 else k0 - 1) (-1074)
  let s := e - k
  let num := if 0 ≤ s then n <<< s.toNat else n
  let den := if 0 ≤ s then d else d <<< (-s).toNat
  let q := num / den
  let r := num % den
  let q := if Nat.blt den (2 * r) || (2 * r == den && q % 2 == 1) then q + 1 else q
  let k := if q == 2 ^ 53 then k + 1 else k
  let q := if q == 2 ^ 53 then 2 ^ 52 else q
  if 971 < k then inf neg else if q == 0 then fin neg 0 (-1074) else fin neg q k

/-- The canonical form of a Number: a finite value rounded to the nearest double. -/
def normalize : Double → Double
  | fin neg m e => round neg m 1 e
  | d => d

/-- The Number of an integer. -/
def ofInt (z : ℤ) : Double := if z == 0 then posZero else round (decide (z < 0)) z.natAbs 1 0

/-- The Number of a natural number. -/
def ofNat (n : ℕ) : Double := ofInt n

instance (n : ℕ) : OfNat Double n := ⟨ofNat n⟩

/-- A magnitude `m · 2^e` scaled to exponent `e0 ≤ e`. -/
def scaled (m : ℕ) (e e0 : ℤ) : ℕ := m <<< (e - e0).toNat

/-- A signed magnitude. -/
def signed (neg : Bool) (m : ℕ) : ℤ := if neg then -(m : ℤ) else m

/-- `Number::unaryMinus` (§6.1.6.1.1). -/
def neg : Double → Double
  | nan => nan
  | inf s => inf (!s)
  | fin s m e => fin (!s) m e

/-- `Number::add` (§6.1.6.1.7): the exact sum rounded; `x + (-x)` is `+0`, and `-0 + -0` is
`-0`. -/
def add : Double → Double → Double
  | nan, _ | _, nan => nan
  | inf a, inf b => if a == b then inf a else nan
  | inf a, fin _ _ _ => inf a
  | fin _ _ _, inf b => inf b
  | fin s1 m1 e1, fin s2 m2 e2 =>
    let e := min e1 e2
    let sum := signed s1 (scaled m1 e1 e) + signed s2 (scaled m2 e2 e)
    if sum == 0 then fin (s1 && s2) 0 (-1074) else round (decide (sum < 0)) sum.natAbs 1 e

/-- `Number::subtract` (§6.1.6.1.8). -/
def sub (x y : Double) : Double := add x y.neg

/-- `Number::multiply` (§6.1.6.1.4). -/
def mul : Double → Double → Double
  | nan, _ | _, nan => nan
  | inf a, inf b => inf (a != b)
  | inf a, fin b m _ | fin b m _, inf a => if m == 0 then nan else inf (a != b)
  | fin a m1 e1, fin b m2 e2 => round (a != b) (m1 * m2) 1 (e1 + e2)

/-- `Number::divide` (§6.1.6.1.5). -/
def div : Double → Double → Double
  | nan, _ | _, nan => nan
  | inf _, inf _ => nan
  | inf a, fin b _ _ => inf (a != b)
  | fin a _ _, inf b => fin (a != b) 0 (-1074)
  | fin a m1 e1, fin b m2 e2 =>
    if m2 == 0 then (if m1 == 0 then nan else inf (a != b)) else round (a != b) m1 m2 (e1 - e2)

/-- `Number::remainder` (§6.1.6.1.6): the exact remainder of truncating division, with the
sign of the dividend. -/
def rem : Double → Double → Double
  | nan, _ | _, nan => nan
  | inf _, _ => nan
  | fin a m e, inf _ => fin a m e
  | fin a m1 e1, fin _ m2 e2 =>
    if m2 == 0 then nan
    else if m1 == 0 then fin a 0 (-1074)
    else let e := min e1 e2; round a (scaled m1 e1 e % scaled m2 e2 e) 1 e

/-- The order of two Numbers, `none` when either is `NaN`; `-0` and `+0` are equal. -/
def cmp : Double → Double → Option Ordering
  | nan, _ | _, nan => none
  | inf a, inf b => some (if a == b then .eq else if a then .lt else .gt)
  | inf a, fin _ _ _ => some (if a then .lt else .gt)
  | fin _ _ _, inf b => some (if b then .gt else .lt)
  | fin s1 m1 e1, fin s2 m2 e2 =>
    let e := min e1 e2
    some (compare (signed s1 (scaled m1 e1 e)) (signed s2 (scaled m2 e2 e)))

/-- `Number::equal` (§6.1.6.1.13). -/
def equal (x y : Double) : Bool := cmp x y == some .eq

/-- `Number::sameValueZero` (§6.1.6.1.15): `NaN` equals `NaN`, and `-0` equals `+0`. -/
def sameValueZero : Double → Double → Bool
  | nan, nan => true
  | x, y => equal x y

/-- `ToBoolean` of a Number (§7.1.2): false for `NaN` and the zeros. -/
def truthy : Double → Bool
  | nan => false
  | inf _ => true
  | fin _ m _ => m != 0

/-- The integer a finite Number truncates to. -/
def trunc : Double → Option ℤ
  | fin s m e => some (signed s (if 0 ≤ e then m <<< e.toNat else m >>> (-e).toNat))
  | _ => none

/-- The Number is a finite integer. -/
def isIntegral : Double → Bool
  | fin _ m e => decide (0 ≤ e) || m % 2 ^ (-e).toNat == 0
  | _ => false

/-- `ToUint32` (§7.1.7). -/
def toUint32 (d : Double) : ℕ :=
  match trunc d with
  | some z => (z % 2 ^ 32).toNat
  | none => 0

/-- `ToInt32` (§7.1.6). -/
def toInt32 (d : Double) : ℤ :=
  let u := toUint32 d
  if u < 2 ^ 31 then u else (u : ℤ) - 2 ^ 32

/-- The Number of a 32-bit pattern read as a signed integer. -/
def ofInt32Bits (u : ℕ) : Double := ofInt (if u % 2 ^ 32 < 2 ^ 31 then u % 2 ^ 32 else (u % 2 ^ 32 : ℤ) - 2 ^ 32)

/-- The array index a Number denotes as a property key: an integer `k` with
`0 ≤ k < 2^32 - 1`, `-0` reading as `0` (§6.1.7, `ToString` of the key). -/
def toArrayIndex (d : Double) : Option ℕ :=
  match d with
  | fin s m _ =>
    if isIntegral d && (!s || m == 0) then
      match trunc d with
      | some z => if z.natAbs < 2 ^ 32 - 1 then some z.natAbs else none
      | none => none
    else none
  | _ => none

/-- `Number::toString` (§6.1.6.1.20) for the Numbers it renders without a fraction or an
exponent: `NaN`, the infinities, and the integers of magnitude below `10^21`. Other Numbers
are outside the model. -/
def toPropertyString (d : Double) : Option String :=
  match d with
  | nan => some "NaN"
  | inf false => some "Infinity"
  | inf true => some "-Infinity"
  | fin s m _ =>
    if isIntegral d then
      match trunc d with
      | some z =>
        if z.natAbs < 10 ^ 21 then some ((if s && m != 0 then "-" else "") ++ toString z.natAbs)
        else none
      | none => none
    else none

/-- The exact value `m · 2^e` of a finite magnitude, as a numerator and a power-of-two
denominator exponent: `(m · 2^max e 0) / 2^max (-e) 0`. -/
def ratio (m : ℕ) (e : ℤ) : ℕ × ℕ := (m <<< e.toNat, 2 ^ (-e).toNat)

/-- The decimal exponent `n` of a positive finite magnitude `m · 2^e`: the integer with
`10^(n-1) ≤ m · 2^e < 10^n`, the number of decimal digits of the integer part. The magnitude
times `10^400` is at least `1` for every `m ≥ 1` and `e ≥ -1074`, and a rational `q ≥ 1` has as
many decimal digits before its point as `⌊q⌋`. -/
def decimalExponent (m : ℕ) (e : ℤ) : ℤ :=
  let (num, den) := ratio m e
  ((Nat.repr (num * 10 ^ 400 / den)).length : ℤ) - 400

/-- `round(false, s · 10^(n-k))`: the Number nearest a decimal candidate `s · 10^(n - k)`. -/
def ofDecimal (s : ℕ) (n k : ℤ) : Double :=
  if 0 ≤ n - k then round false (s * 10 ^ (n - k).toNat) 1 0
  else round false s (10 ^ (k - n).toNat) 0

/-- The decimal significand of `m · 2^e` at `k` digits, by `Number::toString` step 5
(§6.1.6.1.20): among the two `k`-digit candidates nearest the value, `⌊m · 2^e · 10^(k-n)⌋` and
the next one, those whose Number is the value itself, the nearer, an even one on a tie; with the
exponent `n` it is read at, which a candidate of `10^k` raises by one. `none` when neither
candidate's Number is the value. -/
def significandAt (x : Double) (m : ℕ) (e n k : ℤ) : Option (ℕ × ℤ) :=
  let (num, den) := ratio m e
  -- `m · 2^e · 10^(k-n) = num' / den'`.
  let num' := if 0 ≤ k - n then num * 10 ^ (k - n).toNat else num
  let den' := if 0 ≤ k - n then den else den * 10 ^ (n - k).toNat
  let lo := num' / den'
  let r := num' % den'
  let norm := fun (s : ℕ) => if s == 10 ^ k.toNat then (10 ^ (k.toNat - 1), n + 1) else (s, n)
  let ok := fun (s : ℕ) => let (s', n') := norm s; decide (1 ≤ s') && ofDecimal s' n' k == x
  let hi := lo + 1
  if r == 0 then (if ok lo then some (norm lo) else none)
  else match ok lo, ok hi with
    | true, true =>
      -- The nearer of the two; on a tie, the even one.
      if 2 * r < den' || (2 * r == den' && lo % 2 == 0) then some (norm lo) else some (norm hi)
    | true, false => some (norm lo)
    | false, true => some (norm hi)
    | false, false => none

/-- The `k`, `s` and `n` of `Number::toString` step 5 for a positive finite Number `m · 2^e`:
the least digit count `k` with a significand (`significandAt`). Every binary64 value has one
with at most 17 digits (IEEE 754-2019 §5.12.2: 17 significant decimal digits identify every
binary64 value), so the search stops by `k = 17`. -/
def shortest (x : Double) (m : ℕ) (e : ℤ) : Option (ℕ × ℕ × ℤ) :=
  let n := decimalExponent m e
  ((List.range 17).map (· + 1)).findSome? fun (k : ℕ) =>
    (significandAt x m e n k).map fun (s, n') => (k, s, n')

/-- `Number::toString(x, 10)` (ECMA-262 §6.1.6.1.20). The result has at most 25 characters: a
sign, then at most 21 digits (step 6, `n ≤ 21`), `0.`, five zeros and 17 digits (step 8,
`n > -6`, `k ≤ 17`), or 17 digits, a point, `e`, a sign and three exponent digits (steps 9 and
10, `|n - 1| ≤ 324`). -/
def toString (x : Double) : String :=
  match x with
  | nan => "NaN"
  | inf false => "Infinity"
  | inf true => "-Infinity"
  | fin neg m e =>
    if m == 0 then "0" else
    let sign := if neg then "-" else ""
    match shortest (fin false m e).normalize m e with
    | none => sign ++ "NaN"
    | some (k, s, n) =>
      let digits := Nat.repr s
      let k : ℤ := k
      let exponent := fun (n : ℤ) =>
        "e" ++ (if 0 ≤ n - 1 then "+" else "-") ++ Nat.repr (n - 1).natAbs
      sign ++
        if k ≤ n ∧ n ≤ 21 then digits ++ String.ofList (List.replicate (n - k).toNat '0')
        else if 0 < n ∧ n ≤ 21 then
          String.ofList (digits.toList.take n.toNat) ++ "." ++
            String.ofList (digits.toList.drop n.toNat)
        else if -6 < n ∧ n ≤ 0 then
          "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ digits
        else if k = 1 then digits ++ exponent n
        else String.ofList (digits.toList.take 1) ++ "." ++
          String.ofList (digits.toList.drop 1) ++ exponent n

end Double

/-! ## Strings -/

/-- The length of a String in UTF-16 code units, as ECMAScript measures it (§6.1.4). The model's
strings hold Unicode scalar values, so a code point above `U+FFFF` is two code units. -/
def utf16Length (s : String) : ℕ :=
  s.toList.foldl (fun n c => n + if 0xFFFF < c.toNat then 2 else 1) 0

/-- The digit value of a decimal digit character. -/
def digitVal (c : Char) : Option ℕ :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- The array index a String property key denotes: its canonical decimal form of an integer
below `2^32 - 1` (§6.1.7). -/
def arrayIndexKey (x : String) : Option ℕ :=
  match x.toList with
  | [] => none
  | c :: cs =>
    if c == '0' && !cs.isEmpty then none
    else
      match (c :: cs).foldl (fun acc c => acc.bind fun n => (digitVal c).map (n * 10 + ·))
          (some 0) with
      | some n => if n < 2 ^ 32 - 1 then some n else none
      | none => none

/-! ## Values and the heap -/

/-- A heap location. -/
abbrev Loc := ℕ

/-- An environment maps names to the heap cells holding their values. -/
abbrev Env := List (Name × Loc)

/-- The modelled built-in functions and methods. Their behaviour and work are fixed
definitions in `Olint.Axioms` (§2.2). -/
inductive Builtin where
  | mapCtor | mapGet | mapHas | mapSet | mapDelete | mapClear
  | setCtor | setHas | setAdd | setDelete | setClear
  | arrayPush | arrayIndexOf | arrayIncludes | arraySort | arrayToSorted
  deriving DecidableEq, Repr

/-- ECMAScript language values. Objects live on the heap behind `ref`. -/
inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (n : Double)
  | str (s : String)
  | ref (l : Loc)
  /-- A built-in function object, fixed by `Olint.Axioms`. -/
  | builtin (b : Builtin)
  deriving DecidableEq, Repr

/-- Heap objects. -/
inductive Obj where
  /-- An initialized variable binding and its declared type (§2.5; `any` when undeclared). -/
  | cell (v : Value) (ty : Ty)
  /-- A `let`, `const` or `class` binding created at its scope's entry and not yet initialized:
  the temporal dead zone of ECMA-262 §9.1.1.1.1 `CreateMutableBinding`, where reading or
  writing the binding throws a ReferenceError (§9.1.1.1.6 `GetBindingValue`). -/
  | uninit (ty : Ty)
  /-- An ordinary object: its own data properties in creation order, the names of its own
  accessor properties, and the class it was constructed from, whose prototype is its
  `[[Prototype]]`. Without a class its `[[Prototype]]` is `%Object.prototype%`, as for every
  object literal (ECMA-262 §13.2.5.5, `OrdinaryObjectCreate(%Object.prototype%)`). The model
  runs no accessor: reading or writing one aborts as outside the model. -/
  | ordinary (props : List (Name × Value)) (accessors : List Name) (cls : Option Loc)
  /-- An Array exotic object, whose `[[Prototype]]` is `%Array.prototype%`. -/
  | array (elems : List Value)
  /-- A Map, holding its `[[MapData]]` List; `none` is a deleted entry. -/
  | map (data : List (Option (Value × Value)))
  /-- A Set, holding its `[[SetData]]` List; `none` is a deleted element. -/
  | set (data : List (Option Value))
  /-- A function closure over its defining environment. A non-arrow call binds `this` in the
  callee's environment under the reserved name `"this"`. -/
  | closure (f : Func) (env : Env)
  /-- A class over its defining environment: its constructor, the closures of its prototype
  methods, created once when the class is evaluated (ECMA-262 §15.7.14
  `ClassDefinitionEvaluation`), and the names of its prototype accessors, which the model does
  not run. The prototype's `[[Prototype]]` is `%Object.prototype%`. -/
  | klass (ctor : Option Func) (methods : List (Name × Loc)) (accessors : List Name) (env : Env)
  /-- A RegExp object. -/
  | regexp (pattern flags : String)

/-- The heap: a partial map from locations and the next free location. -/
structure Heap where
  next : Loc
  get : Loc → Option Obj

namespace Heap

/-- The empty heap. -/
def empty : Heap := ⟨0, fun _ => none⟩

/-- Allocate an object, returning its location. -/
def alloc (h : Heap) (o : Obj) : Loc × Heap :=
  (h.next, ⟨h.next + 1, fun l => if l = h.next then some o else h.get l⟩)

/-- Overwrite the object at a location. -/
def put (h : Heap) (l : Loc) (o : Obj) : Heap :=
  ⟨h.next, fun l' => if l' = l then some o else h.get l'⟩

end Heap

/-- ECMAScript `SameValueZero` (§7.2.11): Numbers by `Number::sameValueZero`, other primitives
by value, objects by identity. -/
def sameValueZero : Value → Value → Bool
  | .num x, .num y => Double.sameValueZero x y
  | a, b => decide (a = b)

/-- ECMAScript `IsStrictlyEqual` (§7.2.15): Numbers by `Number::equal`, so `NaN` differs from
itself and `-0` equals `+0`; other values as `SameValueNonNumber`. -/
def strictEquals : Value → Value → Bool
  | .num x, .num y => Double.equal x y
  | a, b => decide (a = b)

end Olint.Model

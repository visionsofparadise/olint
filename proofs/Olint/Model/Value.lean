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
  /-- A variable binding and its declared type (§2.5; `any` when undeclared). -/
  | cell (v : Value) (ty : Ty)
  /-- An ordinary object with its own properties in creation order, and the class it was
  constructed from. -/
  | ordinary (props : List (Name × Value)) (cls : Option Loc)
  /-- An Array exotic object. -/
  | array (elems : List Value)
  /-- A Map, holding its `[[MapData]]` List; `none` is a deleted entry. -/
  | map (data : List (Option (Value × Value)))
  /-- A Set, holding its `[[SetData]]` List; `none` is a deleted element. -/
  | set (data : List (Option Value))
  /-- A function closure over its defining environment. A non-arrow call binds `this` in the
  callee's environment under the reserved name `"this"`. -/
  | closure (f : Func) (env : Env)
  /-- A class over its defining environment. -/
  | klass (c : Class) (env : Env)
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

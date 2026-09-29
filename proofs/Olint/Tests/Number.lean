import Olint.Model.Value

/-!
# Number semantics

ECMAScript Number results of `Olint.Model.Double`, checked by kernel `decide` against the values
IEEE-754 binary64 arithmetic gives.
-/

namespace Olint.Tests.Number

open Olint.Model Double

/-- `0.1 + 0.2` is `0.30000000000000004`. -/
example : add (fin false 3602879701896397 (-55)) (fin false 3602879701896397 (-54)) =
    fin false 5404319552844596 (-54) := by decide

/-- `2^53 + 1` rounds to even, `2^53`; `2^53 + 3` rounds to `2^53 + 4`. -/
example : add (ofNat (2 ^ 53)) 1 = ofNat (2 ^ 53) := by decide
example : add (ofNat (2 ^ 53)) 3 = ofNat (2 ^ 53 + 4) := by decide

/-- `1 / 0` is `Infinity`, `-1 / 0` is `-Infinity`, `0 / 0` is `NaN`. -/
example : div 1 0 = inf false := by decide
example : div (neg 1) 0 = inf true := by decide
example : div 0 0 = nan := by decide

/-- `-7 % 2` is `-1`; `7 % -2` is `1`. -/
example : rem (ofInt (-7)) 2 = ofInt (-1) := by decide
example : rem 7 (neg 2) = 1 := by decide

/-- `-0 + -0` is `-0`; `1 + -1` is `+0`; `-0 === +0`; `NaN !== NaN`; `SameValueZero(NaN, NaN)`. -/
example : add (neg 0) (neg 0) = fin true 0 (-1074) := by decide
example : add 1 (neg 1) = posZero := by decide
example : equal (neg 0) 0 = true := by decide
example : equal nan nan = false := by decide
example : sameValueZero nan nan = true := by decide

/-- `ToInt32(2^31)` is `-2^31`; `ToUint32(-1)` is `2^32 - 1`. -/
example : toInt32 (ofNat (2 ^ 31)) = -(2 ^ 31) := by decide
example : toUint32 (ofInt (-1)) = 2 ^ 32 - 1 := by decide

/-- The largest double times two overflows to `Infinity`; half the least subnormal rounds to
`+0`. -/
example : mul (fin false (2 ^ 53 - 1) 971) 2 = inf false := by decide
example : mul (fin false 1 (-1074)) (fin false 1 (-1)) = posZero := by decide

end Olint.Tests.Number

import Olint.Certificate

/-!
# End-to-end certificate checks

Concrete certificates checked by kernel `decide`, in the shape the corpus generator writes
(`check_sound _ _ <derivation> (by decide)`), so `lake build` exercises the pipeline end to end.
-/

namespace Olint.Tests

open Olint Olint.Model

/-- A program with no definitions. -/
def program : Program := ⟨[]⟩

/-- `function f(xs: number[]) { 1; let x = 2; if (true) { 3; } else { let y = 4; } }`, costed
over the length of `xs`. -/
def entry : Entry :=
  ⟨.mk [("xs", .array .number)]
    [.expr (.lit (.num 1)), .decl .«let» "x" .any (some (.lit (.num 2))),
      .ite (.lit (.bool true)) (.block [.expr (.lit (.num 3))])
        (some (.block [.decl .«let» "y" .any (some (.lit (.num 4)))]))] false,
    [], [(0, .arg 0)]⟩

/-- `{ 1; let x = 2; }`: a sequence of two constant statements. -/
def block : Node :=
  ⟨entry, .stmt (.block [.expr (.lit (.num 1)), .decl .«let» "x" .any (some (.lit (.num 2)))])⟩

/-- `seq-max`, unit base: the block is `O(1)`. -/
theorem c_unit : Bound program block (.constant 1) :=
  check_sound _ _ .seqUnit (by decide)

/-- A chain through `product-normalise`, `max-normalise`, `max-dominance` and `expr-validity`:
`1 = 1·1`, then `O(max(3, 1·1))`, then `O(n₀ · log n₀)`. -/
theorem c_chain : Bound program block
    (.product [.dimension 0 .size, .log (.dimension 0 .size)]) :=
  check_sound _ _
    (.exprValidity
      (.maxDominance
        (.maxNormalise
          (.productNormalise .seqUnit (.product [.constant 1, .constant 1]))
          (.maximum [.constant 3, .product [.constant 1, .constant 1]]))
        (.product [.dimension 0 .size, .log (.dimension 0 .size)])))
    (by decide)

/-- `seq-max` composing child certificates: the block from one unit certificate per
statement. -/
theorem c_seq : Bound program block (.maximum [.constant 1, .constant 1]) :=
  check_sound _ _ (.seqMax [.seqUnit, .seqUnit]) (by decide)

/-- `branch-join` composing child certificates: the `if` from its literal test and a `seq-max`
certificate per branch. -/
theorem c_branch : Bound program
    ⟨entry, .stmt (.ite (.lit (.bool true)) (.block [.expr (.lit (.num 3))])
      (some (.block [.decl .«let» "y" .any (some (.lit (.num 4)))])))⟩
    (.maximum [.constant 1, .maximum [.constant 1], .maximum [.constant 1]]) :=
  check_sound _ _ (.branchJoin [.seqUnit, .seqMax [.seqUnit], .seqMax [.seqUnit]]) (by decide)

/-- The entry itself, composed from its body: `seq-max` over two unit statements and the
`branch-join` above, then `max-normalise` to `O(1)`. -/
theorem c_entry : Bound program ⟨entry, .entry⟩ (.constant 1) :=
  check_sound _ _
    (.maxNormalise
      (.seqMax [.seqUnit, .seqUnit,
        .maxNormalise (.branchJoin [.seqUnit, .seqMax [.seqUnit], .seqMax [.seqUnit]])
          (.constant 1)])
      (.constant 1))
    (by decide)

/-- `channel-total` composing bounds on channel sets that cover every channel. -/
theorem c_channel : Bound program block (.maximum [.constant 1, .maximum [.constant 1, .constant 1]]) :=
  check_sound _ _
    (.channelTotal [([.normal, .brk], .seqUnit), ([.ret, .cont], .seqMax [.seqUnit, .seqUnit])])
    (by decide)

/-- The entry's bound bounds its `Work`. -/
example : ∀ᶠ i in Admits program entry, Halts program i entry :=
  (Bound.work_isBigO (n := ⟨entry, .entry⟩) rfl c_entry).1

end Olint.Tests

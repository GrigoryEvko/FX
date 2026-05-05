import LeanFX2.Graded.Semiring

/-! # Graded/Instances/NatResource — axiom-clean Nat semiring lemmas

Lean 4.29.1's built-in `Nat.mul_assoc` and `Nat.right_distrib` print
`propext` in this project configuration.  Numeric grade instances need
the same facts without leaking axioms, so this file proves the two
lemmas from axiom-clean primitives.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances.NatResource

/-- Right distributivity of natural-number multiplication, proved
from axiom-clean commutativity and left distributivity. -/
theorem mulRightDistribClean
    (leftBound rightBound scalarBound : Nat) :
    (leftBound + rightBound) * scalarBound =
      leftBound * scalarBound + rightBound * scalarBound := by
  rw [Nat.mul_comm (leftBound + rightBound) scalarBound]
  rw [Nat.left_distrib]
  rw [Nat.mul_comm scalarBound leftBound]
  rw [Nat.mul_comm scalarBound rightBound]

/-- Associativity of natural-number multiplication, proved by
induction without using Lean's `Nat.mul_assoc` theorem. -/
theorem mulAssocClean
    (firstBound secondBound thirdBound : Nat) :
    firstBound * secondBound * thirdBound =
      firstBound * (secondBound * thirdBound) := by
  induction firstBound with
  | zero =>
      exact Eq.trans
        (congrArg (fun valueBound => valueBound * thirdBound)
          (Nat.zero_mul secondBound))
        (Eq.trans
          (Nat.zero_mul thirdBound)
          (Eq.symm (Nat.zero_mul (secondBound * thirdBound))))
  | succ previousBound inductionHypothesis =>
      rw [
        Nat.succ_mul,
        Nat.succ_mul,
        mulRightDistribClean,
        inductionHypothesis
      ]

end LeanFX2.Graded.Instances.NatResource

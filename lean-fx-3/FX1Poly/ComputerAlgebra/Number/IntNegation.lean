import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # Negation versus addition and multiplication

Init's `Int.neg_add`, `Int.neg_mul`, and `Int.mul_neg` leak `propext`; this module rebuilds
all three. Two helpers support them:

  * `intNegNegOfNat` — negation undoes `negOfNat`; both arms definitional.
  * `intNegSubNatNat` — negation flips the arguments of a `subNatNat`, by double recursion:
    the right-zero column via `intSubNatNatZeroRight` and `intNegOfNatEqSubNatNatZero`, the
    left-zero column definitional up to `intSubNatNatZeroRight`, and the step case via
    `intSubNatNatSuccSucc` on both sides of the inductive hypothesis.

`intNegAdd` is a four-way constructor case split (the mixed `Int.add` arms are `subNatNat`
calls that negation flips onto the `negOfNat` addition helpers); `intNegMul` collapses
through the mixed-sign multiplication helpers; `intMulNeg` follows via `intMulComm`.

Structural recursion with `congrArg`/`Eq.trans` chains over `Nat.succ_add` and the corpus
kit; free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, and
`omega`; per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-- Negation undoes `negOfNat`; both arms definitional. -/
theorem intNegNegOfNat : ∀ value : Nat, -(Int.negOfNat value) = Int.ofNat value
  | 0 => rfl
  | _ + 1 => rfl

/-- Negation flips `subNatNat`'s arguments. Double recursion: right-zero column via
`intSubNatNatZeroRight` and `intNegOfNatEqSubNatNatZero`, left-zero column definitional up
to `intSubNatNatZeroRight`, step case via `intSubNatNatSuccSucc`. -/
theorem intNegSubNatNat : ∀ leftValue rightValue : Nat,
    -(Int.subNatNat leftValue rightValue) = Int.subNatNat rightValue leftValue
  | leftValue, 0 =>
      (congrArg Int.neg (intSubNatNatZeroRight leftValue)).trans
        (intNegOfNatEqSubNatNatZero leftValue)
  | 0, rightValue + 1 => (intSubNatNatZeroRight (rightValue + 1)).symm
  | leftValue + 1, rightValue + 1 =>
      (congrArg Int.neg (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intNegSubNatNat leftValue rightValue).trans
          (intSubNatNatSuccSucc rightValue leftValue).symm)

/-- Negation distributes over addition. Four-way constructor case split: same-sign arms
land on the `negOfNat` addition helpers (or a `Nat.succ_add` shuffle), mixed arms are
`subNatNat` calls flipped by `intNegSubNatNat`. -/
theorem intNegAdd : ∀ leftSummand rightSummand : Int,
    -(leftSummand + rightSummand) = -leftSummand + -rightSummand
  | .ofNat leftValue, .ofNat rightValue =>
      (intNegOfNatAddNegOfNat leftValue rightValue).symm
  | .ofNat leftValue, .negSucc rightPredecessor =>
      (intNegSubNatNat leftValue (rightPredecessor + 1)).trans
        (intNegOfNatAddOfNat leftValue (rightPredecessor + 1)).symm
  | .negSucc leftPredecessor, .ofNat rightValue =>
      (intNegSubNatNat rightValue (leftPredecessor + 1)).trans
        (intOfNatAddNegOfNat (leftPredecessor + 1) rightValue).symm
  | .negSucc leftPredecessor, .negSucc rightPredecessor =>
      (congrArg (fun sumValue => Int.ofNat (sumValue + 1))
        (Nat.succ_add leftPredecessor rightPredecessor)).symm

/-- Negating the left factor negates the product. Four-way case split through the
mixed-sign multiplication helpers and `intNegNegOfNat`; the double-`negSucc` arm is
definitional. -/
theorem intNegMul : ∀ leftFactor rightFactor : Int,
    -leftFactor * rightFactor = -(leftFactor * rightFactor)
  | .ofNat leftValue, .ofNat rightValue => intNegOfNatMulOfNat leftValue rightValue
  | .ofNat leftValue, .negSucc rightPredecessor =>
      (intNegOfNatMulNegSucc leftValue rightPredecessor).trans
        (intNegNegOfNat (leftValue * (rightPredecessor + 1))).symm
  | .negSucc leftPredecessor, .ofNat rightValue =>
      (intNegNegOfNat ((leftPredecessor + 1) * rightValue)).symm
  | .negSucc _, .negSucc _ => rfl

/-- Negating the right factor negates the product, a corollary of `intNegMul` through
`intMulComm`. -/
theorem intMulNeg (leftFactor rightFactor : Int) :
    leftFactor * -rightFactor = -(leftFactor * rightFactor) :=
  (intMulComm leftFactor (-rightFactor)).trans
    ((intNegMul rightFactor leftFactor).trans
      (congrArg Int.neg (intMulComm rightFactor leftFactor)))

/-- Negation swaps a difference: `-(minuend - subtrahend) = subtrahend - minuend`.
Subtraction is addition of the negation, so this is `intNegAdd`, `intNegNeg`, and one
commutation. -/
theorem intNegSub (minuend subtrahend : Int) :
    -(minuend - subtrahend) = subtrahend - minuend :=
  (intNegAdd minuend (-subtrahend)).trans
    ((congrArg (-minuend + ·) (intNegNeg subtrahend)).trans
      (intAddComm (-minuend) subtrahend))

end FX1Poly.ComputerAlgebra

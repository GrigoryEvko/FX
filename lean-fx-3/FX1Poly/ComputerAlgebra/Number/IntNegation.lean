import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # FX1Poly/ComputerAlgebra/Number/IntNegation — negation vs add/mul
    (FLOAT-1 brick 6)

Init's `Int.neg_add` / `Int.neg_mul` / `Int.mul_neg` are propext-dirty; this module
hand-rolls all three.  Two new helpers on top of the brick-2..5 substrate:

  * `intNegNegOfNat` — negation undoes `negOfNat`; both arms definitional.
  * `intNegSubNatNat` — negation FLIPS the arguments of a `subNatNat`.  Same double
    recursion as the brick-3 add bridges: the right-zero column goes through
    `intSubNatNatZeroRight` + `intNegOfNatEqSubNatNatZero`, the left-zero column is
    definitional up to `intSubNatNatZeroRight`, and the step case is
    `intSubNatNatSuccSucc` on both sides of the inductive hypothesis.

`intNegAdd` is then a four-way constructor bash (the mixed `Int.add` arms are `subNatNat`
calls, so negation flips them straight onto the brick-4 `negOfNat` addition kit);
`intNegMul` collapses through the brick-5 mixed-sign mul helpers; `intMulNeg` is the
corollary through `intMulComm`.

## Zero-axiom

Structural recursion + `congrArg`/`Eq.trans` chains over clean Nat lemmas
(`Nat.succ_add`) and the brick-2..5 kits.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntNegation.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The negation helpers -/

/-- Negation undoes `negOfNat` — both arms definitional (`-(ofNat 0)` reduces to
`negOfNat 0` which is `ofNat 0`; `-(negSucc m)` reduces to `ofNat (m + 1)`). -/
theorem intNegNegOfNat : ∀ value : Nat, -(Int.negOfNat value) = Int.ofNat value
  | 0 => rfl
  | _ + 1 => rfl

/-- **Negation flips `subNatNat`'s arguments.**  Double recursion in the brick-3 shape:
right-zero column via `intSubNatNatZeroRight` + `intNegOfNatEqSubNatNatZero`, left-zero
column definitional up to `intSubNatNatZeroRight`, step case via `intSubNatNatSuccSucc`
on both sides of the inductive hypothesis. -/
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

/-! ## Negation vs addition -/

/-- **Negation distributes over addition** (Init's `Int.neg_add` is propext-dirty).
Four-way constructor bash: the same-sign arms land on the brick-4 `negOfNat` addition
kit (or one `Nat.succ_add` shuffle), the mixed arms are `subNatNat` calls flipped by
`intNegSubNatNat`. -/
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

/-! ## Negation vs multiplication -/

/-- **Negating the left factor negates the product** (Init's `Int.neg_mul` is
propext-dirty).  Four-way bash through the brick-5 mixed-sign mul helpers and
`intNegNegOfNat`; the double-`negSucc` arm is definitional. -/
theorem intNegMul : ∀ leftFactor rightFactor : Int,
    -leftFactor * rightFactor = -(leftFactor * rightFactor)
  | .ofNat leftValue, .ofNat rightValue => intNegOfNatMulOfNat leftValue rightValue
  | .ofNat leftValue, .negSucc rightPredecessor =>
      (intNegOfNatMulNegSucc leftValue rightPredecessor).trans
        (intNegNegOfNat (leftValue * (rightPredecessor + 1))).symm
  | .negSucc leftPredecessor, .ofNat rightValue =>
      (intNegNegOfNat ((leftPredecessor + 1) * rightValue)).symm
  | .negSucc _, .negSucc _ => rfl

/-- **Negating the right factor negates the product** (Init's `Int.mul_neg` is
propext-dirty) — corollary of `intNegMul` through `intMulComm`. -/
theorem intMulNeg (leftFactor rightFactor : Int) :
    leftFactor * -rightFactor = -(leftFactor * rightFactor) :=
  (intMulComm leftFactor (-rightFactor)).trans
    ((intNegMul rightFactor leftFactor).trans
      (congrArg Int.neg (intMulComm rightFactor leftFactor)))

end FX1Poly.ComputerAlgebra

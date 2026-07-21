import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # The multiplication bridges and distributivity

Init's `Int.mul_add` / `Int.add_mul` leak `propext`, so both are hand-rolled here. Two
pieces sit on top of the `subNatNat` substrate:

  * The `negOfNat` addition kit (`intOfNatAddNegOfNat` / `intNegOfNatAddOfNat` /
    `intNegOfNatAddNegOfNat` / `intNegOfNatEqSubNatNatZero`) — the mixed-sign `Int.mul`
    arms produce `negOfNat`, so distributivity's right-hand sides are sums over `negOfNat`;
    each lemma is a two-case split closing by `rfl` or one `congrArg`.
  * The two mul-over-`subNatNat` bridges (`intOfNatMulSubNatNat` / `intNegSuccMulSubNatNat`):
    multiplication distributes into both arguments of a `subNatNat`, flipping them under a
    negative factor. The step case is `intSubNatNatShiftInvariant`, because `k * (m + 1)`
    is definitionally `k * m + k`, shifting both arguments by the factor.
  * `intLeftDistrib` is then the eight-way constructor bash (every mixed case lands on a
    shared `subNatNat`/`negOfNat` form), and `intRightDistrib` is its corollary through
    `intMulComm`.

Structural recursion with `congrArg`/`Eq.trans` chains over clean Nat lemmas
(`Nat.left_distrib`, `Nat.succ_add`, `Nat.zero_add`); free of `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, and `omega`; per-declaration gated in the
audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The negOfNat addition kit -/

/-- `negOfNat` is the left-zero column of `subNatNat` — both match the same way. -/
theorem intNegOfNatEqSubNatNatZero : ∀ value : Nat, Int.negOfNat value = Int.subNatNat 0 value
  | 0 => rfl
  | _ + 1 => rfl

/-- `ofNat + negOfNat` IS `subNatNat` — the two-case split is definitional up to
`subNatNat value 0`. -/
theorem intOfNatAddNegOfNat : ∀ headValue tailValue : Nat,
    Int.ofNat headValue + Int.negOfNat tailValue = Int.subNatNat headValue tailValue
  | headValue, 0 => (intSubNatNatZeroRight headValue).symm
  | _, _ + 1 => rfl

/-- `negOfNat + ofNat` IS the flipped `subNatNat` — corollary through `intAddComm`. -/
theorem intNegOfNatAddOfNat (headValue tailValue : Nat) :
    Int.negOfNat headValue + Int.ofNat tailValue = Int.subNatNat tailValue headValue :=
  (intAddComm (Int.negOfNat headValue) (Int.ofNat tailValue)).trans
    (intOfNatAddNegOfNat tailValue headValue)

/-- `negOfNat` is additive. -/
theorem intNegOfNatAddNegOfNat : ∀ headValue tailValue : Nat,
    Int.negOfNat headValue + Int.negOfNat tailValue = Int.negOfNat (headValue + tailValue)
  | 0, 0 => rfl
  | 0, tailValue + 1 => congrArg Int.negOfNat (Nat.zero_add (tailValue + 1)).symm
  | _ + 1, 0 => rfl
  | headValue + 1, tailValue + 1 =>
      congrArg Int.negSucc (Nat.succ_add headValue tailValue).symm

/-! ## The mul-over-subNatNat bridges -/

/-- Mul bridge (nonnegative factor): an `ofNat` factor distributes into both arguments of
a `subNatNat`. The step case is `intSubNatNatShiftInvariant`, because `factor * (value + 1)`
is definitionally `factor * value + factor`. -/
theorem intOfNatMulSubNatNat (factorValue : Nat) : ∀ leftValue rightValue : Nat,
    Int.ofNat factorValue * Int.subNatNat leftValue rightValue =
      Int.subNatNat (factorValue * leftValue) (factorValue * rightValue)
  | leftValue, 0 =>
      (congrArg (Int.ofNat factorValue * ·) (intSubNatNatZeroRight leftValue)).trans
        (intSubNatNatZeroRight (factorValue * leftValue)).symm
  | 0, rightValue + 1 => intNegOfNatEqSubNatNatZero (factorValue * (rightValue + 1))
  | leftValue + 1, rightValue + 1 =>
      (congrArg (Int.ofNat factorValue * ·) (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intOfNatMulSubNatNat factorValue leftValue rightValue).trans
          (intSubNatNatShiftInvariant (factorValue * leftValue) (factorValue * rightValue)
            factorValue).symm)

/-- Mul bridge (negative factor): a `negSucc` factor distributes into a `subNatNat` and
flips its arguments; same shape as the nonnegative bridge. -/
theorem intNegSuccMulSubNatNat (factorPredecessor : Nat) : ∀ leftValue rightValue : Nat,
    Int.negSucc factorPredecessor * Int.subNatNat leftValue rightValue =
      Int.subNatNat ((factorPredecessor + 1) * rightValue)
        ((factorPredecessor + 1) * leftValue)
  | leftValue, 0 =>
      (congrArg (Int.negSucc factorPredecessor * ·) (intSubNatNatZeroRight leftValue)).trans
        (intNegOfNatEqSubNatNatZero ((factorPredecessor + 1) * leftValue))
  | 0, rightValue + 1 =>
      (intSubNatNatZeroRight ((factorPredecessor + 1) * (rightValue + 1))).symm
  | leftValue + 1, rightValue + 1 =>
      (congrArg (Int.negSucc factorPredecessor * ·)
          (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intNegSuccMulSubNatNat factorPredecessor leftValue rightValue).trans
          (intSubNatNatShiftInvariant ((factorPredecessor + 1) * rightValue)
            ((factorPredecessor + 1) * leftValue) (factorPredecessor + 1)).symm)

/-! ## Distributivity -/

/-- Left distributivity (Init's `Int.mul_add` leaks `propext`). Eight-way constructor
bash: the mixed cases collapse through the mul bridges and the `negOfNat` addition kit onto
a shared `subNatNat`/`negOfNat` form; the double-`negSucc` summand cases need one
`Nat.succ_add` shuffle before `Nat.left_distrib`. -/
theorem intLeftDistrib : ∀ factor leftSummand rightSummand : Int,
    factor * (leftSummand + rightSummand) = factor * leftSummand + factor * rightSummand
  | .ofNat factorNat, .ofNat leftNat, .ofNat rightNat =>
      congrArg Int.ofNat (Nat.left_distrib factorNat leftNat rightNat)
  | .ofNat factorNat, .ofNat leftNat, .negSucc rightPredecessor =>
      (intOfNatMulSubNatNat factorNat leftNat (rightPredecessor + 1)).trans
        (intOfNatAddNegOfNat (factorNat * leftNat)
          (factorNat * (rightPredecessor + 1))).symm
  | .ofNat factorNat, .negSucc leftPredecessor, .ofNat rightNat =>
      (intOfNatMulSubNatNat factorNat rightNat (leftPredecessor + 1)).trans
        (intNegOfNatAddOfNat (factorNat * (leftPredecessor + 1))
          (factorNat * rightNat)).symm
  | .ofNat factorNat, .negSucc leftPredecessor, .negSucc rightPredecessor =>
      (congrArg Int.negOfNat
          ((congrArg (factorNat * ·)
              (congrArg Nat.succ (Nat.succ_add leftPredecessor rightPredecessor).symm)).trans
            (Nat.left_distrib factorNat (leftPredecessor + 1) (rightPredecessor + 1)))).trans
        (intNegOfNatAddNegOfNat (factorNat * (leftPredecessor + 1))
          (factorNat * (rightPredecessor + 1))).symm
  | .negSucc factorPredecessor, .ofNat leftNat, .ofNat rightNat =>
      (congrArg Int.negOfNat
          (Nat.left_distrib (factorPredecessor + 1) leftNat rightNat)).trans
        (intNegOfNatAddNegOfNat ((factorPredecessor + 1) * leftNat)
          ((factorPredecessor + 1) * rightNat)).symm
  | .negSucc factorPredecessor, .ofNat leftNat, .negSucc rightPredecessor =>
      (intNegSuccMulSubNatNat factorPredecessor leftNat (rightPredecessor + 1)).trans
        (intNegOfNatAddOfNat ((factorPredecessor + 1) * leftNat)
          ((factorPredecessor + 1) * (rightPredecessor + 1))).symm
  | .negSucc factorPredecessor, .negSucc leftPredecessor, .ofNat rightNat =>
      (intNegSuccMulSubNatNat factorPredecessor rightNat (leftPredecessor + 1)).trans
        (intOfNatAddNegOfNat ((factorPredecessor + 1) * (leftPredecessor + 1))
          ((factorPredecessor + 1) * rightNat)).symm
  | .negSucc factorPredecessor, .negSucc leftPredecessor, .negSucc rightPredecessor =>
      congrArg Int.ofNat
        ((congrArg ((factorPredecessor + 1) * ·)
            (congrArg Nat.succ (Nat.succ_add leftPredecessor rightPredecessor).symm)).trans
          (Nat.left_distrib (factorPredecessor + 1) (leftPredecessor + 1)
            (rightPredecessor + 1)))

/-- Right distributivity (Init's `Int.add_mul` leaks `propext`): corollary of
`intLeftDistrib` through `intMulComm`, rewriting each addend back. -/
theorem intRightDistrib (leftSummand rightSummand factor : Int) :
    (leftSummand + rightSummand) * factor = leftSummand * factor + rightSummand * factor :=
  (intMulComm (leftSummand + rightSummand) factor).trans
    ((intLeftDistrib factor leftSummand rightSummand).trans
      ((congrArg (fun leftProduct => leftProduct + factor * rightSummand)
          (intMulComm factor leftSummand)).trans
        (congrArg (fun rightProduct => leftSummand * factor + rightProduct)
          (intMulComm factor rightSummand))))

end FX1Poly.ComputerAlgebra

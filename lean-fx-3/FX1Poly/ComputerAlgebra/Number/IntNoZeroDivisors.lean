import FX1Poly.ComputerAlgebra.Number.IntExactDivision
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # ℤ has no zero divisors (arbitrary sign)

The corpus's positive-multiplier cancellation does not apply when the scaling coefficient is
negative, so this file supplies the arbitrary-sign no-zero-divisor law and the nonvanishing
of powers, which feed the ℤ[x] Euclidean GCD's converse root-containment.

Core `Int.mul_eq_zero` and `Int.natAbs_mul` leak `propext`. Multiplicativity of `natAbs` is
therefore rebuilt hand-structurally in `intNatAbsMulByCases`, cased over the four
`ofNat`/`negSucc` sign combinations, together with a `Nat.noConfusion`-based Nat
no-zero-divisor `natMulEqZeroLeftFactor` (avoiding the propext-leaking `Nat.succ_ne_zero`).
Structural over `Nat`/`Int` constructors, free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, and `omega`; per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-- Nat has no zero divisors (left form): `n ≠ 0 → m · n = 0 → m = 0`. The `m+1, n+1` arm's
product reduces to a successor, refuted by `Nat.noConfusion`. -/
theorem natMulEqZeroLeftFactor : ∀ (leftFactor rightFactor : Nat),
    rightFactor ≠ 0 → leftFactor * rightFactor = 0 → leftFactor = 0
  | 0, _, _, _ => rfl
  | _ + 1, 0, isRightNonzero, _ => absurd rfl isRightNonzero
  | _ + 1, _ + 1, _, productIsZero => Nat.noConfusion productIsZero

/-- `(Int.negOfNat k).natAbs = k`, the magnitude of a `negOfNat`. -/
theorem intNatAbsNegOfNat : ∀ magnitude : Nat, (Int.negOfNat magnitude).natAbs = magnitude
  | 0 => rfl
  | _ + 1 => rfl

/-- `natAbs` is multiplicative: `(a · b).natAbs = a.natAbs · b.natAbs`, by cases on the sign
constructors of `a` and `b`. -/
theorem intNatAbsMulByCases :
    ∀ leftValue rightValue : Int, (leftValue * rightValue).natAbs = leftValue.natAbs * rightValue.natAbs
  | Int.ofNat _, Int.ofNat _ => rfl
  | Int.ofNat leftMag, Int.negSucc rightPred => intNatAbsNegOfNat (leftMag * (rightPred + 1))
  | Int.negSucc leftPred, Int.ofNat rightMag => intNatAbsNegOfNat ((leftPred + 1) * rightMag)
  | Int.negSucc _, Int.negSucc _ => rfl

/-- ℤ has no zero divisors (left form): `left ≠ 0 → left · right = 0 → right = 0`, for
arbitrary sign. Reads the equation at `natAbs`, then applies the Nat no-zero-divisor and
`intEqZeroOfNatAbsEqZero`. -/
theorem intMulEqZeroLeftFactor {leftValue rightValue : Int} (isLeftNonzero : leftValue ≠ 0)
    (productIsZero : leftValue * rightValue = 0) : rightValue = 0 :=
  have magnitudeProductIsZero : leftValue.natAbs * rightValue.natAbs = 0 :=
    (intNatAbsMulByCases leftValue rightValue).symm.trans (congrArg Int.natAbs productIsZero)
  intEqZeroOfNatAbsEqZero
    (natMulEqZeroLeftFactor rightValue.natAbs leftValue.natAbs
      (fun isLeftMagZero => isLeftNonzero (intEqZeroOfNatAbsEqZero isLeftMagZero))
      ((Nat.mul_comm rightValue.natAbs leftValue.natAbs).trans magnitudeProductIsZero))

/-- A product of nonzero integers is nonzero (contrapositive of `intMulEqZeroLeftFactor`). -/
theorem intMulNeZero {leftValue rightValue : Int} (isLeftNonzero : leftValue ≠ 0)
    (isRightNonzero : rightValue ≠ 0) : leftValue * rightValue ≠ 0 :=
  fun productIsZero => isRightNonzero (intMulEqZeroLeftFactor isLeftNonzero productIsZero)

/-- `(1 : Int) ≠ 0`, via `Nat.noConfusion` on the magnitude. -/
theorem intOneNeZero : (1 : Int) ≠ 0 := fun oneIsZero => Nat.noConfusion (congrArg Int.natAbs oneIsZero)

/-- Powers of a nonzero base are nonzero: `base ≠ 0 → intPower base exponent ≠ 0`, by
induction on the exponent. -/
theorem intPowerNeZero {base : Int} (isBaseNonzero : base ≠ 0) :
    ∀ exponent : Nat, intPower base exponent ≠ 0
  | 0 => intOneNeZero
  | _ + 1 => intMulNeZero (intPowerNeZero isBaseNonzero _) isBaseNonzero

/-- `(-3) · 4 ≠ 0`, exercising a negative factor. -/
theorem intMulNeZeroGrounding : ((-3 : Int) * 4) ≠ 0 := by decide

/-- `(-2)³ = -8 ≠ 0`, a negative base's power. -/
theorem intPowerNeZeroGrounding : intPower (-2 : Int) 3 ≠ 0 := by decide

/-- Marker: ℤ has no zero divisors for arbitrary sign (`intMulEqZeroLeftFactor`,
`intMulNeZero`) and powers of a nonzero base are nonzero (`intPowerNeZero`), built
propext-clean via a hand-structural multiplicative `natAbs`. -/
def fxInt_hasNoZeroDivisors : Bool := true

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.Number.IntExactDivision
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # FX1Poly/ComputerAlgebra/Number/IntNoZeroDivisors — ℤ has no zero divisors (arbitrary sign)
(a Number-layer prerequisite of the ℤ[x] Euclidean GCD's converse root-containment, WP-ENDO #2255)

The corpus already has *positive-multiplier* cancellation (`intMulRightCancel`, `intMulPowerRightCancel`),
but the pseudo-division scaling coefficient `leadDivisor` can be **negative**, so those do not apply.  This
file supplies the arbitrary-sign no-zero-divisor law and the nonvanishing of powers.

## Why hand-built

Both `Int.mul_eq_zero` and `Int.natAbs_mul` from core **leak `propext`**, so they are unusable in the
zero-axiom regime.  The clean route routes through a *hand-structural* `natAbs`-multiplicativity
(`intNatAbsMulByCases`, cased over the four `ofNat`/`negSucc` sign combinations, each `rfl` or the
`negOfNat`-natAbs identity) and a `Nat.noConfusion`-based Nat no-zero-divisor (`natMulEqZeroLeftFactor`,
avoiding the propext-leaking `Nat.succ_ne_zero`).

## What is PROVEN

  * `intMulEqZeroLeftFactor`: `left ≠ 0 → left · right = 0 → right = 0`.
  * `intMulNeZero`: `left ≠ 0 → right ≠ 0 → left · right ≠ 0`.
  * `intPowerNeZero`: `base ≠ 0 → intPower base exponent ≠ 0`.

## Zero-axiom design

Structural over `Nat`/`Int` constructors; `Nat.noConfusion`, `congrArg`, the corpus
`intEqZeroOfNatAbsEqZero`, `Nat.mul_comm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntNoZeroDivisors.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## Nat no-zero-divisor (propext-clean) -/

/-- **Nat has no zero divisors (left form).**  `n ≠ 0 → m · n = 0 → m = 0`, structurally: the `m+1, n+1`
arm's product reduces to a successor, refuted by `Nat.noConfusion` (avoiding the propext-leaking
`Nat.succ_ne_zero`). -/
theorem natMulEqZeroLeftFactor : ∀ (leftFactor rightFactor : Nat),
    rightFactor ≠ 0 → leftFactor * rightFactor = 0 → leftFactor = 0
  | 0, _, _, _ => rfl
  | _ + 1, 0, isRightNonzero, _ => absurd rfl isRightNonzero
  | _ + 1, _ + 1, _, productIsZero => Nat.noConfusion productIsZero

/-! ## natAbs is multiplicative (hand-structural, unlike the propext-leaking core `Int.natAbs_mul`) -/

/-- `(Int.negOfNat k).natAbs = k` — the magnitude of a `negOfNat`. -/
theorem intNatAbsNegOfNat : ∀ magnitude : Nat, (Int.negOfNat magnitude).natAbs = magnitude
  | 0 => rfl
  | _ + 1 => rfl

/-- **`natAbs` is multiplicative.**  `(a · b).natAbs = a.natAbs · b.natAbs`, by cases on the sign
constructors of `a` and `b` — each is `rfl` or the `negOfNat`-magnitude identity. -/
theorem intNatAbsMulByCases :
    ∀ leftValue rightValue : Int, (leftValue * rightValue).natAbs = leftValue.natAbs * rightValue.natAbs
  | Int.ofNat _, Int.ofNat _ => rfl
  | Int.ofNat leftMag, Int.negSucc rightPred => intNatAbsNegOfNat (leftMag * (rightPred + 1))
  | Int.negSucc leftPred, Int.ofNat rightMag => intNatAbsNegOfNat ((leftPred + 1) * rightMag)
  | Int.negSucc _, Int.negSucc _ => rfl

/-! ## The arbitrary-sign ℤ no-zero-divisor -/

/-- **ℤ has no zero divisors (left form).**  `left ≠ 0 → left · right = 0 → right = 0`, for *arbitrary
sign*.  Reads the equation at `natAbs` (`natAbs` multiplicative), then applies the Nat no-zero-divisor and
`intEqZeroOfNatAbsEqZero`. -/
theorem intMulEqZeroLeftFactor {leftValue rightValue : Int} (isLeftNonzero : leftValue ≠ 0)
    (productIsZero : leftValue * rightValue = 0) : rightValue = 0 :=
  have magnitudeProductIsZero : leftValue.natAbs * rightValue.natAbs = 0 :=
    (intNatAbsMulByCases leftValue rightValue).symm.trans (congrArg Int.natAbs productIsZero)
  intEqZeroOfNatAbsEqZero
    (natMulEqZeroLeftFactor rightValue.natAbs leftValue.natAbs
      (fun isLeftMagZero => isLeftNonzero (intEqZeroOfNatAbsEqZero isLeftMagZero))
      ((Nat.mul_comm rightValue.natAbs leftValue.natAbs).trans magnitudeProductIsZero))

/-- **A product of nonzero integers is nonzero.**  The contrapositive of `intMulEqZeroLeftFactor`. -/
theorem intMulNeZero {leftValue rightValue : Int} (isLeftNonzero : leftValue ≠ 0)
    (isRightNonzero : rightValue ≠ 0) : leftValue * rightValue ≠ 0 :=
  fun productIsZero => isRightNonzero (intMulEqZeroLeftFactor isLeftNonzero productIsZero)

/-! ## Powers of a nonzero base are nonzero -/

/-- `(1 : Int) ≠ 0` (propext-clean via `Nat.noConfusion` on the magnitude). -/
theorem intOneNeZero : (1 : Int) ≠ 0 := fun oneIsZero => Nat.noConfusion (congrArg Int.natAbs oneIsZero)

/-- **Powers of a nonzero base are nonzero.**  `base ≠ 0 → intPower base exponent ≠ 0`, by induction on
the exponent (`intPower base (e+1) = intPower base e · base`, both factors nonzero). -/
theorem intPowerNeZero {base : Int} (isBaseNonzero : base ≠ 0) :
    ∀ exponent : Nat, intPower base exponent ≠ 0
  | 0 => intOneNeZero
  | _ + 1 => intMulNeZero (intPowerNeZero isBaseNonzero _) isBaseNonzero

/-! ## Groundings -/

/-- `(-3) · 4 ≠ 0` — a negative factor exercised: `intMulNeZero` on `-3 ≠ 0`, `4 ≠ 0`. -/
theorem intMulNeZeroGrounding : ((-3 : Int) * 4) ≠ 0 := by decide

/-- `(-2)³ = -8 ≠ 0` — a negative base's power is nonzero. -/
theorem intPowerNeZeroGrounding : intPower (-2 : Int) 3 ≠ 0 := by decide

/-- Marker: ℤ has no zero divisors for *arbitrary* sign (`intMulEqZeroLeftFactor` / `intMulNeZero`) and
powers of a nonzero base are nonzero (`intPowerNeZero`) — built propext-clean via a hand-structural
multiplicative `natAbs` (the core/corpus versions leak `propext`).  Unblocks the ℤ[x] Euclidean GCD's
converse root-containment (cancelling the `leadDivisor^scalePower` factor). -/
def fxInt_hasNoZeroDivisors : Bool := true

end FX1Poly.ComputerAlgebra

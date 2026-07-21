import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # Nat powers of an Int

The `RadixScaledInteger` carrier (`mantissa * radix ^ exponent`) scales through Nat powers
of the radix; Init's `pow_*` corpus leaks `propext`, so the power function and its algebra
are defined structurally here.

  * `intPower` — structural on the exponent, multiplying on the right, so
    `intPower base (e + 1)` is definitionally `intPower base e * base`.
  * `intPowerAdd` — exponent addition is power multiplication: the scale-alignment law
    that rescaling a mantissa from exponent `e + k` down to `e` multiplies it by
    `radix ^ k`.
  * `intPowerNonNeg` / `intPowerPos` — positivity flows through `intMulNonNeg` /
    `intMulPos`; a positive radix keeps every scale factor positive, making scaled
    comparison order-faithful.
  * `intOnePower` — the degenerate radix-1 collapse.

Structural recursion on the exponent, free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, and `omega`; per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-- Nat power of an Int — structural on the exponent, multiplying on the right so the
successor equation is definitional. -/
def intPower (base : Int) : Nat → Int
  | 0 => 1
  | exponentValue + 1 => intPower base exponentValue * base

/-- The zero-exponent equation, definitional. -/
theorem intPowerZero (base : Int) : intPower base 0 = 1 := rfl

/-- The successor equation, definitional. -/
theorem intPowerSucc (base : Int) (exponentValue : Nat) :
    intPower base (exponentValue + 1) = intPower base exponentValue * base := rfl

/-- Exponent addition is power multiplication (the scale-alignment law); structural on
the right summand, one `intMulAssoc` per step. -/
theorem intPowerAdd (base : Int) (leftExponent : Nat) : ∀ rightExponent : Nat,
    intPower base (leftExponent + rightExponent) =
      intPower base leftExponent * intPower base rightExponent
  | 0 => (intMulOne (intPower base leftExponent)).symm
  | rightExponent + 1 =>
      (congrArg (· * base) (intPowerAdd base leftExponent rightExponent)).trans
        (intMulAssoc (intPower base leftExponent) (intPower base rightExponent) base)

/-- Powers of a nonnegative base are nonnegative. -/
theorem intPowerNonNeg {base : Int} (isBaseNonNegative : (0 : Int) ≤ base) :
    ∀ exponentValue : Nat, (0 : Int) ≤ intPower base exponentValue
  | 0 => intZeroLeOfNat 1
  | exponentValue + 1 =>
      intMulNonNeg (intPowerNonNeg isBaseNonNegative exponentValue) isBaseNonNegative

/-- Powers of a positive base are positive: the scale factors of a positive radix never
vanish, keeping scaled comparison order-faithful. -/
theorem intPowerPos {base : Int} (isBasePositive : (0 : Int) < base) :
    ∀ exponentValue : Nat, (0 : Int) < intPower base exponentValue
  | 0 => intLessEqualRefl (Int.ofNat 1)
  | exponentValue + 1 =>
      intMulPos (intPowerPos isBasePositive exponentValue) isBasePositive

/-- Powers of `1` collapse to `1`. -/
theorem intOnePower : ∀ exponentValue : Nat, intPower 1 exponentValue = 1
  | 0 => rfl
  | exponentValue + 1 =>
      (intMulOne (intPower 1 exponentValue)).trans (intOnePower exponentValue)

/-- Fold a further scaling onto the exponent: multiplying an already-scaled mantissa by
another power accumulates the exponents (one `intMulAssoc`, one `intPowerAdd`). -/
theorem intMulPowerFold (base mantissa : Int) (firstExponent secondExponent : Nat) :
    mantissa * intPower base firstExponent * intPower base secondExponent =
      mantissa * intPower base (firstExponent + secondExponent) :=
  (intMulAssoc mantissa (intPower base firstExponent)
      (intPower base secondExponent)).trans
    (congrArg (mantissa * ·) (intPowerAdd base firstExponent secondExponent).symm)

end FX1Poly.ComputerAlgebra

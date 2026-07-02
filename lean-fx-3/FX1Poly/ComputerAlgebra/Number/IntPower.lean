import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # FX1Poly/ComputerAlgebra/Number/IntPower — Nat powers of an Int
    (FLOAT-2 brick 1)

The RadixScaledInteger carrier (`mantissa * radix ^ exponent`) scales everything through
Nat powers of the radix, and Init's power corpus is propext-dirty (the `pow_*` family was
probed dirty with the division corpus, 2026-07-02).  This module hand-rolls the power
function and its algebra over the brick-1..8 kit:

  * `intPower` — structural on the exponent, multiplying on the RIGHT
    (`intPower base (e + 1)` is DEFINITIONALLY `intPower base e * base`).
  * `intPowerAdd` — exponent addition is power multiplication; structural on the right
    summand, one `intMulAssoc` per step.  This is THE alignment lemma: rescaling a
    mantissa from exponent `e + k` down to `e` multiplies it by `radix ^ k`.
  * `intPowerNonNeg` / `intPowerPos` — positivity flows through `intMulNonNeg` /
    `intMulPos`; a positive radix keeps every scale factor positive, which is what makes
    scaled comparison order-faithful.
  * `intOnePower` — the degenerate radix-1 diagnostic.

## Zero-axiom

Structural recursion on the exponent + the brick-1..8 kit.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntPower.lean`. -/

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

/-- **Exponent addition is power multiplication** — the scale-alignment lemma.
Structural on the right summand (`left + 0` and `intPower base 0` are definitional),
one `intMulAssoc` per step. -/
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

/-- Powers of a positive base are positive — the scale factors of a positive radix
never vanish, which keeps scaled comparison order-faithful. -/
theorem intPowerPos {base : Int} (isBasePositive : (0 : Int) < base) :
    ∀ exponentValue : Nat, (0 : Int) < intPower base exponentValue
  | 0 => intLessEqualRefl (Int.ofNat 1)
  | exponentValue + 1 =>
      intMulPos (intPowerPos isBasePositive exponentValue) isBasePositive

/-- Powers of `1` collapse — the degenerate-radix diagnostic. -/
theorem intOnePower : ∀ exponentValue : Nat, intPower 1 exponentValue = 1
  | 0 => rfl
  | exponentValue + 1 =>
      (intMulOne (intPower 1 exponentValue)).trans (intOnePower exponentValue)

end FX1Poly.ComputerAlgebra

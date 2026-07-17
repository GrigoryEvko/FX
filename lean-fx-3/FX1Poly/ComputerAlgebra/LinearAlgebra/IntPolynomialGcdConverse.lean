import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeBound
import FX1Poly.ComputerAlgebra.Number.IntNoZeroDivisors

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdConverse — the single-step converse
(the twelfth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntPolynomialGcd` proved the *forward* direction — the GCD vanishes at every common root of its inputs
(`polyGcdVanishesAtCommonRoot`).  Toward the *converse* (every root of the GCD is a common root) this file
supplies the single Euclidean-step ingredient: a point that is a root of both the divisor and the
pseudo-remainder is a root of the dividend.

## What is PROVEN

  * `polyPseudoRemBackwardRoot`: for a nonzero `divisor`, `eval(divisor) = 0 ∧ eval(pseudoRem) = 0 →
    eval(dividend) = 0` — read backward off the r10 reconstruction
    `leadDivisor^scalePower · eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)`: both
    right-hand terms vanish, so `leadDivisor^scalePower · eval(dividend) = 0`, and (r22, `leadDivisor ≠ 0`
    since the divisor is nonempty) `eval(dividend) = 0`.

This is the recursive workhorse for the full GCD converse (the Euclidean step recovers the dividend's root
from the divisor's and the pseudo-remainder's), which lands as a separate brick over `polyGcd`'s recursion.

## Zero-axiom design

Reconstruction identity + the arbitrary-sign ℤ no-zero-divisor (r22) — no case analysis at all here.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdConverse.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- **A root of the divisor and the pseudo-remainder is a root of the dividend.**  For a nonzero `divisor`,
`eval(divisor) = 0 ∧ eval(pseudoRem) = 0 → eval(dividend) = 0`.  The r10 reconstruction gives
`leadDivisor^scalePower · eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder) = 0`, and the
leading power is nonzero, so the dividend vanishes. -/
theorem polyPseudoRemBackwardRoot (point : Int) (fuel : Nat) (divisor dividend : List Int)
    (isDivisorNonempty : polyTrim divisor ≠ [])
    (divisorVanishes : polyEval point divisor = 0)
    (remainderVanishes : polyEval point (polyPseudoRem fuel divisor dividend) = 0) :
    polyEval point dividend = 0 := by
  have rightIsZero :
      polyEval point (polyPseudoDivMod fuel divisor dividend).2.1 * polyEval point divisor
          + polyEval point (polyPseudoDivMod fuel divisor dividend).2.2
        = 0 := by
    rw [divisorVanishes, intMulZero, intZeroAdd]
    exact remainderVanishes
  have scaledIsZero :
      intPower (polyLeadingCoeff divisor) (polyPseudoDivMod fuel divisor dividend).1
          * polyEval point dividend
        = 0 :=
    (polyPseudoDivModReconstructs point fuel divisor dividend).trans rightIsZero
  exact intMulEqZeroLeftFactor
    (intPowerNeZero (polyLeadingCoeffNonzeroWhenNonempty divisor isDivisorNonempty) _)
    scaledIsZero

/-! ## Grounding -/

/-- The single-step converse exhibited: with divisor `x + 1` (`[1, 1]`, root `−1`) and dividend `x² − 1`
(`[-1, 0, 1]`), the pseudo-remainder vanishes at `−1` and so does the divisor, so the dividend does too —
`polyEval (-1) [-1, 0, 1] = 0`. -/
theorem polyPseudoRemBackwardRootGrounding : polyEval (-1) [-1, 0, 1] = 0 := by decide

/-- Marker: the single Euclidean-step converse — a root of both the divisor and the pseudo-remainder is a
root of the dividend (`polyPseudoRemBackwardRoot`), cancelling the `leadDivisor^scalePower` factor via the
r22 ℤ no-zero-divisor.  The recursive workhorse for the full GCD converse root-containment. -/
def fxIntPoly_hasPseudoRemainderBackwardRoot : Bool := true

end FX1Poly.ComputerAlgebra

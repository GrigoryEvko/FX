import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # IntPolynomialPseudoRemBound — the pseudo-remainder degree bound

The single-step degree decrease (`polyPseudoStepDegreeLt`) threaded through the fuel recursion of
`polyPseudoDivMod` gives the fuel-adequacy result: with enough fuel, the pseudo-remainder has degree
strictly below the divisor.  `polyPseudoRemDegreeLtDivisor`: for a non-constant `divisor` and any `dividend`
with `polyDegree dividend < fuel`, the pseudo-remainder satisfies `polyDegree (…).2.2 < polyDegree divisor`.
Induction on fuel: the `isTrue` guard returns the dividend precisely when its degree is already below; the
`isFalse` recursion replaces the dividend by the step, whose degree strictly drops, so the fuel bound is
preserved.  This certifies that the pseudo-remainder genuinely shrinks the problem — why the Euclidean GCD's
fuel is adequate.

Structural recursion on fuel; the guard is `Nat.decLt`; the arithmetic is core Nat order lemmas.  Free of
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The fuel-adequate pseudo-remainder degree bound -/

/-- **The pseudo-remainder degree drops below the divisor (fuel adequate).**  For a non-constant `divisor`
and `polyDegree dividend < fuel`, `polyDegree (polyPseudoDivMod fuel divisor dividend).2.2 < polyDegree
divisor`.  The `isTrue` guard returns the dividend exactly when its degree is already below; the `isFalse`
recursion uses the single-step decrease to keep `polyDegree · < fuel` invariant. -/
theorem polyPseudoRemDegreeLtDivisor (divisor : List Int) (isDivisorNonconstant : 1 ≤ polyDegree divisor) :
    ∀ (fuel : Nat) (dividend : List Int), polyDegree dividend < fuel →
      polyDegree (polyPseudoDivMod fuel divisor dividend).2.2 < polyDegree divisor
  | 0, dividend, isAdequate => absurd isAdequate (Nat.not_lt_zero (polyDegree dividend))
  | fuel + 1, dividend, isAdequate => by
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue isBelow => exact isBelow
      | isFalse isNotBelow =>
          have isDivisorLe : polyDegree divisor ≤ polyDegree dividend := Nat.le_of_not_lt isNotBelow
          have stepDegreeLt :=
            polyPseudoStepDegreeLt dividend divisor isDivisorNonconstant isDivisorLe
          exact polyPseudoRemDegreeLtDivisor divisor isDivisorNonconstant fuel _
            (Nat.lt_of_lt_of_le stepDegreeLt (Nat.le_of_lt_succ isAdequate))

/-! ## Groundings -/

/-- Dividing `x² − 1` (degree 2) by `2x + 3` (degree 1) with fuel `3 > 2`: the pseudo-remainder has degree
`< 1`, i.e. it is constant — `polyDegree (polyPseudoDivMod 3 [3, 2] [-1, 0, 1]).2.2 < polyDegree [3, 2]`. -/
theorem polyPseudoRemDegreeLtDivisorGrounding :
    polyDegree (polyPseudoDivMod 3 [3, 2] [-1, 0, 1]).2.2 < polyDegree [3, 2] := by decide

end FX1Poly.ComputerAlgebra

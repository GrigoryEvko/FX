import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoRemFuelStable — adequate-fuel remainder stability
(the fifteenth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The lynchpin of the fuel-adequacy → true-fixed-point wiring: once the pseudo-division fuel is *adequate*
(`polyDegree dividend < fuel`), adding more fuel does not change the pseudo-remainder — the recursion has
already bottomed out.  Proved for a **non-constant divisor** (`1 ≤ polyDegree divisor`), where r20's strict
single-step degree-decrease keeps the adequacy bound invariant across the recursion (the constant-divisor
case terminates by a different mechanism — the remainder reduces to the zero polynomial — and is out of
scope here).

## What is PROVEN

`polyPseudoRemFuelStableNonconstant`: for a non-constant `divisor` and `polyDegree dividend < fuel`,
`polyPseudoRem (fuel + extra) divisor dividend = polyPseudoRem fuel divisor dividend` for all `extra`.
Induction on fuel: the `isTrue` guard returns the dividend, fuel-independently; the `isFalse` recursion
descends to the step `reduced` whose degree strictly drops (r20 `polyPseudoStepDegreeLt`), so
`polyDegree reduced < fuel` and the IH applies at the reduced dividend with the same `extra`.

This is exactly the fuel-monotonicity the Euclidean GCD's adequacy argument needs: with the remainder stable
past the adequacy threshold, `polyGcdReachesNil` no longer depends on the exact fuel, only on it being
large enough.

## Zero-axiom design

Structural recursion on fuel; the guard is `Nat.decLt`; the fuel arithmetic is `Nat.add_right_comm` and core
Nat order lemmas (`Nat.not_lt_zero`, `Nat.le_of_not_lt`, `Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoRemFuelStable.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- **Adequate-fuel pseudo-remainder stability (non-constant divisor).**  For a non-constant `divisor` and
`polyDegree dividend < fuel`, extra fuel leaves the pseudo-remainder unchanged:
`polyPseudoRem (fuel + extra) divisor dividend = polyPseudoRem fuel divisor dividend`.  The `isFalse`
recursion preserves the adequacy bound through r20's strict step degree-decrease. -/
theorem polyPseudoRemFuelStableNonconstant (divisor : List Int)
    (isDivisorNonconstant : 1 ≤ polyDegree divisor) :
    ∀ (fuel extra : Nat) (dividend : List Int), polyDegree dividend < fuel →
      polyPseudoRem (fuel + extra) divisor dividend = polyPseudoRem fuel divisor dividend
  | 0, _, dividend, isAdequate => absurd isAdequate (Nat.not_lt_zero (polyDegree dividend))
  | fuel + 1, extra, dividend, isAdequate => by
      show (polyPseudoDivMod (fuel + 1 + extra) divisor dividend).2.2
        = (polyPseudoDivMod (fuel + 1) divisor dividend).2.2
      rw [Nat.add_right_comm fuel 1 extra]
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ => rfl
      | isFalse isNotBelow =>
          have isDivisorLe : polyDegree divisor ≤ polyDegree dividend := Nat.le_of_not_lt isNotBelow
          have stepDegreeLt :=
            polyPseudoStepDegreeLt dividend divisor isDivisorNonconstant isDivisorLe
          exact polyPseudoRemFuelStableNonconstant divisor isDivisorNonconstant fuel extra _
            (Nat.lt_of_lt_of_le stepDegreeLt (Nat.le_of_lt_succ isAdequate))

/-! ## Grounding -/

/-- Adequate-fuel stability exhibited: dividing `x² − 1` (degree 2) by `2x + 3` (degree 1, non-constant)
with adequate fuel `3 > 2`, extra fuel (`3 + 4 = 7`) leaves the pseudo-remainder unchanged —
`polyPseudoRem 7 [3, 2] [-1, 0, 1] = polyPseudoRem 3 [3, 2] [-1, 0, 1]`. -/
theorem polyPseudoRemFuelStableGrounding :
    polyPseudoRem 7 [3, 2] [-1, 0, 1] = polyPseudoRem 3 [3, 2] [-1, 0, 1] := by decide

/-- Marker: the ℤ[x] pseudo-remainder is stable under extra fuel once fuel is adequate, for a non-constant
divisor (`polyPseudoRemFuelStableNonconstant`) — the fuel-monotonicity lynchpin of the fuel-adequacy →
true-fixed-point wiring for the Euclidean GCD. -/
def fxIntPoly_hasPseudoRemainderFuelStability : Bool := true

end FX1Poly.ComputerAlgebra

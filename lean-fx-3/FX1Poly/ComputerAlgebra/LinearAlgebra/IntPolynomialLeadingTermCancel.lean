import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingCoeff
import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialLeadingTermCancel — the pseudo-division step
kills the top coefficient
(the seventh brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The pseudo-division step (`IntPolynomialDivision.polyPseudoDivMod`, taken when `polyDegree divisor ≤
polyDegree dividend`) replaces the dividend by

  `polySub (polyScale (polyLeadingCoeff divisor) dividend)
           (polyMul (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend − polyDegree divisor))
                    divisor)`.

## What is PROVEN

`polyPseudoStepTopCoeffCancels`: that replacement's coefficient at position `polyDegree dividend` is `0`
whenever `polyDegree divisor ≤ polyDegree dividend`.  This is the leading-term cancellation — the *reason*
the pseudo-remainder's degree strictly drops, hence the reason the Euclidean recursion terminates.  The
computation:

  * `polyCoeffScale`: the scaled dividend contributes `leadDivisor · polyCoeff dividend (deg dividend)`;
  * `polyCoeffMonomialMul` + `natAddSubOfLe` (`e + (d − e) = d`): the quotient-term product contributes
    `leadDividend · polyCoeff divisor (deg divisor)`;
  * `polyLeadingCoeffEqCoeffDegree`: both positional coefficients are the leading coefficients;
  * commutativity: `leadDivisor · leadDividend − leadDividend · leadDivisor = 0`.

## Zero-axiom design

A `rw` chain over the coefficient homomorphisms, the degree↔coefficient bridge, the propext-clean
`natAddSubOfLe`, and the corpus `Int` ring lemmas — all `Eq` of data.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialLeadingTermCancel.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The leading-term cancellation -/

/-- **The pseudo-division step annihilates the dividend's top coefficient.**  When `polyDegree divisor ≤
polyDegree dividend` (the guard under which the step fires), the replacement dividend
`leadDivisor · dividend − (leadDividend · x^(d−e)) · divisor` has coefficient `0` at position `d =
polyDegree dividend`: the two products share the top coefficient `leadDivisor · leadDividend`, which
cancels. -/
theorem polyPseudoStepTopCoeffCancels (dividend divisor : List Int)
    (isDivisorDegreeLe : polyDegree divisor ≤ polyDegree dividend) :
    polyCoeff
        (polySub (polyScale (polyLeadingCoeff divisor) dividend)
          (polyMul
            (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
            divisor))
        (polyDegree dividend)
      = 0 := by
  have quotientTermTopCoeff :
      polyCoeff
          (polyMul
            (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
            divisor)
          (polyDegree dividend)
        = polyLeadingCoeff dividend * polyCoeff divisor (polyDegree divisor) := by
    have shifted :=
      polyCoeffMonomialMul (polyLeadingCoeff dividend) divisor (polyDegree divisor)
        (polyDegree dividend - polyDegree divisor)
    rw [natAddSubOfLe isDivisorDegreeLe] at shifted
    exact shifted
  rw [polyCoeffSub, polyCoeffScale, quotientTermTopCoeff,
      ← polyLeadingCoeffEqCoeffDegree dividend, ← polyLeadingCoeffEqCoeffDegree divisor,
      intMulComm (polyLeadingCoeff dividend) (polyLeadingCoeff divisor),
      intSubEqAddNeg, intAddRightNeg]

/-! ## Groundings -/

/-- The step on `dividend = x² − 1` (`[-1, 0, 1]`, degree 2, leading `1`) by `divisor = 2x + 3`
(`[3, 2]`, degree 1, leading `2`): the replacement's coefficient at position `2` is `0` — an instance of
`polyPseudoStepTopCoeffCancels` (here `1 ≤ 2`). -/
theorem polyPseudoStepTopCoeffCancelsGrounding :
    polyCoeff
        (polySub (polyScale (polyLeadingCoeff [3, 2]) [-1, 0, 1])
          (polyMul
            (polyMonomial (polyLeadingCoeff [-1, 0, 1]) (polyDegree [-1, 0, 1] - polyDegree [3, 2]))
            [3, 2]))
        (polyDegree [-1, 0, 1])
      = 0 := by decide

/-- Marker: the ℤ[x] pseudo-division step's leading-term cancellation is proven — the replacement
dividend's coefficient at the old top degree vanishes.  This is the coefficient-level content behind the
Euclidean GCD's termination (the degree strictly decreases each step). -/
def fxIntPoly_hasPseudoStepLeadingTermCancellation : Bool := true

end FX1Poly.ComputerAlgebra

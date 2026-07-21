import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingCoeff
import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # IntPolynomialLeadingTermCancel — the pseudo-division step kills the top coefficient

The pseudo-division step (taken when `polyDegree divisor ≤ polyDegree dividend`) replaces the dividend by
`leadDivisor · dividend − (leadDividend · x^(d−e)) · divisor`.  `polyPseudoStepTopCoeffCancels` proves that
replacement's coefficient at position `polyDegree dividend` is `0`: the scaled dividend contributes
`leadDivisor · polyCoeff dividend (deg dividend)`, the quotient-term product contributes `leadDividend ·
polyCoeff divisor (deg divisor)` (via `polyCoeffMonomialMul` and `natAddSubOfLe`), both positional
coefficients are the leading coefficients (`polyLeadingCoeffEqCoeffDegree`), and commutativity cancels them.
This is why the pseudo-remainder's degree strictly drops, hence why the Euclidean recursion terminates.

A `rw` chain over the coefficient homomorphisms, the degree↔coefficient bridge, the propext-clean
`natAddSubOfLe`, and the corpus `Int` ring lemmas.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

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

end FX1Poly.ComputerAlgebra

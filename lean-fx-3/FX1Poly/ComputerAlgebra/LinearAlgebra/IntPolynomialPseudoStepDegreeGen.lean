import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease

/-! # IntPolynomialPseudoStepDegreeGen — the step decrease, generalized

`polyPseudoStepDegreeLt` required a non-constant divisor, using it only to derive `1 ≤ polyDegree dividend`
and `polyTrim divisor ≠ []`.  Taking those two as hypotheses directly generalizes the step decrease to a
constant (degree-0) nonzero divisor as well — the case at the tail of the Euclidean GCD, where a coprime
pair reaches a nonzero-constant remainder.

`polyPseudoStepDegreeLtGen`: for a nonempty `divisor`, a non-constant `dividend`, and `polyDegree divisor ≤
polyDegree dividend`, the step's replacement dividend has degree strictly below `polyDegree dividend`.
`polyPseudoConstantStepDegreeLt` specializes this to a constant divisor.  Both feed the Euclidean
termination measure, which must also shrink in the tail case where the secondary is a nonzero constant.

Reuses the helpers of the non-generalized step (`natLeOfSubOneLt`, `natSubAddCancel`,
`polyTrimLengthEqDegreeSucc`, `polyMonomialMulCoeffVanishesFarAbove`).  Free of `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-- **The pseudo-division step strictly decreases the degree (generalized).**  For a nonempty `divisor`, a
non-constant `dividend`, and `polyDegree divisor ≤ polyDegree dividend`, the step's replacement dividend has
degree strictly below `polyDegree dividend` — the non-generalized step with the divisor-nonconstant
hypothesis relaxed to divisor-nonempty plus dividend-nonconstant, so it also covers a constant nonzero
divisor. -/
theorem polyPseudoStepDegreeLtGen (dividend divisor : List Int)
    (isDivisorNonempty : polyTrim divisor ≠ [])
    (isDividendNonconstant : 1 ≤ polyDegree dividend)
    (isDivisorDegreeLe : polyDegree divisor ≤ polyDegree dividend) :
    polyDegree
        (polySub (polyScale (polyLeadingCoeff divisor) dividend)
          (polyMul
            (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
            divisor))
      < polyDegree dividend := by
  apply polyDegreeLtOfCoeffVanishingAbove _ (polyDegree dividend) isDividendNonconstant
  intro position isDegreeLePosition
  cases Nat.eq_or_lt_of_le isDegreeLePosition with
  | inl degreeEqPosition =>
      rw [← degreeEqPosition]
      exact polyPseudoStepTopCoeffCancels dividend divisor isDivisorDegreeLe
  | inr isDegreeLtPosition =>
      have scaleVanishes :
          polyCoeff (polyScale (polyLeadingCoeff divisor) dividend) position = 0 := by
        rw [polyCoeffScale,
          polyCoeffZeroFromTrimLength dividend position (natLeOfSubOneLt _ _ isDegreeLtPosition)]
        exact intMulZero _
      have mulVanishes :
          polyCoeff (polyMul
              (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
              divisor) position = 0 := by
        obtain ⟨extra, hExtra⟩ := Nat.le.dest isDegreeLtPosition
        have indexEq :
            ((polyTrim divisor).length + extra) + (polyDegree dividend - polyDegree divisor)
              = position := by
          rw [polyTrimLengthEqDegreeSucc divisor isDivisorNonempty]
          calc ((polyDegree divisor + 1) + extra) + (polyDegree dividend - polyDegree divisor)
              = ((polyDegree divisor + 1) + (polyDegree dividend - polyDegree divisor)) + extra := by
                rw [Nat.add_assoc, Nat.add_comm extra, ← Nat.add_assoc]
            _ = (polyDegree dividend + 1) + extra := by
                rw [Nat.add_comm (polyDegree divisor + 1)
                      (polyDegree dividend - polyDegree divisor),
                  ← Nat.add_assoc, natSubAddCancel isDivisorDegreeLe]
            _ = position := hExtra
        have applied := polyMonomialMulCoeffVanishesFarAbove (polyLeadingCoeff dividend) divisor
          (polyDegree dividend - polyDegree divisor) ((polyTrim divisor).length + extra)
          (Nat.le_add_right (polyTrim divisor).length extra)
        rw [indexEq] at applied
        exact applied
      rw [polyCoeffSub, scaleVanishes, mulVanishes]
      exact (intSubEqAddNeg (0 : Int) 0).trans (intAddRightNeg 0)

/-- **A constant nonzero divisor drops a non-constant dividend's degree.**  The `polyDegree divisor = 0`
specialization of `polyPseudoStepDegreeLtGen` — the Euclidean tail case where the secondary is a nonzero
constant.  Here `polyDegree divisor ≤ polyDegree dividend` is automatic (`0 ≤ _`). -/
theorem polyPseudoConstantStepDegreeLt (dividend divisor : List Int)
    (isDivisorNonempty : polyTrim divisor ≠ [])
    (isDivisorConstant : polyDegree divisor = 0)
    (isDividendNonconstant : 1 ≤ polyDegree dividend) :
    polyDegree
        (polySub (polyScale (polyLeadingCoeff divisor) dividend)
          (polyMul
            (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
            divisor))
      < polyDegree dividend :=
  polyPseudoStepDegreeLtGen dividend divisor isDivisorNonempty isDividendNonconstant
    (isDivisorConstant ▸ Nat.zero_le (polyDegree dividend))

/-! ## Grounding -/

/-- The generalized step on `x² − 1` (degree 2) by the constant `3` (`[3]`, degree 0): the replacement has
degree `< 2` — a constant divisor still drops the degree of a non-constant dividend. -/
theorem polyPseudoStepDegreeLtGenGrounding :
    polyDegree
        (polySub (polyScale (polyLeadingCoeff [3]) [-1, 0, 1])
          (polyMul
            (polyMonomial (polyLeadingCoeff [-1, 0, 1]) (polyDegree [-1, 0, 1] - polyDegree [3]))
            [3]))
      < polyDegree [-1, 0, 1] := by decide

end FX1Poly.ComputerAlgebra

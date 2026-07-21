import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingTermCancel
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeBound

/-! # IntPolynomialPseudoDegreeDecrease — the degree strictly drops

The capstone of the coefficient calculus: `polyPseudoStepDegreeLt` shows the pseudo-division step strictly
decreases the degree, the termination lever the Euclidean GCD's fuel adequacy rests on.  For a non-constant
`divisor` (`1 ≤ polyDegree divisor`) with `polyDegree divisor ≤ polyDegree dividend`, the replacement
dividend has degree strictly below `polyDegree dividend`: its coefficients vanish at the top position
(leading-term cancellation) and above it (the scaled dividend and the quotient-term product each vanish
there), so `polyDegreeLtOfCoeffVanishingAbove` applies.

Assembles the leading-term cancellation, the coefficient-vanishing bounds, and the degree characterization
through the corpus `natAddSubOfLe`, core Nat order lemmas, and the corpus `Int` ring lemmas.  Free of
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Small Nat and degree helpers -/

/-- `value − 1 < bound → value ≤ bound` (a predecessor below `bound` puts the value at most at `bound`). -/
theorem natLeOfSubOneLt : ∀ (value bound : Nat), value - 1 < bound → value ≤ bound
  | 0, bound, _ => Nat.zero_le bound
  | _ + 1, _, isLt => isLt

/-- `smaller ≤ larger → (larger − smaller) + smaller = larger` — the commuted `natAddSubOfLe`. -/
theorem natSubAddCancel {smaller larger : Nat} (isLe : smaller ≤ larger) :
    (larger - smaller) + smaller = larger :=
  (Nat.add_comm (larger - smaller) smaller).trans (natAddSubOfLe isLe)

/-- **A nonzero polynomial's trimmed length is its degree plus one.**  `polyTrim coeffs ≠ [] →
(polyTrim coeffs).length = polyDegree coeffs + 1`. -/
theorem polyTrimLengthEqDegreeSucc (coeffs : List Int) (isNonempty : polyTrim coeffs ≠ []) :
    (polyTrim coeffs).length = polyDegree coeffs + 1 := by
  cases hTrim : polyTrim coeffs with
  | nil => exact absurd hTrim isNonempty
  | cons trimHead trimTail =>
      unfold polyDegree
      rw [hTrim]
      rfl

/-! ## The quotient-term product vanishes far above -/

/-- **A monomial-times-polynomial product vanishes past its degree.**  For an `innerPosition` at or past the
divisor's trimmed length, `polyCoeff (coeff · x^degree · divisor) (innerPosition + degree) = 0`: the
product's coefficient there is `coeff · polyCoeff divisor innerPosition`, and that inner coefficient is
already gone.  Stated additively (`innerPosition + degree`) to keep the proof free of Nat subtraction. -/
theorem polyMonomialMulCoeffVanishesFarAbove (coeff : Int) (divisor : List Int)
    (degree innerPosition : Nat) (isFarInner : (polyTrim divisor).length ≤ innerPosition) :
    polyCoeff (polyMul (polyMonomial coeff degree) divisor) (innerPosition + degree) = 0 :=
  (polyCoeffMonomialMul coeff divisor innerPosition degree).trans
    (by rw [polyCoeffZeroFromTrimLength divisor innerPosition isFarInner]; exact intMulZero coeff)

/-! ## The strict degree decrease -/

/-- **The pseudo-division step strictly decreases the degree.**  For `1 ≤ polyDegree divisor` and
`polyDegree divisor ≤ polyDegree dividend`, the replacement dividend `leadDivisor · dividend −
(leadDividend · x^(d−e)) · divisor` has degree strictly below `polyDegree dividend`.  Its coefficients
vanish at `d` (leading-term cancellation) and above `d` (both summands individually vanish), so
`polyDegreeLtOfCoeffVanishingAbove` applies. -/
theorem polyPseudoStepDegreeLt (dividend divisor : List Int)
    (isDivisorNonconstant : 1 ≤ polyDegree divisor)
    (isDivisorDegreeLe : polyDegree divisor ≤ polyDegree dividend) :
    polyDegree
        (polySub (polyScale (polyLeadingCoeff divisor) dividend)
          (polyMul
            (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
            divisor))
      < polyDegree dividend := by
  have isDividendNonconstant : 1 ≤ polyDegree dividend :=
    Nat.le_trans isDivisorNonconstant isDivisorDegreeLe
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
      have isDivisorNonempty : polyTrim divisor ≠ [] := by
        intro isEmpty
        have degreeIsZero : polyDegree divisor = 0 := by
          show (polyTrim divisor).length - 1 = 0
          rw [isEmpty]
          rfl
        rw [degreeIsZero] at isDivisorNonconstant
        exact absurd isDivisorNonconstant (Nat.not_succ_le_zero 0)
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

/-! ## Groundings -/

/-- The step on `x² − 1` (degree 2) by `2x + 3` (degree 1, non-constant): the replacement has degree `< 2`,
here degree `1` (`< 2`). -/
theorem polyPseudoStepDegreeLtGrounding :
    polyDegree
        (polySub (polyScale (polyLeadingCoeff [3, 2]) [-1, 0, 1])
          (polyMul
            (polyMonomial (polyLeadingCoeff [-1, 0, 1]) (polyDegree [-1, 0, 1] - polyDegree [3, 2]))
            [3, 2]))
      < polyDegree [-1, 0, 1] := by decide

end FX1Poly.ComputerAlgebra

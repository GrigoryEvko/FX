import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialNilCascade
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoStepDegreeGen
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingCoeff

/-! # IntPolynomialConstDivisorNil — constant-divisor remainder → nil

The Euclidean GCD's constant-divisor tail: pseudo-dividing any dividend by a nonzero constant divisor yields
a zero remainder once the fuel is adequate, so the GCD reaches its nil-terminating branch after it bottoms
out at a coprime (constant-remainder) step.

`polyPseudoRemConstantTrimsNil`: for a nonzero constant `divisor` (`polyTrim divisor ≠ []`, `polyDegree
divisor = 0`) and `polyDegree dividend < fuel`, `polyTrim (polyPseudoRem fuel divisor dividend) = []`.
Induction on fuel; the guard is always `isFalse` (nothing has degree `< 0`).  A non-constant dividend has
its degree dropped by the constant-divisor step decrease (`polyPseudoConstantStepDegreeLt`); a constant one
has its step coefficients all cancel, so the reduced polynomial is zero and `polyPseudoRemZeroDividendTrimsNil`
finishes.

Structural fuel recursion + a `polyDegree`-value case split; the coefficient homomorphisms, the
leading-coefficient characterization, and core Nat/Int lemmas.  Free of `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-- **A nonzero constant divisor yields a zero pseudo-remainder (fuel adequate).**  For `polyTrim divisor ≠
[]`, `polyDegree divisor = 0`, and `polyDegree dividend < fuel`, `polyTrim (polyPseudoRem fuel divisor
dividend) = []`.  The recursion drops a non-constant dividend's degree or zeroes a constant one, then the
zero-dividend cascade keeps the zero polynomial zero. -/
theorem polyPseudoRemConstantTrimsNil (divisor : List Int)
    (isDivisorNonempty : polyTrim divisor ≠ [])
    (isDivisorConstant : polyDegree divisor = 0) :
    ∀ (fuel : Nat) (dividend : List Int), polyDegree dividend < fuel →
      polyTrim (polyPseudoRem fuel divisor dividend) = []
  | 0, dividend, isAdequate => absurd isAdequate (Nat.not_lt_zero (polyDegree dividend))
  | fuel + 1, dividend, isAdequate => by
      show polyTrim (polyPseudoDivMod (fuel + 1) divisor dividend).2.2 = []
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue isBelow =>
          rw [isDivisorConstant] at isBelow
          exact absurd isBelow (Nat.not_lt_zero (polyDegree dividend))
      | isFalse _ =>
          cases Nat.eq_zero_or_pos (polyDegree dividend) with
          | inr isDividendPos =>
              apply polyPseudoRemConstantTrimsNil divisor isDivisorNonempty isDivisorConstant fuel
              exact Nat.lt_of_lt_of_le
                (polyPseudoConstantStepDegreeLt dividend divisor isDivisorNonempty isDivisorConstant
                  isDividendPos)
                (Nat.le_of_lt_succ isAdequate)
          | inl isDividendConstant =>
              apply polyPseudoRemZeroDividendTrimsNil divisor fuel
              apply polyTrimNilOfAllCoeffZero
              intro pos
              have degreeDiffZero : polyDegree dividend - polyDegree divisor = 0 := by
                rw [isDividendConstant, isDivisorConstant]
              have monMul :
                  polyCoeff (polyMul (polyMonomial (polyLeadingCoeff dividend) 0) divisor) pos
                    = polyLeadingCoeff dividend * polyCoeff divisor pos := by
                have h := polyCoeffMonomialMul (polyLeadingCoeff dividend) divisor pos 0
                rw [Nat.add_zero] at h
                exact h
              rw [polyCoeffSub, polyCoeffScale, degreeDiffZero, monMul]
              cases pos with
              | zero =>
                  have hd : polyCoeff dividend 0 = polyLeadingCoeff dividend := by
                    have hh := polyLeadingCoeffEqCoeffDegree dividend
                    rw [isDividendConstant] at hh
                    exact hh.symm
                  have hv : polyCoeff divisor 0 = polyLeadingCoeff divisor := by
                    have hh := polyLeadingCoeffEqCoeffDegree divisor
                    rw [isDivisorConstant] at hh
                    exact hh.symm
                  rw [hd, hv, intMulComm (polyLeadingCoeff divisor) (polyLeadingCoeff dividend)]
                  exact (intSubEqAddNeg (polyLeadingCoeff dividend * polyLeadingCoeff divisor)
                    (polyLeadingCoeff dividend * polyLeadingCoeff divisor)).trans (intAddRightNeg _)
              | succ predPos =>
                  have hd : polyCoeff dividend (predPos + 1) = 0 := by
                    apply polyCoeffZeroFromTrimLength
                    exact natLeOfSubOneLt (polyTrim dividend).length (predPos + 1)
                      (by rw [show (polyTrim dividend).length - 1 = 0 from isDividendConstant]
                          exact Nat.succ_pos predPos)
                  have hv : polyCoeff divisor (predPos + 1) = 0 := by
                    apply polyCoeffZeroFromTrimLength
                    exact natLeOfSubOneLt (polyTrim divisor).length (predPos + 1)
                      (by rw [show (polyTrim divisor).length - 1 = 0 from isDivisorConstant]
                          exact Nat.succ_pos predPos)
                  rw [hd, hv, intMulZero, intMulZero]
                  exact (intSubEqAddNeg (0 : Int) 0).trans (intAddRightNeg 0)

/-! ## Grounding -/

/-- Pseudo-dividing `x² + 2x + 3` by the nonzero constant `2` (`[2]`) leaves a zero remainder at fuel 5 —
`polyTrim (polyPseudoRem 5 [2] [3, 2, 1]) = []` (a constant divides everything after leading-coefficient
scaling). -/
theorem polyPseudoRemConstantTrimsNilGrounding : polyTrim (polyPseudoRem 5 [2] [3, 2, 1]) = [] := by decide

end FX1Poly.ComputerAlgebra

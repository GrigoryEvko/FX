import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoStepDegreeGen — the step decrease, generalized
(the sixteenth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

r20's `polyPseudoStepDegreeLt` required a **non-constant divisor** (`1 ≤ polyDegree divisor`), which it used
only to derive `1 ≤ polyDegree dividend` and `polyTrim divisor ≠ []`.  Taking those two as hypotheses
directly **generalizes** the step decrease to cover a **constant** (degree-0) nonzero divisor as well — the
case that arises at the tail of the Euclidean GCD (a coprime pair reaches a nonzero-constant remainder).

## What is PROVEN

`polyPseudoStepDegreeLtGen`: for a nonempty `divisor` (`polyTrim divisor ≠ []`), a **non-constant** dividend
(`1 ≤ polyDegree dividend`), and `polyDegree divisor ≤ polyDegree dividend`, the pseudo-division step's
replacement dividend has degree strictly below `polyDegree dividend`.  Identical to r20's argument
(r17 top-cancellation at `d`, r18 vanishing above `d`, r19 degree characterization) with the two derived
facts supplied as hypotheses instead.

`polyPseudoConstantStepDegreeLt`: the specialization to a **constant** divisor (`polyDegree divisor = 0`)
made explicit — a nonzero constant divisor drops the degree of any non-constant dividend.

## Why this matters for fuel-adequacy

The Euclidean GCD's termination measure `(polyTrim secondary).length` strictly decreases each step: for a
non-constant secondary this is r21 (pseudo-rem degree < divisor degree); this brick supplies the tail case
where the secondary is a nonzero **constant** and the dividend is non-constant, so the step still shrinks
the degree toward the nil-terminating branch.

## Zero-axiom design

r20's proof body verbatim minus the two hypothesis derivations; reuses the r20 helpers
(`natLeOfSubOneLt`, `natSubAddCancel`, `polyTrimLengthEqDegreeSucc`, `polyMonomialMulCoeffVanishesFarAbove`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialPseudoStepDegreeGen.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- **The pseudo-division step strictly decreases the degree (generalized).**  For a nonempty `divisor`, a
non-constant `dividend`, and `polyDegree divisor ≤ polyDegree dividend`, the step's replacement dividend has
degree strictly below `polyDegree dividend` — r20 with the divisor-nonconstant hypothesis relaxed to
divisor-nonempty plus dividend-nonconstant, so it also covers a constant nonzero divisor. -/
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

/-- Marker: the ℤ[x] pseudo-division step degree decrease generalized to a nonempty (possibly **constant**)
divisor over a non-constant dividend (`polyPseudoStepDegreeLtGen` / `polyPseudoConstantStepDegreeLt`) — the
Euclidean tail-case degree lever for fuel adequacy. -/
def fxIntPoly_hasGeneralPseudoStepDegreeDecrease : Bool := true

end FX1Poly.ComputerAlgebra

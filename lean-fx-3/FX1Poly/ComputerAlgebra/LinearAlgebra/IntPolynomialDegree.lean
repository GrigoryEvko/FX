import FX1Poly.ComputerAlgebra.LinearAlgebra.IntUnivariatePolynomial

/-! # IntPolynomialDegree — degree, leading coefficient, normal form

A degree and leading coefficient need a canonical form because the ascending coefficient list carries
trailing zeros (`[3]` and `[3, 0, 0]` both denote `3`).  `polyTrim` drops trailing zeros; `polyDegree` is
`(trimmed length) − 1` (the zero polynomial gets `0`); `polyLeadingCoeff` is the last surviving coefficient
(`0` for the zero polynomial).  `polyTrimPreservesEval` makes the normal form sound: trimming does not
change the value at any point.  This is the parent of the ℤ[x] degree sub-arc, whose markers are
consolidated here (`fxIntPoly_hasDegreeAndLeadingCoefficient`).

`polyTrim`'s only non-list case analysis is `Int.decEq coeff 0`; arithmetic routes through the corpus `Int`
lemmas.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The trailing-zero normal form -/

/-- Drop trailing zeros from the ascending coefficient list, giving the canonical representative of the
polynomial.  Structural on the list; the recursive call trims the tail first. -/
def polyTrim : List Int → List Int
  | [] => []
  | coeff :: restCoeffs =>
      match polyTrim restCoeffs with
      | [] =>
          match Int.decEq coeff 0 with
          | isTrue _ => []
          | isFalse _ => [coeff]
      | trimHead :: trimTail => coeff :: trimHead :: trimTail

/-- The last coefficient of a list, or `0` for the empty list — the leading coefficient once applied to a
trimmed polynomial. -/
def lastOrZero : List Int → Int
  | [] => 0
  | coeff :: [] => coeff
  | _ :: (nextCoeff :: rest) => lastOrZero (nextCoeff :: rest)

/-- Degree of the polynomial: one less than the trimmed length (the zero polynomial gets `0`). -/
def polyDegree (coeffs : List Int) : Nat :=
  (polyTrim coeffs).length - 1

/-- Leading coefficient: the last surviving coefficient after trimming (`0` for the zero polynomial). -/
def polyLeadingCoeff (coeffs : List Int) : Int :=
  lastOrZero (polyTrim coeffs)

/-! ## Trimming preserves evaluation (the soundness of the normal form) -/

/-- **Trimming preserves evaluation.**  `polyEval point (polyTrim p) = polyEval point p`: the dropped
trailing zeros contribute `0` at every point.  Induction on the coefficient list, casing on the trimmed
tail and (when empty) on whether the head is zero. -/
theorem polyTrimPreservesEval (point : Int) :
    ∀ coeffs : List Int, polyEval point (polyTrim coeffs) = polyEval point coeffs
  | [] => rfl
  | coeff :: restCoeffs => by
      have ihTail : polyEval point (polyTrim restCoeffs) = polyEval point restCoeffs :=
        polyTrimPreservesEval point restCoeffs
      show polyEval point
          (match polyTrim restCoeffs with
            | [] =>
                match Int.decEq coeff 0 with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail)
        = coeff + point * polyEval point restCoeffs
      cases hTrim : polyTrim restCoeffs with
      | nil =>
          rw [hTrim] at ihTail
          cases Int.decEq coeff 0 with
          | isTrue hHeadZero =>
              show (0 : Int) = coeff + point * polyEval point restCoeffs
              rw [hHeadZero, ← ihTail]
              exact ((intZeroAdd (point * polyEval point ([] : List Int))).trans
                (intMulZero point)).symm
          | isFalse _ =>
              show coeff + point * polyEval point ([] : List Int)
                  = coeff + point * polyEval point restCoeffs
              exact congrArg (coeff + point * ·) ihTail
      | cons trimHead trimTail =>
          rw [hTrim] at ihTail
          show coeff + point * polyEval point (trimHead :: trimTail)
              = coeff + point * polyEval point restCoeffs
          exact congrArg (coeff + point * ·) ihTail

/-! ## Groundings -/

/-- `polyTrim` drops trailing zeros: `polyTrim [3, 0, 0] = [3]`. -/
theorem polyTrimDropsTrailingZeros : polyTrim [3, 0, 0] = [3] := by decide

/-- Interior zeros are kept: `polyTrim [1, 0, 2, 0, 0] = [1, 0, 2]`. -/
theorem polyTrimKeepsInteriorZeros : polyTrim [1, 0, 2, 0, 0] = [1, 0, 2] := by decide

/-- `1 + 2x²` has degree `2`: `polyDegree [1, 0, 2, 0, 0] = 2`. -/
theorem polyDegreeExample : polyDegree [1, 0, 2, 0, 0] = 2 := by decide

/-- Its leading coefficient is `2`: `polyLeadingCoeff [1, 0, 2, 0, 0] = 2`. -/
theorem polyLeadingCoeffExample : polyLeadingCoeff [1, 0, 2, 0, 0] = 2 := by decide

/-- The zero polynomial has degree `0` and leading coefficient `0` (the convention). -/
theorem polyDegreeZeroPolynomial : polyDegree [0, 0, 0] = 0 := by decide

theorem polyLeadingCoeffZeroPolynomial : polyLeadingCoeff [0, 0, 0] = 0 := by decide

/-- The linear factor `x − 5` is monic of degree `1`: `polyDegree (polyLinearFactor 5) = 1` and its leading
coefficient is `1`. -/
theorem polyDegreeLinearFactor : polyDegree (polyLinearFactor 5) = 1 := by decide

theorem polyLeadingCoeffLinearFactor : polyLeadingCoeff (polyLinearFactor 5) = 1 := by decide

/-- Consolidated marker for the ℤ[x] degree and leading-coefficient sub-arc.  Covers: the trailing-zero
normal form, degree, leading coefficient, and evaluation-preservation of trimming (this file); the
leading-coefficient↔positional-coefficient bridge (`IntPolynomialLeadingCoeff`); the nonzero leading
coefficient and the strict degree bound from coefficient vanishing (`IntPolynomialDegreeBound`); and the
fundamental degree law `polyDegree (polyMul p q) = polyDegree p + polyDegree q` with the divisibility
corollary (`IntPolynomialDegreeMul`). -/
def fxIntPoly_hasDegreeAndLeadingCoefficient : Bool := true

end FX1Poly.ComputerAlgebra

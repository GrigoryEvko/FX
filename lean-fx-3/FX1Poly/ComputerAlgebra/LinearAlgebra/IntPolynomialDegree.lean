import FX1Poly.ComputerAlgebra.LinearAlgebra.IntUnivariatePolynomial

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialDegree — degree, leading coefficient, normal form
(the second brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntUnivariatePolynomial` shipped the ℤ[x] ring with evaluation proved to be a ring homomorphism.  The
Euclidean/pseudo-division layer — the next step toward the invariant-factor GCD — needs a *degree* and a
*leading coefficient*, and those need a canonical form because the ascending coefficient list carries
trailing zeros (`[3]` and `[3, 0, 0]` denote the same polynomial `3`).

## The normal form

`polyTrim` drops trailing zeros, structural on the list (case on the *recursively* trimmed tail: an empty
trimmed tail defers to whether this coefficient is zero, a non-empty one keeps the whole prefix).
`polyDegree` is `(length of the trimmed list) − 1` (the zero polynomial gets `0` by convention);
`polyLeadingCoeff` is the last surviving coefficient (`0` for the zero polynomial).

## What is PROVEN

`polyTrimPreservesEval`: trimming does not change the value at any point — `polyEval point (polyTrim p) =
polyEval point p`.  This is what makes the normal form *sound*: the trimmed polynomial is the same
function, so degree/leading-coefficient computed on it describe the genuine polynomial.  The proof is the
zero coefficient's arithmetic (`0 + point·0 = 0`), the delicate case being an all-zero tail under a zero
head.

## Zero-axiom design

`polyTrim`'s only non-list case analysis is `Int.decEq coeff 0` (matched on the `isTrue`/`isFalse`
constructors — a full enumeration, no wildcard).  Every arithmetic step routes through the corpus `Int`
lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialDegree.lean`.
-/

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
trailing zeros contribute `0` at every point, so the canonical representative is the same function.  Proof
by induction on the coefficient list, casing on the trimmed tail and (when empty) on whether the head is
zero. -/
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
          -- ihTail : polyEval point [] = polyEval point restCoeffs, i.e. (0 : Int) = polyEval point restCoeffs
          cases Int.decEq coeff 0 with
          | isTrue hHeadZero =>
              -- goal: polyEval point [] = coeff + point * polyEval point restCoeffs
              show (0 : Int) = coeff + point * polyEval point restCoeffs
              rw [hHeadZero, ← ihTail]
              -- goal: (0 : Int) = 0 + point * polyEval point []
              exact ((intZeroAdd (point * polyEval point ([] : List Int))).trans
                (intMulZero point)).symm
          | isFalse _ =>
              -- goal: polyEval point [coeff] = coeff + point * polyEval point restCoeffs
              show coeff + point * polyEval point ([] : List Int)
                  = coeff + point * polyEval point restCoeffs
              exact congrArg (coeff + point * ·) ihTail
      | cons trimHead trimTail =>
          -- goal: polyEval point (coeff :: trimHead :: trimTail) = coeff + point * polyEval point restCoeffs
          rw [hTrim] at ihTail
          -- ihTail : polyEval point (trimHead :: trimTail) = polyEval point restCoeffs
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

/-- Marker: the ℤ[x] degree/normal-form layer ships with a canonical (trailing-zero-free) representative,
degree, and leading coefficient, and the proof that trimming preserves evaluation.  The
Euclidean/pseudo-division algorithm (recursion on the degree difference) is the next brick. -/
def fxIntPoly_hasDegreeAndLeadingCoefficient : Bool := true

end FX1Poly.ComputerAlgebra

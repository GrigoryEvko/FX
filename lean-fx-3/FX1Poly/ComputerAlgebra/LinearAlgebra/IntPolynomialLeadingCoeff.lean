import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeff
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialLeadingCoeff — the degree↔coefficient bridge
(the sixth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

`IntPolynomialDegree` measures the leading coefficient as `lastOrZero (polyTrim coeffs)` — the last
surviving entry after trailing-zero trimming.  `IntPolynomialCoeff` reads a coefficient positionally.  The
pseudo-division degree-decrease needs these two views to agree: the leading coefficient *is* the
coefficient at the degree position.

## What is PROVEN

`polyLeadingCoeffEqCoeffDegree`: `polyLeadingCoeff p = polyCoeff p (polyDegree p)`.  Because `polyTrim`
keeps a prefix of the list and only drops trailing zeros, reading position `(polyTrim p).length − 1` in the
original list lands on the last surviving coefficient — exactly `lastOrZero (polyTrim p)`.  The proof is
one induction over the list, casing on the trimmed tail (and, when empty, on whether the head is zero),
the same shape as `polyTrimPreservesEval`.

This is the leading-term-cancellation lever's second half: with `polyCoeffMonomialMul` computing the
quotient-term product's top coefficient, and this bridge identifying leading coefficients with positional
ones, the pseudo-division step's top coefficient is `leadDivisor · leadDividend − leadDividend ·
leadDivisor = 0`.

## Zero-axiom design

Structural induction on the coefficient list; the only non-list case analysis is `Int.decEq coeff 0` (full
`isTrue`/`isFalse` enumeration).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialLeadingCoeff.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The positional reading at the degree index equals the last trimmed coefficient -/

/-- Reading the original list at index `(polyTrim coeffs).length − 1` returns the last surviving
coefficient `lastOrZero (polyTrim coeffs)`.  Induction on the list: an empty trimmed tail defers to the
head's zeroness; a non-empty trimmed tail slides the index down by one and recurses. -/
theorem polyCoeffTrimLengthEqLastOrZero :
    ∀ coeffs : List Int,
      polyCoeff coeffs ((polyTrim coeffs).length - 1) = lastOrZero (polyTrim coeffs)
  | [] => rfl
  | coeff :: restCoeffs => by
      show polyCoeff (coeff :: restCoeffs)
          ((match polyTrim restCoeffs with
            | [] =>
                match Int.decEq coeff 0 with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail).length - 1)
        = lastOrZero
            (match polyTrim restCoeffs with
              | [] =>
                  match Int.decEq coeff 0 with
                  | isTrue _ => []
                  | isFalse _ => [coeff]
              | trimHead :: trimTail => coeff :: trimHead :: trimTail)
      cases hTrim : polyTrim restCoeffs with
      | nil =>
          cases Int.decEq coeff 0 with
          | isTrue hHeadZero =>
              show polyCoeff (coeff :: restCoeffs) 0 = (0 : Int)
              exact hHeadZero
          | isFalse _ => rfl
      | cons trimHead trimTail =>
          have ihTail := polyCoeffTrimLengthEqLastOrZero restCoeffs
          rw [hTrim] at ihTail
          show polyCoeff restCoeffs trimTail.length = lastOrZero (trimHead :: trimTail)
          exact ihTail

/-! ## The bridge -/

/-- **The leading coefficient is the coefficient at the degree position.**  `polyLeadingCoeff p =
polyCoeff p (polyDegree p)` — unfolding `polyLeadingCoeff = lastOrZero ∘ polyTrim` and `polyDegree =
(polyTrim ·).length − 1`, this is exactly `polyCoeffTrimLengthEqLastOrZero`. -/
theorem polyLeadingCoeffEqCoeffDegree (coeffs : List Int) :
    polyLeadingCoeff coeffs = polyCoeff coeffs (polyDegree coeffs) :=
  (polyCoeffTrimLengthEqLastOrZero coeffs).symm

/-! ## Groundings -/

/-- `1 + 2x²` (padded) has leading coefficient `2` at its degree position `2`: both
`polyLeadingCoeff [1, 0, 2, 0, 0]` and `polyCoeff [1, 0, 2, 0, 0] (polyDegree [1, 0, 2, 0, 0])` are `2`. -/
theorem polyLeadingCoeffBridgeGrounding :
    polyLeadingCoeff [1, 0, 2, 0, 0] = polyCoeff [1, 0, 2, 0, 0] (polyDegree [1, 0, 2, 0, 0]) := by decide

/-- The zero polynomial: leading coefficient `0` equals the coefficient at its (conventional) degree `0`. -/
theorem polyLeadingCoeffBridgeZeroGrounding :
    polyLeadingCoeff [0, 0, 0] = polyCoeff [0, 0, 0] (polyDegree [0, 0, 0]) := by decide

/-- Marker: the ℤ[x] leading coefficient (measured on the trailing-zero-free normal form) equals the
positional coefficient at the degree index — the second half of the pseudo-division leading-term
cancellation, joining `polyCoeffMonomialMul`. -/
def fxIntPoly_hasLeadingCoeffAtDegree : Bool := true

end FX1Poly.ComputerAlgebra

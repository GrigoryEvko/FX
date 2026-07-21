import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeff
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree

/-! # IntPolynomialLeadingCoeff — the degree↔coefficient bridge

`IntPolynomialDegree` measures the leading coefficient as `lastOrZero (polyTrim coeffs)`;
`IntPolynomialCoeff` reads a coefficient positionally.  The pseudo-division degree-decrease needs these two
views to agree: `polyLeadingCoeffEqCoeffDegree` proves `polyLeadingCoeff p = polyCoeff p (polyDegree p)`,
because `polyTrim` keeps a prefix and only drops trailing zeros, so reading position `(polyTrim p).length −
1` lands on the last surviving coefficient.  Together with `polyCoeffMonomialMul`, this identifies the
pseudo-division step's top coefficient as `leadDivisor · leadDividend − leadDividend · leadDivisor = 0`.

Structural induction on the coefficient list; the only non-list case analysis is `Int.decEq coeff 0`.  Free
of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

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

end FX1Poly.ComputerAlgebra

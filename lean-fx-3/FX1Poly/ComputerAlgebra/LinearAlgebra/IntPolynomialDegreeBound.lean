import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeffBounds

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialDegreeBound — degree from coefficient vanishing
(the ninth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

To turn r17's leading-term cancellation into a strict degree drop we need the converse of the coefficient
bounds: a polynomial whose coefficients all vanish at and above a positive bound has degree strictly below
that bound.  The lever is the *nonzero* leading coefficient — the whole point of the trailing-zero trim.

## What is PROVEN

  * `polyTrimNilOrLastNonzero`: the trimmed list is either empty or ends in a nonzero coefficient (the trim
    invariant).
  * `polyLeadingCoeffNonzeroWhenNonempty`: hence a nonzero polynomial's leading coefficient is nonzero.
  * `polyCoeffAtDegreeNonzeroWhenNonempty`: equivalently (via the r16 bridge), `polyCoeff p (polyDegree p) ≠
    0` for a nonzero `p`.
  * `polyDegreeLtOfCoeffVanishingAbove`: if `polyCoeff p k = 0` for all `k ≥ bound` and `1 ≤ bound`, then
    `polyDegree p < bound` — since otherwise the (nonzero) leading coefficient sits at position ≥ bound.

## Zero-axiom design

Structural induction with `Int.decEq` casing and constructive Nat decidability
(`Nat.lt_of_not_le`); `List.cons_ne_nil`, `Or.resolve_left`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialDegreeBound.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The trim invariant: a trimmed list ends in a nonzero coefficient -/

/-- **A trimmed list is empty or ends nonzero.**  `polyTrim coeffs = [] ∨ lastOrZero (polyTrim coeffs) ≠
0`: trimming removes exactly the trailing zeros, so a surviving list has a nonzero last entry.  Induction
on the list, casing the trimmed tail (and, when empty, the head's zeroness). -/
theorem polyTrimNilOrLastNonzero :
    ∀ coeffs : List Int, polyTrim coeffs = [] ∨ lastOrZero (polyTrim coeffs) ≠ 0
  | [] => Or.inl rfl
  | coeff :: restCoeffs => by
      show (match polyTrim restCoeffs with
            | [] =>
                match Int.decEq coeff 0 with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail) = []
        ∨ lastOrZero
            (match polyTrim restCoeffs with
              | [] =>
                  match Int.decEq coeff 0 with
                  | isTrue _ => []
                  | isFalse _ => [coeff]
              | trimHead :: trimTail => coeff :: trimHead :: trimTail) ≠ 0
      cases hTrim : polyTrim restCoeffs with
      | nil =>
          cases Int.decEq coeff 0 with
          | isTrue _ => exact Or.inl rfl
          | isFalse hHeadNonzero => exact Or.inr hHeadNonzero
      | cons trimHead trimTail =>
          have ihTail := polyTrimNilOrLastNonzero restCoeffs
          rw [hTrim] at ihTail
          exact Or.inr (ihTail.resolve_left (List.cons_ne_nil trimHead trimTail))

/-! ## The nonzero leading coefficient -/

/-- **A nonzero polynomial has a nonzero leading coefficient.**  `polyTrim coeffs ≠ [] → polyLeadingCoeff
coeffs ≠ 0` — resolve the trim invariant against nonemptiness. -/
theorem polyLeadingCoeffNonzeroWhenNonempty (coeffs : List Int) (isTrimNonempty : polyTrim coeffs ≠ []) :
    polyLeadingCoeff coeffs ≠ 0 :=
  (polyTrimNilOrLastNonzero coeffs).resolve_left isTrimNonempty

/-- **The coefficient at the degree position is nonzero for a nonzero polynomial.**  `polyTrim coeffs ≠ []
→ polyCoeff coeffs (polyDegree coeffs) ≠ 0` — the leading coefficient (nonzero) is exactly that positional
coefficient (r16 bridge). -/
theorem polyCoeffAtDegreeNonzeroWhenNonempty (coeffs : List Int) (isTrimNonempty : polyTrim coeffs ≠ []) :
    polyCoeff coeffs (polyDegree coeffs) ≠ 0 :=
  fun coeffIsZero =>
    polyLeadingCoeffNonzeroWhenNonempty coeffs isTrimNonempty
      ((polyLeadingCoeffEqCoeffDegree coeffs).trans coeffIsZero)

/-! ## Degree strictly below a bound from coefficient vanishing -/

/-- **Coefficients vanishing at and above a positive bound force the degree below it.**  If `polyCoeff p k =
0` for all `k ≥ bound` and `1 ≤ bound`, then `polyDegree p < bound`.  For the zero polynomial the degree is
`0 < bound`; otherwise the nonzero leading coefficient — sitting at `polyDegree p` — would have to vanish
were `bound ≤ polyDegree p`, a contradiction. -/
theorem polyDegreeLtOfCoeffVanishingAbove (coeffs : List Int) (bound : Nat) (isPositiveBound : 1 ≤ bound)
    (isVanishingAbove : ∀ position : Nat, bound ≤ position → polyCoeff coeffs position = 0) :
    polyDegree coeffs < bound := by
  cases hTrim : polyTrim coeffs with
  | nil =>
      have degreeIsZero : polyDegree coeffs = 0 := by
        show (polyTrim coeffs).length - 1 = 0
        rw [hTrim]
        rfl
      rw [degreeIsZero]
      exact isPositiveBound
  | cons trimHead trimTail =>
      have isTrimNonempty : polyTrim coeffs ≠ [] := by
        rw [hTrim]; exact List.cons_ne_nil trimHead trimTail
      apply Nat.lt_of_not_le
      intro isBoundLeDegree
      exact absurd (isVanishingAbove (polyDegree coeffs) isBoundLeDegree)
        (polyCoeffAtDegreeNonzeroWhenNonempty coeffs isTrimNonempty)

/-! ## Groundings -/

/-- `x + 2` (`[2, 1]`) has a nonzero leading coefficient `1`: `polyLeadingCoeff [2, 1] ≠ 0`. -/
theorem polyLeadingCoeffNonzeroGrounding : polyLeadingCoeff [2, 1] ≠ (0 : Int) := by decide

/-- `polyCoeff [2, 1] (polyDegree [2, 1]) = polyCoeff [2, 1] 1 = 1 ≠ 0`. -/
theorem polyCoeffAtDegreeNonzeroGrounding : polyCoeff [2, 1] (polyDegree [2, 1]) ≠ (0 : Int) := by decide

/-- Marker: the ℤ[x] degree-from-coefficient-vanishing lever ships — the trim invariant (nonzero last
coefficient), the nonzero leading coefficient, and the strict degree bound when coefficients vanish above a
positive bound.  This turns r17's leading-term cancellation into a strict degree drop. -/
def fxIntPoly_hasDegreeFromCoefficientVanishing : Bool := true

end FX1Poly.ComputerAlgebra

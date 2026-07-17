import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingCoeff

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialCoeffBounds — coefficients vanish past the degree
(the eighth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The degree-decrease needs the *upper* bound facts to complement r17's leading-term cancellation: the
pseudo-division step's replacement dividend has coefficient `0` not only *at* the old top position but
*above* it too.  Those rest on two clean, reusable coefficient bounds.

## What is PROVEN

  * `polyCoeffPastLength`: reading a list at or past its own length returns `0`.
  * `polyCoeffTrimAgree`: trimming trailing zeros never changes a positional coefficient —
    `polyCoeff (polyTrim p) k = polyCoeff p k` for *every* `k` (below the trimmed length they agree as a
    prefix; at or above it both read `0`).
  * `polyCoeffZeroFromTrimLength`: consequently, reading the original list at or past the *trimmed* length
    (hence strictly above the degree) returns `0`.

## Zero-axiom design

Structural induction on the list and the position; the only non-list case analysis is `Int.decEq coeff 0`
(full enumeration).  The Nat plumbing is core `Nat.le_of_succ_le_succ` / `Nat.not_succ_le_zero`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialCoeffBounds.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## Reading past the end of a list -/

/-- **Past the length, every coefficient is zero.**  `coeffs.length ≤ position → polyCoeff coeffs position
= 0`, by simultaneous structural recursion on the list and the position. -/
theorem polyCoeffPastLength :
    ∀ (coeffs : List Int) (position : Nat), coeffs.length ≤ position → polyCoeff coeffs position = 0
  | [], _, _ => rfl
  | _ :: _, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | _ :: restCoeffs, position + 1, hLe =>
      polyCoeffPastLength restCoeffs position (Nat.le_of_succ_le_succ hLe)

/-! ## Trimming preserves every coefficient -/

/-- **Trimming trailing zeros never changes a coefficient.**  `polyCoeff (polyTrim p) k = polyCoeff p k`
for every position `k`: below the trimmed length the trimmed list is a prefix, and at or above it both
sides read `0` (the trimmed list past its end, the original at a dropped trailing zero).  Induction on the
list (casing the trimmed tail, and — when empty — the head's zeroness) and the position. -/
theorem polyCoeffTrimAgree :
    ∀ (coeffs : List Int) (position : Nat),
      polyCoeff (polyTrim coeffs) position = polyCoeff coeffs position
  | [], _ => rfl
  | coeff :: restCoeffs, position => by
      show polyCoeff
          (match polyTrim restCoeffs with
            | [] =>
                match Int.decEq coeff 0 with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail) position
        = polyCoeff (coeff :: restCoeffs) position
      cases hTrim : polyTrim restCoeffs with
      | nil =>
          cases Int.decEq coeff 0 with
          | isTrue hHeadZero =>
              cases position with
              | zero => exact hHeadZero.symm
              | succ priorPosition =>
                  have ihTail := polyCoeffTrimAgree restCoeffs priorPosition
                  rw [hTrim] at ihTail
                  exact ihTail
          | isFalse _ =>
              cases position with
              | zero => rfl
              | succ priorPosition =>
                  have ihTail := polyCoeffTrimAgree restCoeffs priorPosition
                  rw [hTrim] at ihTail
                  exact ihTail
      | cons trimHead trimTail =>
          cases position with
          | zero => rfl
          | succ priorPosition =>
              have ihTail := polyCoeffTrimAgree restCoeffs priorPosition
              rw [hTrim] at ihTail
              exact ihTail

/-! ## Coefficients vanish at and above the trimmed length -/

/-- **At or above the trimmed length, the coefficient is zero.**  `(polyTrim p).length ≤ position →
polyCoeff p position = 0` — the original list agrees with its trim (`polyCoeffTrimAgree`), which reads `0`
past its own length (`polyCoeffPastLength`).  Since `polyDegree p = (polyTrim p).length − 1`, this says
every coefficient strictly above the degree vanishes. -/
theorem polyCoeffZeroFromTrimLength (coeffs : List Int) (position : Nat)
    (isTrimLengthLe : (polyTrim coeffs).length ≤ position) : polyCoeff coeffs position = 0 :=
  (polyCoeffTrimAgree coeffs position).symm.trans
    (polyCoeffPastLength (polyTrim coeffs) position isTrimLengthLe)

/-! ## Groundings -/

/-- Past the length reads `0`: `polyCoeff [1, 2, 3] 7 = 0`. -/
theorem polyCoeffPastLengthGrounding : polyCoeff [1, 2, 3] 7 = 0 := by decide

/-- Trimming agrees: at position `2`, `polyCoeff (polyTrim [5, 0, 0, 0]) 2 = polyCoeff [5, 0, 0, 0] 2`
(both `0`, one past the trimmed `[5]`, the other a dropped trailing zero). -/
theorem polyCoeffTrimAgreeGrounding :
    polyCoeff (polyTrim [5, 0, 0, 0]) 2 = polyCoeff [5, 0, 0, 0] 2 := by decide

/-- Marker: the ℤ[x] coefficient bounds ship — reading past a list's length, trimming-agreement at every
position, and the corollary that coefficients at/above the trimmed length (strictly above the degree)
vanish.  These are the upper-bound half of the pseudo-division degree-decrease. -/
def fxIntPoly_hasCoefficientVanishingBounds : Bool := true

end FX1Poly.ComputerAlgebra

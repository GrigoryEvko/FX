import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmith

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # RationalPolynomialSmithFixedPoint — the ℚ[x] Smith cross fixed point

Building on the one-pass cross clear of `RationalPolynomialSmith` (`rsmCrossClear` replaces every off-pivot
entry of the pivot's row and column by its Euclidean residue against the pivot), this module ships the reduced
cross fixed point. Because each cross entry is reduced modulo the pivot independently — a column entry never
touches a row entry, and no per-entry clear reads another — there is no re-fill: one pass drives every
off-pivot cross entry below the pivot at once.

`rsfCrossDegreeSum` is the cross measure, a single `Nat` summing the trimmed lengths of the off-pivot entries
of the pivot row (`rsfRowWeightExcept`) and column (`rsfColumnWeightExcept`), zero exactly when the cross is
annihilated. The reduced-cross predicate `rsfCrossIsReduced` (every off-pivot cross entry trims to `[]` or has
degree below the pivot) is reached by one pass (`rsfClearCrossReachesReducedCross`) and by every positive fuel
of the iterator (`rsfClearCrossIterateReduced`). The reduced cross is a genuine fixed point: a below-pivot
entry is clear-stable (`rsfClearAgainstStableBelowPivot`) and a zero entry stays zero
(`rsfClearZeroTrimsZero`), so a further pass leaves it entrywise fixed (`rsfClearAgainstPreservesBelow`). It
also ships the `(r-1)×(c-1)` submatrix extractor `rsfSubmatrix` (the descent seed).

The all-zero cleared cross is not reached by re-running the fixed pivot (a below-pivot residue is
division-stable); it needs the Smith re-pivot, supplied downstream in `RationalPolynomialSmithDriver`
(`rseHasAllZeroCrossViaRepivot`). The full Smith normal form remains walled (`rsiHasSmithNormalForm`).

Every definition is structural on the list, the positional index, or the `Nat` fuel; the only non-list case
analysis is `Nat.decLt` (full enumeration). No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`, `funext`, or `WellFounded.fix`. Per-declaration audit twin in the matching
`FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the cross measure -/

/-- The weight of an entry: its trimmed length (`0` iff the entry trims to the zero polynomial). -/
def rsfEntryWeight (entry : List QnfRat) : Nat := (rpxTrim entry).length

/-- Sum of entry weights over a whole row. -/
def rsfRowWeight : List (List QnfRat) → Nat
  | [] => 0
  | entry :: rest => rsfEntryWeight entry + rsfRowWeight rest

/-- Sum of entry weights over a row, skipping the entry at `skipCol` (the pivot column). -/
def rsfRowWeightExcept : List (List QnfRat) → Nat → Nat
  | [], _ => 0
  | _entry :: rest, 0 => rsfRowWeight rest
  | entry :: rest, position + 1 => rsfEntryWeight entry + rsfRowWeightExcept rest position

/-- Sum of the pivot-column entry weights over all rows of a matrix. -/
def rsfColumnWeight : List (List (List QnfRat)) → Nat → Nat
  | [], _ => 0
  | row :: rest, pivotCol => rsfEntryWeight (rbzEntryGet row pivotCol) + rsfColumnWeight rest pivotCol

/-- Sum of the pivot-column entry weights over all rows, skipping the row at `skipRow` (the pivot row). -/
def rsfColumnWeightExcept : List (List (List QnfRat)) → Nat → Nat → Nat
  | [], _, _ => 0
  | _row :: rest, pivotCol, 0 => rsfColumnWeight rest pivotCol
  | row :: rest, pivotCol, position + 1 =>
      rsfEntryWeight (rbzEntryGet row pivotCol) + rsfColumnWeightExcept rest pivotCol position

/-- The cross measure: the total weight of the off-pivot entries of the pivot row and column, `0` exactly
when every off-pivot cross entry trims to the zero polynomial. -/
def rsfCrossDegreeSum (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) : Nat :=
  rsfRowWeightExcept (rbzRowGet matrix pivotRow) pivotCol
    + rsfColumnWeightExcept matrix pivotCol pivotRow

/-! ## T2 — the reduced-cross fixed point -/

/-- An entry is reduced below the pivot when it trims to zero or has degree strictly below the pivot's. -/
def rsfIsBelowPivot (pivot entry : List QnfRat) : Prop :=
  rpxTrim entry = [] ∨ rpxDegree entry < rpxDegree pivot

/-- The reduced-cross predicate: every off-pivot entry of the pivot's row and column is below the pivot. -/
def rsfCrossIsReduced (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) : Prop :=
  (∀ colPosition : Nat, colPosition ≠ pivotCol →
      rsfIsBelowPivot pivot (rbzMatrixEntry matrix pivotRow colPosition))
    ∧ (∀ rowPosition : Nat, rowPosition ≠ pivotRow →
      rsfIsBelowPivot pivot (rbzMatrixEntry matrix rowPosition pivotCol))

/-- The fixed-point driver: a single cross clear reaches the reduced fixed point (no fuel loop needed). -/
def rsfClearCross (pivot : List QnfRat) (pivotCol : Nat)
    (matrix : List (List (List QnfRat))) (pivotRow : Nat) : List (List (List QnfRat)) :=
  rsmCrossClear pivot pivotCol matrix pivotRow

/-- The fuel-structural iterator: applies the fixed-pivot cross clear `fuel` times; one application already
reaches the reduced cross, and further passes are entrywise stable. -/
def rsfClearCrossIterate (pivot : List QnfRat) (pivotCol pivotRow : Nat) :
    Nat → List (List (List QnfRat)) → List (List (List QnfRat))
  | 0, matrix => matrix
  | fuel + 1, matrix =>
      rsmCrossClear pivot pivotCol (rsfClearCrossIterate pivot pivotCol pivotRow fuel matrix) pivotRow

/-! ### The Euclidean-residue stability lemmas (the genuine fixed-point evidence) -/

/-- A below-degree dividend is its own remainder: `deg dividend < deg divisor` fires the first guard,
returning quotient `[]` and remainder `dividend`. -/
theorem rsfDivModSmallRemainder (fuel : Nat) (divisor dividend : List QnfRat)
    (hbelow : rpxDegree dividend < rpxDegree divisor) :
    (rpxDivMod (fuel + 1) divisor dividend).2 = dividend := by
  dsimp only [rpxDivMod]
  cases hcmp : Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
  | isTrue _ => rfl
  | isFalse hnot => exact absurd hbelow hnot

/-- Clearing a below-pivot entry is the identity: `deg entry < deg pivot ⟹ rsmClearAgainst pivot entry =
entry` (quotient `0`), which is why the fixed-pivot clear cannot reach the all-zero cross. -/
theorem rsfClearAgainstStableBelowPivot (pivot entry : List QnfRat)
    (hbelow : rpxDegree entry < rpxDegree pivot) : rsmClearAgainst pivot entry = entry := by
  cases entry with
  | nil => rfl
  | cons headCoeff restCoeffs =>
      show (rpxDivMod (headCoeff :: restCoeffs).length pivot (headCoeff :: restCoeffs)).2
        = headCoeff :: restCoeffs
      exact rsfDivModSmallRemainder restCoeffs.length pivot (headCoeff :: restCoeffs) hbelow

/-- A zero dividend has a zero remainder: the step preserves the nil trim (`rpdStepPreservesTrimNil`), so
the whole recursion does. -/
theorem rsfDivModZeroDividend :
    ∀ (fuel : Nat) (divisor dividend : List QnfRat),
      rpxTrim dividend = [] → rpxTrim (rpxDivMod fuel divisor dividend).2 = []
  | 0, _divisor, _dividend, dividendTrimNil => dividendTrimNil
  | fuel + 1, divisor, dividend, dividendTrimNil => by
      dsimp only [rpxDivMod]
      cases Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
      | isTrue _ => exact dividendTrimNil
      | isFalse _ =>
          exact rsfDivModZeroDividend fuel divisor
            (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))
            (rpdStepPreservesTrimNil divisor dividend dividendTrimNil)

/-- Clearing a zero entry yields a zero entry. -/
theorem rsfClearZeroTrimsZero (pivot entry : List QnfRat) (entryTrimNil : rpxTrim entry = []) :
    rpxTrim (rsmClearAgainst pivot entry) = [] :=
  rsfDivModZeroDividend entry.length pivot entry entryTrimNil

/-- The reduced predicate is entrywise clear-stable: a below-pivot entry stays below-pivot after another
clear, so the reduced cross is a genuine fixed point of the per-entry clear. -/
theorem rsfClearAgainstPreservesBelow (pivot entry : List QnfRat)
    (belowPivot : rsfIsBelowPivot pivot entry) :
    rsfIsBelowPivot pivot (rsmClearAgainst pivot entry) := by
  cases belowPivot with
  | inl entryTrimNil => exact Or.inl (rsfClearZeroTrimsZero pivot entry entryTrimNil)
  | inr degreeBelow =>
      rw [rsfClearAgainstStableBelowPivot pivot entry degreeBelow]
      exact Or.inr degreeBelow

/-! ### Reaching the reduced cross -/

/-- One cross clear reaches the reduced cross: for a nonzero pivot `rsfClearCross` drives every off-pivot
cross entry below the pivot (bundling `rsmCrossClearRowMeasure`/`rsmCrossClearColMeasure`). -/
theorem rsfClearCrossReachesReducedCross (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (pivotNonzero : rpxTrim pivot ≠ []) :
    rsfCrossIsReduced pivot pivotCol pivotRow (rsfClearCross pivot pivotCol matrix pivotRow) :=
  ⟨fun colPosition hne =>
      rsmCrossClearRowMeasure pivot pivotCol pivotRow matrix pivotNonzero colPosition hne,
   fun rowPosition hne =>
      rsmCrossClearColMeasure pivot pivotCol pivotRow matrix pivotNonzero rowPosition hne⟩

/-- Every positive fuel of the iterator reaches the reduced cross: the outermost pass produces a reduced
cross regardless of its input. -/
theorem rsfClearCrossIterateReduced (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (fuel : Nat) (matrix : List (List (List QnfRat))) (pivotNonzero : rpxTrim pivot ≠ []) :
    rsfCrossIsReduced pivot pivotCol pivotRow
      (rsfClearCrossIterate pivot pivotCol pivotRow (fuel + 1) matrix) := by
  show rsfCrossIsReduced pivot pivotCol pivotRow
      (rsmCrossClear pivot pivotCol
        (rsfClearCrossIterate pivot pivotCol pivotRow fuel matrix) pivotRow)
  exact rsfClearCrossReachesReducedCross pivot pivotCol pivotRow
    (rsfClearCrossIterate pivot pivotCol pivotRow fuel matrix) pivotNonzero

/-! ## T3 — the submatrix extractor (the descent seed) -/

/-- Delete the entry at `position` from a row (identity past the end). -/
def rsfDropEntry : List (List QnfRat) → Nat → List (List QnfRat)
  | [], _ => []
  | _entry :: rest, 0 => rest
  | entry :: rest, position + 1 => entry :: rsfDropEntry rest position

/-- Delete the row at `position` from a matrix (identity past the end). -/
def rsfDropRow : List (List (List QnfRat)) → Nat → List (List (List QnfRat))
  | [], _ => []
  | _row :: rest, 0 => rest
  | row :: rest, position + 1 => row :: rsfDropRow rest position

/-- Delete the pivot column from every row of a matrix. -/
def rsfDropColumn : List (List (List QnfRat)) → Nat → List (List (List QnfRat))
  | [], _ => []
  | row :: rest, pivotCol => rsfDropEntry row pivotCol :: rsfDropColumn rest pivotCol

/-- The `(r-1)×(c-1)` submatrix extractor: delete the pivot's row and column, the trailing submatrix on
which Smith descent recurses. -/
def rsfSubmatrix (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) :
    List (List (List QnfRat)) :=
  rsfDropColumn (rsfDropRow matrix pivotRow) pivotCol

/-! ## Groundings (fires) -/

set_option maxRecDepth 8192

/-- Fire: the off-pivot cross of `[[x²−1, x−1], [x+1, 1]]` about the pivot at `(1,1)` weighs `4`. -/
theorem rsfFireCrossMeasureValue : rsfCrossDegreeSum rsmFireMatrix 1 1 = 4 := rfl

/-- Fire: the constant pivot `1` divides every cross entry, so one clear drops the measure to `0`. -/
theorem rsfFireCrossMeasureAfterClearIsZero :
    rsfCrossDegreeSum (rsfClearCross [qnfOfInt 1] 1 rsmFireMatrix 1) 1 1 = 0 := rfl

/-- Fire: iterating the clear twice still leaves the cross annihilated (measure `0`). -/
theorem rsfFireIterateMeasureZero :
    rsfCrossDegreeSum (rsfClearCrossIterate [qnfOfInt 1] 1 1 2 rsmFireMatrix) 1 1 = 0 := rfl

/-- Fire: clearing the constant `2` against the pivot `x − 1` (degree `0 < 1`) is the identity. -/
theorem rsfFireClearStableConstant :
    rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] = [qnfOfInt 2] := rfl

/-- Fire: the same identity through `rsfClearAgainstStableBelowPivot`. -/
theorem rsfFireClearStableTheorem :
    rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] = [qnfOfInt 2] :=
  rsfClearAgainstStableBelowPivot [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] (Nat.le_refl 1)

/-- Fire: one cross clear of the fire matrix about the pivot at `(1,1)` reduces the whole cross. -/
theorem rsfFireDriverReachesReduced :
    rsfCrossIsReduced [qnfOfInt 1] 1 1 (rsfClearCross [qnfOfInt 1] 1 rsmFireMatrix 1) :=
  rsfClearCrossReachesReducedCross [qnfOfInt 1] 1 1 rsmFireMatrix
    (by show rpxTrim [qnfOfInt 1] ≠ []; exact List.cons_ne_nil (qnfOfInt 1) [])

/-- Fire: two iterations of the clear leave the cross reduced below the pivot. -/
theorem rsfFireIterateReachesReduced :
    rsfCrossIsReduced [qnfOfInt 1] 1 1 (rsfClearCrossIterate [qnfOfInt 1] 1 1 2 rsmFireMatrix) :=
  rsfClearCrossIterateReduced [qnfOfInt 1] 1 1 1 rsmFireMatrix
    (by show rpxTrim [qnfOfInt 1] ≠ []; exact List.cons_ne_nil (qnfOfInt 1) [])

/-- Fire: deleting the pivot's row and column `(1,1)` leaves the `1×1` submatrix `[[x²−1]]`. -/
theorem rsfFireSubmatrix :
    rsfSubmatrix rsmFireMatrix 1 1 = [[[qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]]] := rfl

/-! ## Content markers -/

/-- The ℚ[x] Smith reduced cross fixed point is decided. The cross measure `rsfCrossDegreeSum`
(`rsfRowWeightExcept`/`rsfColumnWeightExcept`) is zero exactly when the cross is annihilated. Because each
cross entry is reduced modulo the pivot independently there is no re-fill, so one pass drives every off-pivot
cross entry below the pivot (`rsfCrossIsReduced`, reached by `rsfClearCrossReachesReducedCross` and at every
positive fuel by `rsfClearCrossIterateReduced`), and the reduced cross is a genuine fixed point
(`rsfClearAgainstStableBelowPivot`, `rsfClearZeroTrimsZero`, `rsfClearAgainstPreservesBelow`). The `(r-1)×(c-1)`
submatrix extractor `rsfSubmatrix` ships. The all-zero cross needs the Smith re-pivot, decided downstream
(`rseHasAllZeroCrossViaRepivot`); the full Smith normal form is walled (`rsiHasSmithNormalForm`). -/
def rsfHasReducedCrossFixedPoint : Bool := true

end FX1Poly.ComputerAlgebra

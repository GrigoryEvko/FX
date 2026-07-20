import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmith

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithFixedPoint — the ℚ[x] Smith cross
fixed point

The committed Smith module (`RationalPolynomialSmith`) shipped the pivot search (T1) and the ONE-PASS cross
clear (T2): `rsmCrossClear pivot pivotCol matrix pivotRow` replaces every off-pivot entry of the pivot's row
and column by its Euclidean residue against the pivot (`rsmClearAgainst pivot entry = rbzClearEntry
entry.length pivot entry`), with the pivot preserved (`rsmCrossClearPivotPreserved`), the elementary-op
reconstruction on both arms, and the per-round degree drop (`rsmCrossClearRowMeasure`/
`rsmCrossClearColMeasure`: every off-pivot cross entry trims to `[]` OR has degree strictly below the
pivot's).  It WALLED the cross FIXED POINT owner-false (`rsmHasCrossFixedPoint := false`), fearing the classic
Smith re-fill: "each clear can reintroduce a nonzero residue elsewhere in the pivot's row/column that must be
re-cleared."  This module resolves that fear precisely and ships the honest fixed point.

## The re-fill obstruction: NOT present in the per-entry cross clear

`rsmCrossClear` clears each cross entry INDEPENDENTLY — the pivot-row entries by `rsmRowClearExcept`, the
pivot-column entries by `rsmColumnClearBelow`, each entry mapped to `entry mod pivot` on its own.  Clearing a
column entry does NOT touch a row entry, and vice versa (the two index sets are disjoint, and no per-entry
clear reads another entry).  So there is NO re-fill: a single pass drives EVERY off-pivot cross entry below
the pivot at once.  The feared re-dirtying is an artifact of row/column OPERATIONS (subtracting a multiple of
the whole pivot row from another row); the committed clear is not that.

## What lands (the REDUCED cross fixed point)

  * **T1 — the cross measure** (`rsfCrossDegreeSum`).  A single `Nat` over the pivot cross: the sum of
    trimmed lengths of the off-pivot entries of the pivot row (`rsfRowWeightExcept`) and the pivot column
    (`rsfColumnWeightExcept`).  An entry weighs `0` exactly when it trims to `[]`.

  * **T2 — the fixed-point driver** (`rsfClearCross` = one pass; `rsfClearCrossIterate` = fuel-structural
    iteration).  The reduced-cross predicate `rsfCrossIsReduced` (every off-pivot cross entry trims to `[]`
    OR has degree `<` the pivot) is REACHED by one pass (`rsfClearCrossReachesReducedCross`, bundling the two
    committed measure arms) and by every fuel `≥ 1` of the iterator (`rsfClearCrossIterateReduced` — no
    preservation needed, because the OUTERMOST pass produces a reduced cross regardless of its input).  The
    reduced state is a GENUINE fixed point: a below-pivot entry is clear-STABLE
    (`rsfClearAgainstStableBelowPivot`: `deg entry < deg pivot ⟹ rsmClearAgainst pivot entry = entry`, since
    the division guard fires with quotient `0`) and a zero entry stays zero
    (`rsfClearZeroTrimsZero`), so a further pass leaves the reduced cross entrywise fixed
    (`rsfClearAgainstPreservesBelow`).

## The honest walls

The ALL-ZERO cleared cross — every off-pivot cross entry trims to `[]`, i.e. the measure hits `0` — is NOT
reached by re-running `rsmCrossClear` with the SAME pivot: a residue of degree `<` the pivot is
division-stable (`rsfClearAgainstStableBelowPivot`), so iterating a fixed pivot cannot annihilate an entry
the pivot does not divide.  Reaching `0` requires the textbook Smith RE-PIVOT: swap the smaller-degree
residue into the pivot position and re-clear about the MOVING position, terminating because the min-degree
pivot strictly decreases each round.  That termination rests on `rpxMul` DEGREE ADDITIVITY (a nonzero
pivot-multiple has degree `≥ deg pivot`, so a nonzero non-multiple's residue strictly drops the min degree
and the all-zero cross is the true terminal), which the committed ℚ[x] kit does not have (no `rpxDegreeMul`).
Recorded owner-false (`rsfHasAllZeroCrossFixedPoint := false`); the committed `rsmHasCrossFixedPoint := false`
stays byte-intact.  The submatrix descent + diagonal invariant-factor chain is recorded owner-false
(`rsfHasSubmatrixDescent := false`); the `(r-1)×(c-1)` extractor (`rsfSubmatrix`) ships.

## Zero-axiom design

Every definition is structural on the list (row/column), the positional index, or the `Nat` fuel; every
specification routes through the committed measure/reconstruction lemmas and the calibrated-clean `Nat` order
lemmas.  The only non-list case analyses are `Nat.decLt` (full `isTrue`/`isFalse` enumeration).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithFixedPoint.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the cross measure -/

/-- The weight of a single entry: its trimmed length.  It is `0` exactly when the entry trims to the zero
polynomial, and `rpxDegree entry + 1` otherwise. -/
def rsfEntryWeight (entry : List QnfRat) : Nat := (rpxTrim entry).length

/-- Sum of entry weights over a whole row. -/
def rsfRowWeight : List (List QnfRat) → Nat
  | [] => 0
  | entry :: rest => rsfEntryWeight entry + rsfRowWeight rest

/-- Sum of entry weights over a row, skipping the entry at `skipCol` (the pivot column).  Structural on the
row and the index: once the skipped index is consumed, the remaining entries are summed in full. -/
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

/-- **The cross measure.**  The total weight of the off-pivot cross: the off-pivot entries of the pivot row
plus the off-pivot entries of the pivot column.  It is `0` exactly when every off-pivot cross entry trims to
the zero polynomial (the all-zero cleared cross). -/
def rsfCrossDegreeSum (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) : Nat :=
  rsfRowWeightExcept (rbzRowGet matrix pivotRow) pivotCol
    + rsfColumnWeightExcept matrix pivotCol pivotRow

/-! ## T2 — the reduced-cross fixed point -/

/-- **An entry is reduced below the pivot** when it trims to the zero polynomial or has degree strictly below
the pivot's — exactly the disjunction the committed degree-drop lemmas produce. -/
def rsfIsBelowPivot (pivot entry : List QnfRat) : Prop :=
  rpxTrim entry = [] ∨ rpxDegree entry < rpxDegree pivot

/-- **The reduced-cross predicate.**  Every off-pivot entry of the pivot's row AND column is reduced below
the pivot. -/
def rsfCrossIsReduced (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) : Prop :=
  (∀ colPosition : Nat, colPosition ≠ pivotCol →
      rsfIsBelowPivot pivot (rbzMatrixEntry matrix pivotRow colPosition))
    ∧ (∀ rowPosition : Nat, rowPosition ≠ pivotRow →
      rsfIsBelowPivot pivot (rbzMatrixEntry matrix rowPosition pivotCol))

/-- **The fixed-point driver (one pass).**  A single cross clear reaches the reduced fixed point; no fuel
loop is needed toward the reduced cross (see `rsfClearCrossReachesReducedCross`). -/
def rsfClearCross (pivot : List QnfRat) (pivotCol : Nat)
    (matrix : List (List (List QnfRat))) (pivotRow : Nat) : List (List (List QnfRat)) :=
  rsmCrossClear pivot pivotCol matrix pivotRow

/-- **The fuel-structural iterator.**  Applies the fixed-pivot cross clear `fuel` times.  Provided to honour
the fuel-driven driver shape; one application already reaches the reduced cross (`rsfClearCrossIterateReduced`
holds at every `fuel + 1`), and further passes are entrywise stable. -/
def rsfClearCrossIterate (pivot : List QnfRat) (pivotCol pivotRow : Nat) :
    Nat → List (List (List QnfRat)) → List (List (List QnfRat))
  | 0, matrix => matrix
  | fuel + 1, matrix =>
      rsmCrossClear pivot pivotCol (rsfClearCrossIterate pivot pivotCol pivotRow fuel matrix) pivotRow

/-! ### The Euclidean-residue stability lemmas (the genuine fixed-point evidence) -/

/-- **A below-degree dividend is its own remainder at a successor fuel.**  When `deg dividend < deg divisor`
the very first division guard fires, returning quotient `[]` and remainder `dividend`. -/
theorem rsfDivModSmallRemainder (fuel : Nat) (divisor dividend : List QnfRat)
    (hbelow : rpxDegree dividend < rpxDegree divisor) :
    (rpxDivMod (fuel + 1) divisor dividend).2 = dividend := by
  dsimp only [rpxDivMod]
  cases hcmp : Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
  | isTrue _ => rfl
  | isFalse hnot => exact absurd hbelow hnot

/-- **Clearing a below-pivot entry is the identity.**  `deg entry < deg pivot ⟹ rsmClearAgainst pivot entry
= entry` — the residue of an entry the pivot cannot reduce is the entry itself (quotient `0`).  This is why
re-running the FIXED-pivot clear cannot progress toward the all-zero cross. -/
theorem rsfClearAgainstStableBelowPivot (pivot entry : List QnfRat)
    (hbelow : rpxDegree entry < rpxDegree pivot) : rsmClearAgainst pivot entry = entry := by
  cases entry with
  | nil => rfl
  | cons headCoeff restCoeffs =>
      show (rpxDivMod (headCoeff :: restCoeffs).length pivot (headCoeff :: restCoeffs)).2
        = headCoeff :: restCoeffs
      exact rsfDivModSmallRemainder restCoeffs.length pivot (headCoeff :: restCoeffs) hbelow

/-- **A zero dividend has a zero remainder.**  If `dividend` trims to the zero polynomial, so does the
remainder of `rpxDivMod fuel divisor dividend` — the step preserves the nil trim (`rpdStepPreservesTrimNil`)
so the whole recursion does.  Structural fuel induction. -/
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

/-- **Clearing a zero entry yields a zero entry.**  `rpxTrim entry = [] ⟹ rpxTrim (rsmClearAgainst pivot
entry) = []`. -/
theorem rsfClearZeroTrimsZero (pivot entry : List QnfRat) (entryTrimNil : rpxTrim entry = []) :
    rpxTrim (rsmClearAgainst pivot entry) = [] :=
  rsfDivModZeroDividend entry.length pivot entry entryTrimNil

/-- **The reduced predicate is entrywise clear-stable.**  A below-pivot entry stays below-pivot after
another clear — a zero entry stays zero (`rsfClearZeroTrimsZero`), a strictly-below entry is unchanged
(`rsfClearAgainstStableBelowPivot`).  So the reduced cross is a genuine fixed point of the per-entry
clear. -/
theorem rsfClearAgainstPreservesBelow (pivot entry : List QnfRat)
    (belowPivot : rsfIsBelowPivot pivot entry) :
    rsfIsBelowPivot pivot (rsmClearAgainst pivot entry) := by
  cases belowPivot with
  | inl entryTrimNil => exact Or.inl (rsfClearZeroTrimsZero pivot entry entryTrimNil)
  | inr degreeBelow =>
      rw [rsfClearAgainstStableBelowPivot pivot entry degreeBelow]
      exact Or.inr degreeBelow

/-! ### Reaching the reduced cross -/

/-- **One cross clear reaches the reduced cross.**  For a nonzero pivot, `rsfClearCross` drives every
off-pivot entry of the pivot's row and column below the pivot — the two committed degree-drop arms
(`rsmCrossClearRowMeasure`/`rsmCrossClearColMeasure`) bundled into the single reduced-cross predicate. -/
theorem rsfClearCrossReachesReducedCross (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (pivotNonzero : rpxTrim pivot ≠ []) :
    rsfCrossIsReduced pivot pivotCol pivotRow (rsfClearCross pivot pivotCol matrix pivotRow) :=
  ⟨fun colPosition hne =>
      rsmCrossClearRowMeasure pivot pivotCol pivotRow matrix pivotNonzero colPosition hne,
   fun rowPosition hne =>
      rsmCrossClearColMeasure pivot pivotCol pivotRow matrix pivotNonzero rowPosition hne⟩

/-- **Every positive fuel of the iterator reaches the reduced cross.**  The outermost pass produces a reduced
cross regardless of its input, so no preservation across the inner passes is needed.  Structural on the
successor fuel. -/
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

/-- **The `(r-1)×(c-1)` submatrix extractor.**  Delete the pivot's row and column — the trailing submatrix
on which Smith descent recurses once the pivot's cross is annihilated. -/
def rsfSubmatrix (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) :
    List (List (List QnfRat)) :=
  rsfDropColumn (rsfDropRow matrix pivotRow) pivotCol

/-! ## Groundings (fires)

Closed-value kernel pins on the difference-of-squares fire matrix `[[x² − 1, x − 1], [x + 1, 1]]`, whose
minimum-degree pivot is the constant `1` at `(1, 1)` — which divides every cross entry, so the cross measure
hits `0`. -/

set_option maxRecDepth 8192

/-- Fire (cross measure value): the off-pivot cross of `[[x² − 1, x − 1], [x + 1, 1]]` about the pivot at
`(1, 1)` weighs `4` — the pivot-row entry `x + 1` (weight `2`) plus the pivot-column entry `x − 1`
(weight `2`). -/
theorem rsfFireCrossMeasureValue : rsfCrossDegreeSum rsmFireMatrix 1 1 = 4 := rfl

/-- Fire (measure hits `0` after the clear): the constant pivot `1` divides every cross entry, so one cross
clear annihilates the whole cross and the measure drops to `0`. -/
theorem rsfFireCrossMeasureAfterClearIsZero :
    rsfCrossDegreeSum (rsfClearCross [qnfOfInt 1] 1 rsmFireMatrix 1) 1 1 = 0 := rfl

/-- Fire (fueled driver hits `0`): iterating the fixed-pivot clear twice on the fire matrix still leaves the
cross annihilated — the measure is `0`. -/
theorem rsfFireIterateMeasureZero :
    rsfCrossDegreeSum (rsfClearCrossIterate [qnfOfInt 1] 1 1 2 rsmFireMatrix) 1 1 = 0 := rfl

/-- Fire (below-pivot stability, closed value): clearing the constant residue `2` against the pivot `x − 1`
(degree `0 < 1`) is the identity — the residue the pivot cannot reduce is untouched. -/
theorem rsfFireClearStableConstant :
    rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] = [qnfOfInt 2] := rfl

/-- Fire (below-pivot stability theorem, instantiated): the same identity through
`rsfClearAgainstStableBelowPivot` at `deg [2] = 0 < 1 = deg [x − 1]`. -/
theorem rsfFireClearStableTheorem :
    rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] = [qnfOfInt 2] :=
  rsfClearAgainstStableBelowPivot [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 2] (Nat.le_refl 1)

/-- Fire (driver reaches the reduced cross, instantiated): one cross clear of the fire matrix about the pivot
`1` at `(1, 1)` reduces the whole cross below the pivot. -/
theorem rsfFireDriverReachesReduced :
    rsfCrossIsReduced [qnfOfInt 1] 1 1 (rsfClearCross [qnfOfInt 1] 1 rsmFireMatrix 1) :=
  rsfClearCrossReachesReducedCross [qnfOfInt 1] 1 1 rsmFireMatrix
    (by show rpxTrim [qnfOfInt 1] ≠ []; exact List.cons_ne_nil (qnfOfInt 1) [])

/-- Fire (fueled driver reaches the reduced cross, instantiated): two iterations of the fixed-pivot clear on
the fire matrix leave the cross reduced below the pivot. -/
theorem rsfFireIterateReachesReduced :
    rsfCrossIsReduced [qnfOfInt 1] 1 1 (rsfClearCrossIterate [qnfOfInt 1] 1 1 2 rsmFireMatrix) :=
  rsfClearCrossIterateReduced [qnfOfInt 1] 1 1 1 rsmFireMatrix
    (by show rpxTrim [qnfOfInt 1] ≠ []; exact List.cons_ne_nil (qnfOfInt 1) [])

/-- Fire (submatrix extractor, closed value): deleting the pivot's row and column `(1, 1)` from the fire
matrix leaves the `1×1` submatrix `[[x² − 1]]`. -/
theorem rsfFireSubmatrix :
    rsfSubmatrix rsmFireMatrix 1 1 = [[[qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]]] := rfl

/-! ## Content markers -/

/-- DECIDED: the ℚ[x] Smith cross MEASURE — a single `Nat` `rsfCrossDegreeSum` over the off-pivot cross (the
summed trimmed lengths of the pivot row's and column's off-pivot entries, `0` exactly when the cross is
annihilated), built from `rsfRowWeightExcept`/`rsfColumnWeightExcept`. -/
def rsfHasCrossMeasure : Bool := true

/-- DECIDED (the honest fixed point the committed `rsmHasCrossFixedPoint := false` walled): the REDUCED cross
fixed point over ℚ[x].  There is NO re-fill in the per-entry cross clear (each cross entry is reduced modulo
the pivot independently), so ONE pass drives every off-pivot cross entry below the pivot
(`rsfCrossIsReduced`, reached by `rsfClearCrossReachesReducedCross` and, at every positive fuel, by the
fuel-structural iterator `rsfClearCrossIterate` via `rsfClearCrossIterateReduced`).  The reduced cross is a
GENUINE fixed point: a below-pivot entry is clear-stable (`rsfClearAgainstStableBelowPivot`) and a zero entry
stays zero (`rsfClearZeroTrimsZero`), so a further pass leaves it entrywise fixed
(`rsfClearAgainstPreservesBelow`).  The committed `rsmHasCrossFixedPoint := false` stays byte-intact. -/
def rsfHasReducedCrossFixedPoint : Bool := true

/-- WALLED (owner-false): the ALL-ZERO cleared cross — every off-pivot cross entry trims to `[]`, i.e.
`rsfCrossDegreeSum` hits `0`.  Re-running the FIXED-pivot `rsmCrossClear` cannot reach it: a residue of
degree strictly below the pivot is division-stable (`rsfClearAgainstStableBelowPivot`), so a pivot that does
not DIVIDE a cross entry can never annihilate it.  Reaching `0` requires the textbook Smith RE-PIVOT — swap
the smaller-degree residue into the pivot position and re-clear about the MOVING position — which terminates
because the minimum-degree pivot strictly decreases each round.  That termination rests on `rpxMul` DEGREE
ADDITIVITY (`rpxDegree (rpxMul p q) = rpxDegree p + rpxDegree q` for nonzero `p`, `q`, hence a nonzero
pivot-multiple has degree `≥ deg pivot` and the all-zero cross is the true terminal), which the committed
ℚ[x] kit does not provide (no `rpxDegreeMul`; it would need the leading-coefficient product law over the
field ℚ, i.e. no zero divisors).  Route: `rpxDegreeMul` → the re-pivot driver with a min-degree measure →
the all-zero cross. -/
def rsfHasAllZeroCrossFixedPoint : Bool := false

/-- WALLED (owner-false; the committed `rsmHasSmithNormalForm := false` and `rbzHasSmithNormalForm := false`
stay byte-intact): the FULL Smith normal form over ℚ[x].  The `(r-1)×(c-1)` submatrix extractor
(`rsfSubmatrix`, deleting the pivot's row and column) ships as the descent SEED; the remaining route, resting
on the all-zero cross (`rsfHasAllZeroCrossFixedPoint`, walled above): (1) descend on `rsfSubmatrix` with a
fresh `Nat` measure = matrix size, producing the diagonal `diag(d₁, …, dᵣ, 0, …)`; (2) the invariant-factor
divisibility chain `d₁ | d₂ | ⋯ | dᵣ`, combining `rpeGcdDividesBoth` with `rbzDividesTrans`. -/
def rsfHasSubmatrixDescent : Bool := false

end FX1Poly.ComputerAlgebra

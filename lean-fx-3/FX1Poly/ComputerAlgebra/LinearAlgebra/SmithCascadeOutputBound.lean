import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithCascadeOutputBound — the inner Euclid cascade's
    OUTPUT pivot is bounded by the input minor (H2-SMITH r30, #2261)

The corrected-driver totality (since r22) rests on the single keystone
`SmithCascadeLandedPivotDividesMinor`, sharpened by r29 to the 1-D scalar `landed ∣ gcd(minor)`
(`LandedPivotDividesMinorGcd`).  Route R2 (minimality descent) is the adjudicated attack: the min-abs
Euclid cascade lands the minimal element of the minor's gcd-ideal.  Its first real theorem — the exact
"compose across the whole `smithCascadeSweep` loop to bound its OUTPUT pivot" the r28 footer names as
still-missing — is shipped here.

`smithCascadeReachesCrossClear` (r9/r10, `SmithCascadeTermination`) already proves the cascade output is
CROSS-CLEAR.  This module adds the orthogonal magnitude fact: the cascade output PIVOT is no larger than
the pivot it started with (`smithCascadeSweepOutputPivotLeInputPivot`, the never-raises invariant) and,
composing the first move's min-abs search bound, no larger than ANY nonzero entry of the input minor
(`smithCascadeSweepOutputPivotBounded`, the witness form — recon brick 1 exactly).  Both are pure
function-correctness facts about the definite cascade word on one threaded matrix, refutation-immune.

**Truth-probed** (r30 eval, read-only) — on every recon seed the single cascade output pivot EQUALS the
min-abs of the input minor: `diag(15,10,6,4)` pivot 0 lands 4 (≤ 15); `diag(6,10,8)` lands 6 (= 6, the
non-strict boundary); the non-diagonal `[[6,2,4],[8,10,2],[2,6,8]]` lands 2 (≤ 6, ≤ every minor entry);
`diag(1,-12,-18,10)` pivot 1 lands 10 (≤ 12).  NOTE this is the SINGLE cascade output, NOT the
full-repair landed value (the full repair sweep folds later diagonals in and descends further —
`diag(15,10,6,4)` full-repair lands 1); brick 1 is the single-cascade bound the fold-descent obligation
`SmithFoldDescendsOnNonzeroPivot` rides on the FOLDED matrix.

**What this ships (all zero-axiom, additive; the r18–r29 world byte-intact).**

  * `smithCascadeSweepOutputPivotLeInputPivot` — the never-raises invariant: for a POSITIVE input pivot,
    the cascade output pivot magnitude is `≤` the input pivot magnitude.  Structural induction on the
    inner fuel, riding the shipped magnitude-preservation chain (`smithMoveToPivotEntryOnPivot`,
    `smithSignNormalizeOpsPreservesPivotMagnitude`, `smithClearColumnBelowStepsPreservesRow`,
    `smithClearRowRightStepsPreservesColumn`) and the min-abs search bound
    (`smithFindMinAbsInMinorBoundsWitness`).
  * `smithCascadeSweepOutputPivotBounded` — the witness form (recon brick 1): with a nonzero minor
    witness and fuel-adequacy (`smithMinorAbsSum ≤ innerFuel`), the cascade output pivot magnitude is
    `≤` that witness's magnitude.  The first move drops the pivot to the min-abs (`≤` witness), and
    never-raises keeps it there; fuel-adequacy kills the empty-fuel case via `smithMinorEntryLeAbsSum`.

**HONEST SIZING — this does NOT flip the driver.**  Route R2 is a `≥3`-round arc; r30 ships its first
real theorem (the single-cascade output-pivot bound) and NAMES the residual.  The surviving wall is
UNCHANGED: `SmithReduceCompleteDriverStatement` stays UNINHABITED hypothesis-free; the single
hypothesis-free residual remains K2 = `landed ∣ gcd(minor)` (= `LandedPivotDividesMinorGcd`,
`SmithMinorGcdReduction`), the full-repair minimality wall named at the foot of this file.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeOutputBound.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The never-raises invariant -/

/-- **The cascade never raises a positive pivot** — for a rectangular matrix with the pivot in range and
POSITIVE, the magnitude of the pivot after the whole `smithCascadeSweep` loop is `≤` the input pivot's
magnitude.  Structural induction on the inner `fuel`.

  * **Base (`fuel = 0`) / step-`none`**: the sweep is empty (`applyOperations [] = matrix`), so the output
    pivot IS the input pivot — `Nat.le_refl`.
  * **Step, `some (foundRow, foundCol)`**: the move + sign-normalise + cross-clear leaves the pivot slot
    holding the found min-abs entry (magnitude `= (matrix.entryAt foundRow foundCol).natAbs`, preserved
    through both clears since they touch only rows below / columns right of the pivot), which the min-abs
    search bounds `≤` the input pivot (the pivot slot is itself a nonzero minor witness).  Cross-clear
    `true` reads that off; cross-clear `false` recurses on the reduced matrix whose (positive) pivot IS
    the found entry, and the IH keeps the output `≤` it. -/
theorem smithCascadeSweepOutputPivotLeInputPivot :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      0 < (matrix.diagonalEntryAt pivotIndex).natAbs →
      ((matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width)).diagonalEntryAt
          pivotIndex).natAbs
        ≤ (matrix.diagonalEntryAt pivotIndex).natAbs := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width _ _ _ _
      exact Nat.le_refl _
  | succ fuel ih =>
      intro matrix pivotIndex height width isRect pivotRowInRange pivotColInRange pivotPos
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          exact Nat.le_refl _
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
          -- The min-abs search facts are established BEFORE the `let`s (a later tactic `match` would
          -- otherwise clear the outer `let`-values and break `hSweep`'s definitional unfolding).
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have foundNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 :=
            smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind
          have foundPositive : 0 < (matrix.entryAt foundRow foundCol).natAbs :=
            match Nat.eq_zero_or_pos (matrix.entryAt foundRow foundCol).natAbs with
            | Or.inl isZero => absurd isZero foundNonzero
            | Or.inr isPositive => isPositive
          have inputPivotEntryPos : 0 < (matrix.entryAt pivotIndex pivotIndex).natAbs := pivotPos
          have inputPivotNonzero : (matrix.entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
            fun isZero => Nat.lt_irrefl 0 (Eq.mp (congrArg (0 < ·) isZero) inputPivotEntryPos)
          have foundLeInputPivot :
              (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt pivotIndex pivotIndex).natAbs := by
            match smithFindMinAbsInMinorBoundsWitness matrix pivotIndex height width pivotIndex pivotIndex
                (Nat.le_refl pivotIndex)
                (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pivotRowInRange)
                (Nat.le_refl pivotIndex)
                (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pivotColInRange)
                inputPivotNonzero with
            | ⟨boundRow, boundCol, boundFindEq, boundLe⟩ =>
                have someEq : some (boundRow, boundCol) = some (foundRow, foundCol) :=
                  boundFindEq.symm.trans hFind
                injection someEq with pairEq
                injection pairEq with rowEq colEq
                rw [rowEq, colEq] at boundLe
                exact boundLe
          let moveOps := smithMoveToPivotOps pivotIndex foundRow foundCol
          let afterMove := matrix.applyOperations moveOps
          let signOps := smithSignNormalizeOps afterMove pivotIndex
          let afterSign := afterMove.applyOperations signOps
          let columnClearOps :=
            (smithClearColumnBelowSteps afterSign pivotIndex (height - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.rowOperation
          let afterColumnClear := afterSign.applyOperations columnClearOps
          let rowClearOps :=
            (smithClearRowRightSteps afterColumnClear pivotIndex (width - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.columnOperation
          let afterRowClear := afterColumnClear.applyOperations rowClearOps
          let settledOps := moveOps ++ signOps ++ columnClearOps ++ rowClearOps
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have afterMoveInRows : pivotIndex < afterMove.rows.length :=
            Eq.mp (congrArg (pivotIndex < ·) afterMoveRect.1.symm) pivotRowInRange
          have moveEntry : afterMove.entryAt pivotIndex pivotIndex = matrix.entryAt foundRow foundCol :=
            smithMoveToPivotEntryOnPivot matrix isRect pivotIndex foundRow foundCol pivotRowInRange
              foundInRange.2.1 pivotColInRange foundInRange.2.2.2
          have signMagFound :
              (afterSign.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (smithSignNormalizeOpsPreservesPivotMagnitude afterMove pivotIndex afterMoveInRows).trans
              (congrArg Int.natAbs moveEntry)
          have colClearPreservesPivot :
              afterColumnClear.entryAt pivotIndex pivotIndex = afterSign.entryAt pivotIndex pivotIndex :=
            smithClearColumnBelowStepsPreservesRow afterSign pivotIndex pivotIndex pivotIndex
              (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign (Nat.lt_succ_self pivotIndex)
          have colClearPivotMag :
              (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs colClearPreservesPivot).trans signMagFound
          have rowClearPreservesPivot :
              afterRowClear.entryAt pivotIndex pivotIndex = afterColumnClear.entryAt pivotIndex pivotIndex :=
            smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width
              pivotIndex pivotIndex pivotRowInRange (width - (pivotIndex + 1)) (pivotIndex + 1)
              afterColumnClear afterColumnClearRect (Nat.lt_succ_self pivotIndex)
          have afterRowClearPivotMag :
              (afterRowClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs rowClearPreservesPivot).trans colClearPivotMag
          have afterRowClearPivotPositive : 0 < (afterRowClear.diagonalEntryAt pivotIndex).natAbs :=
            Nat.lt_of_lt_of_le foundPositive (Nat.le_of_eq afterRowClearPivotMag.symm)
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
            rfl
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true =>
              rw [hApplySettled]
              exact Nat.le_trans (Nat.le_of_eq afterRowClearPivotMag) foundLeInputPivot
          | false =>
              rw [applyOperationsAppend, hApplySettled]
              exact Nat.le_trans
                (ih afterRowClear pivotIndex height width afterRowClearRect pivotRowInRange
                  pivotColInRange afterRowClearPivotPositive)
                (Nat.le_trans (Nat.le_of_eq afterRowClearPivotMag) foundLeInputPivot)

/-! ## The witness form (recon brick 1) -/

/-- **The cascade output pivot is bounded by any nonzero minor witness** — with fuel-adequacy
(`smithMinorAbsSum ≤ innerFuel`) and a nonzero entry `(witnessRow, witnessCol)` in the pivot minor, the
cascade output pivot magnitude is `≤` that witness's magnitude.  The first cascade step moves the min-abs
entry to the pivot (magnitude `≤` witness by the search bound `smithFindMinAbsInMinorBoundsWitness`), and
`smithCascadeSweepOutputPivotLeInputPivot` keeps the output `≤` that.  Fuel-adequacy rules out the empty
sweep (`smithMinorEntryLeAbsSum` forces a nonzero witness to weigh `≤ smithMinorAbsSum ≤ innerFuel`, so a
zero `innerFuel` contradicts `witNonzero`). -/
theorem smithCascadeSweepOutputPivotBounded {height width : Nat}
    (innerFuel : Nat) (matrix : IntMatrix) (pivotIndex : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (witnessRow witnessCol : Nat)
    (witRowGe : pivotIndex ≤ witnessRow) (witRowLt : witnessRow < height)
    (witColGe : pivotIndex ≤ witnessCol) (witColLt : witnessCol < width)
    (witNonzero : (matrix.entryAt witnessRow witnessCol).natAbs ≠ 0)
    (fuelAdequate : smithMinorAbsSum matrix pivotIndex height width ≤ innerFuel) :
    ((matrix.applyOperations (smithCascadeSweep innerFuel matrix pivotIndex height width)).diagonalEntryAt
        pivotIndex).natAbs
      ≤ (matrix.entryAt witnessRow witnessCol).natAbs := by
  have witRowLtWindow : witnessRow < pivotIndex + (height - pivotIndex) :=
    Eq.mp (congrArg (witnessRow < ·)
      (smithNatAddSubOfLe pivotIndex height (Nat.le_of_lt pRowLt)).symm) witRowLt
  have witColLtWindow : witnessCol < pivotIndex + (width - pivotIndex) :=
    Eq.mp (congrArg (witnessCol < ·)
      (smithNatAddSubOfLe pivotIndex width (Nat.le_of_lt pColLt)).symm) witColLt
  match smithFindMinAbsInMinorBoundsWitness matrix pivotIndex height width witnessRow witnessCol
      witRowGe witRowLtWindow witColGe witColLtWindow witNonzero with
  | ⟨foundRow, foundCol, hFind, foundLeWitness⟩ =>
      cases innerFuel with
      | zero =>
          exact absurd
            (Nat.le_antisymm
              (Nat.le_trans
                (smithMinorEntryLeAbsSum matrix pivotIndex height width witnessRow witnessCol
                  witRowGe witRowLtWindow witColGe witColLtWindow)
                fuelAdequate)
              (Nat.zero_le _))
            witNonzero
      | succ fuel =>
          let moveOps := smithMoveToPivotOps pivotIndex foundRow foundCol
          let afterMove := matrix.applyOperations moveOps
          let signOps := smithSignNormalizeOps afterMove pivotIndex
          let afterSign := afterMove.applyOperations signOps
          let columnClearOps :=
            (smithClearColumnBelowSteps afterSign pivotIndex (height - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.rowOperation
          let afterColumnClear := afterSign.applyOperations columnClearOps
          let rowClearOps :=
            (smithClearRowRightSteps afterColumnClear pivotIndex (width - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.columnOperation
          let afterRowClear := afterColumnClear.applyOperations rowClearOps
          let settledOps := moveOps ++ signOps ++ columnClearOps ++ rowClearOps
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have afterMoveInRows : pivotIndex < afterMove.rows.length :=
            Eq.mp (congrArg (pivotIndex < ·) afterMoveRect.1.symm) pRowLt
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pRowLt pColLt hFind
          have foundNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 :=
            smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind
          have foundPositive : 0 < (matrix.entryAt foundRow foundCol).natAbs :=
            match Nat.eq_zero_or_pos (matrix.entryAt foundRow foundCol).natAbs with
            | Or.inl isZero => absurd isZero foundNonzero
            | Or.inr isPositive => isPositive
          have moveEntry : afterMove.entryAt pivotIndex pivotIndex = matrix.entryAt foundRow foundCol :=
            smithMoveToPivotEntryOnPivot matrix isRect pivotIndex foundRow foundCol pRowLt
              foundInRange.2.1 pColLt foundInRange.2.2.2
          have signMagFound :
              (afterSign.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (smithSignNormalizeOpsPreservesPivotMagnitude afterMove pivotIndex afterMoveInRows).trans
              (congrArg Int.natAbs moveEntry)
          have colClearPreservesPivot :
              afterColumnClear.entryAt pivotIndex pivotIndex = afterSign.entryAt pivotIndex pivotIndex :=
            smithClearColumnBelowStepsPreservesRow afterSign pivotIndex pivotIndex pivotIndex
              (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign (Nat.lt_succ_self pivotIndex)
          have colClearPivotMag :
              (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs colClearPreservesPivot).trans signMagFound
          have rowClearPreservesPivot :
              afterRowClear.entryAt pivotIndex pivotIndex = afterColumnClear.entryAt pivotIndex pivotIndex :=
            smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width
              pivotIndex pivotIndex pRowLt (width - (pivotIndex + 1)) (pivotIndex + 1)
              afterColumnClear afterColumnClearRect (Nat.lt_succ_self pivotIndex)
          have afterRowClearPivotMag :
              (afterRowClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs rowClearPreservesPivot).trans colClearPivotMag
          have afterRowClearPivotPositive : 0 < (afterRowClear.diagonalEntryAt pivotIndex).natAbs :=
            Nat.lt_of_lt_of_le foundPositive (Nat.le_of_eq afterRowClearPivotMag.symm)
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
            rfl
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true =>
              rw [hApplySettled]
              exact Nat.le_trans (Nat.le_of_eq afterRowClearPivotMag) foundLeWitness
          | false =>
              rw [applyOperationsAppend, hApplySettled]
              exact Nat.le_trans
                (smithCascadeSweepOutputPivotLeInputPivot fuel afterRowClear pivotIndex height width
                  afterRowClearRect pRowLt pColLt afterRowClearPivotPositive)
                (Nat.le_trans (Nat.le_of_eq afterRowClearPivotMag) foundLeWitness)

/-! ## SURVIVING WALL (H2-SMITH r30, #2261)

r30 ships route R2's first real theorem: the SINGLE-cascade output pivot bound.
`smithCascadeSweepOutputPivotLeInputPivot` (never-raises) + `smithCascadeSweepOutputPivotBounded` (the
witness form) prove the inner Euclid loop lands a pivot no larger than any nonzero entry of the input
minor — the exact "compose across the whole `smithCascadeSweep` loop to bound its OUTPUT pivot" the r28
footer named as still-missing.  This is the single-cascade bound; the full-repair sweep descends further
by folding later diagonals in.

The corrected-driver totality residual is UNCHANGED.  `SmithReduceCompleteDriverStatement` stays
UNINHABITED hypothesis-free; the single hypothesis-free residual is K2 = `landed ∣ gcd(minor)`
(`LandedPivotDividesMinorGcd`, `SmithMinorGcdReduction`; equivalently, with the shipped converse
`minorGcdDividesLanded`, the symmetric magnitude `|landed| = gcd(minor)`).  The next rung consumes r30's
bound on the FOLDED matrix to discharge the r28 obligation `SmithFoldDescendsOnNonzeroPivot`
(`pivotMagnitudeWithin` strictly drops on every nonzero-pivot fold, via `smithRepairDecreasesPivotSize`'s
`gcd(d_p, d_found) < d_p`) → fuel-adequacy `SmithClearingOutputFindNone` (the DIAGONAL keystone half); the
OFF-DIAGONAL half K2 remains the irreducible "min-abs Euclid computes the gcd" wall, NOT closed by any
gcd-invariance argument.  The shipped `smithReduceComplete`, its refutation, and the r18–r29 world stay
byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutFindNoneToChainSeed

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutFuelAdequacy — ARC-A DISCHARGED: the fueled
    Bezout position sweep REACHES find-`none` (+ cross-clear), with (α) and (β) inhabited
    (H2-SMITH r50, #2261)

## ★★★★★ ARC-A STATUS: FIRED — (α), (β), and the fuel-adequacy residual are all INHABITED here ★★★★★

This file discharges the THREE recorded residuals feeding the #2261 gate:

  * **(α)** `SmithBezoutRepairRoundLandsPivotPositiveStatement` — inhabited by
    `smithBezoutRepairRoundLandsPivotPositiveHolds`.  The engine is the NEW cascade-output
    NON-VANISHING lever `smithCascadeSweepOutputPivotNonzero` (the lower-bound sibling the r49 recon
    said was missing): with adequate fuel, whenever the cascade's min-abs search finds a nonzero minor
    entry, the OUTPUT pivot is nonzero — after every move+sign+clear rotation the pivot slot holds the
    moved min-abs value (nonzero), the clears never touch the pivot slot, and the loop re-finds the
    nonzero pivot itself.  The find-`some` state feeds it: if the round's fold+sign+Bezout-clear prefix
    were to zero the whole minor, the bounded-below gcd invariance (`minorGcdStableUnderBoundedWord`)
    would force the ORIGINAL offender to zero — contradicting the find's own guard-`false`.
  * **(β)** `SmithBezoutTrailingCascadePreservesFindNoneStatement` — inhabited by
    `smithBezoutTrailingCascadePreservesFindNoneHolds`.  Route: find-`none` ⟺ whole-block divisibility
    (r45 bridge); the r44 keystone pins `|pivot| = |gcd|`; the standalone cascade is bounded below, so
    the gcd is INVARIANT; the output pivot is `≤ |pivot| = |gcd|` (witness: the old pivot), NONZERO
    (the non-vanishing lever), and a gcd multiple — hence EXACTLY `±gcd`, which divides every entry of
    the gcd-invariant output block; the bridge closes find-`none`.  The zero-pivot corner has an
    all-zero block, where the cascade word is literally `[]`.
  * **ARC-A** `SmithBezoutRepairPositionSweepReachesFindNoneStatement` — inhabited by
    `smithBezoutRepairPositionSweepReachesFindNoneHolds`, via the MASTER two-phase fuel induction
    `smithBezoutRepairPositionSweepMasterLandsFindNoneAndCrossClear`, whose invariant is the NEW
    gcd-floored measure bound `0 < p ∧ p ≤ fuel + |minorGcd|`: K1 strict descent burns one fuel per
    round while the measure stays a positive gcd-multiple, so when the fuel is exhausted the pivot has
    descended EXACTLY to the gcd — which divides the whole block, i.e. find-`none` (the fuel-0 base
    proves the landing rather than failing).  The first round from ANY entry state (zero pivot OR
    dirty cross — both r46-refuter shapes) is handled by the unconditional dirty-tolerant bound
    `smithBezoutRepairRoundAtFoundPivotMagnitudeLeMinorAbsSum` (`m1 ≤ seed`, single-witness in every
    corner because the self-transvection guard makes degenerate folds IDENTITIES) + the r48
    maintenance (cross-clean re-established) + (α) (positive pivot) — after which the master takes
    over with `m1 ≤ (seed - 1) + |gcd|` since `|gcd| ≥ 1` on a find-`some` block.

  In fact ARC-A is delivered STRONGER than recorded: the seed-level theorem
  `smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear` needs NO entry cross-clean hypothesis
  at all and ALSO yields output cross-clearance — exactly the per-position fact the ARC-C settling
  induction (sibling file `SmithBezoutMandateFired`) consumes at every pivot.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  ADDITIVE only — the r18-r49 world is
byte-intact.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutFuelAdequacy.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Divisibility micro-kit (all propext-clean; the `Int` facts ride the shipped arithmetic core) -/

/-- **Every integer divides itself** — witness `1` through `intMulOne`. -/
theorem dividesExactlySelf (value : Int) : dividesExactly value value :=
  ⟨1, (intMulOne value).symm⟩

/-- **Zero divides only zero** — a `dividesExactly 0 value` witness collapses through `intZeroMul`. -/
theorem dividesExactlyZeroDivisorForcesZero {value : Int}
    (isDivisible : dividesExactly 0 value) : value = 0 :=
  match isDivisible with
  | ⟨factor, valueEquation⟩ => valueEquation.trans (intZeroMul factor)

/-- **Divisibility survives negating the DIVISOR** — the witness flips sign:
`value = divisor * factor = (-divisor) * (-factor)` through `intNegMul`/`intMulNeg`/`intNegNeg`. -/
theorem dividesExactlyNegDivisor {divisor value : Int}
    (isDivisible : dividesExactly divisor value) : dividesExactly (-divisor) value :=
  match isDivisible with
  | ⟨factor, valueEquation⟩ =>
      ⟨-factor, valueEquation.trans
        (((intNegMul divisor (-factor)).trans
          ((congrArg Neg.neg (intMulNeg divisor factor)).trans
            (intNegNeg (divisor * factor)))).symm)⟩

/-- **A base is at most its product with a positive factor** — `base ≤ base * factor` for
`0 < factor`; the successor arm is `Nat.le_add_left` over the definitional `base * (n+1) =
base * n + base`. -/
theorem natLeMulOfPosRight (base : Nat) :
    ∀ (factor : Nat), 0 < factor → base ≤ base * factor
  | 0, factorPositive => absurd factorPositive (Nat.lt_irrefl 0)
  | factor + 1, _ =>
      show base ≤ base * factor + base from Nat.le_add_left base (base * factor)

/-- **A divisor's magnitude bounds a NONZERO multiple's magnitude below** — from
`value = divisor * factor` with `value ≠ 0`, the factor is nonzero, so
`|divisor| ≤ |divisor| * |factor| = |value|` (`intNatAbsMul` + `natLeMulOfPosRight`). -/
theorem dividesExactlyNonzeroLowerBoundsMagnitude {divisor value : Int}
    (isDivisible : dividesExactly divisor value) (valueNonzero : value.natAbs ≠ 0) :
    divisor.natAbs ≤ value.natAbs := by
  obtain ⟨factor, valueEquation⟩ := isDivisible
  have magnitudeEq : value.natAbs = divisor.natAbs * factor.natAbs :=
    (congrArg Int.natAbs valueEquation).trans (intNatAbsMul divisor factor)
  have factorNonzero : factor.natAbs ≠ 0 := by
    intro factorZero
    rw [magnitudeEq, factorZero] at valueNonzero
    exact valueNonzero rfl
  have factorPositive : 0 < factor.natAbs :=
    match Nat.eq_zero_or_pos factor.natAbs with
    | .inl isZero => absurd isZero factorNonzero
    | .inr isPositive => isPositive
  rw [magnitudeEq]
  exact natLeMulOfPosRight divisor.natAbs factor.natAbs factorPositive

/-- **Equal magnitude against a nonnegative target pins the value to `±target`** — the `ofNat` arm
lands `value = target` through `intOfNatNatAbsOfNonNeg`; the `negSucc` arm lands `value = -target`
(the negation of the reconstructed `ofNat` is definitionally the `negSucc`). -/
theorem intEqOrNegOfNatAbsEqOfNonneg :
    ∀ (value target : Int), 0 ≤ target → value.natAbs = target.natAbs →
      value = target ∨ value = -target
  | .ofNat magnitude, target, targetNonneg, magnitudeEq =>
      Or.inl ((congrArg Int.ofNat magnitudeEq).trans (intOfNatNatAbsOfNonNeg targetNonneg))
  | .negSucc magnitudePredecessor, target, targetNonneg, magnitudeEq =>
      Or.inr (by
        have targetForm : Int.ofNat (magnitudePredecessor + 1) = target :=
          (congrArg Int.ofNat magnitudeEq).trans (intOfNatNatAbsOfNonNeg targetNonneg)
        rw [← targetForm]
        rfl)

/-! ## Self-transvection identities (the operation-level guards, read off as equations) -/

/-- **A self-row-transvection is the identity** — the operation-level `sourceIndex = targetIndex`
guard (`addRowMultiple` excludes the non-unimodular self-fold). -/
theorem addRowMultipleSelfIsIdentity (matrix : IntMatrix) (rowIndex : Nat) (coefficient : Int) :
    matrix.addRowMultiple rowIndex rowIndex coefficient = matrix := by
  unfold IntMatrix.addRowMultiple
  exact if_pos rfl

/-- **A self-column-transvection is the identity** — the column mirror of the row guard. -/
theorem addColumnMultipleSelfIsIdentity (matrix : IntMatrix) (colIndex : Nat) (coefficient : Int) :
    matrix.addColumnMultiple colIndex colIndex coefficient = matrix := by
  unfold IntMatrix.addColumnMultiple
  exact if_pos rfl

/-! ## The cascade-output NON-VANISHING lever (the missing lower-bound sibling of
`smithCascadeSweepOutputPivotBounded`)

After every move+sign+clear rotation the pivot slot holds the moved min-abs entry — NONZERO
(`smithFindMinAbsInMinorFoundNonzero`), preserved by both clears (they target strictly-later
rows/columns).  The cross-clear terminal returns exactly that state; the loop re-enters with the
nonzero pivot itself as a search witness.  The fuel-adequacy hypothesis and its descent re-establishment
mirror the shipped `smithCascadeReachesCrossClear` verbatim. -/

/-- **The seed fuel bound for any found min-abs entry** — the packaged fuel-adequacy input at the
cascade's ACTUAL seed `smithMinorAbsSum` (mirrors the `smithCascadeSweepSeedReachesCrossClear`
instantiation). -/
theorem smithCascadeSweepSeedFuelBound (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    ∀ foundRow foundCol,
      smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol) →
      (matrix.entryAt foundRow foundCol).natAbs
        ≤ smithMinorAbsSum matrix pivotIndex height width := by
  intro foundRow foundCol findEq
  have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
    foundRow foundCol pRowLt pColLt findEq
  exact smithMinorEntryLeAbsSum matrix pivotIndex height width foundRow foundCol
    foundInRange.1
    (natLtAddSubOfLt pivotIndex foundRow height foundInRange.1 foundInRange.2.1)
    foundInRange.2.2.1
    (natLtAddSubOfLt pivotIndex foundCol width foundInRange.2.2.1 foundInRange.2.2.2)

/-- **The cascade output pivot is NONZERO whenever the search finds anything** — with fuel adequacy
(`measure ≤ fuel` for any found entry) and a `some` search on the input, the output pivot slot has
nonzero magnitude.  Structural strong induction on the fuel, the exact skeleton of the shipped
`smithCascadeReachesCrossClear`: the settle word parks the (nonzero) moved entry at the pivot slot
untouched by either clear; the cross-clear terminal returns it; the loop branch feeds the IH the
nonzero pivot itself as the next search witness, with the shipped strict-descent re-establishing the
fuel bound. -/
theorem smithCascadeSweepOutputPivotNonzero :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      (∀ foundRow foundCol,
        smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol) →
        (matrix.entryAt foundRow foundCol).natAbs ≤ fuel) →
      (smithFindMinAbsInMinor matrix pivotIndex height width).isSome = true →
      ((matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width)).entryAt
          pivotIndex pivotIndex).natAbs ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width _ _ _ fuelBound findIsSome
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [hFind] at findIsSome
          exact Bool.noConfusion findIsSome
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
          exact absurd
            (Nat.le_antisymm (fuelBound foundRow foundCol hFind) (Nat.zero_le _))
            (smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind)
  | succ fuel ih =>
      intro matrix pivotIndex height width isRect pivotRowInRange pivotColInRange fuelBound _findIsSome
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [hFind] at _findIsSome
          exact Bool.noConfusion _findIsSome
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
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
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have foundNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 :=
            smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind
          have pivotPositive : 0 < (matrix.entryAt foundRow foundCol).natAbs :=
            match Nat.eq_zero_or_pos (matrix.entryAt foundRow foundCol).natAbs with
            | Or.inl isZero => absurd isZero foundNonzero
            | Or.inr isPositive => isPositive
          have pivotMagLe : (matrix.entryAt foundRow foundCol).natAbs ≤ fuel + 1 :=
            fuelBound foundRow foundCol hFind
          have moveEntry : afterMove.entryAt pivotIndex pivotIndex = matrix.entryAt foundRow foundCol :=
            smithMoveToPivotEntryOnPivot matrix isRect pivotIndex foundRow foundCol pivotRowInRange
              foundInRange.2.1 pivotColInRange foundInRange.2.2.2
          have signMagFound :
              (afterSign.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (smithSignNormalizeOpsPreservesPivotMagnitude afterMove pivotIndex afterMoveInRows).trans
              (congrArg Int.natAbs moveEntry)
          have signNonneg : 0 ≤ afterSign.entryAt pivotIndex pivotIndex :=
            signNormalizeOpsEntryOnPivotNonneg afterMove pivotIndex afterMoveInRows
          have colClearPreservesPivot :
              afterColumnClear.entryAt pivotIndex pivotIndex = afterSign.entryAt pivotIndex pivotIndex :=
            smithClearColumnBelowStepsPreservesRow afterSign pivotIndex pivotIndex pivotIndex
              (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign (Nat.lt_succ_self pivotIndex)
          have colClearPivotMag :
              (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs colClearPreservesPivot).trans signMagFound
          have colClearPivotNonneg : 0 ≤ afterColumnClear.entryAt pivotIndex pivotIndex :=
            Eq.mp (congrArg (0 ≤ ·) colClearPreservesPivot.symm) signNonneg
          have rowClearPreservesPivot :
              afterRowClear.entryAt pivotIndex pivotIndex = afterColumnClear.entryAt pivotIndex pivotIndex :=
            smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width
              pivotIndex pivotIndex pivotRowInRange (width - (pivotIndex + 1)) (pivotIndex + 1)
              afterColumnClear afterColumnClearRect (Nat.lt_succ_self pivotIndex)
          have settledPivotMag :
              (afterRowClear.entryAt pivotIndex pivotIndex).natAbs
                = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs rowClearPreservesPivot).trans colClearPivotMag
          have settledPivotNonzero : (afterRowClear.entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
            settledPivotMag.symm ▸ foundNonzero
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          show ((matrix.applyOperations
              (match smithCrossIsClear afterRowClear pivotIndex height width with
               | true => settledOps
               | false =>
                   settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width)).entryAt
              pivotIndex pivotIndex).natAbs ≠ 0
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true =>
              show ((matrix.applyOperations settledOps).entryAt pivotIndex pivotIndex).natAbs ≠ 0
              rw [hApplySettled]
              exact settledPivotNonzero
          | false =>
              show ((matrix.applyOperations
                  (settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width)).entryAt
                  pivotIndex pivotIndex).natAbs ≠ 0
              rw [applyOperationsAppend, hApplySettled]
              have nextFindIsSome : (smithFindMinAbsInMinor afterRowClear pivotIndex height width).isSome = true :=
                match smithFindMinAbsInMinorBoundsWitness afterRowClear pivotIndex height width
                    pivotIndex pivotIndex (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pivotRowInRange)
                    (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pivotColInRange)
                    settledPivotNonzero with
                | ⟨_, _, nextFindEq, _⟩ => by rw [nextFindEq]; rfl
              refine ih afterRowClear pivotIndex height width afterRowClearRect pivotRowInRange
                pivotColInRange ?_ nextFindIsSome
              intro nextRow nextCol hFindNext
              have boundFromWitness : ∀ witnessRow witnessCol,
                  pivotIndex ≤ witnessRow → witnessRow < pivotIndex + (height - pivotIndex) →
                  pivotIndex ≤ witnessCol → witnessCol < pivotIndex + (width - pivotIndex) →
                  (afterRowClear.entryAt witnessRow witnessCol).natAbs ≠ 0 →
                  (afterRowClear.entryAt witnessRow witnessCol).natAbs
                    < (matrix.entryAt foundRow foundCol).natAbs →
                  (afterRowClear.entryAt nextRow nextCol).natAbs ≤ fuel := by
                intro witnessRow witnessCol wRGe wRLt wCGe wCLt witNonzero witLtPivot
                match smithFindMinAbsInMinorBoundsWitness afterRowClear pivotIndex height width
                    witnessRow witnessCol wRGe wRLt wCGe wCLt witNonzero with
                | ⟨boundRow, boundCol, boundFindEq, boundLe⟩ =>
                    have someEq : some (boundRow, boundCol) = some (nextRow, nextCol) :=
                      boundFindEq.symm.trans hFindNext
                    injection someEq with pairEq
                    injection pairEq with rowEq colEq
                    subst rowEq
                    subst colEq
                    exact Nat.le_trans boundLe
                      (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le witLtPivot pivotMagLe))
              cases smithCrossNotClearWitness afterRowClear pivotIndex height width hCross with
              | inl rowWitness =>
                  obtain ⟨col, colGe, colLt, colNonzero⟩ := rowWitness
                  have colLtWidth : col < width :=
                    Eq.mp (congrArg (col < ·)
                      (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange)) colLt
                  have colClearPivotPositive : 0 < (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs :=
                    Nat.lt_of_lt_of_le pivotPositive (Nat.le_of_eq colClearPivotMag.symm)
                  have rowStrict :
                      (afterRowClear.entryAt pivotIndex col).natAbs
                        < (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs :=
                    smithClearRowRightStepsCrossEntryStrictlyDecreases afterColumnClear
                      afterColumnClearRect pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) col
                      (Nat.lt_succ_self pivotIndex) colGe colLt pivotRowInRange pivotColInRange
                      (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange))
                      colClearPivotNonneg colClearPivotPositive
                  have witLtPivot :
                      (afterRowClear.entryAt pivotIndex col).natAbs
                        < (matrix.entryAt foundRow foundCol).natAbs :=
                    Nat.lt_of_lt_of_le rowStrict (Nat.le_of_eq colClearPivotMag)
                  exact boundFromWitness pivotIndex col (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pivotRowInRange)
                    (Nat.le_of_succ_le colGe)
                    (natLtAddSubOfLt pivotIndex col width (Nat.le_of_succ_le colGe) colLtWidth)
                    colNonzero witLtPivot
              | inr colWitness =>
                  obtain ⟨row, rowGe, rowLt, rowNonzero⟩ := colWitness
                  have rowLtHeight : row < height :=
                    Eq.mp (congrArg (row < ·)
                      (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange)) rowLt
                  have signPositive : 0 < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
                    Nat.lt_of_lt_of_le pivotPositive (Nat.le_of_eq signMagFound.symm)
                  have rowClearPreservesCol :
                      afterRowClear.entryAt row pivotIndex = afterColumnClear.entryAt row pivotIndex :=
                    smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width
                      row pivotIndex rowLtHeight (width - (pivotIndex + 1)) (pivotIndex + 1)
                      afterColumnClear afterColumnClearRect (Nat.lt_succ_self pivotIndex)
                  have colStrict :
                      (afterColumnClear.entryAt row pivotIndex).natAbs
                        < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
                    smithClearColumnBelowStepsCrossEntryStrictlyDecreases afterSign afterSignRect
                      pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1) row
                      (Nat.lt_succ_self pivotIndex) rowGe rowLt pivotRowInRange pivotColInRange
                      (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange))
                      signNonneg signPositive
                  have witLtPivot :
                      (afterRowClear.entryAt row pivotIndex).natAbs
                        < (matrix.entryAt foundRow foundCol).natAbs :=
                    Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg Int.natAbs rowClearPreservesCol))
                      (Nat.lt_of_lt_of_le colStrict (Nat.le_of_eq signMagFound))
                  exact boundFromWitness row pivotIndex (Nat.le_of_succ_le rowGe)
                    (natLtAddSubOfLt pivotIndex row height (Nat.le_of_succ_le rowGe) rowLtHeight)
                    (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pivotColInRange)
                    rowNonzero witLtPivot

/-! ## (β) — the trailing cascade preserves find-`none` (INHABITED) -/

/-- **(β) INHABITED** — on every rectangular, in-range find-`none` state, the standalone trailing
`smithCascadeSweep` at its seed fuel leaves find-`none` intact.  Route: bridge to whole-block
divisibility; keystone pins `|pivot| = |gcd|`; bounded-below gcd invariance; the output pivot is a
NONZERO (non-vanishing lever) gcd-multiple `≤ |pivot| = |gcd|` (witness: the old pivot), hence exactly
`±gcd` — which divides the whole gcd-invariant output block; bridge back.  The zero-pivot corner has
an all-zero block where the cascade word is literally `[]`. -/
theorem smithBezoutTrailingCascadePreservesFindNoneHolds :
    SmithBezoutTrailingCascadePreservesFindNoneStatement := by
  intro matrix pivotIndex height width isRect pRowLt pColLt findNone
  have divisibleWithin :
      MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt pivotIndex) pivotIndex matrix :=
    (smithFindNonDividingInBlockNoneIffDivisibleWithin matrix pivotIndex height width isRect).mp findNone
  cases hPivotAbs : (matrix.diagonalEntryAt pivotIndex).natAbs with
  | zero =>
      -- Zero pivot: the whole block is zero, so the min-abs search is `none` and the word is `[]`.
      have pivotZero : matrix.diagonalEntryAt pivotIndex = 0 := intOfNatAbsZero _ hPivotAbs
      have blockAllZero : ∀ rowIndex, pivotIndex ≤ rowIndex → ∀ colIndex, pivotIndex ≤ colIndex →
          matrix.entryAt rowIndex colIndex = 0 := by
        intro rowIndex rowGe colIndex colGe
        have cellDivisible := matrixEntriesDivisibleByWithinAt divisibleWithin rowIndex colIndex rowGe colGe
        rw [pivotZero] at cellDivisible
        exact dividesExactlyZeroDivisorForcesZero cellDivisible
      cases hFindMin : smithFindMinAbsInMinor matrix pivotIndex height width with
      | some pair =>
          obtain ⟨minRow, minCol⟩ := pair
          have inRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            minRow minCol pRowLt pColLt hFindMin
          exact absurd
            (congrArg Int.natAbs (blockAllZero minRow inRange.1 minCol inRange.2.2.1))
            (smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width minRow minCol hFindMin)
      | none =>
          have wordNil : smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width = [] := by
            cases hSeed : smithMinorAbsSum matrix pivotIndex height width with
            | zero => rfl
            | succ seedPredecessor =>
                rw [smithCascadeSweepSucc seedPredecessor matrix pivotIndex height width, hFindMin]
          rw [wordNil]
          exact findNone
  | succ pivotMagnitudePredecessor =>
      -- Nonzero pivot: `|pivot| = |gcd|`; the output pivot is a nonzero gcd-multiple `≤ |gcd|`.
      have keystone : (matrix.diagonalEntryAt pivotIndex).natAbs
          = (minorGcdWithin matrix pivotIndex height width).natAbs :=
        blockDivisibilityImpliesAbsEqMinorGcd matrix pivotIndex height width isRect divisibleWithin
      have pivotNonzeroAbs : (matrix.entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
        fun absZero => Nat.noConfusion (absZero.symm.trans hPivotAbs)
      have afterRect :
          (matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).IsRectangular height width :=
        applyOperationsPreservesRectangular _ matrix isRect
      have gcdStable :
          minorGcdWithin
              (matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)) pivotIndex height width
            = minorGcdWithin matrix pivotIndex height width :=
        minorGcdStableUnderBoundedWord _ matrix isRect
          (smithCascadeSweepBoundedBelow pivotIndex _ matrix pivotIndex height width
            pRowLt pColLt (Nat.le_refl pivotIndex))
      have upperBound :
          ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
            ≤ (matrix.entryAt pivotIndex pivotIndex).natAbs :=
        smithCascadeSweepOutputPivotBounded (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex isRect pRowLt pColLt pivotIndex pivotIndex
          (Nat.le_refl pivotIndex) pRowLt (Nat.le_refl pivotIndex) pColLt
          pivotNonzeroAbs (Nat.le_refl _)
      have findMinSome : (smithFindMinAbsInMinor matrix pivotIndex height width).isSome = true :=
        match smithFindMinAbsInMinorBoundsWitness matrix pivotIndex height width pivotIndex pivotIndex
            (Nat.le_refl pivotIndex)
            (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
            (Nat.le_refl pivotIndex)
            (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)
            pivotNonzeroAbs with
        | ⟨_, _, findEq, _⟩ => by rw [findEq]; rfl
      have outputNonzero :
          (((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))).entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
        smithCascadeSweepOutputPivotNonzero (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width isRect pRowLt pColLt
          (smithCascadeSweepSeedFuelBound matrix pivotIndex height width pRowLt pColLt) findMinSome
      have gcdDividesAfter :
          MatrixEntriesDivisibleByWithin (minorGcdWithin matrix pivotIndex height width) pivotIndex
            (matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width)) := by
        have gcdDividesOwn := minorGcdWithinDividesWithin
          (matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)) pivotIndex height width afterRect
        rw [gcdStable] at gcdDividesOwn
        exact gcdDividesOwn
      have gcdDividesOutputPivot :
          dividesExactly (minorGcdWithin matrix pivotIndex height width)
            ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width)).entryAt pivotIndex pivotIndex) :=
        matrixEntriesDivisibleByWithinAt gcdDividesAfter pivotIndex pivotIndex
          (Nat.le_refl pivotIndex) (Nat.le_refl pivotIndex)
      have lowerBound :
          (minorGcdWithin matrix pivotIndex height width).natAbs
            ≤ ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)).entryAt pivotIndex pivotIndex).natAbs :=
        dividesExactlyNonzeroLowerBoundsMagnitude gcdDividesOutputPivot outputNonzero
      have outputAbsEqGcdAbs :
          ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
            = (minorGcdWithin matrix pivotIndex height width).natAbs :=
        Nat.le_antisymm (Nat.le_trans upperBound (Nat.le_of_eq keystone)) lowerBound
      have outputPivotCases := intEqOrNegOfNatAbsEqOfNonneg
        ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
        (minorGcdWithin matrix pivotIndex height width)
        (minorGcdWithinNonneg matrix pivotIndex height width)
        outputAbsEqGcdAbs
      refine (smithFindNonDividingInBlockNoneIffDivisibleWithin _ pivotIndex height width afterRect).mpr ?_
      intro rowIndex rowGe colIndex colGe
      show dividesExactly
        ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
        ((matrix.applyOperations (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).entryAt rowIndex colIndex)
      have cellDivisible := matrixEntriesDivisibleByWithinAt gcdDividesAfter rowIndex colIndex rowGe colGe
      cases outputPivotCases with
      | inl outputEqGcd => rw [outputEqGcd]; exact cellDivisible
      | inr outputEqNegGcd => rw [outputEqNegGcd]; exact dividesExactlyNegDivisor cellDivisible

/-! ## (α) — the round output pivot is POSITIVE on every find-`some` state (INHABITED) -/

/-- **(α) INHABITED** — on every rectangular, in-range, whole-block-find-`some` state (NO clean-cross
hypothesis: dirty crosses and zero pivots included), one Bezout-drop round lands a POSITIVE pivot
magnitude.  Route: the round ends with the cascade at `afterClear`'s own seed; if the min-abs search
on `afterClear` were `none`, the whole `afterClear` minor would be zero, forcing (bounded-below gcd
invariance of the fold+sign+Bezout prefix) the input minor's gcd to zero — which divides the found
offender, contradicting the find's guard-`false`; so the search is `some` and the non-vanishing lever
lands a nonzero output pivot. -/
theorem smithBezoutRepairRoundLandsPivotPositiveHolds :
    SmithBezoutRepairRoundLandsPivotPositiveStatement := by
  intro matrix pivotIndex height width isRect pRowLt pColLt findSome
  cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
  | none =>
      rw [hFind] at findSome
      exact Bool.noConfusion findSome
  | some foundPair =>
      obtain ⟨foundRow, foundCol⟩ := foundPair
      obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, guardFalse⟩ :=
        smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
          pRowLt pColLt hFind
      have offenderNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 := by
        intro offenderZero
        have dividesTrue : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
            (matrix.entryAt foundRow foundCol) = true := by
          rw [intOfNatAbsZero _ offenderZero]
          exact smithPivotDividesEntryZero _
        exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)
      have roundEq : smithBezoutRepairRound matrix pivotIndex height width
          = smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol := by
        unfold smithBezoutRepairRound
        rw [hFind]
      rw [roundEq]
      -- The staged matrices (definitionally the round's own `let`s).
      let afterFold := matrix.addRowMultiple foundRow pivotIndex 1
      let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
      let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
        (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
            (afterSign.entryAt pivotIndex foundCol)))
      let prefixWord : List ElementaryOperation :=
        [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
          ++ smithSignNormalizeOps afterFold pivotIndex
          ++ [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple
              pivotIndex foundCol
              (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
                  (afterSign.entryAt pivotIndex foundCol))))]
      have prefixApplied : matrix.applyOperations prefixWord = afterClear := by
        show matrix.applyOperations
            ([ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
              ++ smithSignNormalizeOps afterFold pivotIndex
              ++ [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple
                  pivotIndex foundCol
                  (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
                      (afterSign.entryAt pivotIndex foundCol))))]) = afterClear
        rw [applyOperationsAppend, applyOperationsAppend]
        rfl
      have prefixBounded : allOpsBoundedBelow pivotIndex prefixWord = true :=
        allOpsBoundedBelowAppend pivotIndex _ _
          (allOpsBoundedBelowAppend pivotIndex _ _
            (boolAndBothTrue
              (opBoundedBelowAddRow pivotIndex foundRow pivotIndex 1 pivotLeFoundRow (Nat.le_refl pivotIndex))
              rfl)
            (smithSignNormalizeOpsBoundedBelow afterFold pivotIndex pivotIndex))
          (boolAndBothTrue
            (opBoundedBelowAddColumn pivotIndex pivotIndex foundCol _ (Nat.le_refl pivotIndex) pivotLeFoundCol)
            rfl)
      have afterClearRect : afterClear.IsRectangular height width := by
        rw [← prefixApplied]
        exact applyOperationsPreservesRectangular prefixWord matrix isRect
      cases hFindMin : smithFindMinAbsInMinor afterClear pivotIndex height width with
      | none =>
          -- The `none` search zeroes the whole afterClear minor; gcd invariance kills the offender.
          exfalso
          have zeroDividesWithin : MatrixEntriesDivisibleByWithin 0 pivotIndex afterClear := by
            intro rowIndex rowGe colIndex colGe
            show dividesExactly 0 (afterClear.entryAt rowIndex colIndex)
            cases Nat.lt_or_ge rowIndex height with
            | inr rowGeHeight =>
                rw [entryAtBeyondZero afterClear afterClearRect rowIndex colIndex (Or.inl rowGeHeight)]
                exact dividesExactlyZero 0
            | inl rowLtHeight =>
                cases Nat.lt_or_ge colIndex width with
                | inr colGeWidth =>
                    rw [entryAtBeyondZero afterClear afterClearRect rowIndex colIndex (Or.inr colGeWidth)]
                    exact dividesExactlyZero 0
                | inl colLtWidth =>
                    have cellZeroAbs := smithFindMinAbsInMinorNoneAllZero afterClear pivotIndex height width
                      rowIndex colIndex hFindMin rowGe
                      (natLtAddSubOfLt pivotIndex rowIndex height rowGe rowLtHeight)
                      colGe (natLtAddSubOfLt pivotIndex colIndex width colGe colLtWidth)
                    rw [intOfNatAbsZero _ cellZeroAbs]
                    exact dividesExactlyZero 0
          have gcdAfterClearZero : minorGcdWithin afterClear pivotIndex height width = 0 :=
            dividesExactlyZeroDivisorForcesZero
              (minorGcdWithinGreatest afterClear pivotIndex height width 0 zeroDividesWithin)
          have gcdMatrixZero : minorGcdWithin matrix pivotIndex height width = 0 := by
            have gcdStable := minorGcdStableUnderBoundedWord prefixWord matrix isRect prefixBounded
            rw [prefixApplied] at gcdStable
            exact gcdStable.symm.trans gcdAfterClearZero
          have offenderDivisible : dividesExactly (minorGcdWithin matrix pivotIndex height width)
              (matrix.entryAt foundRow foundCol) :=
            matrixEntriesDivisibleByWithinAt
              (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)
              foundRow foundCol pivotLeFoundRow pivotLeFoundCol
          rw [gcdMatrixZero] at offenderDivisible
          exact offenderNonzero
            (congrArg Int.natAbs (dividesExactlyZeroDivisorForcesZero offenderDivisible))
      | some minPair =>
          have outputPivotNonzero :
              (((afterClear.applyOperations
                  (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width)
                    afterClear pivotIndex height width))).entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
            smithCascadeSweepOutputPivotNonzero (smithMinorAbsSum afterClear pivotIndex height width)
              afterClear pivotIndex height width afterClearRect pRowLt pColLt
              (smithCascadeSweepSeedFuelBound afterClear pivotIndex height width pRowLt pColLt)
              (by rw [hFindMin]; rfl)
          show 0 < ((afterClear.applyOperations
              (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width)
                afterClear pivotIndex height width)).entryAt pivotIndex pivotIndex).natAbs
          exact match Nat.eq_zero_or_pos ((afterClear.applyOperations
              (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width)
                afterClear pivotIndex height width)).entryAt pivotIndex pivotIndex).natAbs with
            | Or.inl isZero => absurd isZero outputPivotNonzero
            | Or.inr isPositive => isPositive

/-! ## The dirty-tolerant first-round bound — `m1 ≤ seed` on EVERY entry state

Every corner has a single-entry witness because the self-transvection guards degrade degenerate folds
to identities: the pivot slot after the prefix is either nonzero (its own witness, worth one or the
sum of two matrix entries collapsing to one), or zero — in which case the Bezout coefficient
multiplies a ZERO source entry and the original offender survives verbatim as the witness. -/

/-- **The dirty-tolerant first-round bound** — on every rectangular, in-range state with a found
in-block non-dividing offender (NO clean-cross, NO positivity), the Bezout-drop round's output pivot
magnitude is `≤ smithMinorAbsSum matrix` (the position sweep's seed).  Four witness corners, each a
single matrix entry. -/
theorem smithBezoutRepairRoundAtFoundPivotMagnitudeLeMinorAbsSum
    (matrix : IntMatrix) (pivotIndex height width foundRow foundCol : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (foundRowLt : foundRow < height)
    (pivotLeFoundCol : pivotIndex ≤ foundCol) (foundColLt : foundCol < width)
    (offenderNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0) :
    pivotMagnitudeWithin (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
        pivotIndex
      ≤ smithMinorAbsSum matrix pivotIndex height width := by
  let afterFold := matrix.addRowMultiple foundRow pivotIndex 1
  let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
  let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
    (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
        (afterSign.entryAt pivotIndex foundCol)))
  have afterFoldRect : afterFold.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
      matrix isRect
  have afterFoldRows : pivotIndex < afterFold.rows.length :=
    Eq.mp (congrArg (pivotIndex < ·) afterFoldRect.1.symm) pRowLt
  have afterSignRect : afterSign.IsRectangular height width :=
    applyOperationsPreservesRectangular (smithSignNormalizeOps afterFold pivotIndex) afterFold afterFoldRect
  have afterClearRect : afterClear.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple pivotIndex foundCol
        (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
            (afterSign.entryAt pivotIndex foundCol))))]
      afterSign afterSignRect
  -- The Bezout column op leaves the pivot COLUMN slot untouched (off-target or identity).
  have clearPivotEq : afterClear.entryAt pivotIndex pivotIndex = afterSign.entryAt pivotIndex pivotIndex := by
    cases Nat.decEq pivotIndex foundCol with
    | isTrue pivotEqFound =>
        show (afterSign.addColumnMultiple pivotIndex foundCol _).entryAt pivotIndex pivotIndex = _
        rw [← pivotEqFound, addColumnMultipleSelfIsIdentity]
    | isFalse pivotNeFound =>
        exact addColumnMultipleEntryOffTargetCol afterSign afterSignRect pivotIndex foundCol
          pivotIndex pivotIndex _ pivotNeFound pRowLt
  have signPivotMagEq : (afterSign.entryAt pivotIndex pivotIndex).natAbs
      = (afterFold.entryAt pivotIndex pivotIndex).natAbs :=
    smithSignNormalizeOpsPreservesPivotMagnitude afterFold pivotIndex afterFoldRows
  -- The delivered goal, shaped once.
  show ((afterClear.applyOperations
      (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width)
        afterClear pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
    ≤ smithMinorAbsSum matrix pivotIndex height width
  -- The one-shot witness closer: any nonzero afterClear cell already `≤ seed(matrix)` bounds the
  -- round output through `smithCascadeSweepOutputPivotBounded` at afterClear's own seed.
  have closeWithWitness : ∀ (witnessRow witnessCol : Nat),
      pivotIndex ≤ witnessRow → witnessRow < height → pivotIndex ≤ witnessCol → witnessCol < width →
      (afterClear.entryAt witnessRow witnessCol).natAbs ≠ 0 →
      (afterClear.entryAt witnessRow witnessCol).natAbs ≤ smithMinorAbsSum matrix pivotIndex height width →
      ((afterClear.applyOperations
          (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width)
            afterClear pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
        ≤ smithMinorAbsSum matrix pivotIndex height width :=
    fun witnessRow witnessCol wRGe wRLt wCGe wCLt wNonzero wLe =>
      Nat.le_trans
        (smithCascadeSweepOutputPivotBounded (smithMinorAbsSum afterClear pivotIndex height width)
          afterClear pivotIndex afterClearRect pRowLt pColLt witnessRow witnessCol
          wRGe wRLt wCGe wCLt wNonzero (Nat.le_refl _))
        wLe
  cases Nat.decEq foundRow pivotIndex with
  | isFalse foundNePivot =>
      cases hColEntryAbs : (matrix.entryAt foundRow pivotIndex).natAbs with
      | succ colEntryPredecessor =>
          -- DIRTY COLUMN: the nonzero column entry survives to afterClear verbatim as the witness.
          have clearColSlotEq : afterClear.entryAt foundRow pivotIndex
              = afterSign.entryAt foundRow pivotIndex := by
            cases Nat.decEq pivotIndex foundCol with
            | isTrue pivotEqFound =>
                show (afterSign.addColumnMultiple pivotIndex foundCol _).entryAt foundRow pivotIndex = _
                rw [← pivotEqFound, addColumnMultipleSelfIsIdentity]
            | isFalse pivotNeFound =>
                exact addColumnMultipleEntryOffTargetCol afterSign afterSignRect pivotIndex foundCol
                  foundRow pivotIndex _ pivotNeFound foundRowLt
          have signColSlotEq : afterSign.entryAt foundRow pivotIndex
              = afterFold.entryAt foundRow pivotIndex :=
            signNormalizeOpsPreserveEntryOffPivot afterFold pivotIndex foundRow pivotIndex foundNePivot
          have foldColSlotEq : afterFold.entryAt foundRow pivotIndex
              = matrix.entryAt foundRow pivotIndex :=
            addRowMultiplePreservesEntryOffTargetRow matrix foundRow pivotIndex 1 foundRow pivotIndex
              foundNePivot
          have witnessValueEq : afterClear.entryAt foundRow pivotIndex
              = matrix.entryAt foundRow pivotIndex :=
            (clearColSlotEq.trans signColSlotEq).trans foldColSlotEq
          refine closeWithWitness foundRow pivotIndex pivotLeFoundRow foundRowLt
            (Nat.le_refl pivotIndex) pColLt ?_ ?_
          · rw [congrArg Int.natAbs witnessValueEq, hColEntryAbs]
            exact fun contra => Nat.noConfusion contra
          · rw [congrArg Int.natAbs witnessValueEq]
            exact smithMinorEntryLeAbsSum matrix pivotIndex height width foundRow pivotIndex
              pivotLeFoundRow
              (natLtAddSubOfLt pivotIndex foundRow height pivotLeFoundRow foundRowLt)
              (Nat.le_refl pivotIndex)
              (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)
      | zero =>
          -- CLEAN COLUMN entry: the fold leaves the pivot slot at the original pivot value.
          have foldPivotEq : afterFold.entryAt pivotIndex pivotIndex
              = matrix.entryAt pivotIndex pivotIndex := by
            show (matrix.addRowMultiple foundRow pivotIndex 1).entryAt pivotIndex pivotIndex = _
            rw [addRowMultipleEntryOnTargetRow matrix isRect foundRow pivotIndex pivotIndex 1
              foundNePivot foundRowLt pRowLt pColLt, intOfNatAbsZero _ hColEntryAbs, intMulZero,
              intAddZero]
          cases hPivotEntryAbs : (matrix.entryAt pivotIndex pivotIndex).natAbs with
          | succ pivotEntryPredecessor =>
              -- The pivot slot itself is the (nonzero) witness.
              have clearPivotAbsEq : (afterClear.entryAt pivotIndex pivotIndex).natAbs
                  = (matrix.entryAt pivotIndex pivotIndex).natAbs :=
                ((congrArg Int.natAbs clearPivotEq).trans signPivotMagEq).trans
                  (congrArg Int.natAbs foldPivotEq)
              refine closeWithWitness pivotIndex pivotIndex (Nat.le_refl pivotIndex) pRowLt
                (Nat.le_refl pivotIndex) pColLt ?_ ?_
              · rw [clearPivotAbsEq, hPivotEntryAbs]
                exact fun contra => Nat.noConfusion contra
              · rw [clearPivotAbsEq]
                exact smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex pivotIndex
                  (Nat.le_refl pivotIndex)
                  (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
                  (Nat.le_refl pivotIndex)
                  (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)
          | zero =>
              -- ZERO pivot after the prefix: the Bezout coefficient multiplies the ZERO pivot-column
              -- source, so the original offender survives to afterClear as the witness.
              have signPivotZero : afterSign.entryAt pivotIndex pivotIndex = 0 :=
                intOfNatAbsZero _ (signPivotMagEq.trans
                  ((congrArg Int.natAbs foldPivotEq).trans hPivotEntryAbs))
              have foundColNePivot : foundCol ≠ pivotIndex := by
                intro foundColEqPivot
                have offenderIsColSlot : (matrix.entryAt foundRow foundCol).natAbs
                    = (matrix.entryAt foundRow pivotIndex).natAbs := by
                  rw [foundColEqPivot]
                exact offenderNonzero (offenderIsColSlot.trans hColEntryAbs)
              have signColZero : afterSign.entryAt foundRow pivotIndex = 0 :=
                ((signNormalizeOpsPreserveEntryOffPivot afterFold pivotIndex foundRow pivotIndex
                  foundNePivot).trans
                  (addRowMultiplePreservesEntryOffTargetRow matrix foundRow pivotIndex 1 foundRow
                    pivotIndex foundNePivot)).trans (intOfNatAbsZero _ hColEntryAbs)
              have clearOffenderEq : afterClear.entryAt foundRow foundCol
                  = afterSign.entryAt foundRow foundCol := by
                have onTarget := addColumnMultipleEntryOnTargetCol afterSign afterSignRect
                  pivotIndex foundCol foundRow
                  (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
                      (afterSign.entryAt pivotIndex foundCol)))
                  (fun pivotEqFound => foundColNePivot pivotEqFound.symm) foundRowLt pColLt foundColLt
                rw [onTarget, signColZero, intMulZero, intAddZero]
              have signOffenderEq : afterSign.entryAt foundRow foundCol
                  = matrix.entryAt foundRow foundCol :=
                (signNormalizeOpsPreserveEntryOffPivot afterFold pivotIndex foundRow foundCol
                  foundNePivot).trans
                  (addRowMultiplePreservesEntryOffTargetRow matrix foundRow pivotIndex 1 foundRow
                    foundCol foundNePivot)
              have witnessValueEq : afterClear.entryAt foundRow foundCol
                  = matrix.entryAt foundRow foundCol :=
                clearOffenderEq.trans signOffenderEq
              refine closeWithWitness foundRow foundCol pivotLeFoundRow foundRowLt
                pivotLeFoundCol foundColLt ?_ ?_
              · rw [congrArg Int.natAbs witnessValueEq]
                exact offenderNonzero
              · rw [congrArg Int.natAbs witnessValueEq]
                exact smithMinorEntryLeAbsSum matrix pivotIndex height width foundRow foundCol
                  pivotLeFoundRow
                  (natLtAddSubOfLt pivotIndex foundRow height pivotLeFoundRow foundRowLt)
                  pivotLeFoundCol
                  (natLtAddSubOfLt pivotIndex foundCol width pivotLeFoundCol foundColLt)
  | isTrue foundEqPivot =>
      -- SELF-FOLD (offender in the pivot row): the fold is the operation-level identity.
      have foldIdentity : matrix.addRowMultiple foundRow pivotIndex 1 = matrix := by
        rw [foundEqPivot]
        exact addRowMultipleSelfIsIdentity matrix pivotIndex 1
      have foldPivotEq : afterFold.entryAt pivotIndex pivotIndex
          = matrix.entryAt pivotIndex pivotIndex := by
        show (matrix.addRowMultiple foundRow pivotIndex 1).entryAt pivotIndex pivotIndex = _
        rw [foldIdentity]
      cases hPivotEntryAbs : (matrix.entryAt pivotIndex pivotIndex).natAbs with
      | succ pivotEntryPredecessor =>
          have clearPivotAbsEq : (afterClear.entryAt pivotIndex pivotIndex).natAbs
              = (matrix.entryAt pivotIndex pivotIndex).natAbs :=
            ((congrArg Int.natAbs clearPivotEq).trans signPivotMagEq).trans
              (congrArg Int.natAbs foldPivotEq)
          refine closeWithWitness pivotIndex pivotIndex (Nat.le_refl pivotIndex) pRowLt
            (Nat.le_refl pivotIndex) pColLt ?_ ?_
          · rw [clearPivotAbsEq, hPivotEntryAbs]
            exact fun contra => Nat.noConfusion contra
          · rw [clearPivotAbsEq]
            exact smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex pivotIndex
              (Nat.le_refl pivotIndex)
              (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
              (Nat.le_refl pivotIndex)
              (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)
      | zero =>
          -- Zero pivot with the offender ON the pivot row: the offender's pivot-ROW slot survives
          -- through the coefficient times the ZERO pivot source.
          have signPivotZero : afterSign.entryAt pivotIndex pivotIndex = 0 :=
            intOfNatAbsZero _ (signPivotMagEq.trans
              ((congrArg Int.natAbs foldPivotEq).trans hPivotEntryAbs))
          have foundColNePivot : foundCol ≠ pivotIndex := by
            intro foundColEqPivot
            have offenderIsPivot : (matrix.entryAt foundRow foundCol).natAbs
                = (matrix.entryAt pivotIndex pivotIndex).natAbs := by
              rw [foundEqPivot, foundColEqPivot]
            exact offenderNonzero (offenderIsPivot.trans hPivotEntryAbs)
          have clearRowSlotEq : afterClear.entryAt pivotIndex foundCol
              = afterSign.entryAt pivotIndex foundCol := by
            have onTarget := addColumnMultipleEntryOnTargetCol afterSign afterSignRect
              pivotIndex foundCol pivotIndex
              (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
                  (afterSign.entryAt pivotIndex foundCol)))
              (fun pivotEqFound => foundColNePivot pivotEqFound.symm) pRowLt pColLt foundColLt
            rw [onTarget, signPivotZero, intMulZero, intAddZero]
          have signRowSlotAbs : (afterSign.entryAt pivotIndex foundCol).natAbs
              = (matrix.entryAt pivotIndex foundCol).natAbs := by
            have rowMag := smithSignNormalizeOpsPreservesRowMagnitude afterFold pivotIndex foundCol
              afterFoldRows
            rw [rowMag]
            show ((matrix.addRowMultiple foundRow pivotIndex 1).entryAt pivotIndex foundCol).natAbs = _
            rw [foldIdentity]
          have offenderOnPivotRow : (matrix.entryAt pivotIndex foundCol).natAbs
              = (matrix.entryAt foundRow foundCol).natAbs := by
            rw [foundEqPivot]
          refine closeWithWitness pivotIndex foundCol (Nat.le_refl pivotIndex) pRowLt
            pivotLeFoundCol foundColLt ?_ ?_
          · rw [congrArg Int.natAbs clearRowSlotEq, signRowSlotAbs, offenderOnPivotRow]
            exact offenderNonzero
          · rw [congrArg Int.natAbs clearRowSlotEq, signRowSlotAbs]
            exact smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex foundCol
              (Nat.le_refl pivotIndex)
              (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
              pivotLeFoundCol
              (natLtAddSubOfLt pivotIndex foundCol width pivotLeFoundCol foundColLt)

/-! ## The word/staged bridge + the succ-unfold equations -/

/-- **The round WORD applied equals the STAGED round** — `applyOperationsAppend` twice over the
word's `(fold ++ sign) ++ bezout ++ cascade` shape; every stage is then definitionally the staged
`let`. -/
theorem smithBezoutRepairRoundWordAtFoundApplied
    (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat) :
    work.applyOperations (smithBezoutRepairRoundWordAtFound work pivotIndex height width foundRow foundCol)
      = smithBezoutRepairRoundAtFound work pivotIndex height width foundRow foundCol := by
  show work.applyOperations
      ([ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
        ++ smithSignNormalizeOps
            (work.applyOperations
              [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)])
            pivotIndex
        ++ _ ++ _) = _
  rw [applyOperationsAppend, applyOperationsAppend, applyOperationsAppend]
  rfl

/-- **The Bezout position sweep's succ-unfold** — the definitional equation with the `let`s
inlined. -/
theorem smithBezoutRepairPositionSweepSucc (fuel : Nat) (matrix : IntMatrix)
    (pivotIndex height width : Nat) :
    smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
      = (match smithFindNonDividingInBlock matrix pivotIndex height width with
         | none =>
             smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
               height width
         | some (foundRow, foundCol) =>
             smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
               ++ smithBezoutRepairPositionSweep fuel
                   (matrix.applyOperations
                     (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                   pivotIndex height width) :=
  rfl

/-! ## THE MASTER — the gcd-floored fuel induction: the sweep lands find-`none` AND cross-clear

The invariant `0 < p ∧ p ≤ fuel + |minorGcd|` burns one fuel per K1 round; at fuel exhaustion the
pivot magnitude has descended EXACTLY to the (invariant, positive) block gcd — and a pivot AT the
gcd divides the whole block, so the fuel-0 base PROVES the landing instead of failing. -/

/-- **The master fuel-adequacy induction** — on a rectangular, in-range, CROSS-CLEAN state whose
pivot is either already whole-block-dividing (find-`none`) or positive with
`p ≤ fuel + |minorGcd|`, the fueled Bezout position sweep lands find-`none` AND a clear cross.
Structural on the fuel; the `none` branch is (β) + the seed cross-clear; the `some` branch burns one
K1 round (strict descent, cross-clean maintenance, (α) positivity, bounded-word gcd invariance) and
recurses. -/
theorem smithBezoutRepairPositionSweepMasterLandsFindNoneAndCrossClear :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      smithPivotCrossClean matrix pivotIndex height width →
      (smithFindNonDividingInBlock matrix pivotIndex height width = none
        ∨ (0 < pivotMagnitudeWithin matrix pivotIndex
            ∧ pivotMagnitudeWithin matrix pivotIndex
                ≤ fuel + (minorGcdWithin matrix pivotIndex height width).natAbs)) →
      smithFindNonDividingInBlock
          (matrix.applyOperations (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width))
          pivotIndex height width = none
        ∧ smithPivotCrossClean
            (matrix.applyOperations (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width))
            pivotIndex height width := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width isRect pRowLt pColLt crossClean measureState
      -- The empty sweep returns the input; find-`none` either holds already or is forced by the
      -- gcd floor: `0 < p ≤ |gcd|` with `gcd ∣ pivot` pins `pivot = ±gcd`, which divides the block.
      refine ⟨?_, crossClean⟩
      cases measureState with
      | inl findNone => exact findNone
      | inr measureBound =>
          obtain ⟨pivotPositive, pivotLeGcd⟩ := measureBound
          have pivotNonzeroAbs : (matrix.entryAt pivotIndex pivotIndex).natAbs ≠ 0 :=
            fun absZero => Nat.lt_irrefl 0 (absZero ▸ pivotPositive)
          have gcdDividesPivot : dividesExactly (minorGcdWithin matrix pivotIndex height width)
              (matrix.entryAt pivotIndex pivotIndex) :=
            matrixEntriesDivisibleByWithinAt
              (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)
              pivotIndex pivotIndex (Nat.le_refl pivotIndex) (Nat.le_refl pivotIndex)
          have gcdLePivot : (minorGcdWithin matrix pivotIndex height width).natAbs
              ≤ (matrix.entryAt pivotIndex pivotIndex).natAbs :=
            dividesExactlyNonzeroLowerBoundsMagnitude gcdDividesPivot pivotNonzeroAbs
          have pivotLeGcdPlain : (matrix.entryAt pivotIndex pivotIndex).natAbs
              ≤ (minorGcdWithin matrix pivotIndex height width).natAbs := by
            have zeroAddEq : (0 : Nat) + (minorGcdWithin matrix pivotIndex height width).natAbs
                = (minorGcdWithin matrix pivotIndex height width).natAbs :=
              Nat.zero_add _
            exact Eq.mp (congrArg (pivotMagnitudeWithin matrix pivotIndex ≤ ·) zeroAddEq) pivotLeGcd
          have pivotAbsEqGcdAbs : (matrix.diagonalEntryAt pivotIndex).natAbs
              = (minorGcdWithin matrix pivotIndex height width).natAbs :=
            Nat.le_antisymm pivotLeGcdPlain gcdLePivot
          have pivotCases := intEqOrNegOfNatAbsEqOfNonneg
            (matrix.diagonalEntryAt pivotIndex) (minorGcdWithin matrix pivotIndex height width)
            (minorGcdWithinNonneg matrix pivotIndex height width) pivotAbsEqGcdAbs
          refine (smithFindNonDividingInBlockNoneIffDivisibleWithin matrix pivotIndex height width
            isRect).mpr ?_
          intro rowIndex rowGe colIndex colGe
          show dividesExactly (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt rowIndex colIndex)
          have cellDivisible := matrixEntriesDivisibleByWithinAt
            (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)
            rowIndex colIndex rowGe colGe
          cases pivotCases with
          | inl pivotEqGcd => rw [pivotEqGcd]; exact cellDivisible
          | inr pivotEqNegGcd => rw [pivotEqNegGcd]; exact dividesExactlyNegDivisor cellDivisible
  | succ fuel ih =>
      intro matrix pivotIndex height width isRect pRowLt pColLt crossClean measureState
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold]
          exact ⟨smithBezoutTrailingCascadePreservesFindNoneHolds matrix pivotIndex height width
              isRect pRowLt pColLt hFind,
            smithCascadeSweepSeedReachesCrossClear matrix pivotIndex height width isRect pRowLt pColLt⟩
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          obtain ⟨pivotPositive, pivotLeBound⟩ : 0 < pivotMagnitudeWithin matrix pivotIndex
              ∧ pivotMagnitudeWithin matrix pivotIndex
                  ≤ (fuel + 1) + (minorGcdWithin matrix pivotIndex height width).natAbs := by
            cases measureState with
            | inl findNone => rw [hFind] at findNone; exact nomatch findNone
            | inr measureBound => exact measureBound
          obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, _guardFalse⟩ :=
            smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
              pRowLt pColLt hFind
          have findSomeBool : (smithFindNonDividingInBlock matrix pivotIndex height width).isSome
              = true := by
            rw [hFind]; rfl
          have dispatchEq : smithBezoutRepairRound matrix pivotIndex height width
              = smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol := by
            unfold smithBezoutRepairRound
            rw [hFind]
          -- (α): positive landed pivot.
          have alphaPositive := smithBezoutRepairRoundLandsPivotPositiveHolds matrix pivotIndex
            height width isRect pRowLt pColLt findSomeBool
          rw [dispatchEq] at alphaPositive
          -- K1: strict descent.
          have k1Descends := smithBezoutRoundStrictlyDescendsOnCleanCross matrix pivotIndex height
            width isRect pRowLt pColLt crossClean pivotPositive findSomeBool
          rw [dispatchEq] at k1Descends
          -- Maintenance: the round re-establishes the clean cross.
          have maintained := smithBezoutRepairRoundAtFoundReEstablishesCrossClean matrix pivotIndex
            height width foundRow foundCol isRect pRowLt pColLt
          -- Content: the round word preserves the block gcd.
          have roundWordApplied := smithBezoutRepairRoundWordAtFoundApplied matrix pivotIndex height
            width foundRow foundCol
          have gcdInvariant :
              minorGcdWithin (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                  pivotIndex height width
                = minorGcdWithin matrix pivotIndex height width := by
            rw [← roundWordApplied]
            exact minorGcdStableUnderBoundedWord _ matrix isRect
              (smithBezoutRepairRoundWordAtFoundBoundedBelow pivotIndex matrix pivotIndex height width
                foundRow foundCol pRowLt pColLt (Nat.le_refl pivotIndex) pivotLeFoundRow pivotLeFoundCol)
          have atFoundRect :
              (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol).IsRectangular
                height width := by
            rw [← roundWordApplied]
            exact applyOperationsPreservesRectangular _ matrix isRect
          -- The descended measure fits the remaining fuel.
          have measureDescended :
              pivotMagnitudeWithin
                  (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                  pivotIndex
                ≤ fuel + (minorGcdWithin
                    (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                    pivotIndex height width).natAbs := by
            rw [gcdInvariant]
            have strictBound : pivotMagnitudeWithin
                (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                pivotIndex
                < (fuel + 1) + (minorGcdWithin matrix pivotIndex height width).natAbs :=
              Nat.lt_of_lt_of_le k1Descends pivotLeBound
            have shiftedForm : (fuel + 1) + (minorGcdWithin matrix pivotIndex height width).natAbs
                = (fuel + (minorGcdWithin matrix pivotIndex height width).natAbs) + 1 :=
              Nat.succ_add fuel (minorGcdWithin matrix pivotIndex height width).natAbs
            exact Nat.le_of_lt_succ (Eq.mp (congrArg (_ < ·) shiftedForm) strictBound)
          -- Unfold one sweep round and recurse.
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
                  ++ smithBezoutRepairPositionSweep fuel
                      (matrix.applyOperations
                        (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                      pivotIndex height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold, applyOperationsAppend, roundWordApplied]
          exact ih (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
            pivotIndex height width atFoundRect pRowLt pColLt maintained
            (Or.inr ⟨alphaPositive, measureDescended⟩)

/-! ## ARC-A at the ACTUAL seed — NO entry-state hypotheses beyond rectangularity + range

The first round from ANY entry state (zero pivot, dirty cross, both) burns one fuel and lands a
positive-pivot, cross-clean state whose measure fits `(seed - 1) + |gcd|` because the dirty-tolerant
bound gives `m1 ≤ seed` and a find-`some` block has `|gcd| ≥ 1`. -/

/-- **ARC-A, seed-level, STRENGTHENED** — for every rectangular matrix with the pivot in range
(NO cross-clean hypothesis), the Bezout position sweep at its ACTUAL seed `smithMinorAbsSum` lands
whole-block find-`none` AND a clear pivot cross.  Exactly the per-position fact the ARC-C settling
and chain inductions consume. -/
theorem smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithFindNonDividingInBlock
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width = none
      ∧ smithPivotCrossClean
          (matrix.applyOperations
            (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          pivotIndex height width := by
  cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
  | none =>
      cases hSeed : smithMinorAbsSum matrix pivotIndex height width with
      | zero =>
          -- Zero seed: the whole block (hence the cross) is zero and the sweep is empty.
          have crossPointwiseZero : smithPivotCrossClean matrix pivotIndex height width := by
            show (smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) &&
              smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)) = true
            have rowTrue := smithRowSegmentAllZeroOfPointwiseZero matrix pivotIndex
              (width - (pivotIndex + 1)) (pivotIndex + 1)
              (fun col colGe colLt => by
                have colLtWidth : col < width :=
                  Eq.mp (congrArg (col < ·) (smithNatAddSubOfLe (pivotIndex + 1) width pColLt)) colLt
                have entryLeSeed := smithMinorEntryLeAbsSum matrix pivotIndex height width pivotIndex col
                  (Nat.le_refl pivotIndex)
                  (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pRowLt)
                  (Nat.le_of_succ_le colGe)
                  (natLtAddSubOfLt pivotIndex col width (Nat.le_of_succ_le colGe) colLtWidth)
                rw [hSeed] at entryLeSeed
                exact Nat.le_antisymm entryLeSeed (Nat.zero_le _))
            have colTrue := smithColSegmentAllZeroOfPointwiseZero matrix pivotIndex
              (height - (pivotIndex + 1)) (pivotIndex + 1)
              (fun row rowGe rowLt => by
                have rowLtHeight : row < height :=
                  Eq.mp (congrArg (row < ·) (smithNatAddSubOfLe (pivotIndex + 1) height pRowLt)) rowLt
                have entryLeSeed := smithMinorEntryLeAbsSum matrix pivotIndex height width row pivotIndex
                  (Nat.le_of_succ_le rowGe)
                  (natLtAddSubOfLt pivotIndex row height (Nat.le_of_succ_le rowGe) rowLtHeight)
                  (Nat.le_refl pivotIndex)
                  (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pColLt)
                rw [hSeed] at entryLeSeed
                exact Nat.le_antisymm entryLeSeed (Nat.zero_le _))
            rw [rowTrue, colTrue]
            rfl
          exact ⟨hFind, crossPointwiseZero⟩
      | succ seedPredecessor =>
          have hUnfold : smithBezoutRepairPositionSweep (seedPredecessor + 1) matrix pivotIndex
              height width
              = smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold]
          exact ⟨smithBezoutTrailingCascadePreservesFindNoneHolds matrix pivotIndex height width
              isRect pRowLt pColLt hFind,
            smithCascadeSweepSeedReachesCrossClear matrix pivotIndex height width isRect pRowLt pColLt⟩
  | some foundPair =>
      obtain ⟨foundRow, foundCol⟩ := foundPair
      obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, guardFalse⟩ :=
        smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
          pRowLt pColLt hFind
      have offenderNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 := by
        intro offenderZero
        have dividesTrue : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
            (matrix.entryAt foundRow foundCol) = true := by
          rw [intOfNatAbsZero _ offenderZero]
          exact smithPivotDividesEntryZero _
        exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)
      have offenderLeSeed : (matrix.entryAt foundRow foundCol).natAbs
          ≤ smithMinorAbsSum matrix pivotIndex height width :=
        smithMinorEntryLeAbsSum matrix pivotIndex height width foundRow foundCol
          pivotLeFoundRow (natLtAddSubOfLt pivotIndex foundRow height pivotLeFoundRow foundRowLt)
          pivotLeFoundCol (natLtAddSubOfLt pivotIndex foundCol width pivotLeFoundCol foundColLt)
      have offenderPositive : 0 < (matrix.entryAt foundRow foundCol).natAbs :=
        match Nat.eq_zero_or_pos (matrix.entryAt foundRow foundCol).natAbs with
        | Or.inl isZero => absurd isZero offenderNonzero
        | Or.inr isPositive => isPositive
      have gcdNonzeroAbs : (minorGcdWithin matrix pivotIndex height width).natAbs ≠ 0 := by
        intro gcdZeroAbs
        have offenderDivisible := matrixEntriesDivisibleByWithinAt
          (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)
          foundRow foundCol pivotLeFoundRow pivotLeFoundCol
        rw [intOfNatAbsZero _ gcdZeroAbs] at offenderDivisible
        exact offenderNonzero
          (congrArg Int.natAbs (dividesExactlyZeroDivisorForcesZero offenderDivisible))
      have gcdPositiveAbs : 0 < (minorGcdWithin matrix pivotIndex height width).natAbs :=
        match Nat.eq_zero_or_pos (minorGcdWithin matrix pivotIndex height width).natAbs with
        | Or.inl isZero => absurd isZero gcdNonzeroAbs
        | Or.inr isPositive => isPositive
      cases hSeed : smithMinorAbsSum matrix pivotIndex height width with
      | zero =>
          rw [hSeed] at offenderLeSeed
          exact absurd (Nat.le_antisymm offenderLeSeed (Nat.zero_le _)) offenderNonzero
      | succ seedPredecessor =>
          -- One dirty-tolerant round, then the master.
          have findSomeBool : (smithFindNonDividingInBlock matrix pivotIndex height width).isSome
              = true := by
            rw [hFind]; rfl
          have dispatchEq : smithBezoutRepairRound matrix pivotIndex height width
              = smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol := by
            unfold smithBezoutRepairRound
            rw [hFind]
          have alphaPositive := smithBezoutRepairRoundLandsPivotPositiveHolds matrix pivotIndex
            height width isRect pRowLt pColLt findSomeBool
          rw [dispatchEq] at alphaPositive
          have maintained := smithBezoutRepairRoundAtFoundReEstablishesCrossClean matrix pivotIndex
            height width foundRow foundCol isRect pRowLt pColLt
          have roundWordApplied := smithBezoutRepairRoundWordAtFoundApplied matrix pivotIndex height
            width foundRow foundCol
          have atFoundRect :
              (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol).IsRectangular
                height width := by
            rw [← roundWordApplied]
            exact applyOperationsPreservesRectangular _ matrix isRect
          have gcdInvariant :
              minorGcdWithin (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                  pivotIndex height width
                = minorGcdWithin matrix pivotIndex height width := by
            rw [← roundWordApplied]
            exact minorGcdStableUnderBoundedWord _ matrix isRect
              (smithBezoutRepairRoundWordAtFoundBoundedBelow pivotIndex matrix pivotIndex height width
                foundRow foundCol pRowLt pColLt (Nat.le_refl pivotIndex) pivotLeFoundRow pivotLeFoundCol)
          have dirtyRoundBound := smithBezoutRepairRoundAtFoundPivotMagnitudeLeMinorAbsSum matrix
            pivotIndex height width foundRow foundCol isRect pRowLt pColLt pivotLeFoundRow foundRowLt
            pivotLeFoundCol foundColLt offenderNonzero
          rw [hSeed] at dirtyRoundBound
          have measureFits :
              pivotMagnitudeWithin
                  (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                  pivotIndex
                ≤ seedPredecessor + (minorGcdWithin
                    (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
                    pivotIndex height width).natAbs := by
            rw [gcdInvariant]
            exact Nat.le_trans dirtyRoundBound
              (Nat.add_le_add_left gcdPositiveAbs seedPredecessor)
          have hUnfold : smithBezoutRepairPositionSweep (seedPredecessor + 1) matrix pivotIndex
              height width
              = smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
                  ++ smithBezoutRepairPositionSweep seedPredecessor
                      (matrix.applyOperations
                        (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                      pivotIndex height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold, applyOperationsAppend, roundWordApplied]
          exact smithBezoutRepairPositionSweepMasterLandsFindNoneAndCrossClear seedPredecessor
            (smithBezoutRepairRoundAtFound matrix pivotIndex height width foundRow foundCol)
            pivotIndex height width atFoundRect pRowLt pColLt maintained
            (Or.inr ⟨alphaPositive, measureFits⟩)

/-- **ARC-A INHABITED** — the recorded r48 fuel-adequacy residual
`SmithBezoutRepairPositionSweepReachesFindNoneStatement` holds: the fueled Bezout position sweep at
its ACTUAL seed reaches whole-block find-`none`.  Delivered by the seed-level theorem (which needs no
cross-clean at all — the recorded hypothesis is simply unused). -/
theorem smithBezoutRepairPositionSweepReachesFindNoneHolds :
    SmithBezoutRepairPositionSweepReachesFindNoneStatement :=
  fun matrix pivotIndex height width isRect pRowLt pColLt _crossClean =>
    (smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear matrix pivotIndex height width
      isRect pRowLt pColLt).1

end FX1Poly.ComputerAlgebra

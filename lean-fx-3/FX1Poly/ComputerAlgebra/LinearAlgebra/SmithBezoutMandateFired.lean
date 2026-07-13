import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutFuelAdequacy

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutMandateFired — THE #2261 MANDATE FIRED:
    `SmithReduceCompleteBezoutDriverStatement` is INHABITED (H2-SMITH r50)

## ★★★★★ MANDATE STATUS: FIRED — the ∀-correctness theorem of the Bezout Smith driver is PROVEN ★★★★★

`smithReduceCompleteBezoutDriverHolds : SmithReduceCompleteBezoutDriverStatement` — for EVERY
rectangular integer matrix, the Bezout-drop driver `smithReduceCompleteBezout` emits a certificate
reducing it to Smith normal form (off-diagonal vanishing + nonnegative diagonal + full divisibility
chain).  Zero axioms.  The 50-round arc closes through the r48 reduction
`smithReduceCompleteBezoutMandateReducesToInvariants` applied to a GENUINE inhabitant of the r49 gate
`SmithBezoutRepairInvariantsStatement` — no weakened variant anywhere.

## The ARC-C port that fires the gate (all consuming the ARC-A seed theorem of the sibling file)

  * **CONJUNCT-1 (window-diagonality)**: the settled-prefix frame (`SmithPrefixSettled`) advances
    `p -> p+1` across each Bezout position sweep — low-low cells are FROZEN
    (`smithBezoutRepairPositionSweepFreezesBelow`), the above-right / below-left zero bands survive
    every letter (`...PreservesRowBandZero` / `...PreservesColBandZero`, riding the shipped cascade
    band lemmas), and the fresh cross at `p` is CLEARED by ARC-A (`...SeedLandsFindNoneAndCrossClear`).
    The outer fold to `Nat.min` (`smithBezoutDivisibilityRepairSweepSettlesThroughPivots`) delivers
    `IsWindowDiagonal` at `0` (`repairWindowDiagHoldsForBezout`).
  * **CONJUNCT-2 (divisibility chain)**: the carried invariant
    `SmithBezoutSettledDiagonalsDivideAdvancedBlocks` — every settled diagonal `d_e` divides the whole
    `[e+1, ·)²` sub-block — advances across each position: old divisors survive (the position word is
    bounded below `p`, so `applyOperationsPreservesEntriesDivisibleWithin` transports the ideal, and
    the settled diagonals are frozen), and the fresh `d_p` enters via the r49 word-agnostic seed
    `smithBezoutFindNoneImpliesLandsDivisibleSubBlock` fed by ARC-A's landed find-`none` — exactly the
    CoqEAL/Isabelle "placed pivot divides the residual block" invariant, mechanized over the Bezout
    word.  The outer fold (`smithBezoutDivisibilityRepairSweepCarriesChain`) delivers
    `SmithChainPrefix` at `Nat.min` (`repairChainHoldsForBezout`).

The original min-abs mandate `SmithReduceCompleteInBlockDriverStatement` stays honestly UNINHABITED
(its seed route is REFUTED — `smithCascadeLandsDivisibleSubBlockIsRefuted`); the Bezout sibling is the
corrected driver, and ITS mandate is now a theorem.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  ADDITIVE only — the r18-r50 world is
byte-intact.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutMandateFired.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Freeze twins — the Bezout words freeze the low-low block (mirrors of the r48 boundedness) -/

/-- **The Bezout round word freezes below `lo`** — fold target and sign row at `pivotIndex ≥ lo`,
Bezout column target at `foundCol ≥ lo`, cascade by the shipped freeze. -/
theorem smithBezoutRepairRoundWordAtFoundFreezesBelow (lo : Nat) (work : IntMatrix)
    (pivotIndex height width foundRow foundCol : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (pivotGe : lo ≤ pivotIndex) (foundColGe : lo ≤ foundCol) :
    allOpsFreezeBelow lo (smithBezoutRepairRoundWordAtFound work pivotIndex height width foundRow foundCol)
      = true := by
  refine allOpsFreezeBelowAppend lo _ _
    (allOpsFreezeBelowAppend lo _ _
      (allOpsFreezeBelowAppend lo _ _ ?_ ?_) ?_) ?_
  · exact boolAndBothTrue (opFreezesBelowAddRow lo foundRow pivotIndex 1 pivotGe) rfl
  · exact smithSignNormalizeOpsFreezesBelow _ lo pivotIndex pivotGe
  · exact boolAndBothTrue (opFreezesBelowAddColumn lo pivotIndex foundCol _ foundColGe) rfl
  · exact smithCascadeSweepFreezesBelow lo _ _ pivotIndex height width pRowLt pColLt pivotGe

/-- **The Bezout position sweep freezes below `lo`** — structural on the fuel; the `none` branch is
the shipped cascade freeze, the `some` branch composes the round-word freeze with the recursion. -/
theorem smithBezoutRepairPositionSweepFreezesBelow (lo : Nat) :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsFreezeBelow lo (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      show allOpsFreezeBelow lo
          (match smithFindNonDividingInBlock matrix pivotIndex height width with
           | none =>
               smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                 height width
           | some (foundRow, foundCol) =>
               smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
                 ++ smithBezoutRepairPositionSweep fuel
                     (matrix.applyOperations
                       (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                     pivotIndex height width) = true
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          exact smithCascadeSweepFreezesBelow lo _ matrix pivotIndex height width
            pivotRowInRange pivotColInRange pivotGe
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          obtain ⟨_, _, pivotLeFoundCol, _, _⟩ :=
            smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
              pivotRowInRange pivotColInRange hFind
          exact allOpsFreezeBelowAppend lo _ _
            (smithBezoutRepairRoundWordAtFoundFreezesBelow lo matrix pivotIndex height width foundRow
              foundCol pivotRowInRange pivotColInRange pivotGe (Nat.le_trans pivotGe pivotLeFoundCol))
            (smithBezoutRepairPositionSweepFreezesBelow lo fuel _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe)

/-! ## Band twins — the Bezout words preserve the above-right and below-left zero bands -/

/-- **The Bezout round word preserves an above-right ROW band** — a zero row `lowRow < pivotIndex`
over columns `≥ pivotIndex` survives the fold (off its target row), the sign (off the pivot row), the
Bezout column op (its source column is a band cell), and the trailing cascade (shipped band lemma). -/
theorem smithBezoutRepairRoundWordAtFoundPreservesRowBandZero
    (matrix : IntMatrix) (pivotIndex height width foundRow foundCol lowRow : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (lowRowLtPivot : lowRow < pivotIndex)
    (pivotLeFoundCol : pivotIndex ≤ foundCol) (foundColLt : foundCol < width)
    (bandZero : ∀ col, pivotIndex ≤ col → col < width → matrix.entryAt lowRow col = 0) :
    ∀ col, pivotIndex ≤ col → col < width →
      (matrix.applyOperations
          (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol)).entryAt
          lowRow col = 0 := by
  have lowRowNePivot : lowRow ≠ pivotIndex := Nat.ne_of_lt lowRowLtPivot
  have lowRowLtHeight : lowRow < height := Nat.lt_trans lowRowLtPivot pRowLt
  let afterFold := matrix.addRowMultiple foundRow pivotIndex 1
  let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
  let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
    (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
        (afterSign.entryAt pivotIndex foundCol)))
  have afterFoldRect : afterFold.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
      matrix isRect
  have afterSignRect : afterSign.IsRectangular height width :=
    applyOperationsPreservesRectangular (smithSignNormalizeOps afterFold pivotIndex) afterFold afterFoldRect
  have afterClearRect : afterClear.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple pivotIndex foundCol
        (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
            (afterSign.entryAt pivotIndex foundCol))))]
      afterSign afterSignRect
  have signBand : ∀ col, pivotIndex ≤ col → col < width → afterSign.entryAt lowRow col = 0 :=
    fun col pivotLeCol colLtWidth =>
      ((signNormalizeOpsPreserveEntryOffPivot afterFold pivotIndex lowRow col lowRowNePivot).trans
        (addRowMultiplePreservesEntryOffTargetRow matrix foundRow pivotIndex 1 lowRow col
          lowRowNePivot)).trans (bandZero col pivotLeCol colLtWidth)
  have clearBand : ∀ col, pivotIndex ≤ col → col < width → afterClear.entryAt lowRow col = 0 := by
    intro col pivotLeCol colLtWidth
    cases Nat.decEq pivotIndex foundCol with
    | isTrue pivotEqFound =>
        show (afterSign.addColumnMultiple pivotIndex foundCol _).entryAt lowRow col = 0
        rw [← pivotEqFound, addColumnMultipleSelfIsIdentity]
        exact signBand col pivotLeCol colLtWidth
    | isFalse pivotNeFound =>
        cases Nat.decEq col foundCol with
        | isTrue colEqFound =>
            rw [colEqFound]
            rw [addColumnMultipleEntryOnTargetCol afterSign afterSignRect pivotIndex foundCol lowRow
              (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex)
                  (afterSign.entryAt pivotIndex foundCol)))
              pivotNeFound lowRowLtHeight pColLt foundColLt,
              signBand foundCol pivotLeFoundCol foundColLt,
              signBand pivotIndex (Nat.le_refl pivotIndex) pColLt, intMulZero, intAddZero]
        | isFalse colNeFound =>
            rw [addColumnMultipleEntryOffTargetCol afterSign afterSignRect pivotIndex foundCol lowRow
              col _ colNeFound lowRowLtHeight]
            exact signBand col pivotLeCol colLtWidth
  intro col pivotLeCol colLtWidth
  rw [smithBezoutRepairRoundWordAtFoundApplied]
  show ((afterClear.applyOperations
      (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex
        height width)).entryAt lowRow col) = 0
  exact smithCascadeSweepPreservesAboveRightRowBandZero
    (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex height width lowRow
    afterClearRect pRowLt pColLt lowRowLtPivot clearBand col pivotLeCol colLtWidth

/-- **The Bezout round word preserves a below-left COLUMN band** — a zero column
`lowCol < pivotIndex` over rows `≥ pivotIndex` survives the fold (its two read rows are band cells),
the sign (band cell magnitude), the Bezout column op (off its target column), and the trailing
cascade (shipped band lemma). -/
theorem smithBezoutRepairRoundWordAtFoundPreservesColBandZero
    (matrix : IntMatrix) (pivotIndex height width foundRow foundCol lowCol : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (lowColLtPivot : lowCol < pivotIndex)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (foundRowLt : foundRow < height)
    (pivotLeFoundCol : pivotIndex ≤ foundCol)
    (bandZero : ∀ row, pivotIndex ≤ row → row < height → matrix.entryAt row lowCol = 0) :
    ∀ row, pivotIndex ≤ row → row < height →
      (matrix.applyOperations
          (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol)).entryAt
          row lowCol = 0 := by
  have lowColLtWidth : lowCol < width := Nat.lt_trans lowColLtPivot pColLt
  have lowColNeFound : lowCol ≠ foundCol :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le lowColLtPivot pivotLeFoundCol)
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
  have foldBand : ∀ row, pivotIndex ≤ row → row < height → afterFold.entryAt row lowCol = 0 := by
    intro row pivotLeRow rowLtHeight
    cases Nat.decEq foundRow pivotIndex with
    | isTrue foundEqPivot =>
        show (matrix.addRowMultiple foundRow pivotIndex 1).entryAt row lowCol = 0
        rw [foundEqPivot, addRowMultipleSelfIsIdentity]
        exact bandZero row pivotLeRow rowLtHeight
    | isFalse foundNePivot =>
        cases Nat.decEq row pivotIndex with
        | isTrue rowEqPivot =>
            show (matrix.addRowMultiple foundRow pivotIndex 1).entryAt row lowCol = 0
            rw [rowEqPivot,
              addRowMultipleEntryOnTargetRow matrix isRect foundRow pivotIndex lowCol 1
                foundNePivot foundRowLt pRowLt lowColLtWidth,
              bandZero pivotIndex (Nat.le_refl pivotIndex) pRowLt,
              bandZero foundRow pivotLeFoundRow foundRowLt, intMulZero, intAddZero]
        | isFalse rowNePivot =>
            show (matrix.addRowMultiple foundRow pivotIndex 1).entryAt row lowCol = 0
            rw [addRowMultiplePreservesEntryOffTargetRow matrix foundRow pivotIndex 1 row lowCol
              rowNePivot]
            exact bandZero row pivotLeRow rowLtHeight
  have signBand : ∀ row, pivotIndex ≤ row → row < height → afterSign.entryAt row lowCol = 0 := by
    intro row pivotLeRow rowLtHeight
    cases Nat.decEq row pivotIndex with
    | isTrue rowEqPivot =>
        have magnitudePreserved := smithSignNormalizeOpsPreservesRowMagnitude afterFold pivotIndex
          lowCol afterFoldRows
        rw [foldBand pivotIndex (Nat.le_refl pivotIndex) pRowLt] at magnitudePreserved
        rw [rowEqPivot]
        exact intOfNatAbsZero _ magnitudePreserved
    | isFalse rowNePivot =>
        rw [signNormalizeOpsPreserveEntryOffPivot afterFold pivotIndex row lowCol rowNePivot]
        exact foldBand row pivotLeRow rowLtHeight
  have clearBand : ∀ row, pivotIndex ≤ row → row < height → afterClear.entryAt row lowCol = 0 := by
    intro row pivotLeRow rowLtHeight
    rw [addColumnMultipleEntryOffTargetCol afterSign afterSignRect pivotIndex foundCol row lowCol _
      lowColNeFound rowLtHeight]
    exact signBand row pivotLeRow rowLtHeight
  intro row pivotLeRow rowLtHeight
  rw [smithBezoutRepairRoundWordAtFoundApplied]
  show ((afterClear.applyOperations
      (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex
        height width)).entryAt row lowCol) = 0
  exact smithCascadeSweepPreservesBelowLeftColBandZero
    (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex height width lowCol
    afterClearRect pRowLt pColLt lowColLtPivot clearBand row pivotLeRow rowLtHeight

/-- **The Bezout position sweep preserves an above-right ROW band** — structural on the fuel over
the round-word band and the shipped cascade band. -/
theorem smithBezoutRepairPositionSweepPreservesRowBandZero :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width lowRow : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      lowRow < pivotIndex →
      (∀ col, pivotIndex ≤ col → col < width → matrix.entryAt lowRow col = 0) →
      ∀ col, pivotIndex ≤ col → col < width →
        (matrix.applyOperations
            (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width)).entryAt lowRow col
          = 0
  | 0, _, _, _, _, _, _, _, _, _, bandZero => bandZero
  | fuel + 1, matrix, pivotIndex, height, width, lowRow, isRect, pRowLt, pColLt, lowRowLtPivot,
      bandZero => by
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold]
          exact smithCascadeSweepPreservesAboveRightRowBandZero
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width lowRow
            isRect pRowLt pColLt lowRowLtPivot bandZero
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, _⟩ :=
            smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
              pRowLt pColLt hFind
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
                  ++ smithBezoutRepairPositionSweep fuel
                      (matrix.applyOperations
                        (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                      pivotIndex height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold, applyOperationsAppend]
          exact smithBezoutRepairPositionSweepPreservesRowBandZero fuel
            (matrix.applyOperations
              (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
            pivotIndex height width lowRow
            (applyOperationsPreservesRectangular _ matrix isRect) pRowLt pColLt lowRowLtPivot
            (smithBezoutRepairRoundWordAtFoundPreservesRowBandZero matrix pivotIndex height width
              foundRow foundCol lowRow isRect pRowLt pColLt lowRowLtPivot pivotLeFoundCol foundColLt
              bandZero)

/-- **The Bezout position sweep preserves a below-left COLUMN band** — the transpose mirror. -/
theorem smithBezoutRepairPositionSweepPreservesColBandZero :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width lowCol : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      lowCol < pivotIndex →
      (∀ row, pivotIndex ≤ row → row < height → matrix.entryAt row lowCol = 0) →
      ∀ row, pivotIndex ≤ row → row < height →
        (matrix.applyOperations
            (smithBezoutRepairPositionSweep fuel matrix pivotIndex height width)).entryAt row lowCol
          = 0
  | 0, _, _, _, _, _, _, _, _, _, bandZero => bandZero
  | fuel + 1, matrix, pivotIndex, height, width, lowCol, isRect, pRowLt, pColLt, lowColLtPivot,
      bandZero => by
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold]
          exact smithCascadeSweepPreservesBelowLeftColBandZero
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width lowCol
            isRect pRowLt pColLt lowColLtPivot bandZero
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, _⟩ :=
            smithFindNonDividingInBlockSomeProperties matrix pivotIndex height width foundRow foundCol
              pRowLt pColLt hFind
          have hUnfold : smithBezoutRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
                  ++ smithBezoutRepairPositionSweep fuel
                      (matrix.applyOperations
                        (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
                      pivotIndex height width := by
            rw [smithBezoutRepairPositionSweepSucc, hFind]
          rw [hUnfold, applyOperationsAppend]
          exact smithBezoutRepairPositionSweepPreservesColBandZero fuel
            (matrix.applyOperations
              (smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol))
            pivotIndex height width lowCol
            (applyOperationsPreservesRectangular _ matrix isRect) pRowLt pColLt lowColLtPivot
            (smithBezoutRepairRoundWordAtFoundPreservesColBandZero matrix pivotIndex height width
              foundRow foundCol lowCol isRect pRowLt pColLt lowColLtPivot pivotLeFoundRow foundRowLt
              pivotLeFoundCol bandZero)

/-! ## The settled-frame step — one Bezout position sweep advances the frame `p -> p+1` -/

/-- **The Bezout position sweep at its seed advances the settled frame** — low-low cells freeze, the
two bands survive, and the fresh cross at `pivotIndex` is CLEARED by ARC-A.  The Bezout-word
inhabitant of the r18 step-settles shape. -/
theorem smithBezoutRepairPositionSweepSeedStepSettles
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (isSettled : SmithPrefixSettled matrix pivotIndex height width) :
    SmithPrefixSettled
      (matrix.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))
      (pivotIndex + 1) height width := by
  intro rowIndex colIndex rowLtHeight colLtWidth rowNeCol frameHolds
  cases Nat.lt_or_ge rowIndex pivotIndex with
  | inl rowLtPivot =>
      cases Nat.lt_or_ge colIndex pivotIndex with
      | inl colLtPivot =>
          exact (applyOperationsFreezeEntryBelow _ matrix rowIndex colIndex
            (smithBezoutRepairPositionSweepFreezesBelow pivotIndex _ matrix pivotIndex height width
              pRowLt pColLt (Nat.le_refl pivotIndex)) rowLtPivot colLtPivot).trans
            (isSettled rowIndex colIndex rowLtHeight colLtWidth rowNeCol (Or.inl rowLtPivot))
      | inr colGePivot =>
          exact smithBezoutRepairPositionSweepPreservesRowBandZero
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width rowIndex
            isRect pRowLt pColLt rowLtPivot
            (fun bandCol pivotLeBandCol bandColLtWidth =>
              isSettled rowIndex bandCol rowLtHeight bandColLtWidth
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLtPivot pivotLeBandCol)) (Or.inl rowLtPivot))
            colIndex colGePivot colLtWidth
  | inr rowGePivot =>
      cases Nat.lt_or_ge colIndex pivotIndex with
      | inl colLtPivot =>
          exact smithBezoutRepairPositionSweepPreservesColBandZero
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width colIndex
            isRect pRowLt pColLt colLtPivot
            (fun bandRow pivotLeBandRow bandRowLtHeight =>
              isSettled bandRow colIndex bandRowLtHeight colLtWidth
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLtPivot pivotLeBandRow)).symm (Or.inr colLtPivot))
            rowIndex rowGePivot rowLtHeight
      | inr colGePivot =>
          have crossClear :=
            (smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear matrix pivotIndex height
              width isRect pRowLt pColLt).2
          have crossPointwise := smithCrossIsClearPointwise
            (matrix.applyOperations
              (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width))
            pivotIndex height width pRowLt pColLt crossClear
          cases frameHolds with
          | inl rowLtSucc =>
              have rowEqPivot : rowIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ rowLtSucc) rowGePivot
              have pivotLtCol : pivotIndex < colIndex :=
                Nat.lt_of_le_of_ne colGePivot
                  (fun pivotEqCol => rowNeCol (rowEqPivot.trans pivotEqCol))
              rw [rowEqPivot]
              exact crossPointwise.1 colIndex pivotLtCol colLtWidth
          | inr colLtSucc =>
              have colEqPivot : colIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ colLtSucc) colGePivot
              have pivotLtRow : pivotIndex < rowIndex :=
                Nat.lt_of_le_of_ne rowGePivot
                  (fun pivotEqRow => rowNeCol (pivotEqRow.symm.trans colEqPivot.symm))
              rw [colEqPivot]
              exact crossPointwise.2 rowIndex pivotLtRow rowLtHeight

/-! ## The outer folds — settling and chain-carrying across pivots -/

/-- **The outer Bezout sweep's succ-unfold** — the definitional equation with the `let`s inlined. -/
theorem smithBezoutDivisibilityRepairSweepSucc (outerFuel : Nat) (matrix : IntMatrix)
    (pivotIndex height width : Nat) :
    smithBezoutDivisibilityRepairSweep (outerFuel + 1) matrix pivotIndex height width
      = (if pivotIndex + 1 ≤ Nat.min height width then
          smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix
              pivotIndex height width
            ++ smithBezoutDivisibilityRepairSweep outerFuel
                (matrix.applyOperations
                  (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width))
                (pivotIndex + 1) height width
         else []) :=
  rfl

/-- **The Bezout repair sweep advances the settled frame to the capped `Nat.min`** — structural on
the outer fuel; the guard-true step chains the step-settles with the IH on the advanced pivot, the
base / guard-false branches drop to the capped frame by monotonicity. -/
theorem smithBezoutDivisibilityRepairSweepSettlesThroughPivots :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      SmithPrefixSettled matrix pivotIndex height width →
      SmithPrefixSettled
        (matrix.applyOperations
          (smithBezoutDivisibilityRepairSweep outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) height width := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ isSettled
      exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect isSettled
      rw [smithBezoutDivisibilityRepairSweepSucc]
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := natLeTrans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans guardTrue (natMinLeRight height width)
        have afterPositionSettled :
            SmithPrefixSettled
              (matrix.applyOperations
                (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                  matrix pivotIndex height width))
              (pivotIndex + 1) height width :=
          smithBezoutRepairPositionSweepSeedStepSettles matrix pivotIndex height width isRect
            pivotRowInRange pivotColInRange isSettled
        have afterPositionRect :
            (matrix.applyOperations
              (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations
            (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          (pivotIndex + 1) height width afterPositionRect afterPositionSettled
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

/-- **CONJUNCT-1 FIRED** — the Bezout repair output is window-diagonal at `0`, for every rectangular
input: instantiate the settling fold at the driver start (vacuous base frame), collapse the cap, and
read off with `smithPrefixSettledAtMinIsWindowDiagonal`. -/
theorem repairWindowDiagHoldsForBezout :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      IsWindowDiagonal
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        0 height width := by
  intro matrix height width isRect
  have afterDiagRect :
      (matrix.applyOperations (smithReduceTotal matrix height width).operations).IsRectangular
        height width :=
    applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect
  have settledResult := smithBezoutDivisibilityRepairSweepSettlesThroughPivots (Nat.min height width)
    (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width
    afterDiagRect
    (smithPrefixSettledZero (matrix.applyOperations (smithReduceTotal matrix height width).operations)
      height width)
  rw [Nat.zero_add, natMinSelf] at settledResult
  intro rowIndex colIndex _zeroLeRow rowLtHeight _zeroLeCol colLtWidth rowNeCol
  exact smithPrefixSettledAtMinIsWindowDiagonal _ height width settledResult rowIndex colIndex
    rowLtHeight colLtWidth rowNeCol

/-! ## The carried chain invariant — every settled diagonal divides its advanced sub-block -/

/-- **The carried chain invariant** — every settled diagonal `d_e` (`e < pivotIndex`) divides EVERY
entry of the `[e+1, ·)²` sub-block (later settled diagonals AND the live block).  The literature's
"placed pivot divides the residual block" invariant, threaded across pivots. -/
def SmithBezoutSettledDiagonalsDivideAdvancedBlocks (matrix : IntMatrix) (pivotIndex : Nat) : Prop :=
  ∀ earlierIndex, earlierIndex < pivotIndex →
    MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt earlierIndex) (earlierIndex + 1) matrix

/-- **The Bezout repair sweep carries the chain invariant to the capped `Nat.min`** — structural on
the outer fuel.  Old divisors transport through the bounded-below position word
(`applyOperationsPreservesEntriesDivisibleWithin`) with their diagonals FROZEN
(`applyOperationsFreezeEntryBelow`); the fresh position enters via the r49 word-agnostic seed
`smithBezoutFindNoneImpliesLandsDivisibleSubBlock` fed by ARC-A's landed find-`none`. -/
theorem smithBezoutDivisibilityRepairSweepCarriesChain :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      SmithBezoutSettledDiagonalsDivideAdvancedBlocks matrix pivotIndex →
      SmithBezoutSettledDiagonalsDivideAdvancedBlocks
        (matrix.applyOperations
          (smithBezoutDivisibilityRepairSweep outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ carried
      exact fun earlierIndex earlierLt =>
        carried earlierIndex
          (Nat.lt_of_lt_of_le earlierLt (natMinLeRight (Nat.min height width) (pivotIndex + 0)))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect carried
      rw [smithBezoutDivisibilityRepairSweepSucc]
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := natLeTrans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans guardTrue (natMinLeRight height width)
        have positionWordBounded :
            allOpsBoundedBelow pivotIndex
              (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width) = true :=
          smithBezoutRepairPositionSweepBoundedBelow pivotIndex
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
            pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex)
        have positionWordFrozen :
            allOpsFreezeBelow pivotIndex
              (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width) = true :=
          smithBezoutRepairPositionSweepFreezesBelow pivotIndex
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
            pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex)
        have afterPositionRect :
            (matrix.applyOperations
              (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have advancedCarried :
            SmithBezoutSettledDiagonalsDivideAdvancedBlocks
              (matrix.applyOperations
                (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                  matrix pivotIndex height width))
              (pivotIndex + 1) := by
          intro earlierIndex earlierLtSucc
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ earlierLtSucc) with
          | inl earlierEqPivot =>
              rw [earlierEqPivot]
              exact smithBezoutFindNoneImpliesLandsDivisibleSubBlock matrix pivotIndex height width
                isRect
                (smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear matrix pivotIndex
                  height width isRect pivotRowInRange pivotColInRange).1
          | inr earlierLtPivot =>
              have frozenDiagonal :
                  (matrix.applyOperations
                      (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                        matrix pivotIndex height width)).diagonalEntryAt earlierIndex
                    = matrix.diagonalEntryAt earlierIndex :=
                applyOperationsFreezeEntryBelow _ matrix earlierIndex earlierIndex
                  positionWordFrozen earlierLtPivot earlierLtPivot
              have transported :
                  MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt earlierIndex)
                    (earlierIndex + 1)
                    (matrix.applyOperations
                      (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
                        matrix pivotIndex height width)) :=
                applyOperationsPreservesEntriesDivisibleWithin _ matrix
                  (allOpsBoundedBelowMonotone (earlierIndex + 1) pivotIndex earlierLtPivot _
                    positionWordBounded)
                  (carried earlierIndex earlierLtPivot)
              rw [frozenDiagonal]
              exact transported
        have ihResult := ih
          (matrix.applyOperations
            (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          (pivotIndex + 1) height width afterPositionRect advancedCarried
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact fun earlierIndex earlierLt =>
          carried earlierIndex
            (Nat.lt_of_lt_of_le earlierLt
              (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1)))
                minLePivot))

/-- **CONJUNCT-2 FIRED** — the Bezout repair output carries the full prefix divisibility chain, for
every rectangular input: instantiate the chain fold at the driver start (vacuous base), collapse the
cap, and read the chain off the carried invariant (`d_e ∣ d_l` because `(l, l)` is a cell of the
`[e+1, ·)²` block). -/
theorem repairChainHoldsForBezout :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithBezoutDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width := by
  intro matrix height width isRect
  have afterDiagRect :
      (matrix.applyOperations (smithReduceTotal matrix height width).operations).IsRectangular
        height width :=
    applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect
  have chainResult := smithBezoutDivisibilityRepairSweepCarriesChain (Nat.min height width)
    (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width
    afterDiagRect
    (fun earlierIndex earlierLt => absurd earlierLt (Nat.not_lt_zero earlierIndex))
  rw [Nat.zero_add, natMinSelf] at chainResult
  intro earlierIndex earlierLt laterIndex earlierLeLater _laterLt
  cases Nat.eq_or_lt_of_le earlierLeLater with
  | inl earlierEqLater =>
      rw [← earlierEqLater]
      exact dividesExactlySelf _
  | inr earlierLtLater =>
      exact matrixEntriesDivisibleByWithinAt (chainResult earlierIndex earlierLt)
        laterIndex laterIndex earlierLtLater earlierLtLater

/-! ## ★★★★★ THE GATE + THE MANDATE ★★★★★ -/

/-- **THE r49 GATE INHABITED** — both Phase-B invariants of the Bezout repair output hold for every
rectangular input.  The two conjuncts are `repairWindowDiagHoldsForBezout` and
`repairChainHoldsForBezout` — no hypothesis, no weakened variant. -/
theorem smithBezoutRepairInvariantsHold : SmithBezoutRepairInvariantsStatement :=
  ⟨repairWindowDiagHoldsForBezout, repairChainHoldsForBezout⟩

/-- **★★★★★ THE #2261 MANDATE, FIRED ★★★★★** — `SmithReduceCompleteBezoutDriverStatement`: for EVERY
rectangular integer matrix, the Bezout-drop driver `smithReduceCompleteBezout` emits a certificate
reducing it to Smith normal form.  The r48 reduction applied to the genuine gate inhabitant. -/
theorem smithReduceCompleteBezoutDriverHolds : SmithReduceCompleteBezoutDriverStatement :=
  smithReduceCompleteBezoutMandateReducesToInvariants smithBezoutRepairInvariantsHold

-- The mandate's TYPE, for the record: binders exactly `matrix / height / width / IsRectangular`.
#check (smithReduceCompleteBezoutDriverHolds : SmithReduceCompleteBezoutDriverStatement)
#check (SmithReduceCompleteBezoutDriverStatement : Prop)

/-! ## The driver census — `#eval` SNF pins on concrete matrices (modest entries)

Each pin applies the FULL driver certificate `smithReduceCompleteBezout` and prints the reduced
rows: window-diagonal, nonnegative, chained. -/

/-- Census probe: the classical non-chained diagonal `diag(6, 10, 15)` — gcd cascade to
`diag(1, 30, 30)`. -/
def mandateProbeDiagonal : IntMatrix := IntMatrix.mk [[6, 0, 0], [0, 10, 0], [0, 0, 15]]

/-- Census probe: the coprime pair `diag(2, 3)` — chains to `diag(1, 6)`. -/
def mandateProbeCoprime : IntMatrix := IntMatrix.mk [[2, 0], [0, 3]]

/-- Census probe: a dense two-by-two with negative work `[[2, 3], [4, 5]]`. -/
def mandateProbeDense : IntMatrix := IntMatrix.mk [[2, 3], [4, 5]]

/-- Census probe: the r46 zero-pivot refuter shape `[[0, 0], [0, 4]]`. -/
def mandateProbeZeroPivot : IntMatrix := IntMatrix.mk [[0, 0], [0, 4]]

/-- Census probe: the r44 operationally-landed killer `[[6, 0, 0], [0, 0, 10], [0, 0, 0]]`
(rank-deficient, the min-abs seed refuter). -/
def mandateProbeKiller : IntMatrix := IntMatrix.mk [[6, 0, 0], [0, 0, 10], [0, 0, 0]]

/-- Census probe: a wide rectangle `[[4, 6, 8]]`. -/
def mandateProbeWide : IntMatrix := IntMatrix.mk [[4, 6, 8]]

/-- Census probe: a tall rectangle `[[4], [6]]`. -/
def mandateProbeTall : IntMatrix := IntMatrix.mk [[4], [6]]

/-- Census probe: negatives and a dirty mix `[[-4, 6], [8, 10]]`. -/
def mandateProbeNegative : IntMatrix := IntMatrix.mk [[-4, 6], [8, 10]]

#eval (mandateProbeDiagonal.applyOperations
  (smithReduceCompleteBezout mandateProbeDiagonal 3 3).operations).rows
#eval (mandateProbeCoprime.applyOperations
  (smithReduceCompleteBezout mandateProbeCoprime 2 2).operations).rows
#eval (mandateProbeDense.applyOperations
  (smithReduceCompleteBezout mandateProbeDense 2 2).operations).rows
#eval (mandateProbeZeroPivot.applyOperations
  (smithReduceCompleteBezout mandateProbeZeroPivot 2 2).operations).rows
#eval (mandateProbeKiller.applyOperations
  (smithReduceCompleteBezout mandateProbeKiller 3 3).operations).rows
#eval (mandateProbeWide.applyOperations
  (smithReduceCompleteBezout mandateProbeWide 1 3).operations).rows
#eval (mandateProbeTall.applyOperations
  (smithReduceCompleteBezout mandateProbeTall 2 1).operations).rows
#eval (mandateProbeNegative.applyOperations
  (smithReduceCompleteBezout mandateProbeNegative 2 2).operations).rows

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedDivisibility

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithWindowedChainReduction — the seed ⟹ chain reduction
    as a Lean theorem (H2-SMITH r20, #2261)

The r19 wall named EXACTLY ONE residual, `SmithCascadeLandsDivisibleSubBlock` (the per-pivot ESTABLISH
seed), and asserted — in prose only — that seed ⟹ `repairChainHolds`.  The r19 verifier refuted the
prose.  This module makes that reduction a Lean `theorem`:

  * NODE A (the cross-pivot carrier).  `chainWindowedThroughPivots` — GIVEN the seed, the windowed
    diagonal chain `MatrixDiagonalChainWindowed` propagates through the whole clearing repair sweep.
    The load-bearing new obligation r19's prose glossed is the **low-low freeze**: after pivot
    `earlier` settles, the later sub-sweep at `[earlier+1, ·)` leaves `entryAt earlier earlier` (the
    windowed divisor) invariant.  The shipped `allOpsBoundedBelow` cannot supply this (its negate arms
    are unconditionally `true`), so this module ships a PARALLEL confinement `opFreezesBelow` /
    `allOpsFreezeBelow` (guarded negate arms), the entry-level freeze it certifies, and a structural
    re-walk of the sweep proving every emitted word freezes the low-low block.

  * NODE B (the reduction theorem).  `repairChainHoldsOfSeed` — the seed yields the verbatim
    `repairChainHolds` Prop that `smithReduceCompleteDriverOfChain` consumes; and
    `smithReduceCompleteDriverOfSubBlockSeed` collapses `SmithReduceCompleteDriverStatement` onto the
    seed ALONE, as a pure structural assembly term (no kernel evaluation — the defeq ceiling is
    untouched).

Raw Lean 4 + `Init`, STRUCTURAL only (fuel `Nat`).  ASCII identifiers; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowedChainReduction.lean`.  Additive: the r19
world (the seed, `smithReduceCompleteDriverOfChain`, the refuted `smithReduceFull`, the certificate
API) stays byte-intact. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Generic list-slot freeze lemmas — reading at an index OTHER than the write position is invariant -/

/-- **`listReplaceAt` leaves an off-position slot invariant** — reading at any `index ≠ position`
after a replace returns the original slot.  Structural on `(entries, position, index)`. -/
theorem listReplaceAtGetOther {Entry : Type} (defaultEntry newEntry : Entry) :
    ∀ (entries : List Entry) (position index : Nat), index ≠ position →
      listGetWithDefault defaultEntry (listReplaceAt entries position newEntry) index
        = listGetWithDefault defaultEntry entries index
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, 0, indexNe => absurd rfl indexNe
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: remainingEntries, position + 1, index + 1, indexNe =>
      listReplaceAtGetOther defaultEntry newEntry remainingEntries position index
        (fun innerEq => indexNe (congrArg (· + 1) innerEq))

/-- **`listModifyAt` leaves an off-position slot invariant** — reading at any `index ≠ position`
after a modify returns the original slot.  Structural on `(entries, position, index)`. -/
theorem listModifyAtGetOther {Entry : Type} (defaultEntry : Entry) (transform : Entry → Entry) :
    ∀ (entries : List Entry) (position index : Nat), index ≠ position →
      listGetWithDefault defaultEntry (listModifyAt transform entries position) index
        = listGetWithDefault defaultEntry entries index
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, 0, indexNe => absurd rfl indexNe
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: remainingEntries, position + 1, index + 1, indexNe =>
      listModifyAtGetOther defaultEntry transform remainingEntries position index
        (fun innerEq => indexNe (congrArg (· + 1) innerEq))

/-! ## The operation-freezes-below decidable check (guarded negate arms; the freeze-capable sibling of
`opIsBoundedBelow`) -/

/-- **The operation leaves the `[0, lo) × [0, lo)` block frozen** — swap needs both indices at `≥ lo`;
transvection needs only its TARGET at `≥ lo` (the source is read, never written); NEGATION now needs
its index at `≥ lo` (the shipped `opIsBoundedBelow` returns `true` unconditionally on negate, so it is
NOT freeze-capable — this is the whole reason for the parallel predicate).  Fully enumerated arms so
the sweep confinement is propext-clean. -/
def opFreezesBelow (lo : Nat) : ElementaryOperation → Bool
  | .rowOperation (.swapRows firstIndex secondIndex) =>
      decide (lo ≤ firstIndex) && decide (lo ≤ secondIndex)
  | .rowOperation (.negateRow rowIndex) => decide (lo ≤ rowIndex)
  | .rowOperation (.addRowMultiple _ targetIndex _) => decide (lo ≤ targetIndex)
  | .columnOperation (.swapColumns firstIndex secondIndex) =>
      decide (lo ≤ firstIndex) && decide (lo ≤ secondIndex)
  | .columnOperation (.negateColumn colIndex) => decide (lo ≤ colIndex)
  | .columnOperation (.addColumnMultiple _ targetIndex _) => decide (lo ≤ targetIndex)

/-- Every operation in the certificate word freezes the `[0, lo) × [0, lo)` block. -/
def allOpsFreezeBelow (lo : Nat) : List ElementaryOperation → Bool
  | [] => true
  | operation :: remaining => opFreezesBelow lo operation && allOpsFreezeBelow lo remaining

/-! ## Row-level and column-level frozen-slot carriers -/

/-- Reading a non-swapped row after `swapRows` (both indices `≠ rowIndex`) is invariant. -/
theorem swapRowsRowsGetOther (matrix : IntMatrix) (firstIndex secondIndex rowIndex : Nat)
    (rowNeFirst : rowIndex ≠ firstIndex) (rowNeSecond : rowIndex ≠ secondIndex) :
    listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows rowIndex
      = listGetWithDefault [] matrix.rows rowIndex := by
  unfold IntMatrix.swapRows
  split
  · split
    · exact (listReplaceAtGetOther [] (listGetWithDefault [] matrix.rows firstIndex)
        (listReplaceAt matrix.rows firstIndex (listGetWithDefault [] matrix.rows secondIndex))
        secondIndex rowIndex rowNeSecond).trans
        (listReplaceAtGetOther [] (listGetWithDefault [] matrix.rows secondIndex)
          matrix.rows firstIndex rowIndex rowNeFirst)
    · rfl
  · rfl

/-- Reading a non-negated row after `negateRow` (index `≠ rowIndex`) is invariant. -/
theorem negateRowRowsGetOther (matrix : IntMatrix) (targetRowIndex rowIndex : Nat)
    (rowNe : rowIndex ≠ targetRowIndex) :
    listGetWithDefault [] (matrix.negateRow targetRowIndex).rows rowIndex
      = listGetWithDefault [] matrix.rows rowIndex :=
  listModifyAtGetOther [] (fun row => row.map (fun entry => -entry)) matrix.rows targetRowIndex rowIndex rowNe

/-- Reading a non-target row after `addRowMultiple` (index `≠ targetIndex`) is invariant. -/
theorem addRowMultipleRowsGetOther (matrix : IntMatrix) (sourceIndex targetIndex rowIndex : Nat)
    (coefficient : Int) (rowNe : rowIndex ≠ targetIndex) :
    listGetWithDefault [] (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows rowIndex
      = listGetWithDefault [] matrix.rows rowIndex := by
  unfold IntMatrix.addRowMultiple
  split
  · rfl
  · split
    · split
      · exact listModifyAtGetOther []
          (fun targetRow => addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
          matrix.rows targetIndex rowIndex rowNe
      · rfl
    · rfl

/-- Reading an off-column slot after `swapEntriesWithinRow` (both indices `≠ colIndex`) is invariant. -/
theorem swapEntriesWithinRowGetOther (row : IntRow) (firstIndex secondIndex colIndex : Nat)
    (colNeFirst : colIndex ≠ firstIndex) (colNeSecond : colIndex ≠ secondIndex) :
    listGetWithDefault 0 (IntMatrix.swapEntriesWithinRow row firstIndex secondIndex) colIndex
      = listGetWithDefault 0 row colIndex := by
  unfold IntMatrix.swapEntriesWithinRow
  split
  · split
    · exact (listReplaceAtGetOther 0 (listGetWithDefault 0 row firstIndex)
        (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex))
        secondIndex colIndex colNeSecond).trans
        (listReplaceAtGetOther 0 (listGetWithDefault 0 row secondIndex)
          row firstIndex colIndex colNeFirst)
    · rfl
  · rfl

/-- Reading an off-target slot after `addScaledEntryWithinRow` (index `≠ targetIndex`) is invariant. -/
theorem addScaledEntryWithinRowGetOther (row : IntRow) (sourceIndex targetIndex colIndex : Nat)
    (coefficient : Int) (colNe : colIndex ≠ targetIndex) :
    listGetWithDefault 0 (IntMatrix.addScaledEntryWithinRow row sourceIndex targetIndex coefficient) colIndex
      = listGetWithDefault 0 row colIndex := by
  unfold IntMatrix.addScaledEntryWithinRow
  split
  · exact listModifyAtGetOther 0
      (fun targetEntry => targetEntry + coefficient * listGetWithDefault 0 row sourceIndex)
      row targetIndex colIndex colNe
  · rfl

/-- **A row-locally applied transform that fixes column `colIndex` fixes the entry `(·, colIndex)`** —
the `mapAllRows` carrier for column-op freezes: in-range rows read `transform (old row)` (fixed at
`colIndex` by hypothesis), past-end rows read the empty default on both sides. -/
theorem mapAllRowsFreezesColEntry (transform : IntRow → IntRow) (colIndex : Nat)
    (colPreserved : ∀ row, listGetWithDefault 0 (transform row) colIndex = listGetWithDefault 0 row colIndex)
    (rows : List IntRow) (rowIndex : Nat) :
    listGetWithDefault 0 (listGetWithDefault [] (mapAllRows transform rows) rowIndex) colIndex
      = listGetWithDefault 0 (listGetWithDefault [] rows rowIndex) colIndex := by
  by_cases hRange : rowIndex < rows.length
  · rw [listGetWithDefaultMapAllRows transform rows rowIndex hRange]
    exact colPreserved _
  · rw [listGetWithDefaultGe [] (mapAllRows transform rows) rowIndex
        (by rw [mapAllRowsPreservesLength]; exact Nat.not_lt.1 hRange),
      listGetWithDefaultGe [] rows rowIndex (Nat.not_lt.1 hRange)]

/-! ## The single-operation and word freeze -/

/-- Transport a rows-level slot equality to an entry equality (read one more column). -/
theorem entryAtOfRowsGet (leftMatrix rightMatrix : IntMatrix) (rowIndex colIndex : Nat)
    (rowsEq : listGetWithDefault [] leftMatrix.rows rowIndex = listGetWithDefault [] rightMatrix.rows rowIndex) :
    leftMatrix.entryAt rowIndex colIndex = rightMatrix.entryAt rowIndex colIndex :=
  congrArg (fun row => listGetWithDefault 0 row colIndex) rowsEq

/-- **A bounded-below row operation freezes a low-low entry** — its written row is at `≥ lo`, so a
cell at `rowIndex < lo` is untouched (any column). -/
theorem applyRowOperationFreezesEntryBelow {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryRowOperation)
    (opFrozen : opFreezesBelow lo (.rowOperation operation) = true)
    (rowIndex colIndex : Nat) (rowLt : rowIndex < lo) :
    (matrix.applyRowOperation operation).entryAt rowIndex colIndex = matrix.entryAt rowIndex colIndex := by
  cases operation with
  | swapRows firstIndex secondIndex =>
      have firstGe : lo ≤ firstIndex := of_decide_eq_true (boolConjTrueLeft opFrozen)
      have secondGe : lo ≤ secondIndex := of_decide_eq_true (boolConjTrueRight opFrozen)
      exact entryAtOfRowsGet (matrix.swapRows firstIndex secondIndex) matrix rowIndex colIndex
        (swapRowsRowsGetOther matrix firstIndex secondIndex rowIndex
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLt firstGe))
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLt secondGe)))
  | negateRow targetRowIndex =>
      have targetGe : lo ≤ targetRowIndex := of_decide_eq_true opFrozen
      exact entryAtOfRowsGet (matrix.negateRow targetRowIndex) matrix rowIndex colIndex
        (negateRowRowsGetOther matrix targetRowIndex rowIndex (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLt targetGe)))
  | addRowMultiple sourceIndex targetIndex coefficient =>
      have targetGe : lo ≤ targetIndex := of_decide_eq_true opFrozen
      exact entryAtOfRowsGet (matrix.addRowMultiple sourceIndex targetIndex coefficient) matrix rowIndex colIndex
        (addRowMultipleRowsGetOther matrix sourceIndex targetIndex rowIndex coefficient
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLt targetGe)))

/-- **A bounded-below column operation freezes a low-low entry** — its written column is at `≥ lo`, so a
cell at `colIndex < lo` is untouched (any row). -/
theorem applyColumnOperationFreezesEntryBelow {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryColumnOperation)
    (opFrozen : opFreezesBelow lo (.columnOperation operation) = true)
    (rowIndex colIndex : Nat) (colLt : colIndex < lo) :
    (matrix.applyColumnOperation operation).entryAt rowIndex colIndex = matrix.entryAt rowIndex colIndex := by
  cases operation with
  | swapColumns firstIndex secondIndex =>
      have firstGe : lo ≤ firstIndex := of_decide_eq_true (boolConjTrueLeft opFrozen)
      have secondGe : lo ≤ secondIndex := of_decide_eq_true (boolConjTrueRight opFrozen)
      exact mapAllRowsFreezesColEntry (fun row => IntMatrix.swapEntriesWithinRow row firstIndex secondIndex)
        colIndex
        (fun row => swapEntriesWithinRowGetOther row firstIndex secondIndex colIndex
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLt firstGe))
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLt secondGe)))
        matrix.rows rowIndex
  | negateColumn targetColIndex =>
      have targetGe : lo ≤ targetColIndex := of_decide_eq_true opFrozen
      exact mapAllRowsFreezesColEntry (fun row => listModifyAt (fun entry => -entry) row targetColIndex)
        colIndex
        (fun row => listModifyAtGetOther 0 (fun entry => -entry) row targetColIndex colIndex
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLt targetGe)))
        matrix.rows rowIndex
  | addColumnMultiple sourceIndex targetIndex coefficient =>
      have targetGe : lo ≤ targetIndex := of_decide_eq_true opFrozen
      show (matrix.addColumnMultiple sourceIndex targetIndex coefficient).entryAt rowIndex colIndex
        = matrix.entryAt rowIndex colIndex
      unfold IntMatrix.addColumnMultiple
      split
      · rfl
      · exact mapAllRowsFreezesColEntry
          (fun row => IntMatrix.addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          colIndex
          (fun row => addScaledEntryWithinRowGetOther row sourceIndex targetIndex colIndex coefficient
            (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLt targetGe)))
          matrix.rows rowIndex

/-- **A single freeze-below operation freezes a low-low entry** — row/column dispatch. -/
theorem applyOperationFreezesEntryBelow {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryOperation) (opFrozen : opFreezesBelow lo operation = true)
    (rowIndex colIndex : Nat) (rowLt : rowIndex < lo) (colLt : colIndex < lo) :
    (matrix.applyOperation operation).entryAt rowIndex colIndex = matrix.entryAt rowIndex colIndex :=
  match operation, opFrozen with
  | .rowOperation rowOp, opFrozen =>
      applyRowOperationFreezesEntryBelow matrix rowOp opFrozen rowIndex colIndex rowLt
  | .columnOperation colOp, opFrozen =>
      applyColumnOperationFreezesEntryBelow matrix colOp opFrozen rowIndex colIndex colLt

/-- **A whole freeze-below word freezes a low-low entry** — structural on the word (peeling
`allOpsFreezeBelow`). -/
theorem applyOperationsFreezeEntryBelow {lo : Nat} :
    ∀ (operations : List ElementaryOperation) (matrix : IntMatrix) (rowIndex colIndex : Nat),
      allOpsFreezeBelow lo operations = true → rowIndex < lo → colIndex < lo →
      (matrix.applyOperations operations).entryAt rowIndex colIndex = matrix.entryAt rowIndex colIndex
  | [], _, _, _, _, _, _ => rfl
  | operation :: remaining, matrix, rowIndex, colIndex, wordFrozen, rowLt, colLt =>
      (applyOperationsFreezeEntryBelow remaining (matrix.applyOperation operation) rowIndex colIndex
        (boolConjTrueRight wordFrozen) rowLt colLt).trans
        (applyOperationFreezesEntryBelow matrix operation (boolConjTrueLeft wordFrozen)
          rowIndex colIndex rowLt colLt)

/-! ## The sweep re-walk — every emitted repair word freezes the low-low block

Verbatim structural mirror of the `…OpsBoundedBelow` confinement chain (SmithWindowedDivisibility
§confinement), over `allOpsFreezeBelow` in place of `allOpsBoundedBelow`.  The ONLY divergence is the
sign lemma, which now carries `lo ≤ pivotIndex` (the shipped bounded-below sign lemma did not need it,
because `opIsBoundedBelow` returns `true` on negate unconditionally — the exact gap the freeze
predicate closes).  Transvection freezes need only the TARGET at `≥ lo` (source is read, not written),
so the clear-column/clear-row/fold arms are strictly weaker than their bounded-below twins. -/

/-- `allOpsFreezeBelow` distributes over word concatenation. -/
theorem allOpsFreezeBelowAppend (lo : Nat) :
    ∀ (leftOps rightOps : List ElementaryOperation),
      allOpsFreezeBelow lo leftOps = true → allOpsFreezeBelow lo rightOps = true →
      allOpsFreezeBelow lo (leftOps ++ rightOps) = true
  | [], _, _, rightTrue => rightTrue
  | _ :: rest, rightOps, leftTrue, rightTrue =>
      boolAndBothTrue (boolConjTrueLeft leftTrue)
        (allOpsFreezeBelowAppend lo rest rightOps (boolConjTrueRight leftTrue) rightTrue)

/-- Freeze passes through the cascade's cross-clear terminal-vs-loop Bool branching. -/
theorem allOpsFreezeBelowMatchBool (lo : Nat) (flag : Bool)
    (settleOps loopOps : List ElementaryOperation)
    (settleFrozen : allOpsFreezeBelow lo settleOps = true)
    (loopFrozen : allOpsFreezeBelow lo (settleOps ++ loopOps) = true) :
    allOpsFreezeBelow lo (match flag with | true => settleOps | false => settleOps ++ loopOps) = true := by
  cases flag with
  | true => exact settleFrozen
  | false => exact loopFrozen

/-- The row transvection letter freezes below `lo` when its TARGET is at `≥ lo`. -/
theorem opFreezesBelowAddRow (lo sourceIndex targetIndex : Nat) (coefficient : Int)
    (targetGe : lo ≤ targetIndex) :
    opFreezesBelow lo (.rowOperation (.addRowMultiple sourceIndex targetIndex coefficient)) = true :=
  decide_eq_true targetGe

/-- The column transvection letter freezes below `lo` when its TARGET is at `≥ lo`. -/
theorem opFreezesBelowAddColumn (lo sourceIndex targetIndex : Nat) (coefficient : Int)
    (targetGe : lo ≤ targetIndex) :
    opFreezesBelow lo (.columnOperation (.addColumnMultiple sourceIndex targetIndex coefficient)) = true :=
  decide_eq_true targetGe

/-- The clear-column-below word (row transvections with targets `rowStart, rowStart+1, …`) freezes
below `lo` when `lo ≤ rowStart`.  Structural on the step count. -/
theorem smithClearColumnBelowStepsFreezesBelow (matrix : IntMatrix) (pivotIndex lo : Nat) :
    ∀ (stepCount rowStart : Nat), lo ≤ rowStart →
      allOpsFreezeBelow lo ((smithClearColumnBelowSteps matrix pivotIndex stepCount rowStart).map
        ElementaryOperation.rowOperation) = true
  | 0, _, _ => rfl
  | stepCount + 1, rowStart, rowGe =>
      boolAndBothTrue (opFreezesBelowAddRow lo pivotIndex rowStart _ rowGe)
        (smithClearColumnBelowStepsFreezesBelow matrix pivotIndex lo stepCount (rowStart + 1)
          (Nat.le_trans rowGe (Nat.le_succ rowStart)))

/-- The clear-row-right word (column transvections with targets `colStart, colStart+1, …`) freezes
below `lo` when `lo ≤ colStart`.  Structural on the step count. -/
theorem smithClearRowRightStepsFreezesBelow (matrix : IntMatrix) (pivotIndex lo : Nat) :
    ∀ (stepCount colStart : Nat), lo ≤ colStart →
      allOpsFreezeBelow lo ((smithClearRowRightSteps matrix pivotIndex stepCount colStart).map
        ElementaryOperation.columnOperation) = true
  | 0, _, _ => rfl
  | stepCount + 1, colStart, colGe =>
      boolAndBothTrue (opFreezesBelowAddColumn lo pivotIndex colStart _ colGe)
        (smithClearRowRightStepsFreezesBelow matrix pivotIndex lo stepCount (colStart + 1)
          (Nat.le_trans colGe (Nat.le_succ colStart)))

/-- The move-to-pivot word (a row swap and a column swap into the pivot) freezes below `lo` when the
pivot and the found position are at `≥ lo`. -/
theorem smithMoveToPivotOpsFreezesBelow (lo pivotIndex foundRow foundCol : Nat)
    (pivotGe : lo ≤ pivotIndex) (foundRowGe : lo ≤ foundRow) (foundColGe : lo ≤ foundCol) :
    allOpsFreezeBelow lo (smithMoveToPivotOps pivotIndex foundRow foundCol) = true :=
  boolAndBothTrue (boolAndBothTrue (decide_eq_true pivotGe) (decide_eq_true foundRowGe))
    (boolAndBothTrue (boolAndBothTrue (decide_eq_true pivotGe) (decide_eq_true foundColGe)) rfl)

/-- The sign-normalise word (an optional pivot-row negation at `pivotIndex`) freezes below `lo` when
`lo ≤ pivotIndex`.  Unlike the bounded-below twin, the negate index MATTERS for the freeze. -/
theorem smithSignNormalizeOpsFreezesBelow (matrix : IntMatrix) (lo pivotIndex : Nat)
    (pivotGe : lo ≤ pivotIndex) :
    allOpsFreezeBelow lo (smithSignNormalizeOps matrix pivotIndex) = true := by
  unfold smithSignNormalizeOps
  split
  · exact boolAndBothTrue (decide_eq_true pivotGe) rfl
  · rfl

/-- **The Euclid cascade word freezes the low-low block** — every letter (move, sign, cross-clear
transvections, and the recursive loop) is at indices `≥ pivotIndex ≥ lo`.  Verbatim mirror of
`smithCascadeSweepBoundedBelow`, threading the sign lemma's new `pivotGe`. -/
theorem smithCascadeSweepFreezesBelow (lo : Nat) :
    ∀ (innerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsFreezeBelow lo (smithCascadeSweep innerFuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | innerFuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      rw [smithCascadeSweepSucc]
      split
      · rfl
      · rename_i foundRow foundCol hFind
        have foundRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
          foundRow foundCol pivotRowInRange pivotColInRange hFind
        have loLeSucc : lo ≤ pivotIndex + 1 := Nat.le_trans pivotGe (Nat.le_succ pivotIndex)
        have moveFrozen : allOpsFreezeBelow lo (smithMoveToPivotOps pivotIndex foundRow foundCol) = true :=
          smithMoveToPivotOpsFreezesBelow lo pivotIndex foundRow foundCol pivotGe
            (Nat.le_trans pivotGe foundRange.1) (Nat.le_trans pivotGe foundRange.2.2.1)
        exact allOpsFreezeBelowMatchBool lo _ _ _
          (allOpsFreezeBelowAppend lo _ _
            (allOpsFreezeBelowAppend lo _ _
              (allOpsFreezeBelowAppend lo _ _ moveFrozen
                (smithSignNormalizeOpsFreezesBelow _ lo pivotIndex pivotGe))
              (smithClearColumnBelowStepsFreezesBelow _ pivotIndex lo _ (pivotIndex + 1) loLeSucc))
            (smithClearRowRightStepsFreezesBelow _ pivotIndex lo _ (pivotIndex + 1) loLeSucc))
          (allOpsFreezeBelowAppend lo _ _
            (allOpsFreezeBelowAppend lo _ _
              (allOpsFreezeBelowAppend lo _ _
                (allOpsFreezeBelowAppend lo _ _ moveFrozen
                  (smithSignNormalizeOpsFreezesBelow _ lo pivotIndex pivotGe))
                (smithClearColumnBelowStepsFreezesBelow _ pivotIndex lo _ (pivotIndex + 1) loLeSucc))
              (smithClearRowRightStepsFreezesBelow _ pivotIndex lo _ (pivotIndex + 1) loLeSucc))
            (smithCascadeSweepFreezesBelow lo innerFuel _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe))

/-- **The clearing position sweep word freezes the low-low block** — the `none`-branch standalone
cascade and the `some`-branch fold (target `pivotIndex ≥ lo`) + cascade + loop all freeze below `lo`.
Structural on the fuel; mirror of `smithRepairPositionSweepClearingBoundedBelow`. -/
theorem smithRepairPositionSweepClearingFreezesBelow (lo : Nat) :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsFreezeBelow lo (smithRepairPositionSweepClearing fuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      rw [smithRepairPositionSweepClearingSucc]
      split
      · exact smithCascadeSweepFreezesBelow lo _ matrix pivotIndex height width
          pivotRowInRange pivotColInRange pivotGe
      · rename_i foundPos hFind
        have foldFrozen : allOpsFreezeBelow lo
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ] = true :=
          boolAndBothTrue (opFreezesBelowAddRow lo foundPos pivotIndex 1 pivotGe) rfl
        exact allOpsFreezeBelowAppend lo _ _
          (allOpsFreezeBelowAppend lo _ _ foldFrozen
            (smithCascadeSweepFreezesBelow lo _ _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe))
          (smithRepairPositionSweepClearingFreezesBelow lo fuel _ pivotIndex height width
            pivotRowInRange pivotColInRange pivotGe)

/-! ## NODE A — the cross-pivot carrier `chainWindowedThroughPivots` -/

/-- **The windowed diagonal chain is monotone-down in the pivot index** — a chain over `[0, bigPivot)`
restricts to `[0, smallPivot)` for `smallPivot ≤ bigPivot`. -/
theorem matrixDiagonalChainWindowedMonotone (matrix : IntMatrix) (bigPivot smallPivot : Nat)
    (chainHolds : MatrixDiagonalChainWindowed matrix bigPivot) (leMono : smallPivot ≤ bigPivot) :
    MatrixDiagonalChainWindowed matrix smallPivot :=
  fun earlierIndex earlierLtSmall => chainHolds earlierIndex (Nat.lt_of_lt_of_le earlierLtSmall leMono)

/-- **The clearing repair sweep at successor fuel unfolds to the sweep-split** — pivot `p`'s position
sweep, concatenated with the whole repair sweep restarted at `p+1` on the advanced matrix (guard-true),
or `[]` (guard-false).  The definitional split the carrier inducts over (`rfl`). -/
theorem smithDivisibilityRepairSweepClearingSucc (outerFuel : Nat) (matrix : IntMatrix)
    (pivotIndex height width : Nat) :
    smithDivisibilityRepairSweepClearing (outerFuel + 1) matrix pivotIndex height width
      = (if pivotIndex + 1 ≤ Nat.min height width then
          smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width
            ++ smithDivisibilityRepairSweepClearing outerFuel
                (matrix.applyOperations
                  (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width))
                (pivotIndex + 1) height width
         else []) :=
  rfl

/-- **NODE A — the seed propagates the windowed diagonal chain through the whole clearing sweep.**
GIVEN the ESTABLISH seed, the chain `MatrixDiagonalChainWindowed matrix pivotIndex` survives the
repair sweep started at `pivotIndex`, advancing the pivot cap by the outer fuel.  Structural on the
fuel; the guard-true step establishes the chain at `pivotIndex + 1` on the advanced matrix by cases on
`earlier`:

  * `earlier = pivotIndex` — the seed instantiated at this pivot (the advanced matrix IS the seed's
    landed sub-block, divisor `M'.diagonalEntryAt pivotIndex`).
  * `earlier < pivotIndex` — transport the incoming `d_earlier`-divisibility through the position sweep
    (confined below `earlier + 1` via `allOpsBoundedBelowMonotone`), then REWRITE the divisor by the
    LOW-LOW FREEZE (`smithRepairPositionSweepClearingFreezesBelow` fixes `entryAt earlier earlier`
    under the sweep bounded below `pivotIndex > earlier`).

The exact shape-mirror of `smithDivisibilityRepairSweepClearingSettlesThroughPivots`. -/
theorem chainWindowedThroughPivots (seed : SmithCascadeLandsDivisibleSubBlock) :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      MatrixDiagonalChainWindowed matrix pivotIndex →
      MatrixDiagonalChainWindowed
        (matrix.applyOperations (smithDivisibilityRepairSweepClearing outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ chainHolds
      exact matrixDiagonalChainWindowedMonotone matrix pivotIndex _ chainHolds
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect chainHolds
      rw [smithDivisibilityRepairSweepClearingSucc]
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := Nat.le_trans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := Nat.le_trans guardTrue (natMinLeRight height width)
        have afterPositionChain :
            MatrixDiagonalChainWindowed
              (matrix.applyOperations (smithRepairPositionSweepClearing
                (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
              (pivotIndex + 1) := by
          intro earlierIndex earlierLtSucc
          cases Nat.lt_or_ge earlierIndex pivotIndex with
          | inl earlierLtPivot =>
              have positionBounded :
                  allOpsBoundedBelow (earlierIndex + 1)
                    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                      matrix pivotIndex height width) = true :=
                allOpsBoundedBelowMonotone (earlierIndex + 1) pivotIndex earlierLtPivot _
                  (smithRepairPositionSweepClearingBoundedBelow pivotIndex
                    (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
                    pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex))
              have transported :
                  MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt earlierIndex) (earlierIndex + 1)
                    (matrix.applyOperations (smithRepairPositionSweepClearing
                      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)) :=
                applyOperationsPreservesEntriesDivisibleWithin
                  (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width)
                  matrix positionBounded (chainHolds earlierIndex earlierLtPivot)
              have divisorFrozen :
                  (matrix.applyOperations (smithRepairPositionSweepClearing
                      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).diagonalEntryAt earlierIndex
                    = matrix.diagonalEntryAt earlierIndex :=
                applyOperationsFreezeEntryBelow
                  (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
                    matrix pivotIndex height width)
                  matrix earlierIndex earlierIndex
                  (smithRepairPositionSweepClearingFreezesBelow pivotIndex
                    (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
                    pivotRowInRange pivotColInRange (Nat.le_refl pivotIndex))
                  earlierLtPivot earlierLtPivot
              rw [divisorFrozen]
              exact transported
          | inr earlierGePivot =>
              have earlierEqPivot : earlierIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ earlierLtSucc) earlierGePivot
              rw [earlierEqPivot]
              exact seed matrix pivotIndex height width isRect pivotRowInRange pivotColInRange
        have afterPositionRect :
            (matrix.applyOperations (smithRepairPositionSweepClearing
              (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations (smithRepairPositionSweepClearing
            (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
          (pivotIndex + 1) height width afterPositionRect afterPositionChain
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact matrixDiagonalChainWindowedMonotone matrix pivotIndex _ chainHolds
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

end FX1Poly.ComputerAlgebra

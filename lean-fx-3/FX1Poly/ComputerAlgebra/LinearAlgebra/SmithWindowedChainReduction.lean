import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedDivisibility

/-! # Windowed chain reduction: seed implies `repairChainHolds`

Reduces the per-pivot ESTABLISH seed `SmithCascadeLandsDivisibleSubBlock` to the `repairChainHolds`
proposition consumed by `smithReduceCompleteDriverOfChain`, as a machine-checked Lean theorem.

  * NODE A (`chainWindowedThroughPivots`): given the seed, the windowed diagonal chain
    `MatrixDiagonalChainWindowed` propagates through the whole clearing repair sweep. The load-bearing
    obligation is the low-low freeze: after pivot `earlier` settles, the later sub-sweep at
    `[earlier+1, ·)` leaves `entryAt earlier earlier` (the windowed divisor) invariant. The shipped
    `allOpsBoundedBelow` cannot supply this (its negate arms are unconditionally `true`), so this module
    adds a parallel confinement `opFreezesBelow` / `allOpsFreezeBelow` with guarded negate arms, the
    entry-level freeze it certifies, and a structural re-walk of the sweep.

  * NODE B (`repairChainHoldsOfSeed`, `smithReduceCompleteDriverOfSubBlockSeed`): the seed yields the
    verbatim `repairChainHolds` proposition and collapses `SmithReduceCompleteDriverStatement` onto the
    seed alone, as a pure structural assembly term (no kernel evaluation).

Later sections (NODE C–E and the keystone) decompose the seed further and isolate its single open
residual `SmithCascadeLandedPivotDividesMinor` — the landed pivot divides the input minor, i.e. the
min-abs Euclid cascade computes the minor gcd — a standalone major arc not discharged here.

Raw Lean 4 + `Init`, structural on fuel `Nat`; ASCII identifiers; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. Per-declaration gated in the `FX1PolyAudit`
twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Generic list-slot freeze lemmas — reading at an index OTHER than the write position is invariant -/

/-- `listReplaceAt` leaves an off-position slot invariant — reading at any `index ≠ position`
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

/-- `listModifyAt` leaves an off-position slot invariant — reading at any `index ≠ position`
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

/-- The operation leaves the `[0, lo) × [0, lo)` block frozen — swap needs both indices at `≥ lo`;
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

/-- A row-locally applied transform that fixes column `colIndex` fixes the entry `(·, colIndex)` —
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

/-- A bounded-below row operation freezes a low-low entry — its written row is at `≥ lo`, so a
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

/-- A bounded-below column operation freezes a low-low entry — its written column is at `≥ lo`, so a
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

/-- A single freeze-below operation freezes a low-low entry — row/column dispatch. -/
theorem applyOperationFreezesEntryBelow {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryOperation) (opFrozen : opFreezesBelow lo operation = true)
    (rowIndex colIndex : Nat) (rowLt : rowIndex < lo) (colLt : colIndex < lo) :
    (matrix.applyOperation operation).entryAt rowIndex colIndex = matrix.entryAt rowIndex colIndex :=
  match operation, opFrozen with
  | .rowOperation rowOp, opFrozen =>
      applyRowOperationFreezesEntryBelow matrix rowOp opFrozen rowIndex colIndex rowLt
  | .columnOperation colOp, opFrozen =>
      applyColumnOperationFreezesEntryBelow matrix colOp opFrozen rowIndex colIndex colLt

/-- A whole freeze-below word freezes a low-low entry — structural on the word (peeling
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

Structural mirror of the `…OpsBoundedBelow` confinement chain over `allOpsFreezeBelow` in place of
`allOpsBoundedBelow`. The one divergence is the sign lemma, which now carries `lo ≤ pivotIndex`: the
bounded-below sign lemma did not need it because `opIsBoundedBelow` returns `true` on negate
unconditionally, the exact gap the freeze predicate closes. Transvection freezes need only the target at
`≥ lo` (the source is read, not written). -/

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

/-- The Euclid cascade word freezes the low-low block — every letter (move, sign, cross-clear
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

/-- The clearing position sweep word freezes the low-low block — the `none`-branch standalone
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

/-- The windowed diagonal chain is monotone-down in the pivot index — a chain over `[0, bigPivot)`
restricts to `[0, smallPivot)` for `smallPivot ≤ bigPivot`. -/
theorem matrixDiagonalChainWindowedMonotone (matrix : IntMatrix) (bigPivot smallPivot : Nat)
    (chainHolds : MatrixDiagonalChainWindowed matrix bigPivot) (leMono : smallPivot ≤ bigPivot) :
    MatrixDiagonalChainWindowed matrix smallPivot :=
  fun earlierIndex earlierLtSmall => chainHolds earlierIndex (Nat.lt_of_lt_of_le earlierLtSmall leMono)

/-- The clearing repair sweep at successor fuel unfolds to the sweep-split — pivot `p`'s position
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

/-- NODE A: given the ESTABLISH seed, the chain `MatrixDiagonalChainWindowed matrix pivotIndex` survives
the repair sweep started at `pivotIndex`, advancing the pivot cap by the outer fuel. Structural on the
fuel; the guard-true step establishes the chain at `pivotIndex + 1` on the advanced matrix by cases on
`earlier`: at `earlier = pivotIndex` it is the seed at this pivot, and at `earlier < pivotIndex` it
transports the incoming divisibility through the position sweep (confined below `earlier + 1`) and rewrites
the divisor by the low-low freeze `smithRepairPositionSweepClearingFreezesBelow`. Shape-mirrors
`smithDivisibilityRepairSweepClearingSettlesThroughPivots`. -/
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

/-! ## NODE B — the kernel reduction theorem: seed ⟹ `repairChainHolds` (THE r20 verifier deliverable) -/

/-- NODE B: the seed yields the corrected driver's `repairChainHolds`. Instantiating the NODE A carrier at
the driver start (`pivotIndex := 0`, `outerFuel := Nat.min height width`, matrix := the Phase-A output)
collapses the cap to `Nat.min height width` (`Nat.zero_add` + `natMinSelf`), the base chain being vacuous;
`smithChainPrefixOfDiagonalChainWindowed` then yields exactly the `SmithChainPrefix` conjunct that
`smithReduceCompleteDriverOfChain` consumes. Hypothesis is the seed alone. -/
theorem repairChainHoldsOfSeed (seed : SmithCascadeLandsDivisibleSubBlock) :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweepClearing (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width :=
  fun matrix height width isRect =>
    smithChainPrefixOfDiagonalChainWindowed
      ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
        (smithDivisibilityRepairSweepClearing (Nat.min height width)
          (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
      (Nat.min height width) height width
      (by
        have windowedAtCap :=
          chainWindowedThroughPivots seed (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations)
            0 height width
            (applyOperationsPreservesRectangular _ matrix isRect)
            (fun earlierIndex earlierLtZero => absurd earlierLtZero (Nat.not_lt_zero earlierIndex))
        rw [Nat.zero_add, natMinSelf] at windowedAtCap
        exact windowedAtCap)

/-- NODE B: the corrected driver totality on the seed alone. Feeds the reduced chain
`repairChainHoldsOfSeed` into `smithReduceCompleteDriverOfChain`, a pure structural assembly term (no
kernel evaluation). The corrected driver's totality residual count is then one:
`SmithCascadeLandsDivisibleSubBlock`. -/
theorem smithReduceCompleteDriverOfSubBlockSeed (seed : SmithCascadeLandsDivisibleSubBlock) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfChain (repairChainHoldsOfSeed seed)

/-! ## NODE C — seed decomposition (partial results only)

Diagonality-at-exit is not a valid decomposition: the position sweep's final Euclid cascade clears interior
cells (`smithCrossIsClear` checks only the pivot cross, never the `[p+1,·)²` interior), so the landed
sub-block is generally non-diagonal, and the seed's off-diagonal content is genuine gcd-ideal invariance —
the SNF invariant-factor theorem, a standalone major arc. This section ships the machine-checked partials:
the diagonal/off-diagonal split (`matrixEntriesDivisibleByWithinOfHalves`, naming where the wall lies), the
beyond-window diagonal-zero fact, and the C2 diagonal bridge `subBlockDiagonalDivisibleOfFindNone` (from a
find-loop `none`-exit plus rectangularity, the pivot divides every later diagonal of the sub-block). The
seed is not fabricated. -/

/-- The sub-block DIAGONAL half — the pivot divides every diagonal at `≥ lo`. -/
def SubBlockDiagonalDivisibleFrom (divisor : Int) (lo : Nat) (matrix : IntMatrix) : Prop :=
  ∀ position, lo ≤ position → dividesExactly divisor (matrix.diagonalEntryAt position)

/-- The sub-block OFF-DIAGONAL half — the pivot divides every off-diagonal cell of the `[lo, ·)²`
quadrant.  THIS is the gcd-ideal-invariance wall (C1); NOT proven in r20. -/
def SubBlockOffDiagonalDivisibleFrom (divisor : Int) (lo : Nat) (matrix : IntMatrix) : Prop :=
  ∀ rowIndex colIndex, lo ≤ rowIndex → lo ≤ colIndex → rowIndex ≠ colIndex →
    dividesExactly divisor (matrix.entryAt rowIndex colIndex)

/-- The seed splits into its diagonal and off-diagonal halves — a cell of the `[lo, ·)²` quadrant
is either on the diagonal (`SubBlockDiagonalDivisibleFrom`) or off it (`SubBlockOffDiagonalDivisibleFrom`).
The clean decomposition that names EXACTLY where the seed's wall lies. -/
theorem matrixEntriesDivisibleByWithinOfHalves (divisor : Int) (lo : Nat) (matrix : IntMatrix)
    (diagDivisible : SubBlockDiagonalDivisibleFrom divisor lo matrix)
    (offDiagDivisible : SubBlockOffDiagonalDivisibleFrom divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo matrix := by
  intro rowIndex rowGe colIndex colGe
  cases Nat.decEq rowIndex colIndex with
  | isTrue rowEqCol =>
      rw [← rowEqCol]
      exact diagDivisible rowIndex rowGe
  | isFalse rowNeCol =>
      exact offDiagDivisible rowIndex colIndex rowGe colGe rowNeCol

/-- The disjunction `Nat.min h w ≤ n → h ≤ n ∨ w ≤ n` — propext-clean via the `if h ≤ w` unfold of
`Nat.min` (the `Nat.min_eq_left` route leaks propext). -/
theorem natMinLeToOr (height width position : Nat) (minLe : Nat.min height width ≤ position) :
    height ≤ position ∨ width ≤ position := by
  have minLeUnfold : (if height ≤ width then height else width) ≤ position := minLe
  cases Nat.decLe height width with
  | isTrue isLe => rw [if_pos isLe] at minLeUnfold; exact Or.inl minLeUnfold
  | isFalse isNotLe => rw [if_neg isNotLe] at minLeUnfold; exact Or.inr minLeUnfold

/-- A cell beyond the matrix window reads zero — for a rectangular matrix, an entry whose row is at
`≥ height` or whose column is at `≥ width` is the default `0`. -/
theorem entryAtBeyondZero {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) (rowIndex colIndex : Nat)
    (beyond : height ≤ rowIndex ∨ width ≤ colIndex) :
    matrix.entryAt rowIndex colIndex = 0 := by
  cases beyond with
  | inl rowGe =>
      show listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) colIndex = 0
      rw [listGetWithDefaultGe [] matrix.rows rowIndex (by rw [isRect.1]; exact rowGe)]
      exact listGetWithDefaultGe 0 [] colIndex (Nat.zero_le colIndex)
  | inr colGe =>
      cases Nat.lt_or_ge rowIndex matrix.rows.length with
      | inl rowLt =>
          show listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) colIndex = 0
          exact listGetWithDefaultGe 0 (listGetWithDefault [] matrix.rows rowIndex) colIndex
            (by rw [listGetWithDefaultHasWidth matrix.rows rowIndex isRect.2 rowLt]; exact colGe)
      | inr rowGe2 =>
          show listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) colIndex = 0
          rw [listGetWithDefaultGe [] matrix.rows rowIndex rowGe2]
          exact listGetWithDefaultGe 0 [] colIndex (Nat.zero_le colIndex)

/-- A diagonal beyond the `Nat.min height width` window reads zero — the diagonal cell
`(position, position)` at `position ≥ Nat.min height width` is beyond the rows (if `min = height`) or
beyond the row width (if `min = width`). -/
theorem diagonalEntryAtBeyondWindowZero {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) (position : Nat)
    (positionGe : Nat.min height width ≤ position) :
    matrix.diagonalEntryAt position = 0 :=
  entryAtBeyondZero matrix isRect position position (natMinLeToOr height width position positionGe)

/-- C2 — the diagonal bridging lemma: find-loop `none`-exit ⟹ the diagonal half.  When the driver's
non-dividing scan over the window `[pivotIndex+1, Nat.min height width)` reports `none`, the pivot
diagonal divides every later diagonal of the `[pivotIndex+1, ·)` sub-block: window diagonals via the
shipped `smithFindNonDividingLaterDiagonalNoneDividesAll`, beyond-window diagonals via
`diagonalEntryAtBeyondWindowZero` (they are `0`).  The DIAGONAL half of the seed, from the exit
condition alone — non-vacuous; `findNone` is the genuine loop-terminal predicate the (unbuilt) C3
fuel-adequacy would establish for the sweep output. -/
theorem subBlockDiagonalDivisibleOfFindNone {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) (pivotIndex : Nat)
    (findNone : smithFindNonDividingLaterDiagonal matrix pivotIndex
      (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none) :
    SubBlockDiagonalDivisibleFrom (matrix.diagonalEntryAt pivotIndex) (pivotIndex + 1) matrix := by
  intro position positionGe
  cases Nat.lt_or_ge position (Nat.min height width) with
  | inl positionLtMin =>
      have pivotSuccLeMin : pivotIndex + 1 ≤ Nat.min height width :=
        Nat.le_of_lt (Nat.lt_of_le_of_lt positionGe positionLtMin)
      exact smithFindNonDividingLaterDiagonalNoneDividesAll matrix pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) findNone position positionGe
        (Eq.mp (congrArg (position < ·)
          (smithNatAddSubOfLe (pivotIndex + 1) (Nat.min height width) pivotSuccLeMin).symm) positionLtMin)
  | inr positionGeMin =>
      rw [diagonalEntryAtBeyondWindowZero matrix isRect position positionGeMin]
      exact dividesExactlyZero (matrix.diagonalEntryAt pivotIndex)

/-! ## NODE D — the C3 fuel-adequacy descent reduction

C2 reduces the seed's diagonal half to a single fact: the clearing position-sweep output satisfies the
find-loop `none`-exit. NODE D discharges the fuel-counting half of that fact — the descent induction on the
sweep fuel — as a Lean theorem, isolating the two irreducible cascade-output residuals as explicit named
hypotheses. The two steps of a genuine fold iteration are named as helpers (`smithClearingFoldStep`,
`smithClearingTerminalStep`), mirroring the loop's `some`- and `none`-branch bodies. The reduction
`smithClearingSweepReachesFindNoneOfDescent` takes a descent `measure : IntMatrix → Nat` whose base
(measure `0`) forces the `none`-exit, a `terminalKeepsFindNone` hypothesis (the terminal cascade preserves
the exit), and a `foldDescends` hypothesis (a genuine fold strictly drops the measure), and concludes by
structural induction on the fuel that the sweep output satisfies find-`none` whenever `measure matrix ≤
fuel`. The fuel-counting is complete; the cascade residuals are named, not fabricated. -/

/-- One clearing fold+cascade step: the `some`-branch body of `smithRepairPositionSweepClearing` — fold
the found row into the pivot row, then fire the standalone Euclid cascade. Mirrors the loop body. -/
def smithClearingFoldStep (work : IntMatrix) (foundPos pivotIndex height width : Nat) : IntMatrix :=
  let afterFold := work.applyOperations
    [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]
  afterFold.applyOperations
    (smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width) afterFold pivotIndex height width)

/-- The clearing terminal cascade: the `none`-branch body — fire the standalone Euclid cascade on the
current matrix, which clears an earlier pivot's stranded cross residue. -/
def smithClearingTerminalStep (work : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  work.applyOperations
    (smithCascadeSweep (smithMinorAbsSum work pivotIndex height width) work pivotIndex height width)

/-- The fold step preserves rectangularity (two confined `applyOperations`). -/
theorem smithClearingFoldStepPreservesRectangular {height width : Nat}
    (work : IntMatrix) (foundPos pivotIndex : Nat) (isRect : work.IsRectangular height width) :
    (smithClearingFoldStep work foundPos pivotIndex height width).IsRectangular height width :=
  applyOperationsPreservesRectangular _ _
    (applyOperationsPreservesRectangular _ work isRect)

/-- NODE D: the fuel-adequacy descent reduction. Given a descent `measure` whose base forces the
find-`none` exit, whose terminal cascade preserves it, and whose genuine fold strictly drops it, the
clearing position sweep started with any `fuel ≥ measure matrix` lands the find-`none` exit on its output.
Structural induction on the fuel: the `none`-branch discharges via `terminalKeepsFindNone`; the
`some`-branch rewrites the output through `applyOperationsAppend` and rides the IH at the dropped measure;
the `fuel = 0` base rides `measureBaseFindNone`. The cascade residuals are named, not fabricated. -/
theorem smithClearingSweepReachesFindNoneOfDescent
    (pivotIndex height width : Nat)
    (measure : IntMatrix → Nat)
    (measureBaseFindNone : ∀ (work : IntMatrix),
        measure work = 0 →
        smithFindNonDividingLaterDiagonal work pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (terminalKeepsFindNone : ∀ (work : IntMatrix), work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (foldDescends : ∀ (work : IntMatrix), work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          measure (smithClearingFoldStep work foundPos pivotIndex height width) < measure work) :
    ∀ (fuel : Nat) (matrix : IntMatrix), matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width → measure matrix ≤ fuel →
      smithFindNonDividingLaterDiagonal
        (matrix.applyOperations (smithRepairPositionSweepClearing fuel matrix pivotIndex height width))
        pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix _ _ _ measureLe
      exact measureBaseFindNone matrix (Nat.le_antisymm measureLe (Nat.zero_le _))
  | succ fuel ih =>
      intro matrix isRect pRowLt pColLt measureLe
      cases hFind : smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) with
      | none =>
          rw [smithRepairPositionSweepClearingSucc, hFind]
          exact terminalKeepsFindNone matrix isRect pRowLt pColLt hFind
      | some foundPos =>
          rw [smithRepairPositionSweepClearingSucc, hFind, applyOperationsAppend, applyOperationsAppend]
          exact ih (smithClearingFoldStep matrix foundPos pivotIndex height width)
            (smithClearingFoldStepPreservesRectangular matrix foundPos pivotIndex isRect)
            pRowLt pColLt
            (Nat.le_of_lt_succ
              (Nat.lt_of_lt_of_le (foldDescends matrix isRect pRowLt pColLt foundPos hFind) measureLe))

/-- NODE D: the seed's diagonal half from the descent reduction. Composes the NODE D reduction (at the
driver's fuel `smithMinorAbsSum matrix pivotIndex height width`) with the C2 bridge
`subBlockDiagonalDivisibleOfFindNone`. Given the descent hypotheses and the fuel-budget bound
`measure matrix ≤ smithMinorAbsSum matrix pivotIndex height width`, the sweep output satisfies the seed's
`SubBlockDiagonalDivisibleFrom` — the diagonal half at this pivot, modulo the named cascade/measure
residuals. The off-diagonal half remains open (NODE E). -/
theorem smithClearingSweepDiagonalHalfOfDescent
    (pivotIndex height width : Nat)
    (measure : IntMatrix → Nat)
    (measureBaseFindNone : ∀ (work : IntMatrix),
        measure work = 0 →
        smithFindNonDividingLaterDiagonal work pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (terminalKeepsFindNone : ∀ (work : IntMatrix), work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (foldDescends : ∀ (work : IntMatrix), work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          measure (smithClearingFoldStep work foundPos pivotIndex height width) < measure work)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (measureBudget : measure matrix ≤ smithMinorAbsSum matrix pivotIndex height width) :
    SubBlockDiagonalDivisibleFrom
      ((matrix.applyOperations (smithRepairPositionSweepClearing
          (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).diagonalEntryAt
        pivotIndex)
      (pivotIndex + 1)
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)) :=
  subBlockDiagonalDivisibleOfFindNone
    (matrix.applyOperations (smithRepairPositionSweepClearing
      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
    (applyOperationsPreservesRectangular _ matrix isRect)
    pivotIndex
    (smithClearingSweepReachesFindNoneOfDescent pivotIndex height width measure
      measureBaseFindNone terminalKeepsFindNone foldDescends
      (smithMinorAbsSum matrix pivotIndex height width) matrix isRect pRowLt pColLt measureBudget)

/-! ## NODE E — the "sub-block stays diagonal" route is refuted

One route hoped to close the seed's off-diagonal half by proving the single-pivot clearing sweep leaves
the trailing sub-block diagonal (so every off-diagonal is `0`). This is false: `diag(15,10,6,4)` at pivot
`0` lands `-20` in cell `(3,1)`. A `4x4` single-pivot kernel pin (`decide` at `maxRecDepth 8000`). So the
off-diagonal half genuinely needs the gcd-ideal invariance route — the fill-in is divisible by the landed
pivot only via the SNF invariant-factor argument, not via diagonality. The whole sweep (all pivots) does
restore full diagonality, but the seed is stated per pivot, where the interior is generally
non-diagonal. -/

set_option maxRecDepth 8000 in
/-- NODE E — route (i) refuted.  A diagonal rectangular matrix whose single-pivot clearing sweep
output has a nonzero interior off-diagonal entry (`diag(15,10,6,4)`, pivot `0`, cell `(3,1) = -20`).  So
"the single-pivot sweep output is sub-block-diagonal" is FALSE; the seed's off-diagonal half is the
gcd-ideal (SNF invariant-factor) major arc, not a diagonality bridge. -/
theorem smithClearingSweepInteriorNotDiagonalWitness :
    ∃ (matrix : IntMatrix) (pivotIndex height width rowIndex colIndex : Nat),
      matrix.IsRectangular height width ∧
      pivotIndex < height ∧ pivotIndex < width ∧
      pivotIndex < rowIndex ∧ pivotIndex < colIndex ∧ rowIndex ≠ colIndex ∧
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).entryAt
        rowIndex colIndex ≠ 0 :=
  ⟨{ rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] }, 0, 4, 4, 3, 1,
   ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩,
   by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Measure candidates for `foldDescends` are machine-refuted

The NODE D reduction leaves the seed's diagonal half resting on `foldDescends` — a strict drop of some
descent `measure` on each genuine fold — plus the fuel-budget fit `measure matrix ≤ smithMinorAbsSum …`.
`foldDescends` does not compose from the shipped pure-`Int` `smithRepairDecreasesPivotSize`, because two
candidate measures fail, both refuted below as theorems: the minor-abs-sum itself is not monotone-down on
a fold (`smithMinorAbsSumRaisesOnFoldWitness`, `24 → 40`), and the zero-pivot fold saturates the budget so
no fixed-`K` lexicographic-into-`Nat` measure both fits the budget and descends
(`smithZeroPivotFoldSaturatesBudgetWitness`, `|pivot| = 4 =` budget on `diag(0,4)`). The genuine content
is the cascade-output magnitude, not plumbing. -/

set_option maxRecDepth 8000 in
/-- The minor-abs-sum measure rises on a fold: `smithMinorAbsSum` (the budget, trivially an upper bound)
is not a descent measure — on `diag(6, 10, 8)` pivot `0` the single genuine fold+cascade raises it
`24 → 40`. So `measure := smithMinorAbsSum` cannot drive `foldDescends`. -/
theorem smithMinorAbsSumRaisesOnFoldWitness :
    ∃ (matrix : IntMatrix) (foundPos pivotIndex height width : Nat),
      smithMinorAbsSum matrix pivotIndex height width
        < smithMinorAbsSum (smithClearingFoldStep matrix foundPos pivotIndex height width)
            pivotIndex height width :=
  ⟨{ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] }, 1, 0, 3, 3, by decide⟩

set_option maxRecDepth 8000 in
/-- The zero-pivot fold saturates the budget: on `diag(0, 4)` the fold lands `|pivot| = 4`, exactly the
fuel budget `smithMinorAbsSum = 4`, while the input pivot is `0`. A lexicographic measure
`(isPivotZero, pivotAbs)` must rank the zero-flag strictly above `pivotAbs`, so any collapse
`flag · K + pivotAbs` needs `K > pivotAbs`, which forces `measure(diag(0, 4)) > 4` and violates the
budget. No fixed-`K` lexicographic-into-`Nat` measure both fits the budget and strictly descends. -/
theorem smithZeroPivotFoldSaturatesBudgetWitness :
    ∃ (matrix : IntMatrix) (foundPos pivotIndex height width : Nat),
      matrix.diagonalEntryAt pivotIndex = 0 ∧
      ((smithClearingFoldStep matrix foundPos pivotIndex height width).diagonalEntryAt pivotIndex).natAbs
        = smithMinorAbsSum matrix pivotIndex height width :=
  ⟨{ rows := [[0, 0], [0, 4]] }, 1, 0, 2, 2, by decide, by decide⟩

/-! ## NODE 1 — the gcd-ideal invariance via the forward tower

The off-diagonal ideal invariance rides the shipped forward tower; no backward tower (op inverses) is
needed. The pivot-`p` clearing position sweep is confined to indices `≥ p`
(`smithRepairPositionSweepClearingBoundedBelow` with `lo := p`), so for any divisor `g` of the whole
`[p, ·)` minor of the input, `applyOperationsPreservesEntriesDivisibleWithin` carries `g`-divisibility to
the whole `[p, ·)` block of the output, fill-in included (each fill-in cell is a ℤ-combination of
`g`-divisible input cells). `matrixEntriesDivisibleByWithinLoMono` then restricts up to the `[p+1, ·)`
sub-block the seed reads. On the concrete window `diag(6,10,8)` the sweep lands `2 = gcd(6,10,8)` at the
pivot, a common divisor of the whole minor. -/

/-- Sub-block divisibility restricts UP in the window floor — the `[loSmall, ·)²` block being
`divisor`-divisible implies the smaller `[loBig, ·)²` block is (`loSmall ≤ loBig`).  Both the row guard
and the column guard weaken through `Nat.le_trans`.  The plumbing that turns the pivot-`p` forward-tower
output `MatrixEntriesDivisibleByWithin g p M'` into the seed's `[p+1, ·)` sub-block. -/
theorem matrixEntriesDivisibleByWithinLoMono {divisor : Int} {loSmall loBig : Nat} {matrix : IntMatrix}
    (leMono : loSmall ≤ loBig)
    (divisible : MatrixEntriesDivisibleByWithin divisor loSmall matrix) :
    MatrixEntriesDivisibleByWithin divisor loBig matrix :=
  fun rowIndex rowGe colIndex colGe =>
    divisible rowIndex (Nat.le_trans leMono rowGe) colIndex (Nat.le_trans leMono colGe)

set_option maxRecDepth 8000 in
/-- The cascade lands the minor gcd on a concrete gcd > 1 window — the pivot-0 clearing position
sweep of `diag(6, 10, 8)` lands `2 = gcd(6, 10, 8)` at the pivot.  A machine-checked positive instance
of the keystone `SmithCascadeLandedPivotDividesMinor`: on this non-coprime window the landed pivot is a
common divisor of the whole minor, so the seed's sub-block divisibility holds by NODE 1 (forward tower).
Probe-first for B2. -/
theorem smithClearingSweepLandsMinorGcdOnConcreteWindow :
    (({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3)
          { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3)).diagonalEntryAt 0 = 2 := by
  decide

/-! ## NODE 2 — both seed halves from one within-predicate

Both halves of the seed are read off a single `MatrixEntriesDivisibleByWithin divisor lo` fact — the one
the NODE 1 forward tower produces. The diagonal half is the on-diagonal slice (`diagonalEntryAt position =
entryAt position position`); the off-diagonal half drops the `rowIndex ≠ colIndex` witness. Every fill-in
cell of the `[lo, ·)` block is `divisor`-divisible because the forward tower carries `divisor` across the
confined sweep. -/

/-- The diagonal half from the within-predicate — a `[lo, ·)²` block that is entirely
`divisor`-divisible has every diagonal cell `divisor`-divisible (`diagonalEntryAt` is the on-diagonal
`entryAt`).  The DIAGONAL half of the seed, read off the forward-tower within-predicate directly. -/
theorem subBlockDiagonalDivisibleOfWithin {divisor : Int} {lo : Nat} {matrix : IntMatrix}
    (within : MatrixEntriesDivisibleByWithin divisor lo matrix) :
    SubBlockDiagonalDivisibleFrom divisor lo matrix :=
  fun position positionGe => within position positionGe position positionGe

/-- The off-diagonal half from the within-predicate — a `[lo, ·)²` block that is entirely
`divisor`-divisible has every off-diagonal cell `divisor`-divisible (drop the distinctness witness).
The OFF-DIAGONAL half of the seed (r21's gcd-ideal wall) is now a trivial slice of the SAME within-fact
the forward tower supplies — no separate ideal argument once the within-predicate is in hand. -/
theorem subBlockOffDiagonalDivisibleOfWithin {divisor : Int} {lo : Nat} {matrix : IntMatrix}
    (within : MatrixEntriesDivisibleByWithin divisor lo matrix) :
    SubBlockOffDiagonalDivisibleFrom divisor lo matrix :=
  fun rowIndex colIndex rowGe colGe _ => within rowIndex rowGe colIndex colGe

/-! ## NODE 4 — the keystone assembled: the seed reduced to one residual

The residual is `SmithCascadeLandedPivotDividesMinor`: the landed pivot divides every entry of the input's
`[pivotIndex, ·)` minor (a common divisor of the whole minor; since the cascade is unimodular, its
magnitude equals the minor gcd). This replaces the earlier "divides the folded pair" candidate, which is
false — `diag(15,10,6,4)` at pivot `0` lands `4`, and `4 ∤ 15`. From the residual the whole seed follows
via the NODE 1 forward tower (sweep confined below `p`) and the NODE 2 read-off, restricting `[p, ·)` up to
`[p+1, ·)` by `matrixEntriesDivisibleByWithinLoMono`. Composing with
`smithReduceCompleteDriverOfSubBlockSeed` collapses the entire driver totality onto this one residual. -/

/-- The keystone residual: the landed pivot divides the input minor. After pivot `pivotIndex`'s clearing
position sweep, the landed pivot diagonal `M'.diagonalEntryAt pivotIndex` divides every entry of the input
matrix's `[pivotIndex, ·) × [pivotIndex, ·)` minor — the min-abs Euclid cascade lands a common divisor of
the whole minor (the minor gcd, since the unimodular cascade keeps the landed pivot in the minor's
gcd-ideal). Replaces the false "divides the folded pair" candidate (`diag(15,10,6,4)` lands `4 ∤ 15`); a
concrete gcd > 1 witness is `smithClearingSweepLandsMinorGcdOnConcreteWindow`. -/
def SmithCascadeLandedPivotDividesMinor : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix

/-- NODE 4: the seed from the keystone. Given `SmithCascadeLandedPivotDividesMinor`, the per-pivot
ESTABLISH seed `SmithCascadeLandsDivisibleSubBlock` holds — carry the landed-pivot divisibility of the
input `[p, ·)` minor across the pivot-`p` sweep (confined below `p`, forward tower
`applyOperationsPreservesEntriesDivisibleWithin`), then restrict the floor `p → p+1`
(`matrixEntriesDivisibleByWithinLoMono`). A pure structural assembly. -/
theorem seedOfLandedPivotDividesMinor (landedDivides : SmithCascadeLandedPivotDividesMinor) :
    SmithCascadeLandsDivisibleSubBlock := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  exact matrixEntriesDivisibleByWithinLoMono (Nat.le_succ pivotIndex)
    (applyOperationsPreservesEntriesDivisibleWithin
      (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width)
      matrix
      (smithRepairPositionSweepClearingBoundedBelow pivotIndex
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
        pRowLt pColLt (Nat.le_refl pivotIndex))
      (landedDivides matrix pivotIndex height width isRect pRowLt pColLt))

/-- NODE 4: the driver totality on the keystone alone. Composes the seed reduction with the
seed-conditional driver totality `smithReduceCompleteDriverOfSubBlockSeed`.
`SmithReduceCompleteDriverStatement` is inhabited given the single residual
`SmithCascadeLandedPivotDividesMinor`. -/
theorem smithReduceCompleteDriverOfLandedPivotDividesMinor
    (landedDivides : SmithCascadeLandedPivotDividesMinor) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfSubBlockSeed (seedOfLandedPivotDividesMinor landedDivides)

/-! ## Summary: the single open residual

`SmithReduceCompleteDriverStatement` is inhabited given `SmithCascadeLandedPivotDividesMinor`, the one
surviving obligation: the pivot-`p` clearing position sweep lands, at the pivot, a divisor of every entry
of the input's `[p, ·)` minor (equivalently, its magnitude equals the minor gcd). This is the "min-abs
Euclid cascade computes the gcd" correctness over the threaded work matrix — a standalone major arc, true
on every probed fixture (`smithClearingSweepLandsMinorGcdOnConcreteWindow` is a machine-checked instance)
but not proven in general. Hypothesis-free driver totality is not reached here. -/

end FX1Poly.ComputerAlgebra

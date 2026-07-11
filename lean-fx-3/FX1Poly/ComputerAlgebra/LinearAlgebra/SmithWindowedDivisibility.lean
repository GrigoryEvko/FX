import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithWindowedDivisibility — the WINDOWED sub-block
    divisibility preserve tower + operation confinement (H2-SMITH r19, #2261)

The shipped whole-matrix ideal-invariance `applyOperationsPreservesEntriesDivisible`
(SmithCascadeTermination §r14) carries a divisor `d` through ANY certificate word, but only when `d`
divides EVERY entry.  The invariant-factor chain `repairChainHolds` needs a WINDOWED version: the
settled prefix entry `d_earlier` divides only the sub-block at indices `≥ earlier + 1` (it does NOT
divide the prefix `d_0 .. d_{earlier-1}`), and the later-pivot repair operations are confined to
indices `≥ earlier + 1`, so they permute / combine divisible cells within that sub-block.

This module ships that windowed preserve tower zero-axiom:

  * `MatrixEntriesDivisibleByWithin` — the `[lo, ·) × [lo, ·)` sub-block ideal predicate, and its
    row-level companion `RowSlotsDivisibleByFrom`.
  * Two generic GUARDED slot carriers (`listReplaceAtGuardedSlot`, `listModifyAtGuardedSlot`) that
    thread the index guard `lo ≤ i + startIndex` through the structural recursion — the guarded
    mirror of the r14 range-free slot carriers.
  * The six windowed single-operation deltas (swap/negate/transvection, row and column) preserving
    `MatrixEntriesDivisibleByWithin`, each conditioned on the operation being bounded BELOW by `lo`.
  * `opIsBoundedBelow` / `allOpsBoundedBelow` (fully-enumerated, propext-clean decidable checks) and
    the word fold `applyOperationsPreservesEntriesDivisibleWithin`.
  * The CONFINEMENT discharge: every operation the later-pivot repair sweeps emit is bounded below by
    the start pivot (`smithDivisibilityRepairSweepClearingOpsBoundedBelow`), truth-probed by `#eval`.

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowedDivisibility.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The windowed sub-block ideal predicate -/

/-- **Every slot at column `≥ lo` of a row is `divisor`-divisible** — the col-guarded row-level ideal
predicate (the ragged/below-`lo` slots are unconstrained). -/
def RowSlotsDivisibleByFrom (divisor : Int) (lo : Nat) (row : IntRow) : Prop :=
  ∀ colIndex, lo ≤ colIndex → dividesExactly divisor (listGetWithDefault 0 row colIndex)

/-- **Every entry of the `[lo, ·) × [lo, ·)` sub-block is `divisor`-divisible** — the windowed
whole-matrix ideal predicate (both coordinates at or beyond `lo`). -/
def MatrixEntriesDivisibleByWithin (divisor : Int) (lo : Nat) (matrix : IntMatrix) : Prop :=
  ∀ rowIndex, lo ≤ rowIndex → RowSlotsDivisibleByFrom divisor lo (listGetWithDefault [] matrix.rows rowIndex)

/-- The empty row's slots are all `divisor`-divisible-from-`lo` (every read is the default `0`). -/
theorem rowSlotsDivisibleByFromEmpty (divisor : Int) (lo : Nat) : RowSlotsDivisibleByFrom divisor lo [] :=
  fun colIndex _ => match colIndex with
    | 0 => dividesExactlyZero divisor
    | _ + 1 => dividesExactlyZero divisor

/-- Read `MatrixEntriesDivisibleByWithin` at a single sub-block entry (defeq unfold). -/
theorem matrixEntriesDivisibleByWithinAt {divisor : Int} {lo : Nat} {matrix : IntMatrix}
    (matrixDivisible : MatrixEntriesDivisibleByWithin divisor lo matrix)
    (rowIndex colIndex : Nat) (rowGe : lo ≤ rowIndex) (colGe : lo ≤ colIndex) :
    dividesExactly divisor (matrix.entryAt rowIndex colIndex) :=
  matrixDivisible rowIndex rowGe colIndex colGe

/-! ## Two generic GUARDED slot carriers (the index guard `lo ≤ i + startIndex` threads the shift) -/

/-- **`listReplaceAt` preserves a guarded slot predicate** — if `predicate` holds of the default and
the new entry and every original slot at guarded index, it holds of every slot at guarded index after
the replace.  Structural on `(entries, position)`; the guard `lo ≤ i + startIndex` shifts by one on
the tail (the offset-on-the-right convention makes the `startIndex = 0` instantiation defeq). -/
theorem listReplaceAtGuardedSlot {Entry : Type} (defaultEntry : Entry)
    (predicate : Entry → Prop) (isDefaultOk : predicate defaultEntry) (newEntry : Entry)
    (isNewOk : predicate newEntry) (lo : Nat) :
    ∀ (entries : List Entry) (position startIndex : Nat),
      (∀ i, lo ≤ i + startIndex → predicate (listGetWithDefault defaultEntry entries i)) →
      ∀ i, lo ≤ i + startIndex →
        predicate (listGetWithDefault defaultEntry (listReplaceAt entries position newEntry) i)
  | [], 0, _, _ => fun i _ => match i with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | [], _ + 1, _, _ => fun i _ => match i with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | _ :: _, 0, _, guarded => fun i loLe => match i, loLe with
      | 0, _ => isNewOk
      | successor + 1, loLe => guarded (successor + 1) loLe
  | headEntry :: remainingEntries, position + 1, startIndex, guarded => fun i loLe => match i, loLe with
      | 0, loLe => guarded 0 loLe
      | successor + 1, loLe =>
          let shiftEq : successor + 1 + startIndex = successor + (startIndex + 1) :=
            (Nat.succ_add successor startIndex).trans (Nat.add_succ successor startIndex).symm
          listReplaceAtGuardedSlot defaultEntry predicate isDefaultOk newEntry isNewOk lo
            remainingEntries position (startIndex + 1)
            (fun innerIndex innerLoLe =>
              guarded (innerIndex + 1)
                (Eq.mp (congrArg (lo ≤ ·)
                  ((Nat.succ_add innerIndex startIndex).trans
                    (Nat.add_succ innerIndex startIndex).symm).symm) innerLoLe))
            successor (Eq.mp (congrArg (lo ≤ ·) shiftEq) loLe)

/-- **`listModifyAt` preserves a guarded slot predicate** — when the transform preserves it and it
holds of the default and every original guarded slot, it holds of every guarded slot after the modify.
Structural on `(entries, position)`; the transform lands on the head in the `position = 0` arm. -/
theorem listModifyAtGuardedSlot {Entry : Type} (defaultEntry : Entry)
    (predicate : Entry → Prop) (isDefaultOk : predicate defaultEntry) (transform : Entry → Entry)
    (isTransformOk : ∀ entry, predicate entry → predicate (transform entry)) (lo : Nat) :
    ∀ (entries : List Entry) (position startIndex : Nat),
      (∀ i, lo ≤ i + startIndex → predicate (listGetWithDefault defaultEntry entries i)) →
      ∀ i, lo ≤ i + startIndex →
        predicate (listGetWithDefault defaultEntry (listModifyAt transform entries position) i)
  | [], 0, _, _ => fun i _ => match i with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | [], _ + 1, _, _ => fun i _ => match i with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | _ :: _, 0, _, guarded => fun i loLe => match i, loLe with
      | 0, loLe => isTransformOk _ (guarded 0 loLe)
      | successor + 1, loLe => guarded (successor + 1) loLe
  | headEntry :: remainingEntries, position + 1, startIndex, guarded => fun i loLe => match i, loLe with
      | 0, loLe => guarded 0 loLe
      | successor + 1, loLe =>
          let shiftEq : successor + 1 + startIndex = successor + (startIndex + 1) :=
            (Nat.succ_add successor startIndex).trans (Nat.add_succ successor startIndex).symm
          listModifyAtGuardedSlot defaultEntry predicate isDefaultOk transform isTransformOk lo
            remainingEntries position (startIndex + 1)
            (fun innerIndex innerLoLe =>
              guarded (innerIndex + 1)
                (Eq.mp (congrArg (lo ≤ ·)
                  ((Nat.succ_add innerIndex startIndex).trans
                    (Nat.add_succ innerIndex startIndex).symm).symm) innerLoLe))
            successor (Eq.mp (congrArg (lo ≤ ·) shiftEq) loLe)

/-- Past-the-end read is the default — `list.length ≤ index` gives `listGetWithDefault d list index = d`.
Structural on `(list, index)`. -/
theorem listGetWithDefaultGe {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (index : Nat), entries.length ≤ index →
      listGetWithDefault defaultEntry entries index = defaultEntry
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, isBeyond => absurd isBeyond (Nat.not_le.2 (Nat.succ_pos _))
  | _ :: remainingEntries, index + 1, isBeyond =>
      listGetWithDefaultGe defaultEntry remainingEntries index (Nat.le_of_succ_le_succ isBeyond)

/-! ## The row-level (column-guarded) preservers for the within-row transforms -/

/-- The row map-negation preserves guarded row divisibility (each slot negates a divisible entry). -/
theorem rowSlotsDivisibleFromMapNeg {divisor : Int} {lo : Nat} {row : IntRow}
    (rowDivisible : RowSlotsDivisibleByFrom divisor lo row) :
    RowSlotsDivisibleByFrom divisor lo (row.map (fun entry => -entry)) :=
  fun colIndex loLe => by
    rw [listGetWithDefaultMapNeg]
    exact dividesExactlyNeg (rowDivisible colIndex loLe)

/-- The row scaled-add preserves guarded row divisibility — structural (offset-shifted) mirror of
`rowSlotsDivisibleAddScaledEntries`: each zipped slot is `target + coefficient * source`, both
divisible; the ragged/past-end/below-`lo` slots read `0`. -/
theorem rowSlotsDivisibleFromAddScaledEntriesAt {divisor : Int} (coefficient : Int) (lo : Nat) :
    ∀ (sourceRow targetRow : IntRow) (startIndex : Nat),
      (∀ i, lo ≤ i + startIndex → dividesExactly divisor (listGetWithDefault 0 sourceRow i)) →
      (∀ i, lo ≤ i + startIndex → dividesExactly divisor (listGetWithDefault 0 targetRow i)) →
      ∀ i, lo ≤ i + startIndex →
        dividesExactly divisor (listGetWithDefault 0 (addScaledEntries coefficient sourceRow targetRow) i)
  | [], [], _, _, _ => fun i _ => match i with | 0 => dividesExactlyZero divisor | _ + 1 => dividesExactlyZero divisor
  | [], _ :: _, _, _, _ => fun i _ => match i with | 0 => dividesExactlyZero divisor | _ + 1 => dividesExactlyZero divisor
  | _ :: _, [], _, _, _ => fun i _ => match i with | 0 => dividesExactlyZero divisor | _ + 1 => dividesExactlyZero divisor
  | sourceHead :: sourceRest, targetHead :: targetRest, startIndex, sourceDiv, targetDiv =>
      fun i loLe => match i, loLe with
        | 0, loLe => dividesExactlyAddScaled coefficient (targetDiv 0 loLe) (sourceDiv 0 loLe)
        | successor + 1, loLe =>
            let shiftEq : successor + 1 + startIndex = successor + (startIndex + 1) :=
              (Nat.succ_add successor startIndex).trans (Nat.add_succ successor startIndex).symm
            rowSlotsDivisibleFromAddScaledEntriesAt coefficient lo sourceRest targetRest (startIndex + 1)
              (fun innerIndex innerLoLe =>
                sourceDiv (innerIndex + 1)
                  (Eq.mp (congrArg (lo ≤ ·)
                    ((Nat.succ_add innerIndex startIndex).trans
                      (Nat.add_succ innerIndex startIndex).symm).symm) innerLoLe))
              (fun innerIndex innerLoLe =>
                targetDiv (innerIndex + 1)
                  (Eq.mp (congrArg (lo ≤ ·)
                    ((Nat.succ_add innerIndex startIndex).trans
                      (Nat.add_succ innerIndex startIndex).symm).symm) innerLoLe))
              successor (Eq.mp (congrArg (lo ≤ ·) shiftEq) loLe)

/-- The row scaled-add preserves guarded row divisibility (the `startIndex = 0` instantiation). -/
theorem rowSlotsDivisibleFromAddScaledEntries {divisor : Int} (coefficient : Int) {lo : Nat}
    {sourceRow targetRow : IntRow}
    (sourceDiv : RowSlotsDivisibleByFrom divisor lo sourceRow)
    (targetDiv : RowSlotsDivisibleByFrom divisor lo targetRow) :
    RowSlotsDivisibleByFrom divisor lo (addScaledEntries coefficient sourceRow targetRow) :=
  fun colIndex loLe =>
    rowSlotsDivisibleFromAddScaledEntriesAt coefficient lo sourceRow targetRow 0
      (fun i h => sourceDiv i h) (fun i h => targetDiv i h) colIndex loLe

/-- The within-row column negation preserves guarded row divisibility (a single `listModifyAt` of a
negation — unconditional in the negated column). -/
theorem rowSlotsDivisibleFromModifyNeg {divisor : Int} {lo : Nat} (row : IntRow) (colIndex : Nat)
    (rowDivisible : RowSlotsDivisibleByFrom divisor lo row) :
    RowSlotsDivisibleByFrom divisor lo (listModifyAt (fun entry => -entry) row colIndex) :=
  fun readIndex loLe =>
    listModifyAtGuardedSlot (0 : Int) (dividesExactly divisor) (dividesExactlyZero divisor)
      (fun entry => -entry) (fun _ isDivisible => dividesExactlyNeg isDivisible) lo row colIndex 0
      (fun i h => rowDivisible i h) readIndex loLe

/-- The within-row column swap preserves guarded row divisibility, when both swapped columns are at
`≥ lo` (a permutation of divisible cells; the range-guard identity branches return the hypothesis). -/
theorem rowSlotsDivisibleFromSwapEntries {divisor : Int} {lo : Nat} (row : IntRow)
    (firstIndex secondIndex : Nat) (firstGe : lo ≤ firstIndex) (secondGe : lo ≤ secondIndex)
    (rowDivisible : RowSlotsDivisibleByFrom divisor lo row) :
    RowSlotsDivisibleByFrom divisor lo (swapEntriesWithinRow row firstIndex secondIndex) := by
  unfold IntMatrix.swapEntriesWithinRow
  split
  · split
    · exact fun readIndex loLe =>
        listReplaceAtGuardedSlot (0 : Int) (dividesExactly divisor) (dividesExactlyZero divisor)
          (listGetWithDefault 0 row firstIndex) (rowDivisible firstIndex firstGe) lo
          (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex 0
          (fun i h =>
            listReplaceAtGuardedSlot (0 : Int) (dividesExactly divisor) (dividesExactlyZero divisor)
              (listGetWithDefault 0 row secondIndex) (rowDivisible secondIndex secondGe) lo
              row firstIndex 0 (fun j hj => rowDivisible j hj) i h)
          readIndex loLe
    · exact rowDivisible
  · exact rowDivisible

/-- The within-row column scaled-add preserves guarded row divisibility, when both source and target
columns are at `≥ lo` (the range-guard identity branch returns the hypothesis). -/
theorem rowSlotsDivisibleFromAddScaledWithinRow {divisor : Int} {lo : Nat} (row : IntRow)
    (sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceGe : lo ≤ sourceIndex)
    (rowDivisible : RowSlotsDivisibleByFrom divisor lo row) :
    RowSlotsDivisibleByFrom divisor lo (addScaledEntryWithinRow row sourceIndex targetIndex coefficient) := by
  unfold IntMatrix.addScaledEntryWithinRow
  split
  · exact fun readIndex loLe =>
      listModifyAtGuardedSlot (0 : Int) (dividesExactly divisor) (dividesExactlyZero divisor)
        (fun targetEntry => targetEntry + coefficient * listGetWithDefault 0 row sourceIndex)
        (fun _ isDivisible => dividesExactlyAddScaled coefficient isDivisible (rowDivisible sourceIndex sourceGe))
        lo row targetIndex 0 (fun j hj => rowDivisible j hj) readIndex loLe
  · exact rowDivisible

/-- **`mapAllRows` preserves a guarded row predicate** — when the row transform preserves it and it
holds of the empty row and every original guarded row, it holds of every guarded row after the map.
Pointwise: the in-range read is `transform (old row)`, the past-end read is the empty default. -/
theorem mapAllRowsGuardedRowPred (predicate : IntRow → Prop) (transform : IntRow → IntRow)
    (isEmptyOk : predicate []) (isTransformOk : ∀ row, predicate row → predicate (transform row))
    (lo : Nat) (rows : List IntRow)
    (guarded : ∀ r, lo ≤ r → predicate (listGetWithDefault [] rows r)) :
    ∀ r, lo ≤ r → predicate (listGetWithDefault [] (mapAllRows transform rows) r) := by
  intro r loLeR
  by_cases hRange : r < rows.length
  · rw [listGetWithDefaultMapAllRows transform rows r hRange]
    exact isTransformOk _ (guarded r loLeR)
  · rw [listGetWithDefaultGe [] (mapAllRows transform rows) r
        (by rw [mapAllRowsPreservesLength]; exact Nat.not_lt.1 hRange)]
    exact isEmptyOk

/-! ## The operation-bounded-below decidable check (fully enumerated, propext-clean) -/

/-- Left conjunct of a true boolean conjunction (local; the Homology sibling lives in a disjoint
namespace). -/
theorem boolConjTrueLeft {left right : Bool} (conjTrue : (left && right) = true) : left = true := by
  cases left with
  | true => rfl
  | false => exact conjTrue

/-- Right conjunct of a true boolean conjunction. -/
theorem boolConjTrueRight {left right : Bool} (conjTrue : (left && right) = true) : right = true := by
  cases left with
  | true => exact conjTrue
  | false => exact Bool.noConfusion conjTrue

/-- **The operation is confined to indices `≥ lo`** — swap / transvection require both indices at
`≥ lo`; negation is unconditional (it never mixes a below-`lo` cell into the sub-block).  Fully
enumerated match arms (no wildcard) so the confinement discharge is propext-clean. -/
def opIsBoundedBelow (lo : Nat) : ElementaryOperation → Bool
  | .rowOperation (.swapRows firstIndex secondIndex) =>
      decide (lo ≤ firstIndex) && decide (lo ≤ secondIndex)
  | .rowOperation (.negateRow _) => true
  | .rowOperation (.addRowMultiple sourceIndex targetIndex _) =>
      decide (lo ≤ sourceIndex) && decide (lo ≤ targetIndex)
  | .columnOperation (.swapColumns firstIndex secondIndex) =>
      decide (lo ≤ firstIndex) && decide (lo ≤ secondIndex)
  | .columnOperation (.negateColumn _) => true
  | .columnOperation (.addColumnMultiple sourceIndex targetIndex _) =>
      decide (lo ≤ sourceIndex) && decide (lo ≤ targetIndex)

/-- Every operation in the certificate word is confined to indices `≥ lo`. -/
def allOpsBoundedBelow (lo : Nat) : List ElementaryOperation → Bool
  | [] => true
  | operation :: remaining => opIsBoundedBelow lo operation && allOpsBoundedBelow lo remaining

/-! ## The six windowed single-operation deltas -/

/-- **A single bounded-below row operation preserves windowed divisibility** — swap permutes rows,
negate negates a row (unconditional), transvection scaled-adds a row; each identity guard returns the
hypothesis.  The guarded-slot mirror of `applyRowOperationPreservesEntriesDivisible`. -/
theorem applyRowOperationPreservesEntriesDivisibleWithin {divisor : Int} {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryRowOperation)
    (opBounded : opIsBoundedBelow lo (.rowOperation operation) = true)
    (matrixDivisible : MatrixEntriesDivisibleByWithin divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo (matrix.applyRowOperation operation) := by
  cases operation with
  | swapRows firstIndex secondIndex =>
      have firstGe : lo ≤ firstIndex := of_decide_eq_true (boolConjTrueLeft opBounded)
      have secondGe : lo ≤ secondIndex := of_decide_eq_true (boolConjTrueRight opBounded)
      show MatrixEntriesDivisibleByWithin divisor lo (matrix.swapRows firstIndex secondIndex)
      unfold IntMatrix.swapRows
      split
      · split
        · exact fun readRow loLeRead =>
            listReplaceAtGuardedSlot [] (RowSlotsDivisibleByFrom divisor lo)
              (rowSlotsDivisibleByFromEmpty divisor lo)
              (listGetWithDefault [] matrix.rows firstIndex) (matrixDivisible firstIndex firstGe) lo
              (listReplaceAt matrix.rows firstIndex (listGetWithDefault [] matrix.rows secondIndex))
              secondIndex 0
              (fun innerIndex innerLoLe =>
                listReplaceAtGuardedSlot [] (RowSlotsDivisibleByFrom divisor lo)
                  (rowSlotsDivisibleByFromEmpty divisor lo)
                  (listGetWithDefault [] matrix.rows secondIndex) (matrixDivisible secondIndex secondGe)
                  lo matrix.rows firstIndex 0 (fun slotIndex slotLoLe => matrixDivisible slotIndex slotLoLe)
                  innerIndex innerLoLe)
              readRow loLeRead
        · exact matrixDivisible
      · exact matrixDivisible
  | negateRow rowIndex =>
      show MatrixEntriesDivisibleByWithin divisor lo (matrix.negateRow rowIndex)
      exact fun readRow loLeRead =>
        listModifyAtGuardedSlot [] (RowSlotsDivisibleByFrom divisor lo)
          (rowSlotsDivisibleByFromEmpty divisor lo) (fun row => row.map (fun entry => -entry))
          (fun _ rowDiv => rowSlotsDivisibleFromMapNeg rowDiv) lo matrix.rows rowIndex 0
          (fun slotIndex slotLoLe => matrixDivisible slotIndex slotLoLe) readRow loLeRead
  | addRowMultiple sourceIndex targetIndex coefficient =>
      have sourceGe : lo ≤ sourceIndex := of_decide_eq_true (boolConjTrueLeft opBounded)
      show MatrixEntriesDivisibleByWithin divisor lo
        (matrix.addRowMultiple sourceIndex targetIndex coefficient)
      unfold IntMatrix.addRowMultiple
      split
      · exact matrixDivisible
      · split
        · split
          · exact fun readRow loLeRead =>
              listModifyAtGuardedSlot [] (RowSlotsDivisibleByFrom divisor lo)
                (rowSlotsDivisibleByFromEmpty divisor lo)
                (fun targetRow =>
                  addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
                (fun _ rowDiv =>
                  rowSlotsDivisibleFromAddScaledEntries coefficient (matrixDivisible sourceIndex sourceGe) rowDiv)
                lo matrix.rows targetIndex 0
                (fun slotIndex slotLoLe => matrixDivisible slotIndex slotLoLe) readRow loLeRead
          · exact matrixDivisible
        · exact matrixDivisible

/-- **A single bounded-below column operation preserves windowed divisibility** — swap/negate/
transvection applied row-locally via `mapAllRows`, over the within-row guarded preservers. -/
theorem applyColumnOperationPreservesEntriesDivisibleWithin {divisor : Int} {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryColumnOperation)
    (opBounded : opIsBoundedBelow lo (.columnOperation operation) = true)
    (matrixDivisible : MatrixEntriesDivisibleByWithin divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo (matrix.applyColumnOperation operation) := by
  cases operation with
  | swapColumns firstIndex secondIndex =>
      have firstGe : lo ≤ firstIndex := of_decide_eq_true (boolConjTrueLeft opBounded)
      have secondGe : lo ≤ secondIndex := of_decide_eq_true (boolConjTrueRight opBounded)
      show MatrixEntriesDivisibleByWithin divisor lo (matrix.swapColumns firstIndex secondIndex)
      exact mapAllRowsGuardedRowPred (RowSlotsDivisibleByFrom divisor lo)
        (fun row => swapEntriesWithinRow row firstIndex secondIndex) (rowSlotsDivisibleByFromEmpty divisor lo)
        (fun row rowDiv => rowSlotsDivisibleFromSwapEntries row firstIndex secondIndex firstGe secondGe rowDiv)
        lo matrix.rows matrixDivisible
  | negateColumn colIndex =>
      show MatrixEntriesDivisibleByWithin divisor lo (matrix.negateColumn colIndex)
      exact mapAllRowsGuardedRowPred (RowSlotsDivisibleByFrom divisor lo)
        (fun row => listModifyAt (fun entry => -entry) row colIndex) (rowSlotsDivisibleByFromEmpty divisor lo)
        (fun row rowDiv => rowSlotsDivisibleFromModifyNeg row colIndex rowDiv)
        lo matrix.rows matrixDivisible
  | addColumnMultiple sourceIndex targetIndex coefficient =>
      have sourceGe : lo ≤ sourceIndex := of_decide_eq_true (boolConjTrueLeft opBounded)
      show MatrixEntriesDivisibleByWithin divisor lo
        (matrix.addColumnMultiple sourceIndex targetIndex coefficient)
      unfold IntMatrix.addColumnMultiple
      split
      · exact matrixDivisible
      · exact mapAllRowsGuardedRowPred (RowSlotsDivisibleByFrom divisor lo)
          (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          (rowSlotsDivisibleByFromEmpty divisor lo)
          (fun row rowDiv =>
            rowSlotsDivisibleFromAddScaledWithinRow row sourceIndex targetIndex coefficient sourceGe rowDiv)
          lo matrix.rows matrixDivisible

/-- **A single bounded-below elementary operation preserves windowed divisibility** — dispatch to the
row/column halves. -/
theorem applyOperationPreservesEntriesDivisibleWithin {divisor : Int} {lo : Nat} (matrix : IntMatrix)
    (operation : ElementaryOperation)
    (opBounded : opIsBoundedBelow lo operation = true)
    (matrixDivisible : MatrixEntriesDivisibleByWithin divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo (matrix.applyOperation operation) :=
  match operation, opBounded with
  | .rowOperation rowOp, opBounded =>
      applyRowOperationPreservesEntriesDivisibleWithin matrix rowOp opBounded matrixDivisible
  | .columnOperation colOp, opBounded =>
      applyColumnOperationPreservesEntriesDivisibleWithin matrix colOp opBounded matrixDivisible

/-- **A whole bounded-below certificate word preserves windowed divisibility** — the windowed
ideal-invariance atom: if `divisor` divides every sub-block entry `≥ lo` of `matrix` and every
operation of the word is confined to indices `≥ lo`, it divides every sub-block entry `≥ lo` of
`matrix.applyOperations operations`.  Structural on the word (peeling `allOpsBoundedBelow`). -/
theorem applyOperationsPreservesEntriesDivisibleWithin {divisor : Int} {lo : Nat} :
    ∀ (operations : List ElementaryOperation) (matrix : IntMatrix),
      allOpsBoundedBelow lo operations = true →
      MatrixEntriesDivisibleByWithin divisor lo matrix →
      MatrixEntriesDivisibleByWithin divisor lo (matrix.applyOperations operations)
  | [], _, _, matrixDivisible => matrixDivisible
  | operation :: remainingOperations, matrix, wordBounded, matrixDivisible =>
      applyOperationsPreservesEntriesDivisibleWithin remainingOperations (matrix.applyOperation operation)
        (boolConjTrueRight wordBounded)
        (applyOperationPreservesEntriesDivisibleWithin matrix operation
          (boolConjTrueLeft wordBounded) matrixDivisible)

end FX1Poly.ComputerAlgebra

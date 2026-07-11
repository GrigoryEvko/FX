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

/-! ## The CONFINEMENT discharge — the later-pivot repair operations are bounded below by the pivot

The repair sweep started at `startPivot` emits ONLY operations at indices `≥ startPivot`.  Truth-probed
by `#eval` (a pivot-1 sub-sweep is `allOpsBoundedBelow 1`, and the pivot-0 driver sweep is NOT).  The
chain: every generated letter — move, sign, cross-clear transvections, the Euclid fold — reads/writes
indices `≥ pivotIndex ≥ startPivot`; the cascade and position sweeps thread this structurally. -/

/-- A true boolean conjunction from both conjuncts true. -/
theorem boolAndBothTrue {leftFlag rightFlag : Bool} (leftTrue : leftFlag = true)
    (rightTrue : rightFlag = true) : (leftFlag && rightFlag) = true := by
  subst leftTrue; subst rightTrue; rfl

/-- Confinement passes through a Bool-branching (the cascade's cross-clear terminal vs loop) — both
arms are bounded when the settle word and the settle-plus-loop word are. -/
theorem allOpsBoundedBelowMatchBool (lo : Nat) (flag : Bool)
    (settleOps loopOps : List ElementaryOperation)
    (settleBounded : allOpsBoundedBelow lo settleOps = true)
    (loopBounded : allOpsBoundedBelow lo (settleOps ++ loopOps) = true) :
    allOpsBoundedBelow lo (match flag with | true => settleOps | false => settleOps ++ loopOps) = true := by
  cases flag with
  | true => exact settleBounded
  | false => exact loopBounded

/-- `allOpsBoundedBelow` distributes over word concatenation. -/
theorem allOpsBoundedBelowAppend (lo : Nat) :
    ∀ (leftOps rightOps : List ElementaryOperation),
      allOpsBoundedBelow lo leftOps = true → allOpsBoundedBelow lo rightOps = true →
      allOpsBoundedBelow lo (leftOps ++ rightOps) = true
  | [], _, _, rightTrue => rightTrue
  | _ :: rest, rightOps, leftTrue, rightTrue =>
      boolAndBothTrue (boolConjTrueLeft leftTrue)
        (allOpsBoundedBelowAppend lo rest rightOps (boolConjTrueRight leftTrue) rightTrue)

/-- Confinement is monotone downward in the threshold — ops bounded below `loBig` are bounded below
any smaller `loSmall`. -/
theorem opIsBoundedBelowMonotone (loSmall loBig : Nat) (leMono : loSmall ≤ loBig) :
    ∀ (operation : ElementaryOperation),
      opIsBoundedBelow loBig operation = true → opIsBoundedBelow loSmall operation = true
  | .rowOperation (.swapRows _ _), opBounded =>
      boolAndBothTrue (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueLeft opBounded))))
        (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueRight opBounded))))
  | .rowOperation (.negateRow _), _ => rfl
  | .rowOperation (.addRowMultiple _ _ _), opBounded =>
      boolAndBothTrue (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueLeft opBounded))))
        (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueRight opBounded))))
  | .columnOperation (.swapColumns _ _), opBounded =>
      boolAndBothTrue (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueLeft opBounded))))
        (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueRight opBounded))))
  | .columnOperation (.negateColumn _), _ => rfl
  | .columnOperation (.addColumnMultiple _ _ _), opBounded =>
      boolAndBothTrue (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueLeft opBounded))))
        (decide_eq_true (Nat.le_trans leMono (of_decide_eq_true (boolConjTrueRight opBounded))))

/-- Word confinement is monotone downward in the threshold. -/
theorem allOpsBoundedBelowMonotone (loSmall loBig : Nat) (leMono : loSmall ≤ loBig) :
    ∀ (operations : List ElementaryOperation),
      allOpsBoundedBelow loBig operations = true → allOpsBoundedBelow loSmall operations = true
  | [], _ => rfl
  | operation :: rest, wordBounded =>
      boolAndBothTrue (opIsBoundedBelowMonotone loSmall loBig leMono operation (boolConjTrueLeft wordBounded))
        (allOpsBoundedBelowMonotone loSmall loBig leMono rest (boolConjTrueRight wordBounded))

/-- The row transvection letter is bounded below `lo` when both its rows are. -/
theorem opBoundedBelowAddRow (lo sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceGe : lo ≤ sourceIndex) (targetGe : lo ≤ targetIndex) :
    opIsBoundedBelow lo (.rowOperation (.addRowMultiple sourceIndex targetIndex coefficient)) = true :=
  boolAndBothTrue (decide_eq_true sourceGe) (decide_eq_true targetGe)

/-- The column transvection letter is bounded below `lo` when both its columns are. -/
theorem opBoundedBelowAddColumn (lo sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceGe : lo ≤ sourceIndex) (targetGe : lo ≤ targetIndex) :
    opIsBoundedBelow lo (.columnOperation (.addColumnMultiple sourceIndex targetIndex coefficient)) = true :=
  boolAndBothTrue (decide_eq_true sourceGe) (decide_eq_true targetGe)

/-- The clear-column-below word (row transvections `pivotIndex → rowStart, rowStart+1, …`) is bounded
below `lo` when `lo ≤ pivotIndex` and `lo ≤ rowStart`.  Structural on the step count. -/
theorem smithClearColumnBelowStepsBoundedBelow (matrix : IntMatrix) (pivotIndex lo : Nat)
    (pivotGe : lo ≤ pivotIndex) :
    ∀ (stepCount rowStart : Nat), lo ≤ rowStart →
      allOpsBoundedBelow lo ((smithClearColumnBelowSteps matrix pivotIndex stepCount rowStart).map
        ElementaryOperation.rowOperation) = true
  | 0, _, _ => rfl
  | stepCount + 1, rowStart, rowGe =>
      boolAndBothTrue (opBoundedBelowAddRow lo pivotIndex rowStart _ pivotGe rowGe)
        (smithClearColumnBelowStepsBoundedBelow matrix pivotIndex lo pivotGe stepCount (rowStart + 1)
          (Nat.le_trans rowGe (Nat.le_succ rowStart)))

/-- The clear-row-right word (column transvections `pivotIndex → colStart, colStart+1, …`) is bounded
below `lo` when `lo ≤ pivotIndex` and `lo ≤ colStart`.  Structural on the step count. -/
theorem smithClearRowRightStepsBoundedBelow (matrix : IntMatrix) (pivotIndex lo : Nat)
    (pivotGe : lo ≤ pivotIndex) :
    ∀ (stepCount colStart : Nat), lo ≤ colStart →
      allOpsBoundedBelow lo ((smithClearRowRightSteps matrix pivotIndex stepCount colStart).map
        ElementaryOperation.columnOperation) = true
  | 0, _, _ => rfl
  | stepCount + 1, colStart, colGe =>
      boolAndBothTrue (opBoundedBelowAddColumn lo pivotIndex colStart _ pivotGe colGe)
        (smithClearRowRightStepsBoundedBelow matrix pivotIndex lo pivotGe stepCount (colStart + 1)
          (Nat.le_trans colGe (Nat.le_succ colStart)))

/-- The move-to-pivot word (a row swap and a column swap into the pivot) is bounded below `lo` when the
pivot and the found position are at `≥ lo`. -/
theorem smithMoveToPivotOpsBoundedBelow (lo pivotIndex foundRow foundCol : Nat)
    (pivotGe : lo ≤ pivotIndex) (foundRowGe : lo ≤ foundRow) (foundColGe : lo ≤ foundCol) :
    allOpsBoundedBelow lo (smithMoveToPivotOps pivotIndex foundRow foundCol) = true :=
  boolAndBothTrue (boolAndBothTrue (decide_eq_true pivotGe) (decide_eq_true foundRowGe))
    (boolAndBothTrue (boolAndBothTrue (decide_eq_true pivotGe) (decide_eq_true foundColGe)) rfl)

/-- The sign-normalise word (an optional pivot-row negation) is bounded below any `lo` (negation is
unconditional; the empty word trivially). -/
theorem smithSignNormalizeOpsBoundedBelow (matrix : IntMatrix) (lo pivotIndex : Nat) :
    allOpsBoundedBelow lo (smithSignNormalizeOps matrix pivotIndex) = true := by
  unfold smithSignNormalizeOps
  split
  · rfl
  · rfl

/-- **The Euclid cascade word is bounded below the pivot** — every letter (move, sign, cross-clear
transvections, and the recursive loop) is at indices `≥ pivotIndex ≥ lo`.  Structural on the inner
fuel; the found position sits at `≥ pivotIndex` by `smithFindMinAbsInMinorFoundInRange`. -/
theorem smithCascadeSweepBoundedBelow (lo : Nat) :
    ∀ (innerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsBoundedBelow lo (smithCascadeSweep innerFuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | innerFuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      rw [smithCascadeSweepSucc]
      split
      · rfl
      · rename_i foundRow foundCol hFind
        have foundRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
          foundRow foundCol pivotRowInRange pivotColInRange hFind
        have loLeSucc : lo ≤ pivotIndex + 1 := Nat.le_trans pivotGe (Nat.le_succ pivotIndex)
        have moveBounded : allOpsBoundedBelow lo (smithMoveToPivotOps pivotIndex foundRow foundCol) = true :=
          smithMoveToPivotOpsBoundedBelow lo pivotIndex foundRow foundCol pivotGe
            (Nat.le_trans pivotGe foundRange.1) (Nat.le_trans pivotGe foundRange.2.2.1)
        exact allOpsBoundedBelowMatchBool lo _ _ _
          (allOpsBoundedBelowAppend lo _ _
            (allOpsBoundedBelowAppend lo _ _
              (allOpsBoundedBelowAppend lo _ _ moveBounded
                (smithSignNormalizeOpsBoundedBelow _ lo pivotIndex))
              (smithClearColumnBelowStepsBoundedBelow _ pivotIndex lo pivotGe _ (pivotIndex + 1) loLeSucc))
            (smithClearRowRightStepsBoundedBelow _ pivotIndex lo pivotGe _ (pivotIndex + 1) loLeSucc))
          (allOpsBoundedBelowAppend lo _ _
            (allOpsBoundedBelowAppend lo _ _
              (allOpsBoundedBelowAppend lo _ _
                (allOpsBoundedBelowAppend lo _ _ moveBounded
                  (smithSignNormalizeOpsBoundedBelow _ lo pivotIndex))
                (smithClearColumnBelowStepsBoundedBelow _ pivotIndex lo pivotGe _ (pivotIndex + 1) loLeSucc))
              (smithClearRowRightStepsBoundedBelow _ pivotIndex lo pivotGe _ (pivotIndex + 1) loLeSucc))
            (smithCascadeSweepBoundedBelow lo innerFuel _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe))

/-- **The clearing position sweep word is bounded below the pivot** — the `none`-branch cascade, and
the `some`-branch fold+cascade loop, all emit letters at indices `≥ pivotIndex ≥ lo`.  Structural on
the fuel; the fold target sits at `> pivotIndex` by `smithFindNonDividingLaterDiagonalSomeInRange`. -/
theorem smithRepairPositionSweepClearingBoundedBelow (lo : Nat) :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsBoundedBelow lo (smithRepairPositionSweepClearing fuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      rw [smithRepairPositionSweepClearingSucc]
      split
      · exact smithCascadeSweepBoundedBelow lo _ matrix pivotIndex height width
          pivotRowInRange pivotColInRange pivotGe
      · rename_i foundPos hFind
        have foundRange := smithFindNonDividingLaterDiagonalSomeInRange matrix pivotIndex height width
          foundPos pivotRowInRange pivotColInRange hFind
        have foundGe : lo ≤ foundPos := Nat.le_of_lt (Nat.lt_of_le_of_lt pivotGe foundRange.1)
        have foldBounded : allOpsBoundedBelow lo
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ] = true :=
          boolAndBothTrue (opBoundedBelowAddRow lo foundPos pivotIndex 1 foundGe pivotGe) rfl
        exact allOpsBoundedBelowAppend lo _ _
          (allOpsBoundedBelowAppend lo _ _ foldBounded
            (smithCascadeSweepBoundedBelow lo _ _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe))
          (smithRepairPositionSweepClearingBoundedBelow lo fuel _ pivotIndex height width
            pivotRowInRange pivotColInRange pivotGe)

/-- **The top-down clearing repair sweep is bounded below the start pivot** — every operation the
sweep started at `startPivot` emits is confined to indices `≥ startPivot`.  Structural on the outer
fuel; each pivot `q ≥ startPivot` emits a position sweep bounded below `startPivot` (via the
position-sweep confinement with `lo := startPivot ≤ q`), and the tail rides the IH.  The confinement
discharge the windowed cross-pivot preserve reads off (truth-probed by `#eval`). -/
theorem smithDivisibilityRepairSweepClearingOpsBoundedBelow :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (startPivot height width : Nat),
      allOpsBoundedBelow startPivot
        (smithDivisibilityRepairSweepClearing outerFuel matrix startPivot height width) = true
  | 0, _, _, _, _ => rfl
  | outerFuel + 1, matrix, startPivot, height, width => by
      show allOpsBoundedBelow startPivot
        (if startPivot + 1 ≤ Nat.min height width then
            smithRepairPositionSweepClearing (smithMinorAbsSum matrix startPivot height width) matrix
                startPivot height width
              ++ smithDivisibilityRepairSweepClearing outerFuel
                  (matrix.applyOperations
                    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix startPivot height width)
                      matrix startPivot height width))
                  (startPivot + 1) height width
           else []) = true
      split
      · rename_i guardTrue
        have pivotRowInRange : startPivot < height := Nat.le_trans guardTrue (natMinLeLeft height width)
        have pivotColInRange : startPivot < width := Nat.le_trans guardTrue (natMinLeRight height width)
        exact allOpsBoundedBelowAppend startPivot _ _
          (smithRepairPositionSweepClearingBoundedBelow startPivot _ matrix startPivot height width
            pivotRowInRange pivotColInRange (Nat.le_refl startPivot))
          (allOpsBoundedBelowMonotone startPivot (startPivot + 1) (Nat.le_succ startPivot) _
            (smithDivisibilityRepairSweepClearingOpsBoundedBelow outerFuel _ (startPivot + 1) height width))
      · rfl

/-! ## The windowed sub-block predicate yields the invariant-factor chain (Node 3 read-off)

The chain `SmithChainPrefix` reads only the diagonal.  A prefix in which every settled `d_earlier`
divides its OWN `[earlier+1, ·) × [earlier+1, ·)` sub-block yields the chain directly: every later
diagonal `d_later` (`later > earlier`) sits at `(later, later)` inside that sub-block, so
`d_earlier ∣ d_later`; the `later = earlier` case is the trivial self-divisibility.  This is the exact
second conjunct of the Node-3 motive `ChainWindowedThroughPivots` — the windowed preserve tower
propagates it, the confinement bounds the propagating ops, and the ONLY residual is the ESTABLISH seed
(each pivot's cascade LANDS a `d_p`-divisible sub-block; the gcd-ideal-invariance wall). -/

/-- **The windowed diagonal chain** — every settled prefix diagonal `d_earlier` divides its own
`[earlier+1, ·)` sub-block.  The (a) invariant that DIRECTLY implies `SmithChainPrefix`, and (b) is
preserved by the confined later-pivot repair ops via the windowed tower. -/
def MatrixDiagonalChainWindowed (matrix : IntMatrix) (pivotIndex : Nat) : Prop :=
  ∀ earlierIndex, earlierIndex < pivotIndex →
    MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt earlierIndex) (earlierIndex + 1) matrix

/-- **The windowed diagonal chain yields `SmithChainPrefix`** — the Node-3 read-off.  For
`earlier < later`, the later diagonal `(later, later)` lies in `d_earlier`'s sub-block
(`earlier + 1 ≤ later`), so it is `d_earlier`-divisible; the `earlier = later` case is `d ∣ d`. -/
theorem smithChainPrefixOfDiagonalChainWindowed (matrix : IntMatrix) (pivotIndex height width : Nat)
    (windowed : MatrixDiagonalChainWindowed matrix pivotIndex) :
    SmithChainPrefix matrix pivotIndex height width := by
  intro earlierIndex earlierLt laterIndex earlierLeLater _laterLtMin
  cases Nat.eq_or_lt_of_le earlierLeLater with
  | inl earlierEqLater =>
      rw [← earlierEqLater]
      exact ⟨1, (intMulOne (matrix.diagonalEntryAt earlierIndex)).symm⟩
  | inr earlierLtLater =>
      exact matrixEntriesDivisibleByWithinAt (windowed earlierIndex earlierLt)
        laterIndex laterIndex earlierLtLater earlierLtLater

/-! ## The single surviving wall, named precisely (H2-SMITH r19, B4/B5, #2261)

`repairChainHolds` (the corrected driver's sole residual, consumed by the SHIPPED
`smithReduceCompleteDriverOfChain`) is reduced by r19 to EXACTLY ONE structural obligation: the
per-pivot ESTABLISH seed below.  The reduction chain, all zero-axiom shipped this round:

  1. `smithChainPrefixOfDiagonalChainWindowed` — the windowed diagonal chain yields `SmithChainPrefix`
     (read-off, §Node 3).
  2. `applyOperationsPreservesEntriesDivisibleWithin` — the windowed tower PROPAGATES each settled
     `d_earlier`'s sub-block divisibility across any word confined to indices `≥ earlier + 1` (§Node 1).
  3. `smithDivisibilityRepairSweepClearingOpsBoundedBelow` — the later-pivot repair ops ARE so
     confined (§Node 1 confinement, truth-probed).

What remains — the ESTABLISH SEED `SmithCascadeLandsDivisibleSubBlock` — is the statement that each
pivot's clearing position sweep LANDS a `d_p`-divisible sub-block `≥ p+1`.  Semantically this is the
gcd-ideal invariance (the gcd of the pivot minor is preserved by the unimodular cascade, and the
cascade lands that gcd at the pivot), which the shipped cascade properties (cross-clear, low-low,
band-zero) do NOT yet supply — the cascade's interior is transient, guaranteed cross-clear but not
divisible-interior.  This is the genuine r20 arc (the recon's standing POLE-A-adjacent node); r19
reduces to it and names it, WITHOUT fabricating it.  Building it plus the cross-pivot carrier (a
sweep-split + the `d_earlier` low-low freeze threading the motive `ChainWindowedThroughPivots`) closes
`repairChainHolds` and, via `smithReduceCompleteDriverOfChain`, flips
`SmithReduceCompleteDriverStatement` to unconditionally inhabited. -/

/-- **The ESTABLISH seed — the single surviving `repairChainHolds` residual.**  After pivot
`pivotIndex`'s clearing position sweep, the landed pivot diagonal `d_p` divides the WHOLE sub-block at
indices `≥ pivotIndex + 1` (off-diagonals included, not merely the later diagonals the shipped
`smithFindNonDividingLaterDiagonalNoneDividesAll` supplies).  The gcd-ideal-invariance content the
cascade does not yet prove; the r20 arc onto which r19 reduces `repairChainHolds`. -/
def SmithCascadeLandsDivisibleSubBlock : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (pivotIndex + 1)
      (matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))

end FX1Poly.ComputerAlgebra

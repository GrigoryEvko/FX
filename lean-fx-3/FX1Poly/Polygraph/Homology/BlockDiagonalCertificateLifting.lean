import FX1Poly.ComputerAlgebra.IntMatrix
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore

/-! # FX1Poly/Polygraph/Homology/BlockDiagonalCertificateLifting — the fully cert-free block-lifting
    (the H2-SQUIER-NOGO r5 payment on the r4 wall, #2139)

The r4 END-TO-END homology-preservation theorems left ONE residual: the connection of the generic recipe
certificate to the ACTUAL expanded boundary stayed a per-instance `rfl` (`…RecipeProducesUnitLast`),
because deriving the reduced diagonal generically for an ARBITRARY base certificate needs the
BLOCK-LIFTING lemma — an induction over the base certificate's operation list proving each unimodular op
acts on the block-diagonal `[[A | 0]; [0 | +1]]` exactly as on `A`, with the fresh row/column inert.  The
r4 ledger walled this because its entry-level matrix-operation lemmas were said to live only in
`ComputerAlgebra/LinearAlgebra/SmithNormalForm.lean` / `SmithCascadeTermination.lean`, which the Homology
lane must NOT import.  This file RE-DERIVES those entry-level lemmas in-lane against the `IntMatrix`
primitives ONLY (`listReplaceAt` / `listModifyAt` / `mapAllRows` / `addScaledEntries`), and closes the
block-lifting:

  * `blockDiagWithFreshUnit A width` — the block-diagonal `[[A | 0]; [0 | +1]]` (extend each `A`-row by a
    trailing `0`; append the fresh unit row `replicate width 0 ++ [1]`);
  * six SINGLE-OP block-inertness lemmas — one per elementary operation (`blockDiag{Swap,Negate,
    AddRowMultiple}RowInert`, `blockDiag{SwapColumns,NegateColumn,AddColumnMultiple}Inert`) — each a
    structural `List`/`Nat`/`Int` equality, no propext;
  * `opIsBounded` / `allOpsBounded` — the decidable boundedness side-condition (fully-enumerated match
    arms, propext-clean) the r5 recon adjudicated as LOAD-BEARING and NOT derivable from
    `reducesToSmithForm` (a base cert may contain a boundary op that is a no-op on `A` but ACTIVE on the
    expansion);
  * `applyOperationBlockInert` (the single-op combiner) + `applyOperationPreservesRect` (rectangularity
    carried through the induction);
  * ★★ `liftedBaseCertAgreesOnBlock` — THE block-lifting induction: for any rectangular base and any
    bounded certificate word, `(blockDiag A width).applyOperations ops = blockDiag (A.applyOperations ops)
    width`;
  * the recipe corollary `blockRecipeReducesToBlockDiag`, `applyOperationsAppend`, and the diagonal
    read-off (`blockDiagDiagonalBelow`, `blockDiagDiagonalAtFreshSquare`) the homology reader consumes.

The clearing wrapper (`expandedD2 → blockDiag A` via `clearingOps ++ [negateColumn width]`) stays the
per-instance connector: its generic form needs the abelianization structure of the expansion (the r6
bill).  Everything here is generic over the base matrix and certificate.

## Zero-axiom design decisions

  * Every match is on non-indexed inductives (`List`, `Prod`, `Nat`, `Int`, `Bool`, and the `IntMatrix`
    operation alphabet); no `Fin` elimination, no indexed-match propext trap.
  * `opIsBounded` uses fully-enumerated match arms (no wildcard) so the discharge is propext-clean; the
    Bool conjuncts are peeled by the structural `boolAndTrueLeft` / `boolAndTrueRight`, the `decide`
    conjuncts by core `of_decide_eq_true` (axiom-free).
  * `Nat` index arithmetic via the shared `natLeOfSuccLeSucc` peel and `congrArg Nat.pred` for successor
    injectivity — never `omega` / `add_mul` / `le_max`.
  * `Int` bookkeeping via `intMulZero` / `intAddZero` only; `-0 = 0` by `decide` on the literal.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/BlockDiagonalCertificateLifting.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.ComputerAlgebra.IntMatrix

/-! ## Phase 1: generic list infrastructure -/

theorem mapAllRowsLength (transform : IntRow → IntRow) :
    ∀ (rows : List IntRow), (mapAllRows transform rows).length = rows.length
  | [] => rfl
  | _ :: tail => congrArg (· + 1) (mapAllRowsLength transform tail)

theorem mapAllRowsAppend (transform : IntRow → IntRow) :
    ∀ (leftRows rightRows : List IntRow),
      mapAllRows transform (leftRows ++ rightRows)
        = mapAllRows transform leftRows ++ mapAllRows transform rightRows
  | [], _ => rfl
  | row :: tail, rightRows =>
      congrArg (transform row :: ·) (mapAllRowsAppend transform tail rightRows)

theorem listReplaceAtLength {Entry : Type} :
    ∀ (entries : List Entry) (index : Nat) (newEntry : Entry),
      (listReplaceAt entries index newEntry).length = entries.length
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: tail, index + 1, newEntry =>
      congrArg (· + 1) (listReplaceAtLength tail index newEntry)

theorem listReplaceAtAppendLeft {Entry : Type} :
    ∀ (leftEntries rightEntries : List Entry) (index : Nat) (newEntry : Entry),
      index < leftEntries.length →
      listReplaceAt (leftEntries ++ rightEntries) index newEntry
        = listReplaceAt leftEntries index newEntry ++ rightEntries
  | [], _, index, _, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _, _ => rfl
  | head :: tail, rightEntries, index + 1, newEntry, isBelow =>
      congrArg (head :: ·)
        (listReplaceAtAppendLeft tail rightEntries index newEntry (natLeOfSuccLeSucc isBelow))

theorem listModifyAtAppendLeft {Entry : Type} (transform : Entry → Entry) :
    ∀ (leftEntries rightEntries : List Entry) (index : Nat),
      index < leftEntries.length →
      listModifyAt transform (leftEntries ++ rightEntries) index
        = listModifyAt transform leftEntries index ++ rightEntries
  | [], _, index, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | head :: tail, rightEntries, index + 1, isBelow =>
      congrArg (head :: ·)
        (listModifyAtAppendLeft transform tail rightEntries index (natLeOfSuccLeSucc isBelow))

theorem listReplaceAtMapAllRows (transform : IntRow → IntRow) :
    ∀ (rows : List IntRow) (index : Nat) (newRow : IntRow),
      listReplaceAt (mapAllRows transform rows) index (transform newRow)
        = mapAllRows transform (listReplaceAt rows index newRow)
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | head :: tail, index + 1, newRow =>
      congrArg (transform head :: ·) (listReplaceAtMapAllRows transform tail index newRow)

/-- reading below the left length ignores the appended tail. -/
theorem listGetWithDefaultAppendLeft' {Entry : Type} (defaultEntry : Entry) :
    ∀ (leftEntries rightEntries : List Entry) (index : Nat), index < leftEntries.length →
      listGetWithDefault defaultEntry (leftEntries ++ rightEntries) index
        = listGetWithDefault defaultEntry leftEntries index
  | [], _, index, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: tail, rightEntries, index + 1, isBelow =>
      listGetWithDefaultAppendLeft' defaultEntry tail rightEntries index (natLeOfSuccLeSucc isBelow)

/-- reading index i < length of mapAllRows returns the transform of the i-th row (both defaults `[]`). -/
theorem getMapAllRowsInRange (transform : IntRow → IntRow) :
    ∀ (rows : List IntRow) (index : Nat), index < rows.length →
      listGetWithDefault [] (mapAllRows transform rows) index
        = transform (listGetWithDefault [] rows index)
  | [], index, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: tail, index + 1, isBelow =>
      getMapAllRowsInRange transform tail index (natLeOfSuccLeSucc isBelow)

/-! ## Phase 2: the block constructor + row-operation inertness -/

/-- Extend one row by a trailing `0` (the fresh column, zero in every old row). -/
def extendRow (row : IntRow) : IntRow := row ++ [0]

/-- The fresh generator row: `freshCols` zeros then the `+1` pivot. -/
def freshUnitRow (freshCols : Nat) : IntRow := List.replicate freshCols 0 ++ [1]

/-- The block-diagonal `[[A | 0]; [0 | +1]]`: extend each `A`-row by a trailing zero, append the fresh
unit row. -/
def blockDiagWithFreshUnit (matrix : IntMatrix) (freshCols : Nat) : IntMatrix :=
  ⟨mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]⟩

/-- Rows of a rectangular matrix have the declared width at every in-range index. -/
theorem rowsAllHaveWidthGet (width : Nat) :
    ∀ (rows : List IntRow) (index : Nat), rowsAllHaveWidth width rows → index < rows.length →
      (listGetWithDefault [] rows index).length = width
  | [], index, _, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, 0, widthPair, _ => widthPair.left
  | _ :: tail, index + 1, widthPair, isBelow =>
      rowsAllHaveWidthGet width tail index widthPair.right (natLeOfSuccLeSucc isBelow)

/-- `addScaledEntries` distributes over an append when the source prefixes match in length. -/
theorem addScaledEntriesAppend (coefficient : Int) :
    ∀ (sourceLeft targetLeft sourceRight targetRight : IntRow),
      sourceLeft.length = targetLeft.length →
      addScaledEntries coefficient (sourceLeft ++ sourceRight) (targetLeft ++ targetRight)
        = addScaledEntries coefficient sourceLeft targetLeft
            ++ addScaledEntries coefficient sourceRight targetRight
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, lengthEq => Nat.noConfusion lengthEq
  | _ :: _, [], _, _, lengthEq => Nat.noConfusion lengthEq
  | sourceEntry :: sourceRest, targetEntry :: targetRest, sourceRight, targetRight, lengthEq =>
      congrArg ((targetEntry + coefficient * sourceEntry) :: ·)
        (addScaledEntriesAppend coefficient sourceRest targetRest sourceRight targetRight
          (congrArg Nat.pred lengthEq))

/-- Negation commutes with the row extension (`-0 = 0`). -/
theorem mapNegExtendRow :
    ∀ (row : IntRow), (extendRow row).map (fun entry => -entry) = extendRow (row.map (fun entry => -entry))
  | [] => rfl
  | entry :: rest => congrArg ((-entry) :: ·) (mapNegExtendRow rest)

/-- `addScaledEntries` intertwines with the row extension when both operand rows have width `width`. -/
theorem addScaledEntriesExtendRow (coefficient : Int) (sourceRow : IntRow) (width : Nat)
    (sourceWidth : sourceRow.length = width) :
    ∀ (targetRow : IntRow), targetRow.length = width →
      addScaledEntries coefficient (extendRow sourceRow) (extendRow targetRow)
        = extendRow (addScaledEntries coefficient sourceRow targetRow) := by
  intro targetRow targetWidth
  show addScaledEntries coefficient (sourceRow ++ [0]) (targetRow ++ [0])
    = addScaledEntries coefficient sourceRow targetRow ++ [0]
  rw [addScaledEntriesAppend coefficient sourceRow targetRow [0] [0]
        (sourceWidth.trans targetWidth.symm)]
  show addScaledEntries coefficient sourceRow targetRow ++ [(0 : Int) + coefficient * 0]
    = addScaledEntries coefficient sourceRow targetRow ++ [0]
  rw [intMulZero coefficient, intAddZero]

/-- `listModifyAt` over a `mapAllRows`, where the two modify-transforms intertwine on width-`width`
rows and every row in the list has width `width`. -/
theorem listModifyAtMapAllRowsUnderWidth (rowTransform modifyOnBlock modifyOnBase : IntRow → IntRow)
    (width : Nat)
    (intertwine : ∀ row, row.length = width →
      modifyOnBlock (rowTransform row) = rowTransform (modifyOnBase row)) :
    ∀ (rows : List IntRow) (index : Nat), rowsAllHaveWidth width rows →
      listModifyAt modifyOnBlock (mapAllRows rowTransform rows) index
        = mapAllRows rowTransform (listModifyAt modifyOnBase rows index)
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | head :: _, 0, widthPair => congrArg (· :: _) (intertwine head widthPair.left)
  | head :: tail, index + 1, widthPair =>
      congrArg (rowTransform head :: ·)
        (listModifyAtMapAllRowsUnderWidth rowTransform modifyOnBlock modifyOnBase width intertwine
          tail index widthPair.right)

/-! ### The three row-operation inertness lemmas -/

/-- `negateRow` acts on the block exactly as on the base (fresh row inert, trailing zero preserved). -/
theorem blockDiagNegateRowInert (matrix : IntMatrix) (freshCols height width : Nat)
    (rect : matrix.IsRectangular height width) (rowIndex : Nat) (rowBelow : rowIndex < height) :
    (blockDiagWithFreshUnit matrix freshCols).negateRow rowIndex
      = blockDiagWithFreshUnit (matrix.negateRow rowIndex) freshCols := by
  have lengthEq : matrix.rows.length = height := rect.left
  show IntMatrix.mk
      (listModifyAt (fun row => row.map (fun entry => -entry))
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]) rowIndex)
    = ⟨mapAllRows extendRow (listModifyAt (fun row => row.map (fun entry => -entry)) matrix.rows rowIndex)
        ++ [freshUnitRow freshCols]⟩
  have indexBelow : rowIndex < (mapAllRows extendRow matrix.rows).length := by
    rw [mapAllRowsLength, lengthEq]; exact rowBelow
  rw [listModifyAtAppendLeft _ (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols] rowIndex
        indexBelow]
  exact congrArg (fun rowList => IntMatrix.mk (rowList ++ [freshUnitRow freshCols]))
    (listModifyAtMapAllRowsUnderWidth extendRow (fun row => row.map (fun entry => -entry))
      (fun row => row.map (fun entry => -entry)) width
      (fun row _ => mapNegExtendRow row) matrix.rows rowIndex rect.right)

/-- `(xs ++ [y]).length = xs.length + 1`. -/
theorem appendSingletonLength {Entry : Type} (extra : Entry) :
    ∀ (entries : List Entry), (entries ++ [extra]).length = entries.length + 1
  | [] => rfl
  | _ :: tail => congrArg (· + 1) (appendSingletonLength extra tail)

/-- The block-diagonal has `height + 1` rows. -/
theorem blockDiagRowsLength (matrix : IntMatrix) (freshCols height width : Nat)
    (rect : matrix.IsRectangular height width) :
    (blockDiagWithFreshUnit matrix freshCols).rows.length = height + 1 := by
  show (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]).length = height + 1
  rw [appendSingletonLength, mapAllRowsLength, rect.left]

/-- Reducing `swapRows` when both indices are in range. -/
theorem swapRowsOfBounded (matrix : IntMatrix) (firstIndex secondIndex : Nat)
    (firstBelow : firstIndex < matrix.rows.length) (secondBelow : secondIndex < matrix.rows.length) :
    matrix.swapRows firstIndex secondIndex
      = ⟨listReplaceAt (listReplaceAt matrix.rows firstIndex
            (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
            (listGetWithDefault [] matrix.rows firstIndex)⟩ := by
  show (if firstIndex < matrix.rows.length then
      (if secondIndex < matrix.rows.length then
        IntMatrix.mk (listReplaceAt (listReplaceAt matrix.rows firstIndex
            (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
            (listGetWithDefault [] matrix.rows firstIndex))
      else matrix) else matrix) = _
  rw [if_pos firstBelow, if_pos secondBelow]

/-- Reducing `addRowMultiple` when the source equals the target (identity). -/
theorem addRowMultipleSelfIdent (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) (indicesEq : sourceIndex = targetIndex) :
    matrix.addRowMultiple sourceIndex targetIndex coefficient = matrix := by
  show (if sourceIndex = targetIndex then matrix else _) = matrix
  rw [if_pos indicesEq]

/-- Reducing `addRowMultiple` when the source differs from the target and both are in range. -/
theorem addRowMultipleOfBounded (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) (indicesDistinct : sourceIndex ≠ targetIndex)
    (sourceBelow : sourceIndex < matrix.rows.length)
    (targetBelow : targetIndex < matrix.rows.length) :
    matrix.addRowMultiple sourceIndex targetIndex coefficient
      = ⟨listModifyAt (fun targetRow =>
          addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
          matrix.rows targetIndex⟩ := by
  show (if sourceIndex = targetIndex then matrix else
      (if sourceIndex < matrix.rows.length then
        (if targetIndex < matrix.rows.length then
          IntMatrix.mk (listModifyAt (fun targetRow =>
            addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
            matrix.rows targetIndex)
        else matrix) else matrix)) = _
  rw [if_neg indicesDistinct, if_pos sourceBelow, if_pos targetBelow]

/-- `swapRows` acts on the block exactly as on the base (fresh row inert; bounded indices). -/
theorem blockDiagSwapRowsInert (matrix : IntMatrix) (freshCols height width : Nat)
    (rect : matrix.IsRectangular height width) (firstIndex secondIndex : Nat)
    (firstBelow : firstIndex < height) (secondBelow : secondIndex < height) :
    (blockDiagWithFreshUnit matrix freshCols).swapRows firstIndex secondIndex
      = blockDiagWithFreshUnit (matrix.swapRows firstIndex secondIndex) freshCols := by
  have lenEq : matrix.rows.length = height := rect.left
  have mapLen : (mapAllRows extendRow matrix.rows).length = height := by
    rw [mapAllRowsLength, lenEq]
  have firstBase : firstIndex < matrix.rows.length := lenEq ▸ firstBelow
  have secondBase : secondIndex < matrix.rows.length := lenEq ▸ secondBelow
  have firstMap : firstIndex < (mapAllRows extendRow matrix.rows).length := mapLen ▸ firstBelow
  have secondMap : secondIndex < (mapAllRows extendRow matrix.rows).length := mapLen ▸ secondBelow
  have firstBlock : firstIndex < (blockDiagWithFreshUnit matrix freshCols).rows.length := by
    rw [blockDiagRowsLength matrix freshCols height width rect]; exact Nat.le.step firstBelow
  have secondBlock : secondIndex < (blockDiagWithFreshUnit matrix freshCols).rows.length := by
    rw [blockDiagRowsLength matrix freshCols height width rect]; exact Nat.le.step secondBelow
  rw [swapRowsOfBounded (blockDiagWithFreshUnit matrix freshCols) firstIndex secondIndex
        firstBlock secondBlock,
      swapRowsOfBounded matrix firstIndex secondIndex firstBase secondBase]
  show IntMatrix.mk (listReplaceAt (listReplaceAt
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]) firstIndex
        (listGetWithDefault [] (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]) secondIndex))
        secondIndex
        (listGetWithDefault [] (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]) firstIndex))
    = ⟨mapAllRows extendRow (listReplaceAt (listReplaceAt matrix.rows firstIndex
        (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
        (listGetWithDefault [] matrix.rows firstIndex)) ++ [freshUnitRow freshCols]⟩
  rw [listGetWithDefaultAppendLeft' [] (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols]
        secondIndex secondMap,
      getMapAllRowsInRange extendRow matrix.rows secondIndex secondBase,
      listGetWithDefaultAppendLeft' [] (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols]
        firstIndex firstMap,
      getMapAllRowsInRange extendRow matrix.rows firstIndex firstBase,
      listReplaceAtAppendLeft (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols] firstIndex
        (extendRow (listGetWithDefault [] matrix.rows secondIndex)) firstMap,
      listReplaceAtMapAllRows extendRow matrix.rows firstIndex
        (listGetWithDefault [] matrix.rows secondIndex),
      listReplaceAtAppendLeft (mapAllRows extendRow (listReplaceAt matrix.rows firstIndex
          (listGetWithDefault [] matrix.rows secondIndex))) [freshUnitRow freshCols] secondIndex
        (extendRow (listGetWithDefault [] matrix.rows firstIndex))
        (by rw [mapAllRowsLength, listReplaceAtLength]; exact secondBase),
      listReplaceAtMapAllRows extendRow (listReplaceAt matrix.rows firstIndex
          (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
        (listGetWithDefault [] matrix.rows firstIndex)]

/-- `addRowMultiple` acts on the block exactly as on the base (fresh row inert; bounded indices). -/
theorem blockDiagAddRowMultipleInert (matrix : IntMatrix) (freshCols height width : Nat)
    (rect : matrix.IsRectangular height width) (sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceBelow : sourceIndex < height) (targetBelow : targetIndex < height) :
    (blockDiagWithFreshUnit matrix freshCols).addRowMultiple sourceIndex targetIndex coefficient
      = blockDiagWithFreshUnit (matrix.addRowMultiple sourceIndex targetIndex coefficient) freshCols := by
  have lenEq : matrix.rows.length = height := rect.left
  have mapLen : (mapAllRows extendRow matrix.rows).length = height := by rw [mapAllRowsLength, lenEq]
  cases Nat.decEq sourceIndex targetIndex with
  | isTrue indicesEq =>
      rw [addRowMultipleSelfIdent (blockDiagWithFreshUnit matrix freshCols) sourceIndex targetIndex
            coefficient indicesEq,
          addRowMultipleSelfIdent matrix sourceIndex targetIndex coefficient indicesEq]
  | isFalse indicesDistinct =>
      have sourceBase : sourceIndex < matrix.rows.length := lenEq ▸ sourceBelow
      have targetBase : targetIndex < matrix.rows.length := lenEq ▸ targetBelow
      have sourceMap : sourceIndex < (mapAllRows extendRow matrix.rows).length := mapLen ▸ sourceBelow
      have targetMap : targetIndex < (mapAllRows extendRow matrix.rows).length := mapLen ▸ targetBelow
      have sourceBlock : sourceIndex < (blockDiagWithFreshUnit matrix freshCols).rows.length := by
        rw [blockDiagRowsLength matrix freshCols height width rect]; exact Nat.le.step sourceBelow
      have targetBlock : targetIndex < (blockDiagWithFreshUnit matrix freshCols).rows.length := by
        rw [blockDiagRowsLength matrix freshCols height width rect]; exact Nat.le.step targetBelow
      have sourceWidth : (listGetWithDefault [] matrix.rows sourceIndex).length = width :=
        rowsAllHaveWidthGet width matrix.rows sourceIndex rect.right sourceBase
      rw [addRowMultipleOfBounded (blockDiagWithFreshUnit matrix freshCols) sourceIndex targetIndex
            coefficient indicesDistinct sourceBlock targetBlock,
          addRowMultipleOfBounded matrix sourceIndex targetIndex coefficient indicesDistinct
            sourceBase targetBase]
      show IntMatrix.mk (listModifyAt (fun targetRow => addScaledEntries coefficient
            (listGetWithDefault [] (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols])
              sourceIndex) targetRow)
            (mapAllRows extendRow matrix.rows ++ [freshUnitRow freshCols]) targetIndex)
        = ⟨mapAllRows extendRow (listModifyAt (fun targetRow => addScaledEntries coefficient
            (listGetWithDefault [] matrix.rows sourceIndex) targetRow) matrix.rows targetIndex)
            ++ [freshUnitRow freshCols]⟩
      rw [listGetWithDefaultAppendLeft' [] (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols]
            sourceIndex sourceMap,
          getMapAllRowsInRange extendRow matrix.rows sourceIndex sourceBase,
          listModifyAtAppendLeft _ (mapAllRows extendRow matrix.rows) [freshUnitRow freshCols]
            targetIndex targetMap,
          listModifyAtMapAllRowsUnderWidth extendRow
            (fun targetRow => addScaledEntries coefficient
              (extendRow (listGetWithDefault [] matrix.rows sourceIndex)) targetRow)
            (fun targetRow => addScaledEntries coefficient
              (listGetWithDefault [] matrix.rows sourceIndex) targetRow) width
            (fun row rowWidth => addScaledEntriesExtendRow coefficient
              (listGetWithDefault [] matrix.rows sourceIndex) width sourceWidth row rowWidth)
            matrix.rows targetIndex rect.right]

/-! ### Column-operation infrastructure -/

/-- Replacing an entry with the value already there is a no-op (in or out of range). -/
theorem listReplaceAtGetSelf {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (index : Nat),
      listReplaceAt entries index (listGetWithDefault defaultEntry entries index) = entries
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | head :: tail, index + 1 => congrArg (head :: ·) (listReplaceAtGetSelf defaultEntry tail index)

/-- Modifying by a transform that fixes the entry there is a no-op. -/
theorem listModifyAtFixed {Entry : Type} (transform : Entry → Entry) (defaultEntry : Entry) :
    ∀ (entries : List Entry) (index : Nat),
      transform (listGetWithDefault defaultEntry entries index)
        = listGetWithDefault defaultEntry entries index →
      listModifyAt transform entries index = entries
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | head :: tail, 0, fixedHead => congrArg (· :: tail) fixedHead
  | head :: tail, index + 1, fixedEntry =>
      congrArg (head :: ·) (listModifyAtFixed transform defaultEntry tail index fixedEntry)

/-- The fresh unit row has `freshCols + 1` entries. -/
theorem freshUnitRowLength : ∀ (freshCols : Nat), (freshUnitRow freshCols).length = freshCols + 1
  | 0 => rfl
  | freshCols + 1 => congrArg (· + 1) (freshUnitRowLength freshCols)

/-- Reading a low position (`< freshCols`) of the fresh unit row returns `0`. -/
theorem freshRowLowEntryZero :
    ∀ (freshCols position : Nat), position < freshCols →
      listGetWithDefault 0 (freshUnitRow freshCols) position = 0
  | 0, position, isBelow => absurd isBelow (Nat.not_lt_zero position)
  | _ + 1, 0, _ => rfl
  | freshCols + 1, position + 1, isBelow =>
      freshRowLowEntryZero freshCols position (natLeOfSuccLeSucc isBelow)

/-- Replacing a low position of the fresh row by `0` is a no-op. -/
theorem freshReplaceZeroInert (freshCols position : Nat) (positionBelow : position < freshCols) :
    listReplaceAt (freshUnitRow freshCols) position 0 = freshUnitRow freshCols :=
  (congrArg (listReplaceAt (freshUnitRow freshCols) position)
    (freshRowLowEntryZero freshCols position positionBelow).symm).trans
    (listReplaceAtGetSelf 0 (freshUnitRow freshCols) position)

/-- Reducing `swapEntriesWithinRow` when both indices are in range. -/
theorem swapEntriesWithinRowOfBounded (row : IntRow) (firstIndex secondIndex : Nat)
    (firstBelow : firstIndex < row.length) (secondBelow : secondIndex < row.length) :
    swapEntriesWithinRow row firstIndex secondIndex
      = listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
          (listGetWithDefault 0 row firstIndex) := by
  show (if firstIndex < row.length then
      (if secondIndex < row.length then
        listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
          (listGetWithDefault 0 row firstIndex)
      else row) else row) = _
  rw [if_pos firstBelow, if_pos secondBelow]

/-- Reducing `addScaledEntryWithinRow` when the source index is in range. -/
theorem addScaledEntryWithinRowOfBounded (row : IntRow) (sourceIndex targetIndex : Nat)
    (coefficient : Int) (sourceBelow : sourceIndex < row.length) :
    addScaledEntryWithinRow row sourceIndex targetIndex coefficient
      = listModifyAt (fun targetEntry =>
          targetEntry + coefficient * listGetWithDefault 0 row sourceIndex) row targetIndex := by
  show (if sourceIndex < row.length then
      listModifyAt (fun targetEntry =>
        targetEntry + coefficient * listGetWithDefault 0 row sourceIndex) row targetIndex
    else row) = _
  rw [if_pos sourceBelow]

/-- Reducing `addColumnMultiple` when the source equals the target (identity). -/
theorem addColumnMultipleSelfIdent (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) (indicesEq : sourceIndex = targetIndex) :
    matrix.addColumnMultiple sourceIndex targetIndex coefficient = matrix := by
  show (if sourceIndex = targetIndex then matrix else _) = matrix
  rw [if_pos indicesEq]

/-- Reducing `addColumnMultiple` when the source differs from the target. -/
theorem addColumnMultipleOfBounded (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) (indicesDistinct : sourceIndex ≠ targetIndex) :
    matrix.addColumnMultiple sourceIndex targetIndex coefficient
      = ⟨mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          matrix.rows⟩ := by
  show (if sourceIndex = targetIndex then matrix else
      IntMatrix.mk (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
        matrix.rows)) = _
  rw [if_neg indicesDistinct]

/-- `swapColumns` fixes the fresh unit row (bounded indices swap two of its leading zeros). -/
theorem swapEntriesWithinRowFreshInert (firstIndex secondIndex freshCols : Nat)
    (firstBelow : firstIndex < freshCols) (secondBelow : secondIndex < freshCols) :
    swapEntriesWithinRow (freshUnitRow freshCols) firstIndex secondIndex = freshUnitRow freshCols := by
  have firstFresh : firstIndex < (freshUnitRow freshCols).length := by
    rw [freshUnitRowLength]; exact Nat.le.step firstBelow
  have secondFresh : secondIndex < (freshUnitRow freshCols).length := by
    rw [freshUnitRowLength]; exact Nat.le.step secondBelow
  rw [swapEntriesWithinRowOfBounded (freshUnitRow freshCols) firstIndex secondIndex firstFresh
        secondFresh,
      freshRowLowEntryZero freshCols secondIndex secondBelow,
      freshRowLowEntryZero freshCols firstIndex firstBelow,
      freshReplaceZeroInert freshCols firstIndex firstBelow]
  exact freshReplaceZeroInert freshCols secondIndex secondBelow

/-- `negateColumn` fixes the fresh unit row (bounded index negates one of its leading zeros). -/
theorem negateColumnFreshInert (freshCols position : Nat) (positionBelow : position < freshCols) :
    listModifyAt (fun entry => -entry) (freshUnitRow freshCols) position = freshUnitRow freshCols :=
  listModifyAtFixed (fun entry => -entry) 0 (freshUnitRow freshCols) position
    (by rw [freshRowLowEntryZero freshCols position positionBelow]; decide)

/-- `addColumnMultiple` fixes the fresh unit row (bounded indices touch only leading zeros). -/
theorem addScaledEntryWithinRowFreshInert (freshCols sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceBelow : sourceIndex < freshCols) :
    addScaledEntryWithinRow (freshUnitRow freshCols) sourceIndex targetIndex coefficient
      = freshUnitRow freshCols := by
  have sourceFresh : sourceIndex < (freshUnitRow freshCols).length := by
    rw [freshUnitRowLength]; exact Nat.le.step sourceBelow
  rw [addScaledEntryWithinRowOfBounded (freshUnitRow freshCols) sourceIndex targetIndex coefficient
        sourceFresh]
  refine listModifyAtFixed
    (fun targetEntry => targetEntry + coefficient * listGetWithDefault 0 (freshUnitRow freshCols) sourceIndex)
    0 (freshUnitRow freshCols) targetIndex ?_
  show listGetWithDefault 0 (freshUnitRow freshCols) targetIndex
      + coefficient * listGetWithDefault 0 (freshUnitRow freshCols) sourceIndex
    = listGetWithDefault 0 (freshUnitRow freshCols) targetIndex
  rw [freshRowLowEntryZero freshCols sourceIndex sourceBelow, intMulZero, intAddZero]

/-- `swapColumns` intertwines with the row extension on width-`width` rows. -/
theorem swapEntriesWithinRowExtendRow (firstIndex secondIndex width : Nat)
    (firstBelow : firstIndex < width) (secondBelow : secondIndex < width) :
    ∀ (row : IntRow), row.length = width →
      swapEntriesWithinRow (extendRow row) firstIndex secondIndex
        = extendRow (swapEntriesWithinRow row firstIndex secondIndex) := by
  intro row rowWidth
  have firstRow : firstIndex < row.length := rowWidth ▸ firstBelow
  have secondRow : secondIndex < row.length := rowWidth ▸ secondBelow
  have firstExt : firstIndex < (row ++ [0]).length := by
    rw [appendSingletonLength]; exact Nat.le.step firstRow
  have secondExt : secondIndex < (row ++ [0]).length := by
    rw [appendSingletonLength]; exact Nat.le.step secondRow
  rw [swapEntriesWithinRowOfBounded (extendRow row) firstIndex secondIndex firstExt secondExt,
      swapEntriesWithinRowOfBounded row firstIndex secondIndex firstRow secondRow]
  show listReplaceAt (listReplaceAt (row ++ [0]) firstIndex
        (listGetWithDefault 0 (row ++ [0]) secondIndex)) secondIndex
        (listGetWithDefault 0 (row ++ [0]) firstIndex)
    = listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
        (listGetWithDefault 0 row firstIndex) ++ [0]
  rw [listGetWithDefaultAppendLeft' 0 row [0] secondIndex secondRow,
      listGetWithDefaultAppendLeft' 0 row [0] firstIndex firstRow,
      listReplaceAtAppendLeft row [0] firstIndex (listGetWithDefault 0 row secondIndex) firstRow,
      listReplaceAtAppendLeft (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) [0]
        secondIndex (listGetWithDefault 0 row firstIndex)
        (by rw [listReplaceAtLength]; exact secondRow)]

/-- `negateColumn` intertwines with the row extension on width-`width` rows. -/
theorem negateColumnExtendRow (position width : Nat) (positionBelow : position < width) :
    ∀ (row : IntRow), row.length = width →
      listModifyAt (fun entry => -entry) (extendRow row) position
        = extendRow (listModifyAt (fun entry => -entry) row position) := by
  intro row rowWidth
  show listModifyAt (fun entry => -entry) (row ++ [0]) position
    = listModifyAt (fun entry => -entry) row position ++ [0]
  exact listModifyAtAppendLeft (fun entry => -entry) row [0] position (rowWidth ▸ positionBelow)

/-- `addColumnMultiple` intertwines with the row extension on width-`width` rows. -/
theorem addScaledEntryWithinRowExtendRow (sourceIndex targetIndex width : Nat) (coefficient : Int)
    (sourceBelow : sourceIndex < width) (targetBelow : targetIndex < width) :
    ∀ (row : IntRow), row.length = width →
      addScaledEntryWithinRow (extendRow row) sourceIndex targetIndex coefficient
        = extendRow (addScaledEntryWithinRow row sourceIndex targetIndex coefficient) := by
  intro row rowWidth
  have sourceRow : sourceIndex < row.length := rowWidth ▸ sourceBelow
  have targetRow : targetIndex < row.length := rowWidth ▸ targetBelow
  have sourceExt : sourceIndex < (row ++ [0]).length := by
    rw [appendSingletonLength]; exact Nat.le.step sourceRow
  rw [addScaledEntryWithinRowOfBounded (extendRow row) sourceIndex targetIndex coefficient sourceExt,
      addScaledEntryWithinRowOfBounded row sourceIndex targetIndex coefficient sourceRow]
  show listModifyAt (fun targetEntry =>
        targetEntry + coefficient * listGetWithDefault 0 (row ++ [0]) sourceIndex) (row ++ [0]) targetIndex
    = listModifyAt (fun targetEntry =>
        targetEntry + coefficient * listGetWithDefault 0 row sourceIndex) row targetIndex ++ [0]
  rw [listGetWithDefaultAppendLeft' 0 row [0] sourceIndex sourceRow,
      listModifyAtAppendLeft _ row [0] targetIndex targetRow]

/-- Fuse a column transform through the row extension (both operands same transform). -/
theorem mapAllRowsColumnFuse (rowTransform : IntRow → IntRow) (width : Nat)
    (intertwine : ∀ row, row.length = width →
      rowTransform (extendRow row) = extendRow (rowTransform row)) :
    ∀ (rows : List IntRow), rowsAllHaveWidth width rows →
      mapAllRows rowTransform (mapAllRows extendRow rows)
        = mapAllRows extendRow (mapAllRows rowTransform rows)
  | [], _ => rfl
  | head :: tail, widthPair => by
      show rowTransform (extendRow head) :: mapAllRows rowTransform (mapAllRows extendRow tail)
        = extendRow (rowTransform head) :: mapAllRows extendRow (mapAllRows rowTransform tail)
      rw [intertwine head widthPair.left,
          mapAllRowsColumnFuse rowTransform width intertwine tail widthPair.right]

/-- A column operation acts on the block exactly as on the base (fresh row inert, generic combiner). -/
theorem columnOpBlockInert (rowTransform : IntRow → IntRow) (width : Nat) (freshRow : IntRow)
    (freshInert : rowTransform freshRow = freshRow)
    (intertwine : ∀ row, row.length = width →
      rowTransform (extendRow row) = extendRow (rowTransform row)) :
    ∀ (rows : List IntRow), rowsAllHaveWidth width rows →
      mapAllRows rowTransform (mapAllRows extendRow rows ++ [freshRow])
        = mapAllRows extendRow (mapAllRows rowTransform rows) ++ [freshRow] := by
  intro rows allWidth
  rw [mapAllRowsAppend, mapAllRowsColumnFuse rowTransform width intertwine rows allWidth]
  show mapAllRows extendRow (mapAllRows rowTransform rows) ++ [rowTransform freshRow]
    = mapAllRows extendRow (mapAllRows rowTransform rows) ++ [freshRow]
  rw [freshInert]

/-- `swapColumns` acts on the block exactly as on the base (bounded indices). -/
theorem blockDiagSwapColumnsInert (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) (firstIndex secondIndex : Nat)
    (firstBelow : firstIndex < width) (secondBelow : secondIndex < width) :
    (blockDiagWithFreshUnit matrix width).swapColumns firstIndex secondIndex
      = blockDiagWithFreshUnit (matrix.swapColumns firstIndex secondIndex) width := by
  show IntMatrix.mk (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex)
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]))
    = ⟨mapAllRows extendRow (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex)
        matrix.rows) ++ [freshUnitRow width]⟩
  exact congrArg IntMatrix.mk
    (columnOpBlockInert (fun row => swapEntriesWithinRow row firstIndex secondIndex) width
      (freshUnitRow width)
      (swapEntriesWithinRowFreshInert firstIndex secondIndex width firstBelow secondBelow)
      (swapEntriesWithinRowExtendRow firstIndex secondIndex width firstBelow secondBelow)
      matrix.rows rect.right)

/-- `negateColumn` acts on the block exactly as on the base (bounded index). -/
theorem blockDiagNegateColumnInert (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) (position : Nat) (positionBelow : position < width) :
    (blockDiagWithFreshUnit matrix width).negateColumn position
      = blockDiagWithFreshUnit (matrix.negateColumn position) width := by
  show IntMatrix.mk (mapAllRows (fun row => listModifyAt (fun entry => -entry) row position)
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]))
    = ⟨mapAllRows extendRow (mapAllRows (fun row => listModifyAt (fun entry => -entry) row position)
        matrix.rows) ++ [freshUnitRow width]⟩
  exact congrArg IntMatrix.mk
    (columnOpBlockInert (fun row => listModifyAt (fun entry => -entry) row position) width
      (freshUnitRow width)
      (negateColumnFreshInert width position positionBelow)
      (negateColumnExtendRow position width positionBelow)
      matrix.rows rect.right)

/-- `addColumnMultiple` acts on the block exactly as on the base (bounded indices). -/
theorem blockDiagAddColumnMultipleInert (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) (sourceIndex targetIndex : Nat) (coefficient : Int)
    (sourceBelow : sourceIndex < width) (targetBelow : targetIndex < width) :
    (blockDiagWithFreshUnit matrix width).addColumnMultiple sourceIndex targetIndex coefficient
      = blockDiagWithFreshUnit (matrix.addColumnMultiple sourceIndex targetIndex coefficient) width := by
  cases Nat.decEq sourceIndex targetIndex with
  | isTrue indicesEq =>
      rw [addColumnMultipleSelfIdent (blockDiagWithFreshUnit matrix width) sourceIndex targetIndex
            coefficient indicesEq,
          addColumnMultipleSelfIdent matrix sourceIndex targetIndex coefficient indicesEq]
  | isFalse indicesDistinct =>
      rw [addColumnMultipleOfBounded (blockDiagWithFreshUnit matrix width) sourceIndex targetIndex
            coefficient indicesDistinct,
          addColumnMultipleOfBounded matrix sourceIndex targetIndex coefficient indicesDistinct]
      show IntMatrix.mk (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
            (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]))
        = ⟨mapAllRows extendRow (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex
            coefficient) matrix.rows) ++ [freshUnitRow width]⟩
      exact congrArg IntMatrix.mk
        (columnOpBlockInert (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          width (freshUnitRow width)
          (addScaledEntryWithinRowFreshInert width sourceIndex targetIndex coefficient sourceBelow)
          (addScaledEntryWithinRowExtendRow sourceIndex targetIndex width coefficient sourceBelow
            targetBelow)
          matrix.rows rect.right)

/-! ### Length / width preservation and the boundedness predicate -/

theorem listModifyAtLength {Entry : Type} (transform : Entry → Entry) :
    ∀ (entries : List Entry) (index : Nat), (listModifyAt transform entries index).length = entries.length
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: tail, index + 1 => congrArg (· + 1) (listModifyAtLength transform tail index)

theorem listMapNegLength : ∀ (row : IntRow), (row.map (fun entry => -entry)).length = row.length
  | [] => rfl
  | _ :: tail => congrArg (· + 1) (listMapNegLength tail)

theorem addScaledEntriesLength (coefficient : Int) :
    ∀ (sourceRow targetRow : IntRow), sourceRow.length = targetRow.length →
      (addScaledEntries coefficient sourceRow targetRow).length = targetRow.length
  | [], [], _ => rfl
  | [], _ :: _, lengthEq => Nat.noConfusion lengthEq
  | _ :: _, [], lengthEq => Nat.noConfusion lengthEq
  | _ :: sourceRest, _ :: targetRest, lengthEq =>
      congrArg (· + 1) (addScaledEntriesLength coefficient sourceRest targetRest (congrArg Nat.pred lengthEq))

theorem swapEntriesWithinRowLengthUnderWidth (firstIndex secondIndex width : Nat)
    (firstBelow : firstIndex < width) (secondBelow : secondIndex < width) (row : IntRow)
    (rowWidth : row.length = width) : (swapEntriesWithinRow row firstIndex secondIndex).length = width := by
  rw [swapEntriesWithinRowOfBounded row firstIndex secondIndex (rowWidth ▸ firstBelow)
        (rowWidth ▸ secondBelow), listReplaceAtLength, listReplaceAtLength]
  exact rowWidth

theorem addScaledEntryWithinRowLengthUnderWidth (sourceIndex targetIndex width : Nat) (coefficient : Int)
    (sourceBelow : sourceIndex < width) (row : IntRow) (rowWidth : row.length = width) :
    (addScaledEntryWithinRow row sourceIndex targetIndex coefficient).length = width := by
  rw [addScaledEntryWithinRowOfBounded row sourceIndex targetIndex coefficient (rowWidth ▸ sourceBelow),
      listModifyAtLength]
  exact rowWidth

theorem rowsAllHaveWidthListReplaceAt {width : Nat} (newRow : IntRow) (newRowWidth : newRow.length = width) :
    ∀ (rows : List IntRow) (index : Nat), rowsAllHaveWidth width rows →
      rowsAllHaveWidth width (listReplaceAt rows index newRow)
  | [], 0, _ => True.intro
  | [], _ + 1, _ => True.intro
  | _ :: tail, 0, widthPair => ⟨newRowWidth, widthPair.right⟩
  | head :: tail, index + 1, widthPair =>
      ⟨widthPair.left, rowsAllHaveWidthListReplaceAt newRow newRowWidth tail index widthPair.right⟩

theorem rowsAllHaveWidthListModifyAt {width : Nat} (transform : IntRow → IntRow)
    (widthPreserving : ∀ row, row.length = width → (transform row).length = width) :
    ∀ (rows : List IntRow) (index : Nat), rowsAllHaveWidth width rows →
      rowsAllHaveWidth width (listModifyAt transform rows index)
  | [], 0, _ => True.intro
  | [], _ + 1, _ => True.intro
  | _ :: tail, 0, widthPair => ⟨widthPreserving _ widthPair.left, widthPair.right⟩
  | head :: tail, index + 1, widthPair =>
      ⟨widthPair.left, rowsAllHaveWidthListModifyAt transform widthPreserving tail index widthPair.right⟩

theorem rowsAllHaveWidthMapAllRows {width widthOut : Nat} (transform : IntRow → IntRow)
    (widthMap : ∀ row, row.length = width → (transform row).length = widthOut) :
    ∀ (rows : List IntRow), rowsAllHaveWidth width rows →
      rowsAllHaveWidth widthOut (mapAllRows transform rows)
  | [], _ => True.intro
  | head :: tail, widthPair =>
      ⟨widthMap head widthPair.left, rowsAllHaveWidthMapAllRows transform widthMap tail widthPair.right⟩

/-- The boundedness predicate: every row index `< height`, every column index `< width`.  Fully
enumerated match arms (no wildcard) so the certificate discharge is propext-clean. -/
def opIsBounded (height width : Nat) : ElementaryOperation → Bool
  | .rowOperation (.swapRows firstIndex secondIndex) =>
      decide (firstIndex < height) && decide (secondIndex < height)
  | .rowOperation (.negateRow rowIndex) => decide (rowIndex < height)
  | .rowOperation (.addRowMultiple sourceIndex targetIndex _) =>
      decide (sourceIndex < height) && decide (targetIndex < height)
  | .columnOperation (.swapColumns firstIndex secondIndex) =>
      decide (firstIndex < width) && decide (secondIndex < width)
  | .columnOperation (.negateColumn colIndex) => decide (colIndex < width)
  | .columnOperation (.addColumnMultiple sourceIndex targetIndex _) =>
      decide (sourceIndex < width) && decide (targetIndex < width)

/-- Every operation in the certificate word is bounded. -/
def allOpsBounded (height width : Nat) : List ElementaryOperation → Bool
  | [] => true
  | operation :: remaining => opIsBounded height width operation && allOpsBounded height width remaining

/-- Left conjunct of a true boolean conjunction. -/
theorem boolAndTrueLeft {left right : Bool} (conjTrue : (left && right) = true) : left = true := by
  cases left with
  | true => rfl
  | false => exact conjTrue

/-- Right conjunct of a true boolean conjunction. -/
theorem boolAndTrueRight {left right : Bool} (conjTrue : (left && right) = true) : right = true := by
  cases left with
  | true => exact conjTrue
  | false => exact Bool.noConfusion conjTrue

/-! ### The single-operation combiner and rectangularity preservation -/

/-- ★ **Single-operation block inertness.**  A bounded elementary operation acts on the block-diagonal
`[[A | 0]; [0 | +1]]` exactly as on `A`, with the fresh row/column inert. -/
theorem applyOperationBlockInert (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) (operation : ElementaryOperation)
    (opBounded : opIsBounded height width operation = true) :
    (blockDiagWithFreshUnit matrix width).applyOperation operation
      = blockDiagWithFreshUnit (matrix.applyOperation operation) width := by
  cases operation with
  | rowOperation rowOp =>
      cases rowOp with
      | swapRows firstIndex secondIndex =>
          have boundedForm : (decide (firstIndex < height) && decide (secondIndex < height)) = true :=
            opBounded
          exact blockDiagSwapRowsInert matrix width height width rect firstIndex secondIndex
            (of_decide_eq_true (boolAndTrueLeft boundedForm))
            (of_decide_eq_true (boolAndTrueRight boundedForm))
      | negateRow rowIndex =>
          have boundedForm : decide (rowIndex < height) = true := opBounded
          exact blockDiagNegateRowInert matrix width height width rect rowIndex
            (of_decide_eq_true boundedForm)
      | addRowMultiple sourceIndex targetIndex coefficient =>
          have boundedForm : (decide (sourceIndex < height) && decide (targetIndex < height)) = true :=
            opBounded
          exact blockDiagAddRowMultipleInert matrix width height width rect sourceIndex targetIndex
            coefficient (of_decide_eq_true (boolAndTrueLeft boundedForm))
            (of_decide_eq_true (boolAndTrueRight boundedForm))
  | columnOperation colOp =>
      cases colOp with
      | swapColumns firstIndex secondIndex =>
          have boundedForm : (decide (firstIndex < width) && decide (secondIndex < width)) = true :=
            opBounded
          exact blockDiagSwapColumnsInert matrix height width rect firstIndex secondIndex
            (of_decide_eq_true (boolAndTrueLeft boundedForm))
            (of_decide_eq_true (boolAndTrueRight boundedForm))
      | negateColumn colIndex =>
          have boundedForm : decide (colIndex < width) = true := opBounded
          exact blockDiagNegateColumnInert matrix height width rect colIndex
            (of_decide_eq_true boundedForm)
      | addColumnMultiple sourceIndex targetIndex coefficient =>
          have boundedForm : (decide (sourceIndex < width) && decide (targetIndex < width)) = true :=
            opBounded
          exact blockDiagAddColumnMultipleInert matrix height width rect sourceIndex targetIndex
            coefficient (of_decide_eq_true (boolAndTrueLeft boundedForm))
            (of_decide_eq_true (boolAndTrueRight boundedForm))

/-- ★ **Rectangularity is preserved by a bounded operation.**  Needed so the block-lifting induction can
re-apply its hypothesis after each step. -/
theorem applyOperationPreservesRect (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) (operation : ElementaryOperation)
    (opBounded : opIsBounded height width operation = true) :
    (matrix.applyOperation operation).IsRectangular height width := by
  have lenEq : matrix.rows.length = height := rect.left
  cases operation with
  | rowOperation rowOp =>
      cases rowOp with
      | swapRows firstIndex secondIndex =>
          have boundedForm : (decide (firstIndex < height) && decide (secondIndex < height)) = true :=
            opBounded
          have firstBase : firstIndex < matrix.rows.length :=
            lenEq ▸ of_decide_eq_true (boolAndTrueLeft boundedForm)
          have secondBase : secondIndex < matrix.rows.length :=
            lenEq ▸ of_decide_eq_true (boolAndTrueRight boundedForm)
          rw [show matrix.applyOperation (.rowOperation (.swapRows firstIndex secondIndex))
                = matrix.swapRows firstIndex secondIndex from rfl,
              swapRowsOfBounded matrix firstIndex secondIndex firstBase secondBase]
          exact ⟨by rw [listReplaceAtLength, listReplaceAtLength]; exact lenEq,
            rowsAllHaveWidthListReplaceAt _ (rowsAllHaveWidthGet width matrix.rows firstIndex rect.right firstBase)
              _ secondIndex (rowsAllHaveWidthListReplaceAt _
                (rowsAllHaveWidthGet width matrix.rows secondIndex rect.right secondBase) _ firstIndex rect.right)⟩
      | negateRow rowIndex =>
          exact ⟨by
              show (listModifyAt (fun row => row.map (fun entry => -entry)) matrix.rows rowIndex).length = height
              rw [listModifyAtLength]; exact lenEq,
            rowsAllHaveWidthListModifyAt _ (fun row rowWidth => (listMapNegLength row).trans rowWidth)
              matrix.rows rowIndex rect.right⟩
      | addRowMultiple sourceIndex targetIndex coefficient =>
          cases Nat.decEq sourceIndex targetIndex with
          | isTrue indicesEq =>
              show (matrix.addRowMultiple sourceIndex targetIndex coefficient).IsRectangular height width
              rw [addRowMultipleSelfIdent matrix sourceIndex targetIndex coefficient indicesEq]
              exact rect
          | isFalse indicesDistinct =>
              have boundedForm : (decide (sourceIndex < height) && decide (targetIndex < height)) = true :=
                opBounded
              have sourceBase : sourceIndex < matrix.rows.length :=
                lenEq ▸ of_decide_eq_true (boolAndTrueLeft boundedForm)
              have targetBase : targetIndex < matrix.rows.length :=
                lenEq ▸ of_decide_eq_true (boolAndTrueRight boundedForm)
              have sourceWidth : (listGetWithDefault [] matrix.rows sourceIndex).length = width :=
                rowsAllHaveWidthGet width matrix.rows sourceIndex rect.right sourceBase
              show (matrix.addRowMultiple sourceIndex targetIndex coefficient).IsRectangular height width
              rw [addRowMultipleOfBounded matrix sourceIndex targetIndex coefficient indicesDistinct
                    sourceBase targetBase]
              exact ⟨by rw [listModifyAtLength]; exact lenEq,
                rowsAllHaveWidthListModifyAt _
                  (fun row rowWidth =>
                    (addScaledEntriesLength coefficient (listGetWithDefault [] matrix.rows sourceIndex) row
                      (sourceWidth.trans rowWidth.symm)).trans rowWidth)
                  matrix.rows targetIndex rect.right⟩
  | columnOperation colOp =>
      cases colOp with
      | swapColumns firstIndex secondIndex =>
          have boundedForm : (decide (firstIndex < width) && decide (secondIndex < width)) = true :=
            opBounded
          have firstBelow : firstIndex < width := of_decide_eq_true (boolAndTrueLeft boundedForm)
          have secondBelow : secondIndex < width := of_decide_eq_true (boolAndTrueRight boundedForm)
          exact ⟨by
              show (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex) matrix.rows).length = height
              rw [mapAllRowsLength]; exact lenEq,
            rowsAllHaveWidthMapAllRows _
              (fun row rowWidth =>
                swapEntriesWithinRowLengthUnderWidth firstIndex secondIndex width firstBelow secondBelow row rowWidth)
              matrix.rows rect.right⟩
      | negateColumn colIndex =>
          exact ⟨by
              show (mapAllRows (fun row => listModifyAt (fun entry => -entry) row colIndex) matrix.rows).length = height
              rw [mapAllRowsLength]; exact lenEq,
            rowsAllHaveWidthMapAllRows _
              (fun row rowWidth => (listModifyAtLength _ row colIndex).trans rowWidth)
              matrix.rows rect.right⟩
      | addColumnMultiple sourceIndex targetIndex coefficient =>
          cases Nat.decEq sourceIndex targetIndex with
          | isTrue indicesEq =>
              show (matrix.addColumnMultiple sourceIndex targetIndex coefficient).IsRectangular height width
              rw [addColumnMultipleSelfIdent matrix sourceIndex targetIndex coefficient indicesEq]
              exact rect
          | isFalse indicesDistinct =>
              have boundedForm : (decide (sourceIndex < width) && decide (targetIndex < width)) = true :=
                opBounded
              have sourceBelow : sourceIndex < width := of_decide_eq_true (boolAndTrueLeft boundedForm)
              show (matrix.addColumnMultiple sourceIndex targetIndex coefficient).IsRectangular height width
              rw [addColumnMultipleOfBounded matrix sourceIndex targetIndex coefficient indicesDistinct]
              exact ⟨by
                  show (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
                      matrix.rows).length = height
                  rw [mapAllRowsLength]; exact lenEq,
                rowsAllHaveWidthMapAllRows _
                  (fun row rowWidth =>
                    addScaledEntryWithinRowLengthUnderWidth sourceIndex targetIndex width coefficient sourceBelow
                      row rowWidth)
                  matrix.rows rect.right⟩

/-- ★★ **THE BLOCK-LIFTING INDUCTION.**  For any base matrix rectangular of shape `height × width` and
any bounded certificate word, the block-diagonal `[[A | 0]; [0 | +1]]` reduced by that word equals the
block-diagonal of `A` reduced by that word — the fresh row and fresh column stay inert throughout.  This
is the fully cert-free block-lifting the r4 ledger walled: an induction over the operation list, each step
discharged by `applyOperationBlockInert` with rectangularity carried by `applyOperationPreservesRect`. -/
theorem liftedBaseCertAgreesOnBlock :
    ∀ (operations : List ElementaryOperation) (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width → allOpsBounded height width operations = true →
      (blockDiagWithFreshUnit matrix width).applyOperations operations
        = blockDiagWithFreshUnit (matrix.applyOperations operations) width
  | [], _, _, _, _, _ => rfl
  | operation :: remaining, matrix, height, width, rect, allBounded => by
      have opBounded : opIsBounded height width operation = true := boolAndTrueLeft allBounded
      have remainingBounded : allOpsBounded height width remaining = true :=
        boolAndTrueRight allBounded
      show ((blockDiagWithFreshUnit matrix width).applyOperation operation).applyOperations remaining
        = blockDiagWithFreshUnit ((matrix.applyOperation operation).applyOperations remaining) width
      rw [applyOperationBlockInert matrix height width rect operation opBounded]
      exact liftedBaseCertAgreesOnBlock remaining (matrix.applyOperation operation) height width
        (applyOperationPreservesRect matrix height width rect operation opBounded) remainingBounded

/-- `applyOperations` splits over a certificate append. -/
theorem applyOperationsAppend :
    ∀ (leftOps rightOps : List ElementaryOperation) (matrix : IntMatrix),
      matrix.applyOperations (leftOps ++ rightOps)
        = (matrix.applyOperations leftOps).applyOperations rightOps
  | [], _, _ => rfl
  | operation :: remaining, rightOps, matrix =>
      applyOperationsAppend remaining rightOps (matrix.applyOperation operation)

/-- ★ **The generic recipe reduces the block through a bounded base certificate.**  A restatement of the
block-lifting for direct use in the recipe assembly: the block-diagonal reduced by a bounded base
certificate is the block-diagonal of the base reduced by that certificate. -/
theorem blockRecipeReducesToBlockDiag (baseMatrix : IntMatrix) (baseCert : List ElementaryOperation)
    (height width : Nat) (rect : baseMatrix.IsRectangular height width)
    (bounded : allOpsBounded height width baseCert = true) :
    (blockDiagWithFreshUnit baseMatrix width).applyOperations baseCert
      = blockDiagWithFreshUnit (baseMatrix.applyOperations baseCert) width :=
  liftedBaseCertAgreesOnBlock baseCert baseMatrix height width rect bounded

/-! ### Diagonal read-off from the block-diagonal -/

/-- Reading a low diagonal position (`< width`, `< height`) of the block-diagonal returns the base
diagonal entry — the base block sits index-stable at the top-left. -/
theorem blockDiagDiagonalBelow (matrix : IntMatrix) (height width position : Nat)
    (rect : matrix.IsRectangular height width) (rowBelow : position < height)
    (colBelow : position < width) :
    (blockDiagWithFreshUnit matrix width).diagonalEntryAt position = matrix.diagonalEntryAt position := by
  have rowWidth : (listGetWithDefault [] matrix.rows position).length = width :=
    rowsAllHaveWidthGet width matrix.rows position rect.right (rect.left ▸ rowBelow)
  have mapLen : position < (mapAllRows extendRow matrix.rows).length := by
    rw [mapAllRowsLength, rect.left]; exact rowBelow
  show listGetWithDefault 0 (listGetWithDefault []
      (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]) position) position
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows position) position
  rw [listGetWithDefaultAppendLeft' [] (mapAllRows extendRow matrix.rows) [freshUnitRow width] position
        mapLen,
      getMapAllRowsInRange extendRow matrix.rows position (rect.left ▸ rowBelow)]
  show listGetWithDefault 0 (listGetWithDefault [] matrix.rows position ++ [0]) position
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows position) position
  exact listGetWithDefaultAppendLeft' 0 (listGetWithDefault [] matrix.rows position) [0] position
    (rowWidth ▸ colBelow)

/-- Reading at index `= left.length` of an append reads the head of the right list. -/
theorem listGetAtLeftLengthReadsRightHead {Entry : Type} (defaultEntry : Entry) :
    ∀ (leftEntries rightEntries : List Entry),
      listGetWithDefault defaultEntry (leftEntries ++ rightEntries) leftEntries.length
        = listGetWithDefault defaultEntry rightEntries 0
  | [], _ => rfl
  | _ :: tail, rightEntries => listGetAtLeftLengthReadsRightHead defaultEntry tail rightEntries

/-- The fresh unit row has its `+1` pivot at position `width`. -/
theorem freshRowPivotEntry : ∀ (width : Nat), listGetWithDefault 0 (freshUnitRow width) width = 1
  | 0 => rfl
  | width + 1 => freshRowPivotEntry width

/-- The block-diagonal's diagonal entry at the fresh position `width` is the unit `1` (the pivot) when
the base is square (`height = width`) — the fresh generator/rule pivot. -/
theorem blockDiagDiagonalAtFreshSquare (matrix : IntMatrix) (width : Nat)
    (rect : matrix.IsRectangular width width) :
    (blockDiagWithFreshUnit matrix width).diagonalEntryAt width = 1 := by
  have mapLen : (mapAllRows extendRow matrix.rows).length = width := by
    rw [mapAllRowsLength, rect.left]
  have outerRead : listGetWithDefault []
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]) width = freshUnitRow width :=
    (congrArg (fun index => listGetWithDefault []
        (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]) index) mapLen.symm).trans
      (listGetAtLeftLengthReadsRightHead [] (mapAllRows extendRow matrix.rows) [freshUnitRow width])
  show listGetWithDefault 0 (listGetWithDefault []
      (mapAllRows extendRow matrix.rows ++ [freshUnitRow width]) width) width = 1
  rw [outerRead]
  exact freshRowPivotEntry width

/-! ### Non-square swap read-off — the fresh unit moved onto the diagonal by ONE `swapColumns`

For a base SNF of shape `height × width` with `height < width` (the r2 Tietze `2 × 4`), the block's fresh
unit sits at the OFF-diagonal position `(height, width)`, invisible to the homology reader (which counts
DIAGONAL positions only).  ONE `swapColumns height width` moves it onto `(height, height)`: base SNF
column `height` is a zero column (past the base rank `height`), so the swap is clean.  The two targeted
read-offs below (base diagonal below `height`, unit at `height`) discharge the non-square assembly's
`fromHigherDiag…` hypotheses WITHOUT a full swapped-matrix equality.  Both are `height < width`-gated so
the square case (`swapColumns width width` = identity) is never routed through them. -/

/-- Reading a position DIFFERENT from the written index returns the original entry — a write is invisible
off its own slot.  Structural on the list and both indices; the diagonal `0 ≠ 0` case is discharged by
the hypothesis. -/
theorem listGetReplaceAtNe {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (writeIndex readIndex : Nat) (newEntry : Entry),
      readIndex ≠ writeIndex →
      listGetWithDefault defaultEntry (listReplaceAt entries writeIndex newEntry) readIndex
        = listGetWithDefault defaultEntry entries readIndex
  | [], 0, _, _, _ => rfl
  | [], _ + 1, _, _, _ => rfl
  | _ :: _, 0, 0, _, readNeWrite => absurd rfl readNeWrite
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: tail, writeIndex + 1, readIndex + 1, newEntry, readNeWrite =>
      listGetReplaceAtNe defaultEntry tail writeIndex readIndex newEntry
        (fun readEqWrite => readNeWrite (congrArg (· + 1) readEqWrite))

/-- Reading the WRITTEN index returns the new entry — the write lands exactly on its slot (in range).
Structural on the list and index. -/
theorem listGetReplaceAtSame {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (index : Nat) (newEntry : Entry),
      index < entries.length →
      listGetWithDefault defaultEntry (listReplaceAt entries index newEntry) index = newEntry
  | [], index, _, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _, _ => rfl
  | _ :: tail, index + 1, newEntry, isBelow =>
      listGetReplaceAtSame defaultEntry tail index newEntry (natLeOfSuccLeSucc isBelow)

/-- `rowsAllHaveWidth` distributes over an append — structural on the left row list. -/
theorem rowsAllHaveWidthAppend {width : Nat} :
    ∀ (leftRows rightRows : List IntRow),
      rowsAllHaveWidth width leftRows → rowsAllHaveWidth width rightRows →
      rowsAllHaveWidth width (leftRows ++ rightRows)
  | [], _, _, rightWidth => rightWidth
  | _ :: tail, rightRows, leftWidth, rightWidth =>
      ⟨leftWidth.left, rowsAllHaveWidthAppend tail rightRows leftWidth.right rightWidth⟩

/-- The block-diagonal `[[A | 0]; [0 | +1]]` is rectangular of shape `(height + 1) × (width + 1)` — the
extended base rows and the fresh unit row both have width `width + 1`. -/
theorem blockDiagIsRectangular (matrix : IntMatrix) (height width : Nat)
    (rect : matrix.IsRectangular height width) :
    (blockDiagWithFreshUnit matrix width).IsRectangular (height + 1) (width + 1) :=
  ⟨blockDiagRowsLength matrix width height width rect,
   rowsAllHaveWidthAppend (mapAllRows extendRow matrix.rows) [freshUnitRow width]
     (rowsAllHaveWidthMapAllRows extendRow
       (fun row rowWidth => (appendSingletonLength (0 : Int) row).trans (congrArg (· + 1) rowWidth))
       matrix.rows rect.right)
     ⟨freshUnitRowLength width, True.intro⟩⟩

/-- ★ **Below-window swap read-off.**  For a base SNF of shape `height × width` with `height < width`,
reading a diagonal position `< height` of the block after `swapColumns height width` returns the BASE
diagonal entry — column `position` (`≠ height`, `≠ width`) is untouched by the swap. -/
theorem blockDiagSwapFreshDiagonalBelow (baseSNF : IntMatrix) (height width position : Nat)
    (rect : baseSNF.IsRectangular height width) (heightBelowWidth : height < width)
    (positionBelowHeight : position < height) :
    ((blockDiagWithFreshUnit baseSNF width).swapColumns height width).diagonalEntryAt position
      = baseSNF.diagonalEntryAt position := by
  have positionBelowWidth : position < width := Nat.lt_trans positionBelowHeight heightBelowWidth
  have baseRowWidth : (listGetWithDefault [] baseSNF.rows position).length = width :=
    rowsAllHaveWidthGet width baseSNF.rows position rect.right (rect.left ▸ positionBelowHeight)
  have mapLen : position < (mapAllRows extendRow baseSNF.rows).length := by
    rw [mapAllRowsLength, rect.left]; exact positionBelowHeight
  have mapLenSwap : position < (mapAllRows (fun row => swapEntriesWithinRow row height width)
      (mapAllRows extendRow baseSNF.rows)).length := by rw [mapAllRowsLength]; exact mapLen
  have extLen : (extendRow (listGetWithDefault [] baseSNF.rows position)).length = width + 1 := by
    show ((listGetWithDefault [] baseSNF.rows position) ++ [0]).length = width + 1
    rw [appendSingletonLength]; exact congrArg (· + 1) baseRowWidth
  have heightExt : height < (extendRow (listGetWithDefault [] baseSNF.rows position)).length := by
    rw [extLen]; exact Nat.le.step heightBelowWidth
  have widthExt : width < (extendRow (listGetWithDefault [] baseSNF.rows position)).length := by
    rw [extLen]; exact Nat.le.refl
  have posNeHeight : position ≠ height := Nat.ne_of_lt positionBelowHeight
  have posNeWidth : position ≠ width := Nat.ne_of_lt positionBelowWidth
  show listGetWithDefault 0
      (listGetWithDefault []
        (mapAllRows (fun row => swapEntriesWithinRow row height width)
          (mapAllRows extendRow baseSNF.rows ++ [freshUnitRow width])) position) position
    = listGetWithDefault 0 (listGetWithDefault [] baseSNF.rows position) position
  rw [mapAllRowsAppend (fun row => swapEntriesWithinRow row height width)
        (mapAllRows extendRow baseSNF.rows) [freshUnitRow width],
      listGetWithDefaultAppendLeft' [] (mapAllRows (fun row => swapEntriesWithinRow row height width)
        (mapAllRows extendRow baseSNF.rows)) _ position mapLenSwap,
      getMapAllRowsInRange (fun row => swapEntriesWithinRow row height width)
        (mapAllRows extendRow baseSNF.rows) position mapLen,
      getMapAllRowsInRange extendRow baseSNF.rows position (rect.left ▸ positionBelowHeight),
      swapEntriesWithinRowOfBounded (extendRow (listGetWithDefault [] baseSNF.rows position))
        height width heightExt widthExt,
      listGetReplaceAtNe 0 _ width position _ posNeWidth,
      listGetReplaceAtNe 0 (extendRow (listGetWithDefault [] baseSNF.rows position)) height position
        _ posNeHeight]
  show listGetWithDefault 0 ((listGetWithDefault [] baseSNF.rows position) ++ [0]) position
    = listGetWithDefault 0 (listGetWithDefault [] baseSNF.rows position) position
  exact listGetWithDefaultAppendLeft' 0 (listGetWithDefault [] baseSNF.rows position) [0] position
    (baseRowWidth ▸ positionBelowWidth)

/-- ★ **At-window swap read-off.**  For a base SNF of shape `height × width` with `height < width`, the
block's diagonal entry at position `height` AFTER `swapColumns height width` is the unit `1` — the fresh
pivot, moved from the off-diagonal `(height, width)` onto the diagonal. -/
theorem blockDiagSwapFreshDiagonalAtHeight (baseSNF : IntMatrix) (height width : Nat)
    (rect : baseSNF.IsRectangular height width) (heightBelowWidth : height < width) :
    ((blockDiagWithFreshUnit baseSNF width).swapColumns height width).diagonalEntryAt height = 1 := by
  have heightFresh : height < (freshUnitRow width).length := by
    rw [freshUnitRowLength]; exact Nat.le.step heightBelowWidth
  have widthFresh : width < (freshUnitRow width).length := by
    rw [freshUnitRowLength]; exact Nat.le.refl
  have heightNeWidth : height ≠ width := Nat.ne_of_lt heightBelowWidth
  have leftLen : (mapAllRows (fun row => swapEntriesWithinRow row height width)
      (mapAllRows extendRow baseSNF.rows)).length = height := by
    rw [mapAllRowsLength, mapAllRowsLength, rect.left]
  have outerRead : listGetWithDefault []
        (mapAllRows (fun row => swapEntriesWithinRow row height width) (mapAllRows extendRow baseSNF.rows)
          ++ mapAllRows (fun row => swapEntriesWithinRow row height width) [freshUnitRow width]) height
      = swapEntriesWithinRow (freshUnitRow width) height width :=
    (congrArg (fun idx => listGetWithDefault []
        (mapAllRows (fun row => swapEntriesWithinRow row height width) (mapAllRows extendRow baseSNF.rows)
          ++ mapAllRows (fun row => swapEntriesWithinRow row height width) [freshUnitRow width]) idx)
        leftLen.symm).trans
      (listGetAtLeftLengthReadsRightHead []
        (mapAllRows (fun row => swapEntriesWithinRow row height width) (mapAllRows extendRow baseSNF.rows))
        (mapAllRows (fun row => swapEntriesWithinRow row height width) [freshUnitRow width]))
  show listGetWithDefault 0
      (listGetWithDefault []
        (mapAllRows (fun row => swapEntriesWithinRow row height width)
          (mapAllRows extendRow baseSNF.rows ++ [freshUnitRow width])) height) height = 1
  rw [mapAllRowsAppend (fun row => swapEntriesWithinRow row height width)
        (mapAllRows extendRow baseSNF.rows) [freshUnitRow width], outerRead,
      swapEntriesWithinRowOfBounded (freshUnitRow width) height width heightFresh widthFresh,
      freshRowPivotEntry width, freshRowLowEntryZero width height heightBelowWidth,
      listGetReplaceAtNe 0 (listReplaceAt (freshUnitRow width) height 1) width height 0 heightNeWidth,
      listGetReplaceAtSame 0 (freshUnitRow width) height 1 heightFresh]

end FX1Poly.Polygraph.Homology

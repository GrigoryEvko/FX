import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithOperationRoundTrip — the operation-inversion kit
    (the `ComputerAlgebra/` substrate; Part B of the H2-SMITH reconnection)

Every letter of the unimodular certificate alphabet (`SmithNormalForm.inverseOperation`) has a genuine
INVERSE over the integers: swap and negate are self-inverse, a transvection negates its coefficient.
This file proves that INVERSION actually inverts — first per constructor at the matrix level, then across
a whole word via `reverseOperationWord`.  The payoff is the ℤ-equivalence witness the certificate design
promised (`A = M'.applyOperations (reverseOperationWord S)` for any reduction word `S`): every checked
reduction is invertible, so the reduced matrix is genuinely ℤ-equivalent to the input.

Two consumers downstream:
  * the fold round-trip `applyOperationsReverseRoundTrip` lets `SmithMinorTransportEquivalence`
    transport minor-divisibility BACKWARD across a confined sweep (the exit-divides ⟹ input-divides half);
  * the boundedness transport `reverseOperationWordBoundedBelow` shows the reverse word is confined below
    exactly where the forward word is, so the shipped forward tower applies to it unchanged.

## Zero-axiom design
Every proof is structural over non-indexed `List` / `Nat` inductives, so none of the indexed-match
propext traps apply.  The only arithmetic is the shipped `Int` cancel kit
(`intAddAssoc` / `intRightDistrib` / `intAddRightNeg` / `intZeroMul` / `intAddZero` / `intNegNeg`).
The Bool identities are hand-rolled by `cases` (never `decide`, never the Init lemmas) so nothing leaks
`propext`.  Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithOperationRoundTrip.lean`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Bool identities (hand-rolled by `cases` — propext-clean) -/

/-- `b && true = b`. -/
theorem boolAndTrueRight (flag : Bool) : (flag && true) = flag := by cases flag <;> rfl

/-- `true && b = b` (definitional). -/
theorem boolTrueAndLeft (flag : Bool) : (true && flag) = flag := rfl

/-- `&&` is commutative. -/
theorem boolAndCommute (leftFlag rightFlag : Bool) : (leftFlag && rightFlag) = (rightFlag && leftFlag) := by
  cases leftFlag <;> cases rightFlag <;> rfl

/-- `&&` is associative. -/
theorem boolAndAssociate (firstFlag secondFlag thirdFlag : Bool) :
    ((firstFlag && secondFlag) && thirdFlag) = (firstFlag && (secondFlag && thirdFlag)) := by
  cases firstFlag <;> cases secondFlag <;> cases thirdFlag <;> rfl

/-! ## Generic `listReplaceAt` algebra atoms -/

/-- **Two replaces at the SAME index collapse** — the earlier write is overwritten. -/
theorem listReplaceAtCollapse {Entry : Type} :
    ∀ (entries : List Entry) (position : Nat) (firstEntry secondEntry : Entry),
      listReplaceAt (listReplaceAt entries position firstEntry) position secondEntry
        = listReplaceAt entries position secondEntry
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | _ :: remainingEntries, position + 1, firstEntry, secondEntry =>
      congrArg (_ :: ·) (listReplaceAtCollapse remainingEntries position firstEntry secondEntry)

/-- **Two replaces at DISTINCT indices commute.** -/
theorem listReplaceAtCommute {Entry : Type} :
    ∀ (entries : List Entry) (firstIndex secondIndex : Nat) (firstEntry secondEntry : Entry),
      firstIndex ≠ secondIndex →
      listReplaceAt (listReplaceAt entries firstIndex firstEntry) secondIndex secondEntry
        = listReplaceAt (listReplaceAt entries secondIndex secondEntry) firstIndex firstEntry
  | [], 0, 0, _, _, indexNe => absurd rfl indexNe
  | [], 0, _ + 1, _, _, _ => rfl
  | [], _ + 1, 0, _, _, _ => rfl
  | [], _ + 1, _ + 1, _, _, _ => rfl
  | _ :: _, 0, 0, _, _, indexNe => absurd rfl indexNe
  | _ :: _, 0, _ + 1, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | _ :: remainingEntries, firstIndex + 1, secondIndex + 1, firstEntry, secondEntry, indexNe =>
      congrArg (_ :: ·)
        (listReplaceAtCommute remainingEntries firstIndex secondIndex firstEntry secondEntry
          (fun innerEq => indexNe (congrArg (· + 1) innerEq)))

/-- **Replacing a slot with the value already there is a no-op** (in range). -/
theorem listReplaceAtIdentity {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (position : Nat), position < entries.length →
      listReplaceAt entries position (listGetWithDefault defaultEntry entries position) = entries
  | [], 0, isInRange => absurd isInRange (Nat.not_lt_zero 0)
  | [], _ + 1, isInRange => absurd isInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | entry :: remainingEntries, position + 1, isInRange =>
      congrArg (entry :: ·)
        (listReplaceAtIdentity defaultEntry remainingEntries position (Nat.lt_of_succ_lt_succ isInRange))

/-- **Two modifies at the SAME index cancel when the composed transform fixes that slot.** -/
theorem listModifyAtCancelAt {Entry : Type} (defaultEntry : Entry) (firstTransform secondTransform : Entry → Entry) :
    ∀ (entries : List Entry) (position : Nat),
      secondTransform (firstTransform (listGetWithDefault defaultEntry entries position))
        = listGetWithDefault defaultEntry entries position →
      listModifyAt secondTransform (listModifyAt firstTransform entries position) position = entries
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _entry :: remainingEntries, 0, slotFixed => congrArg (· :: remainingEntries) slotFixed
  | entry :: remainingEntries, position + 1, slotFixed =>
      congrArg (entry :: ·) (listModifyAtCancelAt defaultEntry firstTransform secondTransform remainingEntries position slotFixed)

/-! ## The `mapAllRows` cancel carrier -/

/-- **`mapAllRows` cancels row-locally** — if the second transform undoes the first on every row, two
row-local maps compose to the identity on the whole row list. -/
theorem mapAllRowsCancel (firstTransform secondTransform : IntRow → IntRow)
    (rowCancel : ∀ row, secondTransform (firstTransform row) = row) :
    ∀ rows : List IntRow, mapAllRows secondTransform (mapAllRows firstTransform rows) = rows
  | [] => rfl
  | row :: remainingRows =>
      (congrArg (· :: mapAllRows secondTransform (mapAllRows firstTransform remainingRows)) (rowCancel row)).trans
        (congrArg (row :: ·) (mapAllRowsCancel firstTransform secondTransform rowCancel remainingRows))

/-! ## Matrix equality by row equality -/

/-- Two matrices are equal when their row lists are equal (structure eta). -/
theorem intMatrixEqOfRowsEq {leftMatrix rightMatrix : IntMatrix}
    (rowsEq : leftMatrix.rows = rightMatrix.rows) : leftMatrix = rightMatrix := by
  cases leftMatrix; cases rightMatrix; exact congrArg IntMatrix.mk rowsEq

/-! ## The pair-swap self-inverse (shared by row swaps and column swaps) -/

/-- The common shape of `swapRows` and `swapEntriesWithinRow`: swap two slots of a list (identity unless
both indices are in range). -/
def listPairSwap {Entry : Type} (defaultEntry : Entry) (entries : List Entry) (firstIndex secondIndex : Nat) :
    List Entry :=
  if firstIndex < entries.length then
    if secondIndex < entries.length then
      listReplaceAt (listReplaceAt entries firstIndex (listGetWithDefault defaultEntry entries secondIndex))
        secondIndex (listGetWithDefault defaultEntry entries firstIndex)
    else entries
  else entries

/-- Expand `listPairSwap` when both indices are in range (avoids `unfold` touching a nested swap). -/
theorem listPairSwapExpand {Entry : Type} (defaultEntry : Entry) (entries : List Entry)
    (firstIndex secondIndex : Nat) (firstInRange : firstIndex < entries.length)
    (secondInRange : secondIndex < entries.length) :
    listPairSwap defaultEntry entries firstIndex secondIndex
      = listReplaceAt (listReplaceAt entries firstIndex (listGetWithDefault defaultEntry entries secondIndex))
          secondIndex (listGetWithDefault defaultEntry entries firstIndex) := by
  unfold listPairSwap; rw [if_pos firstInRange, if_pos secondInRange]

/-- Swapping a slot with itself is a no-op. -/
theorem listPairSwapSame {Entry : Type} (defaultEntry : Entry) (entries : List Entry) (position : Nat) :
    listPairSwap defaultEntry entries position position = entries := by
  by_cases inRange : position < entries.length
  · unfold listPairSwap
    rw [if_pos inRange, if_pos inRange, listReplaceAtCollapse, listReplaceAtIdentity defaultEntry entries position inRange]
  · unfold listPairSwap
    rw [if_neg inRange]

/-- **The pair-swap is its own inverse** — swapping the same two slots twice restores the list.  The core
combinatorial lemma; the `a = b` case collapses through `listPairSwapSame`, the distinct case threads the
commute / collapse / identity atoms. -/
theorem listPairSwapSelfInverse {Entry : Type} (defaultEntry : Entry) (entries : List Entry)
    (firstIndex secondIndex : Nat) :
    listPairSwap defaultEntry (listPairSwap defaultEntry entries firstIndex secondIndex) firstIndex secondIndex
      = entries := by
  by_cases indexEq : firstIndex = secondIndex
  · subst indexEq
    rw [listPairSwapSame, listPairSwapSame]
  · by_cases firstInRange : firstIndex < entries.length
    · by_cases secondInRange : secondIndex < entries.length
      · have innerEq : listPairSwap defaultEntry entries firstIndex secondIndex
            = listReplaceAt (listReplaceAt entries firstIndex (listGetWithDefault defaultEntry entries secondIndex))
                secondIndex (listGetWithDefault defaultEntry entries firstIndex) :=
          listPairSwapExpand defaultEntry entries firstIndex secondIndex firstInRange secondInRange
        have innerLen : (listPairSwap defaultEntry entries firstIndex secondIndex).length = entries.length := by
          rw [innerEq, listReplaceAtPreservesLength, listReplaceAtPreservesLength]
        have getAtFirst : listGetWithDefault defaultEntry (listPairSwap defaultEntry entries firstIndex secondIndex) firstIndex
            = listGetWithDefault defaultEntry entries secondIndex := by
          rw [innerEq, listGetWithDefaultReplaceAtNe defaultEntry _ secondIndex firstIndex _ indexEq,
            listGetWithDefaultReplaceAtEq defaultEntry entries firstIndex _ firstInRange]
        have getAtSecond : listGetWithDefault defaultEntry (listPairSwap defaultEntry entries firstIndex secondIndex) secondIndex
            = listGetWithDefault defaultEntry entries firstIndex := by
          rw [innerEq, listGetWithDefaultReplaceAtEq defaultEntry _ secondIndex _
            (by rw [listReplaceAtPreservesLength]; exact secondInRange)]
        have rangeFirst : firstIndex < (listPairSwap defaultEntry entries firstIndex secondIndex).length := by
          rw [innerLen]; exact firstInRange
        have rangeSecond : secondIndex < (listPairSwap defaultEntry entries firstIndex secondIndex).length := by
          rw [innerLen]; exact secondInRange
        have outerEq := listPairSwapExpand defaultEntry (listPairSwap defaultEntry entries firstIndex secondIndex)
          firstIndex secondIndex rangeFirst rangeSecond
        rw [outerEq, getAtFirst, getAtSecond, innerEq]
        rw [listReplaceAtCommute (listReplaceAt entries firstIndex (listGetWithDefault defaultEntry entries secondIndex))
              secondIndex firstIndex (listGetWithDefault defaultEntry entries firstIndex) (listGetWithDefault defaultEntry entries firstIndex)
              (fun equalIndices => indexEq equalIndices.symm)]
        rw [listReplaceAtCollapse entries firstIndex (listGetWithDefault defaultEntry entries secondIndex)
              (listGetWithDefault defaultEntry entries firstIndex)]
        rw [listReplaceAtCollapse (listReplaceAt entries firstIndex (listGetWithDefault defaultEntry entries firstIndex))
              secondIndex (listGetWithDefault defaultEntry entries firstIndex) (listGetWithDefault defaultEntry entries secondIndex)]
        rw [listReplaceAtIdentity defaultEntry entries firstIndex firstInRange,
          listReplaceAtIdentity defaultEntry entries secondIndex secondInRange]
      · have innerEq : listPairSwap defaultEntry entries firstIndex secondIndex = entries := by
          unfold listPairSwap; rw [if_pos firstInRange, if_neg secondInRange]
        rw [innerEq]; unfold listPairSwap; rw [if_pos firstInRange, if_neg secondInRange]
    · have innerEq : listPairSwap defaultEntry entries firstIndex secondIndex = entries := by
        unfold listPairSwap; rw [if_neg firstInRange]
      rw [innerEq]; unfold listPairSwap; rw [if_neg firstInRange]

/-! ## Row swap self-inverse -/

/-- `swapRows` acts on the row list exactly as `listPairSwap` (the projection commutes with the guards). -/
theorem swapRowsRowsEq (matrix : IntMatrix) (firstIndex secondIndex : Nat) :
    (matrix.swapRows firstIndex secondIndex).rows = listPairSwap [] matrix.rows firstIndex secondIndex := by
  unfold IntMatrix.swapRows listPairSwap
  split
  · split
    · rfl
    · rfl
  · rfl

/-- **`swapRows` is its own inverse** — swapping the same two rows twice restores the matrix. -/
theorem swapRowsSelfInverse (matrix : IntMatrix) (firstIndex secondIndex : Nat) :
    (matrix.swapRows firstIndex secondIndex).swapRows firstIndex secondIndex = matrix :=
  intMatrixEqOfRowsEq (by
    rw [swapRowsRowsEq, swapRowsRowsEq]
    exact listPairSwapSelfInverse [] matrix.rows firstIndex secondIndex)

/-! ## Column swap self-inverse -/

/-- `swapEntriesWithinRow` is exactly `listPairSwap` on a row (definitional). -/
theorem swapEntriesWithinRowEq (row : IntRow) (firstIndex secondIndex : Nat) :
    swapEntriesWithinRow row firstIndex secondIndex = listPairSwap 0 row firstIndex secondIndex := rfl

/-- **`swapColumns` is its own inverse.** -/
theorem swapColumnsSelfInverse (matrix : IntMatrix) (firstIndex secondIndex : Nat) :
    (matrix.swapColumns firstIndex secondIndex).swapColumns firstIndex secondIndex = matrix :=
  intMatrixEqOfRowsEq
    (mapAllRowsCancel (fun row => swapEntriesWithinRow row firstIndex secondIndex)
      (fun row => swapEntriesWithinRow row firstIndex secondIndex)
      (fun row => listPairSwapSelfInverse 0 row firstIndex secondIndex)
      matrix.rows)

/-! ## Column negate self-inverse -/

/-- **`negateColumn` is its own inverse** — negating a column twice restores the matrix. -/
theorem negateColumnInvolutive (matrix : IntMatrix) (colIndex : Nat) :
    (matrix.negateColumn colIndex).negateColumn colIndex = matrix :=
  intMatrixEqOfRowsEq
    (mapAllRowsCancel (fun row => listModifyAt (fun entry => -entry) row colIndex)
      (fun row => listModifyAt (fun entry => -entry) row colIndex)
      (fun row => listModifyAtCancelAt 0 (fun entry => -entry) (fun entry => -entry) row colIndex
        (intNegNeg (listGetWithDefault 0 row colIndex)))
      matrix.rows)

/-! ## The transvection cancels -/

/-- The scalar transvection cancel `(target + coefficient * source) + (-coefficient) * source = target`
(the head step of every transvection round-trip). -/
theorem intTransvectionCancel (target coefficient source : Int) :
    (target + coefficient * source) + (-coefficient) * source = target :=
  (intAddAssoc target (coefficient * source) ((-coefficient) * source)).trans
    ((congrArg (target + ·)
        ((intRightDistrib coefficient (-coefficient) source).symm.trans
          ((congrArg (· * source) (intAddRightNeg coefficient)).trans (intZeroMul source)))).trans
      (intAddZero target))

/-- Expand `addRowMultiple` when the indices are distinct and in range (avoids `unfold` touching a
nested transvection). -/
theorem addRowMultipleExpand (matrix : IntMatrix) (sourceIndex targetIndex : Nat) (coefficient : Int)
    (indexNe : sourceIndex ≠ targetIndex) (sourceInRange : sourceIndex < matrix.rows.length)
    (targetInRange : targetIndex < matrix.rows.length) :
    matrix.addRowMultiple sourceIndex targetIndex coefficient
      = { rows := listModifyAt (fun targetRow => addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
            matrix.rows targetIndex } := by
  unfold IntMatrix.addRowMultiple; rw [if_neg indexNe, if_pos sourceInRange, if_pos targetInRange]

/-- **The row transvection cancels at the matrix level** — `addRowMultiple s t c` followed by
`addRowMultiple s t (-c)` restores the matrix, for rectangular input (equal-length rows). -/
theorem addRowMultipleRoundTrip {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) (sourceIndex targetIndex : Nat) (coefficient : Int) :
    (matrix.addRowMultiple sourceIndex targetIndex coefficient).addRowMultiple sourceIndex targetIndex (-coefficient)
      = matrix := by
  obtain ⟨_, rowWidths⟩ := isRect
  by_cases indexEq : sourceIndex = targetIndex
  · subst indexEq
    have selfIdent : ∀ coeff, matrix.addRowMultiple sourceIndex sourceIndex coeff = matrix := by
      intro coeff; unfold IntMatrix.addRowMultiple; rw [if_pos rfl]
    rw [selfIdent, selfIdent]
  · by_cases sourceInRange : sourceIndex < matrix.rows.length
    · by_cases targetInRange : targetIndex < matrix.rows.length
      · have innerEq : (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows
            = listModifyAt (fun targetRow => addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
                matrix.rows targetIndex :=
          congrArg IntMatrix.rows (addRowMultipleExpand matrix sourceIndex targetIndex coefficient indexEq sourceInRange targetInRange)
        have innerLen : (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows.length = matrix.rows.length := by
          rw [innerEq]; exact listModifyAtPreservesLength _ _ _
        have getSource : listGetWithDefault [] (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows sourceIndex
            = listGetWithDefault [] matrix.rows sourceIndex :=
          addRowMultipleRowsGetOther matrix sourceIndex targetIndex sourceIndex coefficient indexEq
        apply intMatrixEqOfRowsEq
        rw [addRowMultipleExpand (matrix.addRowMultiple sourceIndex targetIndex coefficient) sourceIndex targetIndex (-coefficient)
              indexEq (by rw [innerLen]; exact sourceInRange) (by rw [innerLen]; exact targetInRange)]
        show listModifyAt (fun targetRow => addScaledEntries (-coefficient) (listGetWithDefault [] (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows sourceIndex) targetRow)
            (matrix.addRowMultiple sourceIndex targetIndex coefficient).rows targetIndex = matrix.rows
        rw [getSource, innerEq]
        exact listModifyAtCancelAt [] _ _ matrix.rows targetIndex
          (addScaledEntriesCancel coefficient (listGetWithDefault [] matrix.rows sourceIndex)
            (listGetWithDefault [] matrix.rows targetIndex)
            ((listGetWithDefaultHasWidth matrix.rows sourceIndex rowWidths sourceInRange).trans
              (listGetWithDefaultHasWidth matrix.rows targetIndex rowWidths targetInRange).symm))
      · have identOuter : ∀ coeff, matrix.addRowMultiple sourceIndex targetIndex coeff = matrix := by
          intro coeff; unfold IntMatrix.addRowMultiple
          rw [if_neg indexEq, if_pos sourceInRange, if_neg targetInRange]
        rw [identOuter, identOuter]
    · have identOuter : ∀ coeff, matrix.addRowMultiple sourceIndex targetIndex coeff = matrix := by
        intro coeff; unfold IntMatrix.addRowMultiple
        rw [if_neg indexEq, if_neg sourceInRange]
      rw [identOuter, identOuter]

/-- **The within-row column transvection cancels** — `addScaledEntryWithinRow row s t c` then
`… (-c)` restores the row, for `s ≠ t` (the column op's op-level guard). -/
theorem addScaledEntryWithinRowCancel (row : IntRow) (sourceIndex targetIndex : Nat) (coefficient : Int)
    (indexNe : sourceIndex ≠ targetIndex) :
    addScaledEntryWithinRow (addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
        sourceIndex targetIndex (-coefficient) = row := by
  by_cases sourceInRange : sourceIndex < row.length
  · have innerEq : addScaledEntryWithinRow row sourceIndex targetIndex coefficient
        = listModifyAt (fun targetEntry => targetEntry + coefficient * listGetWithDefault 0 row sourceIndex)
            row targetIndex := by
      unfold IntMatrix.addScaledEntryWithinRow; rw [if_pos sourceInRange]
    rw [innerEq]
    unfold IntMatrix.addScaledEntryWithinRow
    rw [if_pos (by rw [listModifyAtPreservesLength]; exact sourceInRange),
      listGetWithDefaultModifyAtNe 0 _ row targetIndex sourceIndex indexNe]
    exact listModifyAtCancelAt 0 _ _ row targetIndex
      (intTransvectionCancel (listGetWithDefault 0 row targetIndex) coefficient (listGetWithDefault 0 row sourceIndex))
  · have innerEq : addScaledEntryWithinRow row sourceIndex targetIndex coefficient = row := by
      unfold IntMatrix.addScaledEntryWithinRow; rw [if_neg sourceInRange]
    rw [innerEq]; unfold IntMatrix.addScaledEntryWithinRow; rw [if_neg sourceInRange]

/-- **The column transvection cancels at the matrix level.** -/
theorem addColumnMultipleRoundTrip (matrix : IntMatrix) (sourceIndex targetIndex : Nat) (coefficient : Int) :
    (matrix.addColumnMultiple sourceIndex targetIndex coefficient).addColumnMultiple sourceIndex targetIndex (-coefficient)
      = matrix := by
  by_cases indexEq : sourceIndex = targetIndex
  · subst indexEq
    have selfIdent : ∀ coeff, matrix.addColumnMultiple sourceIndex sourceIndex coeff = matrix := by
      intro coeff; unfold IntMatrix.addColumnMultiple; rw [if_pos rfl]
    rw [selfIdent, selfIdent]
  · have innerEq : matrix.addColumnMultiple sourceIndex targetIndex coefficient
        = { rows := mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient) matrix.rows } := by
      unfold IntMatrix.addColumnMultiple; rw [if_neg indexEq]
    apply intMatrixEqOfRowsEq
    rw [innerEq]
    show (({ rows := mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient) matrix.rows } : IntMatrix).addColumnMultiple
        sourceIndex targetIndex (-coefficient)).rows = matrix.rows
    unfold IntMatrix.addColumnMultiple
    rw [if_neg indexEq]
    exact mapAllRowsCancel (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
      (fun row => addScaledEntryWithinRow row sourceIndex targetIndex (-coefficient))
      (fun row => addScaledEntryWithinRowCancel row sourceIndex targetIndex coefficient indexEq)
      matrix.rows

/-! ## The single-operation dispatch and the whole-word fold round-trip -/

/-- **Every letter inverts** — firing an operation then its inverse restores the (rectangular) matrix.
Dispatches to the six per-constructor round-trips above. -/
theorem applyOperationInverseRoundTrip {height width : Nat} (operation : ElementaryOperation)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) :
    (matrix.applyOperation operation).applyOperation (inverseOperation operation) = matrix := by
  cases operation with
  | rowOperation rowOp =>
      cases rowOp with
      | swapRows firstIndex secondIndex => exact swapRowsSelfInverse matrix firstIndex secondIndex
      | negateRow rowIndex => exact negateRowInvolutive matrix rowIndex
      | addRowMultiple sourceIndex targetIndex coefficient =>
          exact addRowMultipleRoundTrip matrix isRect sourceIndex targetIndex coefficient
  | columnOperation colOp =>
      cases colOp with
      | swapColumns firstIndex secondIndex => exact swapColumnsSelfInverse matrix firstIndex secondIndex
      | negateColumn colIndex => exact negateColumnInvolutive matrix colIndex
      | addColumnMultiple sourceIndex targetIndex coefficient =>
          exact addColumnMultipleRoundTrip matrix sourceIndex targetIndex coefficient

/-- **THE FOLD ROUND-TRIP** — firing a whole certificate word then its `reverseOperationWord` undo word
restores the matrix (`M.applyOperations word` is ℤ-equivalent to `M`, and `reverseOperationWord` witnesses
the inverse).  Structural induction on the word: peel the head, ride the IH on the (rectangular) tail,
close the singleton with `applyOperationInverseRoundTrip`.  This is the ℤ-equivalence witness the
certificate design promised — every checked reduction is genuinely invertible. -/
theorem applyOperationsReverseRoundTrip {height width : Nat} :
    ∀ (word : List ElementaryOperation) (matrix : IntMatrix), matrix.IsRectangular height width →
      (matrix.applyOperations word).applyOperations (reverseOperationWord word) = matrix
  | [], _, _ => rfl
  | operation :: remainingWord, matrix, isRect => by
      show ((matrix.applyOperation operation).applyOperations remainingWord).applyOperations
            (reverseOperationWord remainingWord ++ [inverseOperation operation]) = matrix
      rw [applyOperationsAppend,
        applyOperationsReverseRoundTrip remainingWord (matrix.applyOperation operation)
          (applyOperationPreservesRectangular operation matrix isRect)]
      exact applyOperationInverseRoundTrip operation matrix isRect

/-! ## The B2 transport-fit — the reverse word is confined exactly where the forward word is -/

/-- The inverse letter keeps the SAME indices (it only flips the coefficient, which the confinement
check ignores), so its bounded-below flag is identical. -/
theorem inverseOperationBoundedBelow (lo : Nat) (operation : ElementaryOperation) :
    opIsBoundedBelow lo (inverseOperation operation) = opIsBoundedBelow lo operation := by
  cases operation with
  | rowOperation rowOp => cases rowOp <;> rfl
  | columnOperation colOp => cases colOp <;> rfl

/-- `allOpsBoundedBelow` computes over concatenation (the equational form). -/
theorem allOpsBoundedBelowAppendEq (lo : Nat) :
    ∀ (leadingWord trailingWord : List ElementaryOperation),
      allOpsBoundedBelow lo (leadingWord ++ trailingWord)
        = (allOpsBoundedBelow lo leadingWord && allOpsBoundedBelow lo trailingWord)
  | [], trailingWord => (boolTrueAndLeft (allOpsBoundedBelow lo trailingWord)).symm
  | operation :: remainingWord, trailingWord => by
      show (opIsBoundedBelow lo operation && allOpsBoundedBelow lo (remainingWord ++ trailingWord))
        = ((opIsBoundedBelow lo operation && allOpsBoundedBelow lo remainingWord) && allOpsBoundedBelow lo trailingWord)
      rw [allOpsBoundedBelowAppendEq lo remainingWord trailingWord, boolAndAssociate]

/-- **THE B2 TRANSPORT-FIT** — the reverse word is bounded below `lo` exactly when the forward word is.
So the shipped forward tower `applyOperationsPreservesEntriesDivisibleWithin` applies to
`reverseOperationWord S` for any confined sweep `S` — no re-derivation, no side condition. -/
theorem reverseOperationWordBoundedBelow (lo : Nat) :
    ∀ word : List ElementaryOperation,
      allOpsBoundedBelow lo (reverseOperationWord word) = allOpsBoundedBelow lo word
  | [] => rfl
  | operation :: remainingWord => by
      show allOpsBoundedBelow lo (reverseOperationWord remainingWord ++ [inverseOperation operation])
        = (opIsBoundedBelow lo operation && allOpsBoundedBelow lo remainingWord)
      rw [allOpsBoundedBelowAppendEq lo (reverseOperationWord remainingWord) [inverseOperation operation]]
      show (allOpsBoundedBelow lo (reverseOperationWord remainingWord) && (opIsBoundedBelow lo (inverseOperation operation) && true))
        = (opIsBoundedBelow lo operation && allOpsBoundedBelow lo remainingWord)
      rw [boolAndTrueRight, reverseOperationWordBoundedBelow lo remainingWord, inverseOperationBoundedBelow lo operation]
      exact boolAndCommute (allOpsBoundedBelow lo remainingWord) (opIsBoundedBelow lo operation)

end FX1Poly.ComputerAlgebra

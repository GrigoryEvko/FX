import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockRoundDescentRefuted
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeOutputBound

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachable — the Bezout-drop sibling round
    strictly descends the pivot magnitude on a clean cross (H2-SMITH r47, #2261)

## Where r46 left the mandate

r46 (`SmithBlockRoundDescentRefuted`) REFUTED the per-round `pivotMagnitudeWithin` descent of the
shipped whole-block round `smithBlockRoundOnce`: on the DIRTY-cross seed `[[2,0],[4,3]]` one round
RISES `2 -> 3` (the fold adds the dirty pivot-column entry `4` into the pivot slot, then the min-abs
cascade lands `3` verbatim, computing NO gcd), and on the zero-pivot seed `[[0,0],[0,4]]` it rises
`0 -> 4` off the measure floor.  So the graveyard forbids any UNGUARDED `pivotMagnitudeWithin` descent
of the shipped round, and Route A (hunt a subtler measure over the shipped min-abs fold) collapses into
the refuted "min-abs Euclid lands the gcd" characterization (K2).

## What this ships — the ADJUDICATED Route B (the literature is unanimous: amend the fold to a Bezout
   combination so the pivot itself descends by construction)

Both r46 refuters are UNREACHABLE loop states: `[[2,0],[4,3]]` has a dirty pivot cross, and
`[[0,0],[0,4]]` has a zero pivot; a reachable loop state (post `smithReduceTotal`, loop-threaded) is
cross-CLEAN with a nonzero pivot.  On that reachable restriction the descent is provable BY
CONSTRUCTION, reusing 100 %-shipped levers plus NO new fuel-induction gcd machinery:

  * `smithBezoutRepairRound` — a NEW SIBLING round (the r45 driver `smithRepairPositionSweepClearing
    InBlock` stays BYTE-INTACT): fold the found ROW into the pivot row, sign-normalise the pivot, fire
    ONE Bezout column-clear op that plants the residue `offender mod pivot` at `(pivotIndex, foundCol)`,
    then the shipped `smithCascadeSweep`.
  * **K1** `smithBezoutRoundStrictlyDescendsOnCleanCross` — on a clean-cross, positive-pivot, find-`some`
    rectangular state, one sibling round STRICTLY lowers `pivotMagnitudeWithin`.  The proof is a plain
    strict `<` (NOT the refuted `sdvd`): the residue is a nonzero minor witness of magnitude
    `intMagnitudeRemainder |pivot| offender < |pivot|` (shipped `smithSingleClearResidueLands` +
    `smithRotationDecreasesPivotSize`), so the shipped `smithCascadeSweepOutputPivotBounded` (never-raise,
    output `<=` any nonzero minor witness) lands the round's pivot `<= |residue| < |pivot|`.

The GUARD `smithPivotCrossClean` is load-bearing: K1 is a DIFFERENT proposition from the r46-refuted
UNGUARDED forall — it does not revive the graveyard measure.  Reachability MAINTENANCE (that the loop
keeps the cross clean) is the r48 fuel-adequacy gate, NOT claimed here.

## The mandate is NOT fired

The r46 mandate object `SmithReduceCompleteInBlockDriverStatement` stays UNINHABITED and BYTE-INTACT in
`SmithBlockFindRepairDriver`.  This file records the sibling driver's mandate Prop
`SmithReduceCompleteBezoutDriverStatement` with the IDENTICAL shape, likewise UNINHABITED
hypothesis-free (it needs K1 lifted to fuel adequacy (r48) AND the K2 chain twins AND the reduction
port).  The #2261 mandate fires on K1 and K2 and the mechanical reduction ONLY.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  ADDITIVE only — the r18-r46 world is byte-intact.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutRoundReachable.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## The reachable-state guard -/

/-- **The pivot cross is clean** — the reachable-loop invariant (a `Prop` lift of the shipped Bool
`smithCrossIsClear`): every entry of the pivot row right of the pivot and every entry of the pivot
column below it is zero.  Both r46 refuters violate it (`[[2,0],[4,3]]` has `entry(1,0) = 4`;
`[[0,0],[0,4]]` has a zero pivot handled by the separate positivity guard).  Decoded pointwise by the
shipped `smithCrossIsClearPointwise`. -/
def smithPivotCrossClean (matrix : IntMatrix) (pivotIndex height width : Nat) : Prop :=
  smithCrossIsClear matrix pivotIndex height width = true

/-! ## Magnitude-only arithmetic bridges for `intMagnitudeRemainder` -/

/-- **The magnitude remainder reads only the mantissa's magnitude** — `intMagnitudeRemainder divisor
mantissa` equals the counting remainder of `mantissa.natAbs` by `divisor`, since both `Int` arms feed
their `natAbs` into `natDivModCounting`.  `cases`-free `rfl` per constructor. -/
theorem intMagnitudeRemainderOnNatAbs (divisor : Nat) :
    ∀ mantissa : Int,
      intMagnitudeRemainder divisor mantissa = (natDivModCounting mantissa.natAbs divisor).snd
  | .ofNat _ => rfl
  | .negSucc _ => rfl

/-- **The magnitude remainder is a congruence in the mantissa's magnitude** — equal magnitudes give
equal remainders.  Rides `intMagnitudeRemainderOnNatAbs` on both sides. -/
theorem intMagnitudeRemainderNatAbsCongr (divisor : Nat) (leftMantissa rightMantissa : Int)
    (natAbsEq : leftMantissa.natAbs = rightMantissa.natAbs) :
    intMagnitudeRemainder divisor leftMantissa = intMagnitudeRemainder divisor rightMantissa :=
  (intMagnitudeRemainderOnNatAbs divisor leftMantissa).trans
    ((congrArg (fun magnitude => (natDivModCounting magnitude divisor).snd) natAbsEq).trans
      (intMagnitudeRemainderOnNatAbs divisor rightMantissa).symm)

/-- **`smithPivotDividesEntry` reads only the two magnitudes** — equal pivot magnitudes and equal entry
magnitudes give the same divisibility verdict, since the test is `natAbs`-gated on the pivot and a
magnitude-remainder on the entry. -/
theorem smithPivotDividesEntryNatAbsCongr (leftPivot leftEntry rightPivot rightEntry : Int)
    (pivotNatAbsEq : leftPivot.natAbs = rightPivot.natAbs)
    (entryNatAbsEq : leftEntry.natAbs = rightEntry.natAbs) :
    smithPivotDividesEntry leftPivot leftEntry = smithPivotDividesEntry rightPivot rightEntry := by
  unfold smithPivotDividesEntry
  rw [pivotNatAbsEq, entryNatAbsEq,
    intMagnitudeRemainderNatAbsCongr rightPivot.natAbs leftEntry rightEntry entryNatAbsEq]

/-! ## The sign phase preserves every pivot-row magnitude -/

/-- **The sign phase preserves the magnitude of any pivot-row entry** — the generalisation of the
shipped `smithSignNormalizeOpsPreservesPivotMagnitude` (which fixes `colIndex = pivotIndex`) to any
column of the pivot row: the negate branch flips the sign (`negateRowEntry` + `intNegNatAbs`), the empty
branch is the identity. -/
theorem smithSignNormalizeOpsPreservesRowMagnitude (matrix : IntMatrix) (pivotIndex colIndex : Nat)
    (isInRange : pivotIndex < matrix.rows.length) :
    ((matrix.applyOperations (smithSignNormalizeOps matrix pivotIndex)).entryAt pivotIndex colIndex).natAbs
      = (matrix.entryAt pivotIndex colIndex).natAbs := by
  show ((matrix.applyOperations
      (if matrix.entryAt pivotIndex pivotIndex < 0 then
        [ElementaryOperation.rowOperation (ElementaryRowOperation.negateRow pivotIndex)]
      else [])).entryAt pivotIndex colIndex).natAbs = _
  cases Int.decLt (matrix.entryAt pivotIndex pivotIndex) 0 with
  | isTrue isNegative =>
      rw [if_pos isNegative]
      show ((matrix.negateRow pivotIndex).entryAt pivotIndex colIndex).natAbs = _
      rw [negateRowEntry matrix pivotIndex colIndex isInRange]
      exact intNegNatAbs _
  | isFalse isNonNegative =>
      rw [if_neg isNonNegative]
      rfl

/-! ## The whole-block non-dividing find reports an interior, non-dividing position -/

/-- **A row scan's `some` reports its own row, an in-window column, and a non-dividing entry.**
Structural on the column count; the shipped `smithScanRowNonDividingInBlockFoundRow` gives only the row
half, this adds the column window and the guard-`false` witness the residue-nonzero step needs. -/
theorem smithScanRowNonDividingInBlockFound (matrix : IntMatrix) (pivotIndex rowIndex : Nat) :
    ∀ (colCount colStart foundRow foundCol : Nat),
      smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount colStart
          = some (foundRow, foundCol) →
      foundRow = rowIndex ∧ colStart ≤ foundCol ∧ foundCol < colStart + colCount ∧
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
            (matrix.entryAt foundRow foundCol) = false := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart foundRow foundCol findEq
      have contra : (none : Option (Nat × Nat)) = some (foundRow, foundCol) := findEq
      contradiction
  | succ colCount ih =>
      intro colStart foundRow foundCol findEq
      have hUnfold : smithScanRowNonDividingInBlock matrix pivotIndex rowIndex (colCount + 1) colStart
          = if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
                (matrix.entryAt rowIndex colStart) then
              smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount (colStart + 1)
            else some (rowIndex, colStart) := rfl
      rw [hUnfold] at findEq
      cases hGuard : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.entryAt rowIndex colStart) with
      | true =>
          rw [if_pos (by rw [hGuard] :
            smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
              (matrix.entryAt rowIndex colStart) = true)] at findEq
          obtain ⟨rowEq, colGe, colLt, guardFalse⟩ := ih (colStart + 1) foundRow foundCol findEq
          have colShiftEq : colStart + 1 + colCount = colStart + (colCount + 1) :=
            (Nat.succ_add colStart colCount).trans (Nat.add_succ colStart colCount).symm
          exact ⟨rowEq, Nat.le_of_succ_le colGe,
            Eq.mp (congrArg (foundCol < ·) colShiftEq) colLt, guardFalse⟩
      | false =>
          rw [if_neg (by rw [hGuard]; exact Bool.noConfusion :
            ¬ (smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
              (matrix.entryAt rowIndex colStart) = true))] at findEq
          have pairEq : (rowIndex, colStart) = (foundRow, foundCol) := Option.some.inj findEq
          have rowEq : foundRow = rowIndex := (congrArg Prod.fst pairEq).symm
          have colEq : foundCol = colStart := (congrArg Prod.snd pairEq).symm
          refine ⟨rowEq, Nat.le_of_eq colEq.symm,
            Eq.mp (congrArg (· < colStart + (colCount + 1)) colEq.symm)
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self colStart)
                (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le colCount)) colStart)), ?_⟩
          have entryEq : matrix.entryAt foundRow foundCol = matrix.entryAt rowIndex colStart := by
            rw [rowEq, colEq]
          rw [entryEq]; exact hGuard

/-- **A block scan's `some` reports an in-window position and a non-dividing entry.**  Structural on the
row count: the head-row hit rides the row lemma; the tail rides the IH.  Delivers the five facts K1
needs — `pivotIndex <= foundRow < height`, `pivotIndex <= foundCol < width`, and the pivot NOT dividing
`entry(foundRow, foundCol)`. -/
theorem smithScanBlockNonDividingFound (matrix : IntMatrix) (pivotIndex colStart colCount : Nat) :
    ∀ (rowCount rowStart foundRow foundCol : Nat),
      smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount rowStart
          = some (foundRow, foundCol) →
      rowStart ≤ foundRow ∧ foundRow < rowStart + rowCount ∧
        colStart ≤ foundCol ∧ foundCol < colStart + colCount ∧
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
            (matrix.entryAt foundRow foundCol) = false := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart foundRow foundCol findEq
      have contra : (none : Option (Nat × Nat)) = some (foundRow, foundCol) := findEq
      contradiction
  | succ rowCount ih =>
      intro rowStart foundRow foundCol findEq
      rw [smithScanBlockNonDividingSucc] at findEq
      cases hRow : smithScanRowNonDividingInBlock matrix pivotIndex rowStart colCount colStart with
      | some foundPair =>
          rw [hRow] at findEq
          have pairEq : foundPair = (foundRow, foundCol) := Option.some.inj findEq
          have hRowFound : smithScanRowNonDividingInBlock matrix pivotIndex rowStart colCount colStart
              = some (foundRow, foundCol) := pairEq ▸ hRow
          obtain ⟨rowEq, colGe, colLt, guardFalse⟩ :=
            smithScanRowNonDividingInBlockFound matrix pivotIndex rowStart colCount colStart
              foundRow foundCol hRowFound
          refine ⟨Nat.le_of_eq rowEq.symm, ?_, colGe, colLt, guardFalse⟩
          rw [rowEq]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rowStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rowCount)) rowStart)
      | none =>
          rw [hRow] at findEq
          obtain ⟨rowGe, rowLt, colGe, colLt, guardFalse⟩ := ih (rowStart + 1) foundRow foundCol findEq
          have rowShiftEq : rowStart + 1 + rowCount = rowStart + (rowCount + 1) :=
            (Nat.succ_add rowStart rowCount).trans (Nat.add_succ rowStart rowCount).symm
          exact ⟨Nat.le_of_succ_le rowGe,
            Eq.mp (congrArg (foundRow < ·) rowShiftEq) rowLt, colGe, colLt, guardFalse⟩

/-- **The whole-block find reports an interior, non-dividing position.**  Instantiates the block lemma
at the pivot window `[pivotIndex, height) x [pivotIndex, width)` and collapses the window sums by
`smithNatAddSubOfLe`.  The five facts K1 consumes. -/
theorem smithFindNonDividingInBlockSomeProperties (matrix : IntMatrix)
    (pivotIndex height width foundRow foundCol : Nat)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (findEq : smithFindNonDividingInBlock matrix pivotIndex height width = some (foundRow, foundCol)) :
    pivotIndex ≤ foundRow ∧ foundRow < height ∧ pivotIndex ≤ foundCol ∧ foundCol < width ∧
      smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.entryAt foundRow foundCol) = false := by
  obtain ⟨rowGe, rowLt, colGe, colLt, guardFalse⟩ :=
    smithScanBlockNonDividingFound matrix pivotIndex pivotIndex (width - pivotIndex)
      (height - pivotIndex) pivotIndex foundRow foundCol findEq
  exact ⟨rowGe,
    Eq.mp (congrArg (foundRow < ·) (smithNatAddSubOfLe pivotIndex height (Nat.le_of_lt pivotRowInRange)))
      rowLt,
    colGe,
    Eq.mp (congrArg (foundCol < ·) (smithNatAddSubOfLe pivotIndex width (Nat.le_of_lt pivotColInRange)))
      colLt,
    guardFalse⟩

/-! ## The pivot divides zero and divides itself (the guard-`false` contradictions) -/

/-- **The pivot divides zero** — `smithPivotDividesEntry pivot 0 = true` unconditionally (`0 = pivot * 0`,
through the shipped `smithPivotDividesEntryEncode`).  Rules out a cleared cross entry being the offender. -/
theorem smithPivotDividesEntryZero (pivotEntry : Int) :
    smithPivotDividesEntry pivotEntry 0 = true :=
  smithPivotDividesEntryEncode pivotEntry 0 ⟨0, (intMulZero pivotEntry).symm⟩

/-- **The pivot divides itself** — `smithPivotDividesEntry pivot pivot = true` unconditionally
(`pivot = pivot * 1`, through the shipped `smithPivotDividesEntryEncode`).  Rules out the pivot slot itself
being the offender. -/
theorem smithPivotDividesEntrySelf (pivotEntry : Int) :
    smithPivotDividesEntry pivotEntry pivotEntry = true :=
  smithPivotDividesEntryEncode pivotEntry pivotEntry ⟨1, (intMulOne pivotEntry).symm⟩

/-! ## On a clean cross the offender is STRICTLY interior -/

/-- **On a clean cross the found non-dividing offender is strictly interior** — both coordinates lie
STRICTLY beyond the pivot (`pivotIndex < foundRow` and `pivotIndex < foundCol`).  If either coordinate
equalled the pivot's, the offender entry would be the pivot itself (`smithPivotDividesEntrySelf`) or a
cleared cross entry (zero, `smithPivotDividesEntryZero`) — both DIVIDED, contradicting the find's
guard-`false`.  Strict interiority makes the fold `addRowMultiple foundRow pivotIndex 1` a genuine
distinct transvection AND lands the offender in the pivot row at a cleared (zero) slot. -/
theorem smithBezoutOffenderInterior (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (crossClean : smithPivotCrossClean work pivotIndex height width)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (foundRowLt : foundRow < height)
    (pivotLeFoundCol : pivotIndex ≤ foundCol) (foundColLt : foundCol < width)
    (guardFalse : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
        (work.entryAt foundRow foundCol) = false) :
    pivotIndex < foundRow ∧ pivotIndex < foundCol := by
  obtain ⟨rowRightZero, colBelowZero⟩ :=
    smithCrossIsClearPointwise work pivotIndex height width pRowLt pColLt crossClean
  cases Nat.eq_or_lt_of_le pivotLeFoundRow with
  | inr foundRowGt =>
      cases Nat.eq_or_lt_of_le pivotLeFoundCol with
      | inr foundColGt => exact ⟨foundRowGt, foundColGt⟩
      | inl pivotEqFoundCol =>
          have entryZero : work.entryAt foundRow foundCol = 0 := by
            rw [← pivotEqFoundCol]; exact colBelowZero foundRow foundRowGt foundRowLt
          have dividesTrue : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
              (work.entryAt foundRow foundCol) = true := by
            rw [entryZero]; exact smithPivotDividesEntryZero _
          exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)
  | inl pivotEqFoundRow =>
      cases Nat.eq_or_lt_of_le pivotLeFoundCol with
      | inr foundColGt =>
          have entryZero : work.entryAt foundRow foundCol = 0 := by
            rw [← pivotEqFoundRow]; exact rowRightZero foundCol foundColGt foundColLt
          have dividesTrue : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
              (work.entryAt foundRow foundCol) = true := by
            rw [entryZero]; exact smithPivotDividesEntryZero _
          exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)
      | inl pivotEqFoundCol =>
          have entryEq : work.entryAt foundRow foundCol = work.diagonalEntryAt pivotIndex := by
            show work.entryAt foundRow foundCol = work.entryAt pivotIndex pivotIndex
            rw [← pivotEqFoundRow, ← pivotEqFoundCol]
          have dividesTrue : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
              (work.entryAt foundRow foundCol) = true := by
            rw [entryEq]; exact smithPivotDividesEntrySelf _
          exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)

/-! ## The Bezout-drop sibling round (the NEW round; the r45 driver stays byte-intact) -/

/-- **The Bezout-drop round at a known found offender** — fold the found ROW into the pivot row, sign-
normalise the pivot nonnegative, fire ONE Bezout column-clear op that plants the residue
`offender mod pivot` at `(pivotIndex, foundCol)`, then the shipped `smithCascadeSweep`.  The
`smithBlockRoundOnce` sibling, but the middle phase is the CoqEAL `improve_pivot` Bezout column step (one
remainder-swap), so the landed pivot descends by CONSTRUCTION.  Returns the applied matrix. -/
def smithBezoutRepairRoundAtFound (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat) :
    IntMatrix :=
  let afterFold := work.addRowMultiple foundRow pivotIndex 1
  let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
  let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
    (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol)))
  afterClear.applyOperations
    (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex height width)

/-- **One Bezout-drop repair round** — dispatches on the whole-block find; `none` leaves `work` unchanged,
`some (foundRow, foundCol)` runs `smithBezoutRepairRoundAtFound`.  The K1 subject. -/
def smithBezoutRepairRound (work : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  match smithFindNonDividingInBlock work pivotIndex height width with
  | none => work
  | some (foundRow, foundCol) => smithBezoutRepairRoundAtFound work pivotIndex height width foundRow foundCol

/-! ## K1 — the per-round strict descent on a clean cross -/

/-- **K1 at a known STRICTLY-interior offender** — one Bezout-drop round strictly lowers the pivot
magnitude.  The proof is a plain strict `<` (NOT the refuted `sdvd`): the fold (a genuine distinct
transvection since `foundRow > pivotIndex`) preserves the pivot on the clean cross (`entry(foundRow,
pivotIndex) = 0`) and lands the offender in the pivot row at the cleared slot `(pivotIndex, foundCol)`
(`entry(pivotIndex, foundCol) = 0`); the sign phase preserves both magnitudes and makes the pivot
nonnegative; the single Bezout column op parks the residue `intMagnitudeRemainder |pivot| offender` there
(`smithSingleClearResidueLands`), which is nonzero (guard-`false`) and `< |pivot|`
(`smithRotationDecreasesPivotSize`); finally the shipped `smithCascadeSweepOutputPivotBounded` lands the
round's pivot `≤` that residue `< |pivot|`. -/
theorem smithBezoutRepairRoundAtFoundStrictlyDescends
    (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat)
    (isRect : work.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (pivotPositive : 0 < pivotMagnitudeWithin work pivotIndex)
    (crossClean : smithPivotCrossClean work pivotIndex height width)
    (foundRowGt : pivotIndex < foundRow) (foundRowLt : foundRow < height)
    (foundColGt : pivotIndex < foundCol) (foundColLt : foundCol < width)
    (guardFalse : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
        (work.entryAt foundRow foundCol) = false) :
    pivotMagnitudeWithin (smithBezoutRepairRoundAtFound work pivotIndex height width foundRow foundCol)
        pivotIndex
      < pivotMagnitudeWithin work pivotIndex := by
  obtain ⟨rowRightZero, colBelowZero⟩ :=
    smithCrossIsClearPointwise work pivotIndex height width pRowLt pColLt crossClean
  have workPivotPositive : 0 < (work.entryAt pivotIndex pivotIndex).natAbs := pivotPositive
  have workPivotNe : (work.entryAt pivotIndex pivotIndex).natAbs ≠ 0 := Nat.ne_of_gt workPivotPositive
  have foundRowNe : foundRow ≠ pivotIndex := fun eq => Nat.lt_irrefl pivotIndex (eq ▸ foundRowGt)
  have pivotNeFoundCol : pivotIndex ≠ foundCol := fun eq => Nat.lt_irrefl pivotIndex (eq ▸ foundColGt)
  -- The staged matrices (definitionally the round's `let`s).
  let afterFold := work.addRowMultiple foundRow pivotIndex 1
  let afterSign := afterFold.applyOperations (smithSignNormalizeOps afterFold pivotIndex)
  let afterClear := afterSign.addColumnMultiple pivotIndex foundCol
    (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol)))
  have afterFoldRect : afterFold.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
      work isRect
  have afterFoldRows : pivotIndex < afterFold.rows.length :=
    Eq.mp (congrArg (pivotIndex < ·) afterFoldRect.1.symm) pRowLt
  have afterSignRect : afterSign.IsRectangular height width :=
    applyOperationsPreservesRectangular (smithSignNormalizeOps afterFold pivotIndex) afterFold afterFoldRect
  -- The fold preserves the pivot and lands the offender in the pivot row.
  have foldPivot : afterFold.entryAt pivotIndex pivotIndex = work.entryAt pivotIndex pivotIndex := by
    show (work.addRowMultiple foundRow pivotIndex 1).entryAt pivotIndex pivotIndex
      = work.entryAt pivotIndex pivotIndex
    rw [addRowMultipleEntryOnTargetRow work isRect foundRow pivotIndex pivotIndex 1 foundRowNe foundRowLt
        pRowLt pColLt, colBelowZero foundRow foundRowGt foundRowLt, intMulZero, intAddZero]
  have foldOffender : afterFold.entryAt pivotIndex foundCol = work.entryAt foundRow foundCol := by
    show (work.addRowMultiple foundRow pivotIndex 1).entryAt pivotIndex foundCol
      = work.entryAt foundRow foundCol
    rw [addRowMultipleEntryOnTargetRow work isRect foundRow pivotIndex foundCol 1 foundRowNe foundRowLt
        pRowLt foundColLt, rowRightZero foundCol foundColGt foundColLt, intOneMul, intZeroAdd]
  -- The sign phase preserves both magnitudes and makes the pivot nonnegative and positive.
  have signPivotMag : (afterSign.entryAt pivotIndex pivotIndex).natAbs
      = (work.entryAt pivotIndex pivotIndex).natAbs :=
    (smithSignNormalizeOpsPreservesPivotMagnitude afterFold pivotIndex afterFoldRows).trans
      (congrArg Int.natAbs foldPivot)
  have signOffenderMag : (afterSign.entryAt pivotIndex foundCol).natAbs
      = (work.entryAt foundRow foundCol).natAbs :=
    (smithSignNormalizeOpsPreservesRowMagnitude afterFold pivotIndex foundCol afterFoldRows).trans
      (congrArg Int.natAbs foldOffender)
  have signNonneg : 0 ≤ afterSign.entryAt pivotIndex pivotIndex :=
    signNormalizeOpsEntryOnPivotNonneg afterFold pivotIndex afterFoldRows
  have signPivotPos : 0 < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
    Nat.lt_of_lt_of_le workPivotPositive (Nat.le_of_eq signPivotMag.symm)
  have afterClearRect : afterClear.IsRectangular height width :=
    applyOperationsPreservesRectangular
      [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple pivotIndex foundCol
        (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol))))]
      afterSign afterSignRect
  -- The single Bezout column op parks the residue at `(pivotIndex, foundCol)`.
  have residueLands : (afterClear.entryAt pivotIndex foundCol).natAbs
      = intMagnitudeRemainder (afterSign.entryAt pivotIndex pivotIndex).natAbs
          (afterSign.entryAt pivotIndex foundCol) :=
    smithSingleClearResidueLands afterSign afterSignRect pivotIndex foundCol pivotNeFoundCol pRowLt pColLt
      foundColLt signNonneg
  have residueDescends :
      intMagnitudeRemainder (afterSign.entryAt pivotIndex pivotIndex).natAbs
          (afterSign.entryAt pivotIndex foundCol)
        < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
    smithRotationDecreasesPivotSize (afterSign.entryAt pivotIndex pivotIndex)
      (afterSign.entryAt pivotIndex foundCol) signPivotPos
  -- The residue is nonzero: the guard-`false` says the pivot does not divide the offender.
  have workRemainderNe :
      intMagnitudeRemainder (work.entryAt pivotIndex pivotIndex).natAbs (work.entryAt foundRow foundCol)
        ≠ 0 := by
    intro remZero
    have guardCondFalse : ¬ (((work.entryAt pivotIndex pivotIndex).natAbs == 0) = true) := by
      rw [natBeqZeroFalseOfNe (work.entryAt pivotIndex pivotIndex).natAbs workPivotNe]
      exact fun isTrue => Bool.noConfusion isTrue
    have dividesTrue : smithPivotDividesEntry (work.diagonalEntryAt pivotIndex)
        (work.entryAt foundRow foundCol) = true := by
      show (if (work.entryAt pivotIndex pivotIndex).natAbs == 0 then
              (work.entryAt foundRow foundCol).natAbs == 0
            else intMagnitudeRemainder (work.entryAt pivotIndex pivotIndex).natAbs
              (work.entryAt foundRow foundCol) == 0) = true
      rw [if_neg guardCondFalse, remZero]
      rfl
    exact Bool.noConfusion (guardFalse.symm.trans dividesTrue)
  have residueBridge :
      intMagnitudeRemainder (afterSign.entryAt pivotIndex pivotIndex).natAbs
          (afterSign.entryAt pivotIndex foundCol)
        = intMagnitudeRemainder (work.entryAt pivotIndex pivotIndex).natAbs (work.entryAt foundRow foundCol) :=
    (congrArg (fun divisor => intMagnitudeRemainder divisor (afterSign.entryAt pivotIndex foundCol))
        signPivotMag).trans
      (intMagnitudeRemainderNatAbsCongr (work.entryAt pivotIndex pivotIndex).natAbs
        (afterSign.entryAt pivotIndex foundCol) (work.entryAt foundRow foundCol) signOffenderMag)
  have residueNonzero : (afterClear.entryAt pivotIndex foundCol).natAbs ≠ 0 := by
    rw [residueLands, residueBridge]; exact workRemainderNe
  -- The shipped cascade never raises the pivot above the parked residue.
  have cascadeBound :
      ((afterClear.applyOperations
          (smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex
            height width)).diagonalEntryAt pivotIndex).natAbs
        ≤ (afterClear.entryAt pivotIndex foundCol).natAbs :=
    smithCascadeSweepOutputPivotBounded (smithMinorAbsSum afterClear pivotIndex height width) afterClear
      pivotIndex afterClearRect pRowLt pColLt pivotIndex foundCol (Nat.le_refl pivotIndex) pRowLt
      (Nat.le_of_lt foundColGt) foundColLt residueNonzero (Nat.le_refl _)
  -- Assemble: round pivot ≤ residue < |pivot|.
  have residueLtPivot : (afterClear.entryAt pivotIndex foundCol).natAbs
      < (work.entryAt pivotIndex pivotIndex).natAbs :=
    Nat.lt_of_lt_of_le
      (Eq.mp (congrArg (· < (afterSign.entryAt pivotIndex pivotIndex).natAbs) residueLands.symm)
        residueDescends)
      (Nat.le_of_eq signPivotMag)
  exact Nat.lt_of_le_of_lt cascadeBound residueLtPivot

/-- **K1 — the Bezout-drop round strictly descends the pivot magnitude on a clean cross.**  On every
rectangular, clean-cross, positive-pivot, whole-block-find-`some` state, one Bezout-drop round STRICTLY
lowers `pivotMagnitudeWithin`.  The GUARD `smithPivotCrossClean` is load-bearing — this is a DIFFERENT
proposition from the r46-refuted UNGUARDED `SmithBlockRoundDescendsPerRound` (whose refuters
`[[2,0],[4,3]]` (dirty cross) and `[[0,0],[0,4]]` (zero pivot) are both EXCLUDED here), so it does NOT
revive the graveyard measure.  Refutation-immune: the descent is `output ≤ gcd-residue < |pivot|` BY
CONSTRUCTION, not a hunt for a subtler measure over the refuted min-abs fold. -/
theorem smithBezoutRoundStrictlyDescendsOnCleanCross
    (work : IntMatrix) (pivotIndex height width : Nat)
    (isRect : work.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (crossClean : smithPivotCrossClean work pivotIndex height width)
    (pivotPositive : 0 < pivotMagnitudeWithin work pivotIndex)
    (findSome : (smithFindNonDividingInBlock work pivotIndex height width).isSome = true) :
    pivotMagnitudeWithin (smithBezoutRepairRound work pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex := by
  cases hFind : smithFindNonDividingInBlock work pivotIndex height width with
  | none =>
      rw [hFind] at findSome
      exact Bool.noConfusion findSome
  | some foundPair =>
      obtain ⟨foundRow, foundCol⟩ := foundPair
      obtain ⟨pivotLeFoundRow, foundRowLt, pivotLeFoundCol, foundColLt, guardFalse⟩ :=
        smithFindNonDividingInBlockSomeProperties work pivotIndex height width foundRow foundCol
          pRowLt pColLt hFind
      obtain ⟨foundRowGt, foundColGt⟩ :=
        smithBezoutOffenderInterior work pivotIndex height width foundRow foundCol pRowLt pColLt
          crossClean pivotLeFoundRow foundRowLt pivotLeFoundCol foundColLt guardFalse
      have roundEq : smithBezoutRepairRound work pivotIndex height width
          = smithBezoutRepairRoundAtFound work pivotIndex height width foundRow foundCol := by
        unfold smithBezoutRepairRound; rw [hFind]
      rw [roundEq]
      exact smithBezoutRepairRoundAtFoundStrictlyDescends work pivotIndex height width foundRow foundCol
        isRect pRowLt pColLt pivotPositive crossClean foundRowGt foundRowLt foundColGt foundColLt guardFalse

/-! ## The Bezout-drop sibling DRIVER + its mandate Prop (recorded, honestly UNINHABITED)

The Bezout-drop round emits an operations WORD; the sibling driver `smithReduceCompleteBezout` mirrors the
shipped `smithReduceCompleteInBlock` structurally — cross-clear (`smithReduceTotal`), then the Bezout
divisibility-repair sweep, then the diagonal sign sweep — but the middle phase uses the Bezout-drop round
in place of the min-abs fold.  The shipped `smithReduceCompleteInBlock` and its mandate object
`SmithReduceCompleteInBlockDriverStatement` stay BYTE-INTACT.

Its mandate Prop `SmithReduceCompleteBezoutDriverStatement` is recorded with the IDENTICAL shape
(`∀ matrix height width, IsRectangular → reducesToSmithForm`).  It stays UNINHABITED hypothesis-free this
round: K1 is the per-round descent, but the mandate additionally needs K1 lifted to fuel adequacy (r48),
the K2 chain twins, AND the mechanical reduction port.  It is NEVER inhabited by a weakened variant. -/

/-- **The Bezout-drop round WORD at a known found offender** — the operational form of
`smithBezoutRepairRoundAtFound`: fold, sign, one Bezout column op, cascade.  Emits the certificate letters
so the sibling driver can compose them. -/
def smithBezoutRepairRoundWordAtFound (work : IntMatrix) (pivotIndex height width foundRow foundCol : Nat) :
    List ElementaryOperation :=
  let foldOps :=
    [ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1)]
  let afterFold := work.applyOperations foldOps
  let signOps := smithSignNormalizeOps afterFold pivotIndex
  let afterSign := afterFold.applyOperations signOps
  let bezoutOps :=
    [ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple pivotIndex foundCol
      (-(intPivotQuotient (afterSign.entryAt pivotIndex pivotIndex) (afterSign.entryAt pivotIndex foundCol))))]
  let afterClear := afterSign.applyOperations bezoutOps
  foldOps ++ signOps ++ bezoutOps ++
    smithCascadeSweep (smithMinorAbsSum afterClear pivotIndex height width) afterClear pivotIndex height width

/-- **One position's Bezout-drop repair sweep** — while a block entry is not divided by the pivot, emit
the Bezout-drop round word and loop on the reduced matrix; when the pivot divides the whole block, fire
the shipped cascade STANDALONE.  The `smithRepairPositionSweepClearingInBlock` sibling with the Bezout-drop
round.  Structural on `fuel`. -/
def smithBezoutRepairPositionSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | fuel + 1, matrix, pivotIndex, height, width =>
      match smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
      | some (foundRow, foundCol) =>
          let roundWord := smithBezoutRepairRoundWordAtFound matrix pivotIndex height width foundRow foundCol
          let afterRound := matrix.applyOperations roundWord
          roundWord ++ smithBezoutRepairPositionSweep fuel afterRound pivotIndex height width

/-- **The top-down Bezout-drop divisibility-repair sweep** — the `smithDivisibilityRepairSweepClearing
InBlock` sibling with the Bezout position sweep.  Structural on `outerFuel`. -/
def smithBezoutDivisibilityRepairSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | outerFuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let positionOps :=
          smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width
        let afterPosition := matrix.applyOperations positionOps
        positionOps ++
          smithBezoutDivisibilityRepairSweep outerFuel afterPosition (pivotIndex + 1) height width
      else []

/-- **The Bezout-drop sibling driver** — the cross-clearing `smithReduceTotal`, then the Bezout
divisibility-repair sweep, then the diagonal sign sweep.  Byte-for-byte `smithReduceCompleteInBlock`
except the middle phase uses `smithBezoutDivisibilityRepairSweep`.  A NEW sibling; the shipped
`smithReduceCompleteInBlock` and its consumers stay untouched. -/
def smithReduceCompleteBezout (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  let diagOps := (smithReduceTotal matrix height width).operations
  let afterDiag := matrix.applyOperations diagOps
  let repairOps := smithBezoutDivisibilityRepairSweep (Nat.min height width) afterDiag 0 height width
  let afterRepair := afterDiag.applyOperations repairOps
  let signOps := smithDiagonalSignSweep (Nat.min height width) afterRepair 0 height width
  { operations := diagOps ++ repairOps ++ signOps }

/-- **The Bezout-drop sibling driver mandate (uninhabited hypothesis-free)** — the ∀-correctness of the
Bezout-drop driver: `smithReduceCompleteBezout` emits a certificate reducing every rectangular integer
matrix to Smith normal form.  The IDENTICAL-shape sibling of the shipped
`SmithReduceCompleteInBlockDriverStatement`; it stays UNINHABITED hypothesis-free this round (needs K1
lifted to fuel adequacy + the K2 chain twins + the reduction port, all r48).  The #2261 mandate does NOT
fire in r47.  NEVER inhabited by a weakened variant. -/
def SmithReduceCompleteBezoutDriverStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduceCompleteBezout matrix height width).reducesToSmithForm matrix height width

end FX1Poly.ComputerAlgebra

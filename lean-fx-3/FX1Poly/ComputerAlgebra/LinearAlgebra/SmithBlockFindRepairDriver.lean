import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockDivisibilityKeystone
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithSubBlockContentInvariantProof
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithClearingHalvesFromKeystone

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBlockFindRepairDriver — the CORRECTED total driver
    (whole-block find repair) + the load-bearing find-none ⟺ block-divisibility bridge (H2-SMITH r45,
    #2261)

## The mandate object, sized honestly (read first)

The r44 keystone `blockDivisibilityImpliesAbsEqMinorGcd` is STATE-LOCAL under the WHOLE-BLOCK landing
condition `MatrixEntriesDivisibleByWithin (M'.diagonalEntryAt p) p M'` (the CoqEAL `improve_pivot`
postcondition `∀ i j, pivot ∣ block[i][j]`).  r44 also proved the OPERATIONAL landing predicate the
SHIPPED driver `smithReduceComplete` uses — nonzero pivot ∧ cross clear ∧ `smithFindNonDividingLater
Diagonal = none` — STRICTLY WEAKER: it is DIAGONAL-only, so the killer `[[6,0,0],[0,0,10],[0,0,0]]`
(and the anti-diagonal `[[2,0,0],[0,0,3],[0,3,0]]`) satisfy all three operational conjuncts on the
injected state yet miss the gcd, because the off-cross `10` at `(1,2)` escapes the diagonal scan
(`offCrossEntryEscapesDiagonalFind`).

This module ships the CORRECTED driver whose termination predicate is the WHOLE-BLOCK find, so the gap
closes AT THE PREDICATE LEVEL: the corrected find `= none` on the landed state is exactly the whole-block
divisibility hypothesis the r44 keystone consumes.  Concretely (all zero-axiom, additive; the shipped
`smithReduceComplete` and the r18–r44 world byte-intact):

  * **C1** `smithFindNonDividingInBlock` — scan the WHOLE `[p, ·)²` sub-block (not just the diagonal) for
    a pivot-non-dividing entry, plus `smithFindNonDividingInBlockSomeRowGe` (the found row sits at
    `≥ pivotIndex`, so the repair transvection is bounded below).
  * **C2, THE BRIDGE** `smithFindNonDividingInBlockNoneIffDivisibleWithin` — `find = none ⟺
    MatrixEntriesDivisibleByWithin (diagonalEntryAt p) p matrix`.  The exact decidable complement of the
    r44 keystone hypothesis: composed with `blockDivisibilityImpliesAbsEqMinorGcd` it fires the keystone
    at the corrected landing.
  * **The corrected repair WORD** `smithRepairPositionSweepClearingInBlock` (a NEW sibling — the shipped
    `smithRepairPositionSweepClearing` is byte-frozen) folding the FOUND ROW into the pivot row, its
    boundedness `smithRepairPositionSweepClearingInBlockBoundedBelow`, and the r43 content invariance
    `smithRepairInBlockPreservesMinorGcd` (the `[p, ·)²` block gcd survives the corrected word).
  * **C3, the state-local landing at the corrected driver** `smithRepairInBlockLandedFindNoneAbsEqInput
    MinorGcd` — IF the corrected repair's landed pivot has whole-block find-`none` (the corrected loop's
    OWN `none`-branch condition), then `|landed pivot| = gcd(INPUT minor)`.  The keystone through the C2
    bridge + r43 content invariance.  Hypothesis-bound only on the OPERATIONAL find-`none` (of the landed
    state), strictly weaker than r44's whole-block hypothesis.
  * **The KILLER PINS** `blockKillerACorrectedLandsMinorGcd` / `blockKillerBCorrectedLandsMinorGcd` — on
    both r44 killers, the corrected repair lands `|landed| = gcd` (`= 2`, `= 1`), the find-`none`-of-landed
    condition discharged by `decide` on the literal landed matrix.  Where the OLD (diagonal) repair lands
    `6` / `2` (WRONG), the corrected repair lands the gcd.

## HONEST SIZING — the #2261 mandate does NOT fire this round

Nothing here inhabits `SmithReduceCompleteInBlockDriverStatement` (the ∀-correctness of the corrected
driver) HYPOTHESIS-FREE.  C3 is bound on the operational find-`none` of the LANDED state; the REACHABILITY
question — does the fuelled sweep REACH a find-`none` state from an arbitrary input — is the deferred
fuel-adequacy (K1-analog), NAMED for r46 in the footer (`SmithReduceCompleteInBlockDriverStatement`,
`SmithBlockRepairReachesFindNone`).  The corrected loop takes EXPLICIT fuel (`smithMinorAbsSum`, as the
shipped drivers do); adequacy is a SEPARATE theorem, never smuggled.  The GRAVEYARD law holds: no
per-round single-Nat magnitude measure is wired as the loop's termination proof.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockFindRepairDriver.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## C1 — the corrected WHOLE-BLOCK non-dividing find -/

/-- **Scan `colCount` entries of row `rowIndex` from `colStart` for the first the pivot does not divide**
(the whole-block analog of `smithFindNonDividingLaterDiagonal`'s guard, reading `entryAt rowIndex colStart`
instead of the diagonal).  Structural on the column count; full-enum (`if`/`else some`, no wildcard). -/
def smithScanRowNonDividingInBlock (matrix : IntMatrix) (pivotIndex rowIndex : Nat) :
    Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | colCount + 1, colStart =>
      if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.entryAt rowIndex colStart) then
        smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount (colStart + 1)
      else some (rowIndex, colStart)

/-- **Scan `rowCount` rows from `rowStart`, each over `colCount` columns from `colStart`, for the first
pivot-non-dividing entry** — the row-major whole-block search.  Structural on the row count; full-enum
`match` on the row scan's `Option` (no wildcard). -/
def smithScanBlockNonDividing (matrix : IntMatrix) (pivotIndex colStart colCount : Nat) :
    Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | rowCount + 1, rowStart =>
      match smithScanRowNonDividingInBlock matrix pivotIndex rowStart colCount colStart with
      | some foundPair => some foundPair
      | none => smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount (rowStart + 1)

/-- **The whole `[pivotIndex, ·) × [pivotIndex, ·)` sub-block non-dividing search** — the corrected find,
scanning rows/cols `≥ pivotIndex` (INCLUSIVE at the pivot slot, which is trivially divisible so never
false-fires), the exact `smithMinorAbsSum`/`minorGcdWithin` window shape.  `none` iff the pivot divides
every block entry (`smithFindNonDividingInBlockNoneIffDivisibleWithin`). -/
def smithFindNonDividingInBlock (matrix : IntMatrix) (pivotIndex height width : Nat) :
    Option (Nat × Nat) :=
  smithScanBlockNonDividing matrix pivotIndex pivotIndex (width - pivotIndex)
    (height - pivotIndex) pivotIndex

/-- The block scan's successor unfold (structural `rfl`). -/
theorem smithScanBlockNonDividingSucc (matrix : IntMatrix) (pivotIndex colStart colCount rowCount rowStart : Nat) :
    smithScanBlockNonDividing matrix pivotIndex colStart colCount (rowCount + 1) rowStart
      = (match smithScanRowNonDividingInBlock matrix pivotIndex rowStart colCount colStart with
         | some foundPair => some foundPair
         | none => smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount (rowStart + 1)) :=
  rfl

/-! ### The found row sits at `≥ pivotIndex` (feeds boundedness) -/

/-- **A row scan reports its own row** — `smithScanRowNonDividingInBlock` at `rowIndex` returns a `some`
whose row coordinate IS `rowIndex` (every non-dividing hit lives on the scanned row).  Structural on the
column count. -/
theorem smithScanRowNonDividingInBlockFoundRow (matrix : IntMatrix) (pivotIndex rowIndex : Nat) :
    ∀ (colCount colStart foundRow foundCol : Nat),
      smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount colStart
          = some (foundRow, foundCol) →
      foundRow = rowIndex := by
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
          exact ih (colStart + 1) foundRow foundCol findEq
      | false =>
          rw [if_neg (by rw [hGuard]; exact Bool.noConfusion :
            ¬ (smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
              (matrix.entryAt rowIndex colStart) = true))] at findEq
          have pairEq : (rowIndex, colStart) = (foundRow, foundCol) := Option.some.inj findEq
          exact (congrArg Prod.fst pairEq).symm

/-- **The block scan returns a row `≥ rowStart`** — every non-dividing hit lies on the scanned rows.
Structural on the row count: the head-row hit returns `rowStart` (via `smithScanRowNonDividingInBlockFound
Row`), the tail rides the IH loosening the bound by one. -/
theorem smithScanBlockNonDividingRowGe (matrix : IntMatrix) (pivotIndex colStart colCount : Nat) :
    ∀ (rowCount rowStart foundRow foundCol : Nat),
      smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount rowStart
          = some (foundRow, foundCol) →
      rowStart ≤ foundRow := by
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
          have rowEq : foundRow = rowStart :=
            smithScanRowNonDividingInBlockFoundRow matrix pivotIndex rowStart colCount colStart
              foundRow foundCol (pairEq ▸ hRow)
          exact Nat.le_of_eq rowEq.symm
      | none =>
          rw [hRow] at findEq
          exact Nat.le_of_succ_le (ih (rowStart + 1) foundRow foundCol findEq)

/-- **The corrected find returns a row `≥ pivotIndex`** — the whole-block search reports a `some` whose
row coordinate is at or beyond the pivot, so `addRowMultiple foundRow pivotIndex 1` is bounded below by
the pivot (`opBoundedBelowAddRow`).  The dual of `smithFindMinAbsInMinorFoundInRange`, but only the row
side is needed for the fold-source boundedness. -/
theorem smithFindNonDividingInBlockSomeRowGe (matrix : IntMatrix) (pivotIndex height width foundRow foundCol : Nat)
    (findEq : smithFindNonDividingInBlock matrix pivotIndex height width = some (foundRow, foundCol)) :
    pivotIndex ≤ foundRow :=
  smithScanBlockNonDividingRowGe matrix pivotIndex pivotIndex (width - pivotIndex)
    (height - pivotIndex) pivotIndex foundRow foundCol findEq

/-! ## C2 — THE BRIDGE: `find = none ⟺ MatrixEntriesDivisibleByWithin` -/

/-- **A row scan whose window the pivot divides reports `none`** — the mpr row atom.  When
`smithPivotDividesEntry pivot (entryAt rowIndex col) = true` for every `col` in `[colStart, colStart +
colCount)`, the row scan finds nothing.  Structural on the column count (the `entryAt` mirror of
`smithFindNonDividingLaterDiagonalNoneOfAllDivide`). -/
theorem smithScanRowNonDividingInBlockNoneOfAllDivide (matrix : IntMatrix) (pivotIndex rowIndex : Nat) :
    ∀ (colCount colStart : Nat),
      (∀ col, colStart ≤ col → col < colStart + colCount →
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt rowIndex col) = true) →
      smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount colStart = none := by
  intro colCount
  induction colCount with
  | zero => intro colStart _; rfl
  | succ colCount ih =>
      intro colStart allDivide
      have hUnfold : smithScanRowNonDividingInBlock matrix pivotIndex rowIndex (colCount + 1) colStart
          = if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
                (matrix.entryAt rowIndex colStart) then
              smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount (colStart + 1)
            else some (rowIndex, colStart) := rfl
      rw [hUnfold]
      have guardTrue : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.entryAt rowIndex colStart) = true :=
        allDivide colStart (Nat.le_refl colStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self colStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le colCount)) colStart))
      rw [if_pos guardTrue]
      have colShiftEq : colStart + 1 + colCount = colStart + (colCount + 1) :=
        (Nat.succ_add colStart colCount).trans (Nat.add_succ colStart colCount).symm
      exact ih (colStart + 1) (fun col colGe colLt =>
        allDivide col (Nat.le_of_succ_le colGe)
          (Eq.mp (congrArg (col < ·) colShiftEq) colLt))

/-- **A block scan whose window the pivot divides reports `none`** — the mpr block lemma.  When every
in-window entry is pivot-divided (`smithPivotDividesEntry = true`), the whole-block search finds nothing.
Structural on the row count: the head row scan runs to `none` (the row lemma), so the `match` takes its
`none` branch and the tail rides the IH. -/
theorem smithScanBlockNonDividingNoneOfAllDivide (matrix : IntMatrix) (pivotIndex colStart colCount : Nat) :
    ∀ (rowCount rowStart : Nat),
      (∀ row, rowStart ≤ row → ∀ col, colStart ≤ col →
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt row col) = true) →
      smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount rowStart = none := by
  intro rowCount
  induction rowCount with
  | zero => intro rowStart _; rfl
  | succ rowCount ih =>
      intro rowStart allDivide
      rw [smithScanBlockNonDividingSucc,
        smithScanRowNonDividingInBlockNoneOfAllDivide matrix pivotIndex rowStart colCount colStart
          (fun col colGe _ => allDivide rowStart (Nat.le_refl rowStart) col colGe)]
      exact ih (rowStart + 1)
        (fun row rowGe col colGe => allDivide row (Nat.le_of_succ_le rowGe) col colGe)

/-- **A row scan reporting `none` divides its whole window** — the mp row atom.  When the row scan finds
nothing over `[colStart, colStart + colCount)`, the pivot divides (via the Bool test) every entry there.
Structural on the column count (the `entryAt` mirror of `smithFindNonDividingLaterDiagonalNoneDividesAll`
for one row). -/
theorem smithScanRowNonDividingInBlockNoneAll (matrix : IntMatrix) (pivotIndex rowIndex : Nat) :
    ∀ (colCount colStart : Nat),
      smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount colStart = none →
      ∀ col, colStart ≤ col → col < colStart + colCount →
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt rowIndex col) = true := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart _ col colGe colLt
      exact absurd
        (Nat.lt_of_lt_of_le (Eq.mp (congrArg (col < ·) (Nat.add_zero colStart)) colLt) colGe)
        (Nat.lt_irrefl col)
  | succ colCount ih =>
      intro colStart noneEq col colGe colLt
      have hUnfold : smithScanRowNonDividingInBlock matrix pivotIndex rowIndex (colCount + 1) colStart
          = if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
                (matrix.entryAt rowIndex colStart) then
              smithScanRowNonDividingInBlock matrix pivotIndex rowIndex colCount (colStart + 1)
            else some (rowIndex, colStart) := rfl
      rw [hUnfold] at noneEq
      cases hGuard : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.entryAt rowIndex colStart) with
      | false =>
          rw [if_neg (by rw [hGuard]; exact Bool.noConfusion :
            ¬ (smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
              (matrix.entryAt rowIndex colStart) = true))] at noneEq
          have contra : (some (rowIndex, colStart) : Option (Nat × Nat)) = none := noneEq
          contradiction
      | true =>
          rw [if_pos (by rw [hGuard] :
            smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
              (matrix.entryAt rowIndex colStart) = true)] at noneEq
          cases Nat.eq_or_lt_of_le colGe with
          | inl colStartEqCol =>
              rw [← colStartEqCol]; exact hGuard
          | inr colStartLtCol =>
              exact ih (colStart + 1) noneEq col colStartLtCol
                (Eq.mp (congrArg (col < ·) (Nat.succ_add colStart colCount).symm) colLt)

/-- **A block scan reporting `none` divides its whole window** — the mp block lemma.  When the whole-block
search finds nothing, the pivot divides (via the Bool test) every in-window entry.  Structural on the row
count: `none` forces the head row scan to `none` (so the row lemma gives the head row) AND the tail scan
to `none` (so later rows ride the IH). -/
theorem smithScanBlockNonDividingNoneAll (matrix : IntMatrix) (pivotIndex colStart colCount : Nat) :
    ∀ (rowCount rowStart : Nat),
      smithScanBlockNonDividing matrix pivotIndex colStart colCount rowCount rowStart = none →
      ∀ row, rowStart ≤ row → row < rowStart + rowCount →
        ∀ col, colStart ≤ col → col < colStart + colCount →
          smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt row col) = true := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart _ row rowGe rowLt col colGe colLt
      exact absurd
        (Nat.lt_of_lt_of_le (Eq.mp (congrArg (row < ·) (Nat.add_zero rowStart)) rowLt) rowGe)
        (Nat.lt_irrefl row)
  | succ rowCount ih =>
      intro rowStart noneEq row rowGe rowLt col colGe colLt
      rw [smithScanBlockNonDividingSucc] at noneEq
      cases hRow : smithScanRowNonDividingInBlock matrix pivotIndex rowStart colCount colStart with
      | some foundPair =>
          rw [hRow] at noneEq
          have contra : (some foundPair : Option (Nat × Nat)) = none := noneEq
          contradiction
      | none =>
          rw [hRow] at noneEq
          cases Nat.eq_or_lt_of_le rowGe with
          | inl rowStartEqRow =>
              rw [← rowStartEqRow]
              exact smithScanRowNonDividingInBlockNoneAll matrix pivotIndex rowStart colCount colStart
                hRow col colGe colLt
          | inr rowStartLtRow =>
              exact ih (rowStart + 1) noneEq row rowStartLtRow
                (Eq.mp (congrArg (row < ·) (Nat.succ_add rowStart rowCount).symm) rowLt) col colGe colLt

/-- **THE LOAD-BEARING BRIDGE** — the corrected find reports `none` iff the pivot divides EVERY entry of
the `[pivotIndex, ·)²` block.  `find = none ⟺ MatrixEntriesDivisibleByWithin (diagonalEntryAt pivotIndex)
pivotIndex matrix`.  The exact decidable complement of the r44 keystone hypothesis
`blockDivisibilityImpliesAbsEqMinorGcd`.  mpr (divisible → none) is the all-`true` block scan
(`smithScanBlockNonDividingNoneOfAllDivide` over `smithPivotDividesEntryEncode`, no `isRect`); mp (none →
divisible) splits beyond-window (`entryAtBeyondZero`, needs `isRect`) from in-window (the `none`-exit
forces the Bool test `true` via `smithScanBlockNonDividingNoneAll`, then `smithPivotDividesEntryDecode`). -/
theorem smithFindNonDividingInBlockNoneIffDivisibleWithin (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    smithFindNonDividingInBlock matrix pivotIndex height width = none
      ↔ MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt pivotIndex) pivotIndex matrix :=
  Iff.intro
    (fun findNone rowIndex rowGe colIndex colGe => by
      show dividesExactly (matrix.diagonalEntryAt pivotIndex) (matrix.entryAt rowIndex colIndex)
      cases Nat.lt_or_ge rowIndex height with
      | inr rowGeHeight =>
          rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inl rowGeHeight)]
          exact dividesExactlyZero (matrix.diagonalEntryAt pivotIndex)
      | inl rowLt =>
          cases Nat.lt_or_ge colIndex width with
          | inr colGeWidth =>
              rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inr colGeWidth)]
              exact dividesExactlyZero (matrix.diagonalEntryAt pivotIndex)
          | inl colLt =>
              exact smithPivotDividesEntryDecode _ _
                (smithScanBlockNonDividingNoneAll matrix pivotIndex pivotIndex (width - pivotIndex)
                  (height - pivotIndex) pivotIndex findNone rowIndex rowGe
                  (natLtAddSubOfLt pivotIndex rowIndex height rowGe rowLt) colIndex colGe
                  (natLtAddSubOfLt pivotIndex colIndex width colGe colLt)))
    (fun divisible =>
      smithScanBlockNonDividingNoneOfAllDivide matrix pivotIndex pivotIndex (width - pivotIndex)
        (height - pivotIndex) pivotIndex
        (fun row rowGe col colGe =>
          smithPivotDividesEntryEncode _ _
            (matrixEntriesDivisibleByWithinAt divisible row col rowGe colGe)))

/-! ## The CORRECTED repair WORD (a NEW sibling; the shipped `smithRepairPositionSweepClearing` is frozen)

`smithRepairPositionSweepClearingInBlock` is byte-for-byte `smithRepairPositionSweepClearing` EXCEPT the
`match` scrutinee is the WHOLE-BLOCK `smithFindNonDividingInBlock` (not the diagonal-only find) and the
fold source is the found ROW coordinate (not a diagonal index).  On a cross-cleared state the block find
always returns `foundRow ≥ pivotIndex` (the pivot slot and the cleared cross are divisible), so the
transvection `addRowMultiple foundRow pivotIndex 1` is genuine.  Structural on `fuel` (EXPLICIT; adequacy
deferred). -/

/-- One position's CORRECTED whole-block divisibility repair: while a block entry is not divided by the
pivot, fold that entry's ROW into the pivot row and re-fire the shipped Euclid cascade at the pivot; when
the pivot divides the whole block, fire the cascade STANDALONE.  The `smithRepairPositionSweepClearing`
twin with the whole-block find + found-row fold source.  Structural on `fuel`. -/
def smithRepairPositionSweepClearingInBlock : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | fuel + 1, matrix, pivotIndex, height, width =>
      match smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width
      | some (foundRow, _) =>
          let foldOps :=
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1) ]
          let afterFold := matrix.applyOperations foldOps
          let clearOps :=
            smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width)
              afterFold pivotIndex height width
          let afterClear := afterFold.applyOperations clearOps
          foldOps ++ clearOps ++
            smithRepairPositionSweepClearingInBlock fuel afterClear pivotIndex height width

/-- The corrected position sweep's successor unfold (structural `rfl`; feeds the boundedness proof). -/
theorem smithRepairPositionSweepClearingInBlockSucc (fuel : Nat) (matrix : IntMatrix)
    (pivotIndex height width : Nat) :
    smithRepairPositionSweepClearingInBlock (fuel + 1) matrix pivotIndex height width
      = (match smithFindNonDividingInBlock matrix pivotIndex height width with
         | none =>
             smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
               matrix pivotIndex height width
         | some (foundRow, _) =>
             let foldOps :=
               [ ElementaryOperation.rowOperation
                   (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1) ]
             let afterFold := matrix.applyOperations foldOps
             let clearOps :=
               smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width)
                 afterFold pivotIndex height width
             let afterClear := afterFold.applyOperations clearOps
             foldOps ++ clearOps ++
               smithRepairPositionSweepClearingInBlock fuel afterClear pivotIndex height width) :=
  rfl

/-- **The corrected repair word is bounded below the pivot** — every letter (the found-row fold, the
Euclid cascade, and the loop) is at indices `≥ pivotIndex ≥ lo`.  Structural on the fuel; the fold source
sits at `≥ pivotIndex` by `smithFindNonDividingInBlockSomeRowGe`, the target IS `pivotIndex`, the cascade
by `smithCascadeSweepBoundedBelow`.  So `minorGcdStableUnderBoundedWord` (r43) applies UNCHANGED to the
corrected word.  The `smithRepairPositionSweepClearingBoundedBelow` twin over the whole-block find. -/
theorem smithRepairPositionSweepClearingInBlockBoundedBelow (lo : Nat) :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      pivotIndex < height → pivotIndex < width → lo ≤ pivotIndex →
      allOpsBoundedBelow lo (smithRepairPositionSweepClearingInBlock fuel matrix pivotIndex height width) = true
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, matrix, pivotIndex, height, width, pivotRowInRange, pivotColInRange, pivotGe => by
      rw [smithRepairPositionSweepClearingInBlockSucc]
      cases hFind : smithFindNonDividingInBlock matrix pivotIndex height width with
      | none =>
          exact smithCascadeSweepBoundedBelow lo _ matrix pivotIndex height width
            pivotRowInRange pivotColInRange pivotGe
      | some foundPair =>
          obtain ⟨foundRow, foundCol⟩ := foundPair
          have foundRowGe : pivotIndex ≤ foundRow :=
            smithFindNonDividingInBlockSomeRowGe matrix pivotIndex height width foundRow foundCol hFind
          have foldBounded : allOpsBoundedBelow lo
              [ ElementaryOperation.rowOperation
                  (ElementaryRowOperation.addRowMultiple foundRow pivotIndex 1) ] = true :=
            boolAndBothTrue (opBoundedBelowAddRow lo foundRow pivotIndex 1
              (Nat.le_trans pivotGe foundRowGe) pivotGe) rfl
          exact allOpsBoundedBelowAppend lo _ _
            (allOpsBoundedBelowAppend lo _ _ foldBounded
              (smithCascadeSweepBoundedBelow lo _ _ pivotIndex height width
                pivotRowInRange pivotColInRange pivotGe))
            (smithRepairPositionSweepClearingInBlockBoundedBelow lo fuel _ pivotIndex height width
              pivotRowInRange pivotColInRange pivotGe)

/-- **The corrected repair word preserves the sub-block content** (r43 applied to the corrected word) —
`minorGcdWithin` of the `[pivotIndex, ·)²` block is INVARIANT across the corrected position repair.  The
boundedness (`smithRepairPositionSweepClearingInBlockBoundedBelow` at `lo := pivotIndex`) feeds
`minorGcdStableUnderBoundedWord`.  So the gcd of the LANDED minor equals the gcd of the INPUT minor. -/
theorem smithRepairInBlockPreservesMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    minorGcdWithin
        (matrix.applyOperations
          (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width
      = minorGcdWithin matrix pivotIndex height width :=
  minorGcdStableUnderBoundedWord _ matrix isRect
    (smithRepairPositionSweepClearingInBlockBoundedBelow pivotIndex
      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
      pRowLt pColLt (Nat.le_refl pivotIndex))

/-! ## C3 — the state-local landing AT THE CORRECTED DRIVER (the round headline, hypothesis-bound on the
    OPERATIONAL find-`none` of the landed state) -/

/-- **The corrected-driver localized keystone** — IF the corrected repair's landed pivot has whole-block
find-`none` (the corrected loop's OWN `none`-branch termination condition, on the LANDED state), THEN
`|landed pivot| = gcd(INPUT minor)`.  Route: the C2 bridge turns `find = none` into the whole-block
divisibility the r44 keystone `blockDivisibilityImpliesAbsEqMinorGcd` consumes, giving `|landed| =
gcd(LANDED minor)`; the r43 content invariance `smithRepairInBlockPreservesMinorGcd` rewrites the LANDED
minor gcd to the INPUT minor gcd.  Hypothesis-bound only on the OPERATIONAL find-`none` — strictly weaker
than r44's whole-block hypothesis, and EXACTLY the corrected loop's landing test.  The corrected-word twin
of r44's `landedDividesInputBlockImpliesAbsEqMinorGcd`, keyed on the operational (whole-block) find-`none`
rather than the whole-block divisibility directly. -/
theorem smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (landedFindNone :
      smithFindNonDividingInBlock
          (matrix.applyOperations
            (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          pivotIndex height width = none) :
    ((matrix.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs := by
  have landedRect :
      (matrix.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).IsRectangular height width :=
    applyOperationsPreservesRectangular _ matrix isRect
  have keystoneAtLanded := blockDivisibilityImpliesAbsEqMinorGcd
    (matrix.applyOperations
      (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width))
    pivotIndex height width landedRect
    ((smithFindNonDividingInBlockNoneIffDivisibleWithin _ pivotIndex height width landedRect).mp
      landedFindNone)
  rw [keystoneAtLanded, smithRepairInBlockPreservesMinorGcd matrix pivotIndex height width isRect pRowLt pColLt]

/-! ## The KILLER PINS — the r44 killers land `|landed| = gcd` through the corrected driver -/

/-- The r44 killer: nonzero pivot `6` at `(0,0)`, off-cross `10` at `(1,2)`. -/
def blockFindKillerA : IntMatrix := { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] }

theorem blockFindKillerAIsRectangular : blockFindKillerA.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **KILLER PIN A — the r44 keystone fires at the CORRECTED landing.**  Where the diagonal-only repair
lands `6` (`|6| ≠ 2 = gcd`, the r44 `operationallyLandedYetMissesMinorGcd`), the corrected whole-block
repair lands `|landed| = 2 = gcd(6, 10)`.  The landed pivot's whole-block find-`none` is `decide` on the
literal landed matrix (`[[2,0,0],[0,0,30],[0,0,0]]` — propext-clean); the keystone-through-bridge +
content invariance close it.  The round headline, kernel-checked. -/
theorem blockKillerACorrectedLandsMinorGcd :
    ((blockFindKillerA.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum blockFindKillerA 0 3 3)
          blockFindKillerA 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin blockFindKillerA 0 3 3).natAbs :=
  smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd blockFindKillerA 0 3 3
    blockFindKillerAIsRectangular (by decide) (by decide) (by decide)

/-- The corrected repair lands `|landed| = 2` on killer A (the concrete gcd, `decide`). -/
theorem blockKillerACorrectedLandsTwo :
    ((blockFindKillerA.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum blockFindKillerA 0 3 3)
          blockFindKillerA 0 3 3)).diagonalEntryAt 0).natAbs = 2 :=
  blockKillerACorrectedLandsMinorGcd.trans (by decide)

/-- The anti-diagonal r44 killer: nonzero pivot `2`, off-cross anti-diagonal `3`. -/
def blockFindKillerB : IntMatrix := { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] }

theorem blockFindKillerBIsRectangular : blockFindKillerB.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **KILLER PIN B — the anti-diagonal twin.**  Where the diagonal-only repair lands `2` (`|2| ≠ 1 = gcd`),
the corrected whole-block repair lands `|landed| = 1 = gcd(2, 3, 3)`.  The landed literal is
`[[1,0,0],[0,0,-6],[0,3,0]]`; find-`none` is `decide`. -/
theorem blockKillerBCorrectedLandsMinorGcd :
    ((blockFindKillerB.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum blockFindKillerB 0 3 3)
          blockFindKillerB 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin blockFindKillerB 0 3 3).natAbs :=
  smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd blockFindKillerB 0 3 3
    blockFindKillerBIsRectangular (by decide) (by decide) (by decide)

/-- The corrected repair lands `|landed| = 1` on the anti-diagonal killer B (`decide`). -/
theorem blockKillerBCorrectedLandsOne :
    ((blockFindKillerB.applyOperations
        (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum blockFindKillerB 0 3 3)
          blockFindKillerB 0 3 3)).diagonalEntryAt 0).natAbs = 1 :=
  blockKillerBCorrectedLandsMinorGcd.trans (by decide)

/-! ## The corrected total driver (full three-phase; only the middle-phase find changes) -/

/-- The top-down CORRECTED-clearing divisibility-repair sweep: the `smithDivisibilityRepairSweepClearing`
twin with the whole-block repair in place of the diagonal one.  Structural on `outerFuel`. -/
def smithDivisibilityRepairSweepClearingInBlock : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | outerFuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let positionOps :=
          smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width
        let afterPosition := matrix.applyOperations positionOps
        positionOps ++
          smithDivisibilityRepairSweepClearingInBlock outerFuel afterPosition (pivotIndex + 1) height width
      else []

/-- **The CORRECTED total driver** — the cross-clearing `smithReduceTotal`, then the WHOLE-BLOCK
divisibility-repair sweep, then the final sign sweep.  Byte-for-byte `smithReduceComplete` except the
middle phase uses `smithDivisibilityRepairSweepClearingInBlock`.  A NEW sibling; the shipped
`smithReduceComplete` and its consumers stay untouched. -/
def smithReduceCompleteInBlock (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  let diagOps := (smithReduceTotal matrix height width).operations
  let afterDiag := matrix.applyOperations diagOps
  let repairOps :=
    smithDivisibilityRepairSweepClearingInBlock (Nat.min height width) afterDiag 0 height width
  let afterRepair := afterDiag.applyOperations repairOps
  let signOps := smithDiagonalSignSweep (Nat.min height width) afterRepair 0 height width
  { operations := diagOps ++ repairOps ++ signOps }

/-! ## SURVIVING WALL + C4, NAMED for r46 (H2-SMITH r45, #2261)

The C2 bridge closes the r44 gap AT THE PREDICATE LEVEL: the corrected find `= none` on the landed state
is EXACTLY the whole-block divisibility the r44 keystone consumes, so the keystone fires at the corrected
landing (`smithRepairInBlockLandedFindNoneAbsEqInputMinorGcd`, and the killer pins).  But nothing here
inhabits the ∀-correctness of the corrected driver HYPOTHESIS-FREE.

Two residuals remain, BOTH named below and deferred to r46, honestly:

  1. **Fuel adequacy (K1-analog)** — `SmithBlockRepairReachesFindNone`: that the fuelled corrected sweep
     REACHES a whole-block find-`none` state from an arbitrary rectangular input.  The corrected loop takes
     EXPLICIT fuel (`smithMinorAbsSum`); this adequacy is a SEPARATE theorem, never smuggled.  The
     web-literature route (CoqEAL `improve_pivot_rec` + `sdvd_Bezout_step` + `ltn_enorm`) is a strict
     Euclidean-norm descent: each firing round lands `gcd(pivot, offender)` with `pivot ∤ offender`, so
     `|new pivot| < |old pivot|` and `new pivot ∣ old pivot` (the `sdvd` shape, probed 15/15 with no rise —
     unlike the diagonal find, r41).  The GRAVEYARD law forbids wiring a per-round single-Nat magnitude
     measure AS the loop's termination proof; the loop stays explicit-fuel and adequacy is the r46 arc.
  2. **The two window-diagonal / chain invariants** — `SmithReduceCompleteInBlockDriverStatement` reduces
     (as `smithReduceComplete` did via `smithReduceCompleteDriverOfRepairInvariants`) to the corrected
     repair output being window-diagonal at `0` and full-prefix-chain-dividing; the chain half rides the
     per-pivot ESTABLISH seed threaded across pivots (the corrected-word twins of `minorGcdDividesLanded`
     + `landedDividesInputBlockImpliesAbsEqMinorGcd`, mechanical re-instantiations over the bounded
     corrected word — but PLUS the fuel adequacy of (1)).

The #2261 mandate does NOT fire this round.  The corrected driver is honestly WALLED. -/

/-- **C4, NAMED (uninhabited hypothesis-free)** — the ∀-correctness of the CORRECTED driver:
`smithReduceCompleteInBlock` emits a certificate reducing every rectangular integer matrix to Smith
normal form.  The corrected-driver analogue of the shipped `SmithReduceCompleteDriverStatement`; it stays
UNINHABITED hypothesis-free this round (needs the fuel adequacy `SmithBlockRepairReachesFindNone` + the
corrected-word chain twins).  Deferred to r46; NOT flagged mandate-fired. -/
def SmithReduceCompleteInBlockDriverStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduceCompleteInBlock matrix height width).reducesToSmithForm matrix height width

/-- **The deferred fuel-adequacy residual (K1-analog), NAMED for r46** — that the fuelled corrected
whole-block repair sweep REACHES a find-`none` state (the loop's landing condition) from an arbitrary
rectangular input.  The strict-divisibility Euclidean-norm descent (CoqEAL `sdvd_Bezout_step`/`ltn_enorm`)
is the route; the loop stays EXPLICIT-fuel, adequacy separate.  Not inhabited this round. -/
def SmithBlockRepairReachesFindNone : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    smithFindNonDividingInBlock
        (matrix.applyOperations
          (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width = none

end FX1Poly.ComputerAlgebra

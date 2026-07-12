import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinNonzeroAbsDescent
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorTransportEquivalence

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithPivotMagnitudeDescent — the CORRECTED descent measure
    `pivotMagnitudeWithin`; the zero-pivot seam scoped away; the correct per-pivot statement
    (H2-SMITH r27, #2261)

r26 (`SmithMinNonzeroAbsDescent`) shipped the candidate `minNonzeroAbsWithin` and machine-CORRECTED its own
recon: `minNonzeroAbs` never rises but STALLS on two fold classes (already-minimal, zero-pivot bootstrap),
so it is not a strict descent measure and a lex refinement was demanded.  **r27 supersedes that demand.**
The eval-traced stall autopsy (recon STEP 2) shows the STALLING quantity is the WRONG one: on the exact r26
stall fixture `diag(15, 10, 6, 4)` the pivot magnitude `pivotAbs := |diagonalEntryAt p|` strictly DESCENDS
`15 -> 4 -> 2 -> 1` on every fold — including the step where `minNonzeroAbs` stalled `4 = 4`.  Switching the
measure to `pivotAbs` DISSOLVES stall class 1.  The ONLY shape that RAISES `pivotAbs` is the zero-pivot
bootstrap (fold fires with pivot `0`), and that arm is UNREACHABLE in the driver's repair input: the find
scan reads DIAGONALS, `0` divides only `0`, and the diagonal is zero-trailing after `smithReduceTotal`, so
`find = some ==> pivot != 0`.  **No lex, no budget clash — `pivotAbs` is a plain Nat that fits the fuel.**

**This module ships (probe-first `#eval`, then `decide`; all at or below the 4x4 defeq ceiling).**

  * `pivotMagnitudeWithin` — the corrected measure `|matrix.diagonalEntryAt pivotIndex|`.
  * `smithPivotMagnitudeDescendsWhereMinNonzeroAbsStalls` — on the EXACT r26 already-minimal stall fixture
    `diag(15, 10, 6, 4)` where `minNonzeroAbsWithin` STALLED `4 = 4`, `pivotMagnitudeWithin` strictly DROPS
    `4 < 15`.  The headline correction: the measure that beats r26's stall.
  * `smithPivotMagnitudeDescendsOnAdversaryBattery` — three more strict drops on hostile same-magnitude
    diagonals (`diag(6,9,10,10)` `6 -> 3`, `diag(12,8,8,8)` `12 -> 4`, `diag(10,4,4)` `10 -> 2`).
  * `smithPivotMagnitudeRisesOnZeroPivotBootstrap` — the SOLE counter-shape, isolated: on `diag(0, 4)` the
    pivot is `0` and the fold RAISES `pivotAbs` `0 -> 4`.  The one obstruction, named.
  * `pivotMagnitudeLeMinorAbsSum` — the budget fit `pivotAbs <= smithMinorAbsSum` (the pivot is one summed
    minor magnitude); free, no lex weighting — this is why the "budget clash" (recon Delta2) is dodged.
  * `smithZeroPivotImpliesFindNone` — the scope: a zero pivot with zero-trailing later diagonals forces the
    find-loop `none`-exit, so the zero-pivot fold arm CANNOT fire under zero-trailing.  Hypothesis-free
    structural (mirrors the shipped `smithFindNonDividingLaterDiagonalNoneDividesAll`).
  * `SmithFoldDescendsOnNonzeroPivot` — the NAMED r28 obligation: `pivotAbs` strictly drops on every
    NONZERO-pivot fold.  A `def ... : Prop` (NOT proved); battery-verified TRUE on the STEP-2 + adversary
    fixtures (`smithFoldDescendsHoldsOnBattery`).
  * `smithClearingSweepReachesFindNoneOfGuardedDescent` — the GUARDED NODE-D variant (threads an invariant
    so the `pivotAbs` measure is only asked to descend where the guard holds); LANDS unconditionally.
  * `smithClearingOutputFindNoneFromFoldDescent` — the fuel-adequacy reduction: `SmithClearingOutputFindNone`
    follows from `SmithFoldDescendsOnNonzeroPivot` + a zero-trailing invariant preserved by the fold, with
    the base zero-trailing supplied at the sweep input.  The `pivotAbs` correction WIRED to fuel-adequacy.
  * `seedOfClearingFindNoneAndOffDiagonalResidual` + `smithReduceCompleteDriverOfFindNoneAndOffDiagonal` —
    the CORRECT per-pivot statement: the driver seed (hence `SmithReduceCompleteDriverStatement`) reduces to
    (fuel-adequacy `SmithClearingOutputFindNone`) + (the off-diagonal half `SmithClearingOutputOffDiagonalDivides`).
    The diagonal half is discharged by fuel-adequacy; the OFF-DIAGONAL half is the irreducible
    "min-abs Euclid computes the gcd" wall (K2), now isolated ALONE (a strict sharpening of the whole-block seed).

**HONEST SIZING — this does NOT inhabit `SmithReduceCompleteDriverStatement` hypothesis-free.**  It is a
MEASURE CORRECTION + REDUCTION SKELETON round.  The single deep obligation r27 hands to r28 is
`SmithFoldDescendsOnNonzeroPivot` (the cascade-output-pivot strict descent, a cascade-inner induction) →
fuel-adequacy → keystone diagonal half; the OFF-DIAGONAL half `SmithClearingOutputOffDiagonalDivides` remains
the irreducible gcd-ideal wall.  The seam is named IN THIS FILE (footer).  Additive only: the r18-r26 world,
`smithReduceComplete`, and the driver stay byte-intact.

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithPivotMagnitudeDescent.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Brick 1 — the corrected measure `pivotMagnitudeWithin` -/

/-- **The corrected descent measure** — the magnitude of the pivot diagonal entry.  Unlike r26's
`minNonzeroAbsWithin` (which stalls on already-minimal folds), THIS strictly descends on every nonzero-pivot
fold (the STEP-2 autopsy: `15 -> 4 -> 2 -> 1`), and it is a plain `Nat` that fits the fuel budget with no
lex weighting. -/
def pivotMagnitudeWithin (matrix : IntMatrix) (pivotIndex : Nat) : Nat :=
  (matrix.diagonalEntryAt pivotIndex).natAbs

/-! ## propext-clean `Nat` subtraction facts (Init's `Nat.sub_pos_of_lt` / `Nat.sub_eq_zero_of_le` leak
propext; these are structural over `Nat.succ_sub_succ`) -/

/-- `smaller < larger` gives `0 < larger - smaller`.  Structural; propext-clean (Init's
`Nat.sub_pos_of_lt` drags propext). -/
theorem natSubPositiveOfLt : ∀ (smaller larger : Nat), smaller < larger → 0 < larger - smaller
  | 0, 0, isLt => absurd isLt (Nat.not_lt_zero 0)
  | 0, Nat.succ upper, _ => Nat.succ_pos upper
  | Nat.succ _, 0, isLt => absurd isLt (Nat.not_lt_zero _)
  | Nat.succ smallerPred, Nat.succ upperPred, isLt =>
      (Nat.succ_sub_succ upperPred smallerPred).symm ▸
        natSubPositiveOfLt smallerPred upperPred (Nat.lt_of_succ_lt_succ isLt)

/-- `smaller ≤ larger` gives `smaller - larger = 0`.  Structural; propext-clean (Init's
`Nat.sub_eq_zero_of_le` drags propext). -/
theorem natSubEqZeroOfLe : ∀ (smaller larger : Nat), smaller ≤ larger → smaller - larger = 0
  | 0, larger, _ => Nat.zero_sub larger
  | Nat.succ smallerPred, 0, isLe => absurd isLe (Nat.not_succ_le_zero smallerPred)
  | Nat.succ smallerPred, Nat.succ largerPred, isLe =>
      (Nat.succ_sub_succ smallerPred largerPred).trans
        (natSubEqZeroOfLe smallerPred largerPred (Nat.le_of_succ_le_succ isLe))

/-! ## Bricks 2-3 — the measure's fold behaviour: strict drop where r26 STALLED, single zero-pivot rise -/

set_option maxRecDepth 8000 in
/-- **The corrected measure DROPS where r26's STALLED.**  On the EXACT `diag(15, 10, 6, 4)` pivot-`0` fold
where `smithMinNonzeroAbsStallsOnAlreadyMinimalFold` shows `minNonzeroAbsWithin` STALLS `4 = 4`,
`pivotMagnitudeWithin` strictly DESCENDS `4 < 15`.  The r26 already-minimal stall class DISSOLVES under the
corrected measure — this is the headline machine-correction of r26's "the measure needs a lex refinement". -/
theorem smithPivotMagnitudeDescendsWhereMinNonzeroAbsStalls :
    pivotMagnitudeWithin
        (smithClearingFoldStep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 1 0 4 4) 0
      < pivotMagnitudeWithin { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 := by
  decide

set_option maxRecDepth 8000 in
/-- **Three more strict drops on hostile same-magnitude diagonals.**  `diag(6, 9, 10, 10)` `6 -> 3`,
`diag(12, 8, 8, 8)` `12 -> 4`, `diag(10, 4, 4)` `10 -> 2` — each an adversary where the later diagonals
repeat magnitudes; `pivotMagnitudeWithin` strictly drops on every one (the find-`some` fold lands the
pair-gcd, strictly below the pivot). -/
theorem smithPivotMagnitudeDescendsOnAdversaryBattery :
    pivotMagnitudeWithin
        (smithClearingFoldStep { rows := [[6, 0, 0, 0], [0, 9, 0, 0], [0, 0, 10, 0], [0, 0, 0, 10]] } 1 0 4 4) 0
      < pivotMagnitudeWithin { rows := [[6, 0, 0, 0], [0, 9, 0, 0], [0, 0, 10, 0], [0, 0, 0, 10]] } 0
    ∧ pivotMagnitudeWithin
        (smithClearingFoldStep { rows := [[12, 0, 0, 0], [0, 8, 0, 0], [0, 0, 8, 0], [0, 0, 0, 8]] } 1 0 4 4) 0
      < pivotMagnitudeWithin { rows := [[12, 0, 0, 0], [0, 8, 0, 0], [0, 0, 8, 0], [0, 0, 0, 8]] } 0
    ∧ pivotMagnitudeWithin
        (smithClearingFoldStep { rows := [[10, 0, 0], [0, 4, 0], [0, 0, 4]] } 1 0 3 3) 0
      < pivotMagnitudeWithin { rows := [[10, 0, 0], [0, 4, 0], [0, 0, 4]] } 0 := by
  decide

set_option maxRecDepth 8000 in
/-- **The SOLE counter-shape — the zero-pivot bootstrap RAISES `pivotAbs`.**  On `diag(0, 4)` pivot-`0` the
pivot is `0`; the fold jumps `pivotMagnitudeWithin` `0 -> 4` (up, not down).  This is the ONLY fold arm on
which `pivotMagnitudeWithin` is not a descent — isolated here as the single obstruction, then proven
driver-UNREACHABLE by `smithZeroPivotImpliesFindNone` below (a zero pivot forces the find-`none` exit, so
this arm never fires under zero-trailing). -/
theorem smithPivotMagnitudeRisesOnZeroPivotBootstrap :
    ({ rows := [[0, 0], [0, 4]] } : IntMatrix).diagonalEntryAt 0 = 0 ∧
    pivotMagnitudeWithin { rows := [[0, 0], [0, 4]] } 0
      < pivotMagnitudeWithin (smithClearingFoldStep { rows := [[0, 0], [0, 4]] } 1 0 2 2) 0 := by
  decide

/-! ## Brick budget — `pivotMagnitudeWithin` fits the fuel (`smithMinorAbsSum`); no lex, no clash -/

/-- The head magnitude of a nonempty row segment is `<=` the segment's magnitude sum (the pivot column is
the first summand). -/
theorem smithRowAbsSumHeadLe (matrix : IntMatrix) (rowIndex colStart : Nat) :
    ∀ colCount, 0 < colCount →
      (matrix.entryAt rowIndex colStart).natAbs ≤ smithRowAbsSum matrix rowIndex colCount colStart := by
  intro colCount colPos
  cases colCount with
  | zero => exact absurd colPos (Nat.lt_irrefl 0)
  | succ colPredecessor =>
      show (matrix.entryAt rowIndex colStart).natAbs
        ≤ (matrix.entryAt rowIndex colStart).natAbs
            + smithRowAbsSum matrix rowIndex colPredecessor (colStart + 1)
      exact Nat.le_add_right _ _

/-- The head row's magnitude sum is `<=` the whole minor's magnitude sum (the pivot row is the first
summand). -/
theorem smithMinorAbsSumRowsHeadLe (matrix : IntMatrix) (colStart colCount rowStart : Nat) :
    ∀ rowCount, 0 < rowCount →
      smithRowAbsSum matrix rowStart colCount colStart
        ≤ smithMinorAbsSumRows matrix colStart colCount rowCount rowStart := by
  intro rowCount rowPos
  cases rowCount with
  | zero => exact absurd rowPos (Nat.lt_irrefl 0)
  | succ rowPredecessor =>
      show smithRowAbsSum matrix rowStart colCount colStart
        ≤ smithRowAbsSum matrix rowStart colCount colStart
            + smithMinorAbsSumRows matrix colStart colCount rowPredecessor (rowStart + 1)
      exact Nat.le_add_right _ _

/-- **The budget fit** — `pivotMagnitudeWithin matrix pivotIndex <= smithMinorAbsSum matrix pivotIndex
height width` whenever the pivot is in range.  The pivot entry is the first summand of the first row of the
minor magnitude sum, so `pivotAbs <= smithMinorAbsSum`.  This is the payoff that dodges the budget clash
(recon Delta2): `pivotAbs` is already a plain `Nat` that fits the fuel — no lex collapse, no reweighting. -/
theorem pivotMagnitudeLeMinorAbsSum (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    pivotMagnitudeWithin matrix pivotIndex ≤ smithMinorAbsSum matrix pivotIndex height width := by
  have entryLe : (matrix.entryAt pivotIndex pivotIndex).natAbs
      ≤ smithRowAbsSum matrix pivotIndex (width - pivotIndex) pivotIndex :=
    smithRowAbsSumHeadLe matrix pivotIndex pivotIndex (width - pivotIndex)
      (natSubPositiveOfLt pivotIndex width pColLt)
  have rowLe : smithRowAbsSum matrix pivotIndex (width - pivotIndex) pivotIndex
      ≤ smithMinorAbsSumRows matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex :=
    smithMinorAbsSumRowsHeadLe matrix pivotIndex (width - pivotIndex) pivotIndex (height - pivotIndex)
      (natSubPositiveOfLt pivotIndex height pRowLt)
  exact Nat.le_trans entryLe rowLe

/-! ## Brick 4 — the zero-pivot seam scoped away: a zero pivot forces the find-`none` exit -/

/-- **A zero pivot over all-zero later diagonals reports find-`none`.**  When the pivot magnitude is `0` and
every scanned later diagonal has magnitude `0`, the non-dividing scan returns `none` — `smithPivotDividesEntry
0 0 = true` at every step (a zero pivot divides a zero entry), so the guard always holds and the loop runs to
its `none` base.  Structural on the scan count; mirrors the shipped `smithFindNonDividingLaterDiagonalNoneDividesAll`. -/
theorem smithFindNonDividingLaterDiagonalNoneOfLaterZero (matrix : IntMatrix) (pivotIndex : Nat)
    (pivotZero : (matrix.diagonalEntryAt pivotIndex).natAbs = 0) :
    ∀ (scanCount scanStart : Nat),
      (∀ laterIndex, scanStart ≤ laterIndex → laterIndex < scanStart + scanCount →
        (matrix.diagonalEntryAt laterIndex).natAbs = 0) →
      smithFindNonDividingLaterDiagonal matrix pivotIndex scanCount scanStart = none := by
  intro scanCount
  induction scanCount with
  | zero => intro scanStart _; rfl
  | succ scanCount ih =>
      intro scanStart allLaterZero
      have hUnfold : smithFindNonDividingLaterDiagonal matrix pivotIndex (scanCount + 1) scanStart
          = if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
                (matrix.diagonalEntryAt scanStart) then
              smithFindNonDividingLaterDiagonal matrix pivotIndex scanCount (scanStart + 1)
            else some scanStart := rfl
      rw [hUnfold]
      have headZero : (matrix.diagonalEntryAt scanStart).natAbs = 0 :=
        allLaterZero scanStart (Nat.le_refl scanStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self scanStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le scanCount)) scanStart))
      have condTrue : ((matrix.diagonalEntryAt pivotIndex).natAbs == 0) = true := by
        rw [pivotZero]; rfl
      have guardTrue : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.diagonalEntryAt scanStart) = true := by
        unfold smithPivotDividesEntry
        rw [if_pos condTrue, headZero]; rfl
      rw [if_pos guardTrue]
      have scanShiftEq : scanStart + 1 + scanCount = scanStart + (scanCount + 1) :=
        (Nat.succ_add scanStart scanCount).trans (Nat.add_succ scanStart scanCount).symm
      exact ih (scanStart + 1) (fun laterIndex laterGe laterLt =>
        allLaterZero laterIndex (Nat.le_of_succ_le laterGe)
          (Eq.mp (congrArg (laterIndex < ·) scanShiftEq) laterLt))

/-- **The scope — a zero pivot with zero-trailing later diagonals forces the driver's find-`none` exit.**
So the zero-pivot fold arm (`smithPivotMagnitudeRisesOnZeroPivotBootstrap`, the sole `pivotAbs`-raising
shape) is UNREACHABLE in the repair loop under zero-trailing: `find = some ==> pivot != 0`.  This is what
lets `pivotMagnitudeWithin` be a genuine descent WITHOUT a lex refinement.  Specialises the structural core
to the driver's scan window `[pivotIndex+1, Nat.min height width)`; the `Nat.min` conversion splits on
`Nat.le_total` (the `>` branch has an empty scan). -/
theorem smithZeroPivotImpliesFindNone (matrix : IntMatrix) (pivotIndex height width : Nat)
    (laterDiagonalsZero : ∀ laterIndex, pivotIndex < laterIndex → laterIndex < Nat.min height width →
        (matrix.diagonalEntryAt laterIndex).natAbs = 0)
    (pivotZero : (matrix.diagonalEntryAt pivotIndex).natAbs = 0) :
    smithFindNonDividingLaterDiagonal matrix pivotIndex
      (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none := by
  apply smithFindNonDividingLaterDiagonalNoneOfLaterZero matrix pivotIndex pivotZero
  intro laterIndex laterGe laterLt
  have pivotLtLater : pivotIndex < laterIndex :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self pivotIndex) laterGe
  cases Nat.le_total (pivotIndex + 1) (Nat.min height width) with
  | inl pivotSuccLe =>
      exact laterDiagonalsZero laterIndex pivotLtLater
        (Eq.mp (congrArg (laterIndex < ·)
          (smithNatAddSubOfLe (pivotIndex + 1) (Nat.min height width) pivotSuccLe)) laterLt)
  | inr minLe =>
      rw [natSubEqZeroOfLe (Nat.min height width) (pivotIndex + 1) minLe, Nat.add_zero] at laterLt
      exact absurd (Nat.lt_of_lt_of_le laterLt laterGe) (Nat.lt_irrefl laterIndex)

/-! ## Brick 5 — the NAMED r28 obligation `SmithFoldDescendsOnNonzeroPivot` + its battery -/

/-- **THE r28 OBLIGATION, named exactly.**  On every NONZERO-pivot find-`some` fold, `pivotMagnitudeWithin`
strictly descends.  This is the corrected `foldDescends` — `pivotAbs` in place of r26's stalling
`minNonzeroAbs`, guarded by `0 < pivotAbs` (the zero-pivot arm is scoped away by
`smithZeroPivotImpliesFindNone`).  A `Prop`, NOT proved here: the general proof is the cascade-inner
descent induction (composing `smithSingleClearStrictlyDecreasesPivot` + `smithRepairDecreasesPivotSize`
across the whole `smithCascadeSweep` loop to bound its OUTPUT pivot) — the r28 major arc.  Battery-verified
TRUE below. -/
def SmithFoldDescendsOnNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

set_option maxRecDepth 8000 in
/-- **The obligation, battery-verified on the STEP-2 + adversary fixtures.**  Each member is the obligation's
CONCLUSION (`pivotAbs` strict drop) on a literal where `#eval` confirmed `find = some 1` and a nonzero pivot:
`diag(6,10,8)` `6 -> 2`, `diag(6,9,10)` `6 -> 3`, `diag(10,4,4)` `10 -> 2`, `diag(9,6,6)` `9 -> 3`,
`diag(15,10,6,4)` `15 -> 4`.  The `find = some` and nonzero-pivot side conditions hold by construction on
these literals (elided from the decidable battery — see `smithZeroPivotImpliesFindNone` for the scope).
Evidence the named obligation is TRUE; NOT a proof of the universal. -/
theorem smithFoldDescendsHoldsOnBattery :
    pivotMagnitudeWithin (smithClearingFoldStep { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 1 0 3 3) 0
        < pivotMagnitudeWithin { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0
    ∧ pivotMagnitudeWithin (smithClearingFoldStep { rows := [[6, 0, 0], [0, 9, 0], [0, 0, 10]] } 1 0 3 3) 0
        < pivotMagnitudeWithin { rows := [[6, 0, 0], [0, 9, 0], [0, 0, 10]] } 0
    ∧ pivotMagnitudeWithin (smithClearingFoldStep { rows := [[10, 0, 0], [0, 4, 0], [0, 0, 4]] } 1 0 3 3) 0
        < pivotMagnitudeWithin { rows := [[10, 0, 0], [0, 4, 0], [0, 0, 4]] } 0
    ∧ pivotMagnitudeWithin (smithClearingFoldStep { rows := [[9, 0, 0], [0, 6, 0], [0, 0, 6]] } 1 0 3 3) 0
        < pivotMagnitudeWithin { rows := [[9, 0, 0], [0, 6, 0], [0, 0, 6]] } 0
    ∧ pivotMagnitudeWithin
          (smithClearingFoldStep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 1 0 4 4) 0
        < pivotMagnitudeWithin { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 := by
  decide

/-! ## Brick 6 — the GUARDED NODE-D variant + the fuel-adequacy reduction on `pivotMagnitudeWithin` -/

/-- **GUARDED NODE D.**  The shipped `smithClearingSweepReachesFindNoneOfDescent` demands `foldDescends` for
ALL rectangular work — which `pivotMagnitudeWithin` fails on zero-pivot work (`smithPivotMagnitudeRisesOnZeroPivotBootstrap`).
This variant threads an `invariant` preserved by the fold, so the measure is only asked to descend WHERE the
guard holds.  Structural induction on the fuel, byte-mirroring the shipped node D with the invariant carried
through both branches.  LANDS unconditionally — the mechanism that lets the corrected `pivotAbs` measure
drive fuel-adequacy. -/
theorem smithClearingSweepReachesFindNoneOfGuardedDescent
    (pivotIndex height width : Nat)
    (measure : IntMatrix → Nat)
    (invariant : IntMatrix → Prop)
    (measureBaseFindNone : ∀ (work : IntMatrix), invariant work → measure work = 0 →
        smithFindNonDividingLaterDiagonal work pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (terminalKeepsFindNone : ∀ (work : IntMatrix), invariant work → work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (foldDescends : ∀ (work : IntMatrix), invariant work → work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          measure (smithClearingFoldStep work foundPos pivotIndex height width) < measure work)
    (foldKeepsInvariant : ∀ (work : IntMatrix), invariant work → work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          invariant (smithClearingFoldStep work foundPos pivotIndex height width)) :
    ∀ (fuel : Nat) (matrix : IntMatrix), invariant matrix → matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width → measure matrix ≤ fuel →
      smithFindNonDividingLaterDiagonal
        (matrix.applyOperations (smithRepairPositionSweepClearing fuel matrix pivotIndex height width))
        pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix invHolds _ _ _ measureLe
      exact measureBaseFindNone matrix invHolds (Nat.le_antisymm measureLe (Nat.zero_le _))
  | succ fuel ih =>
      intro matrix invHolds isRect pRowLt pColLt measureLe
      cases hFind : smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) with
      | none =>
          rw [smithRepairPositionSweepClearingSucc, hFind]
          exact terminalKeepsFindNone matrix invHolds isRect pRowLt pColLt hFind
      | some foundPos =>
          rw [smithRepairPositionSweepClearingSucc, hFind, applyOperationsAppend, applyOperationsAppend]
          exact ih (smithClearingFoldStep matrix foundPos pivotIndex height width)
            (foldKeepsInvariant matrix invHolds isRect pRowLt pColLt foundPos hFind)
            (smithClearingFoldStepPreservesRectangular matrix foundPos pivotIndex isRect)
            pRowLt pColLt
            (Nat.le_of_lt_succ
              (Nat.lt_of_lt_of_le (foldDescends matrix invHolds isRect pRowLt pColLt foundPos hFind) measureLe))

/-- The zero-trailing invariant: IF the pivot magnitude is `0`, every later window diagonal is `0`.  The
scope predicate `smithZeroPivotImpliesFindNone` consumes; the driver's repair input satisfies it (the
diagonal is zero-trailing after `smithReduceTotal`). -/
def ZeroTrailingDiagonalsFrom (pivotIndex height width : Nat) (matrix : IntMatrix) : Prop :=
  (matrix.diagonalEntryAt pivotIndex).natAbs = 0 →
    ∀ laterIndex, pivotIndex < laterIndex → laterIndex < Nat.min height width →
      (matrix.diagonalEntryAt laterIndex).natAbs = 0

/-- **Fuel-adequacy for the `pivotMagnitudeWithin` measure — the wiring.**  The clearing sweep output reports
find-`none` GIVEN the r28 obligation `SmithFoldDescendsOnNonzeroPivot`, a zero-trailing invariant preserved
by the fold (`foldKeepsZeroTrailing`) and by the terminal cascade (`terminalKeepsFindNone`), and the base
zero-trailing at the sweep input.  Instantiates GUARDED NODE D with `measure := pivotMagnitudeWithin ·
pivotIndex` and `invariant := ZeroTrailingDiagonalsFrom pivotIndex height width`: the base is brick 4
(`smithZeroPivotImpliesFindNone`), the guarded descent rides brick 5 with the zero-pivot arm scoped away by
brick 4, and the budget is `pivotMagnitudeLeMinorAbsSum`.  This WIRES the `pivotAbs` correction to
fuel-adequacy; the two invariant-preservation hypotheses are the r28 handoff (NOT fabricated). -/
theorem smithClearingOutputFindNoneFromFoldDescent
    (pivotIndex height width : Nat)
    (foldDescendsOnNonzero : SmithFoldDescendsOnNonzeroPivot)
    (terminalKeepsFindNone : ∀ (work : IntMatrix),
        ZeroTrailingDiagonalsFrom pivotIndex height width work → work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (foldKeepsZeroTrailing : ∀ (work : IntMatrix),
        ZeroTrailingDiagonalsFrom pivotIndex height width work → work.IsRectangular height width →
        pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          ZeroTrailingDiagonalsFrom pivotIndex height width
            (smithClearingFoldStep work foundPos pivotIndex height width))
    (matrix : IntMatrix)
    (baseZeroTrailing : ZeroTrailingDiagonalsFrom pivotIndex height width matrix)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithFindNonDividingLaterDiagonal
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none :=
  smithClearingSweepReachesFindNoneOfGuardedDescent pivotIndex height width
    (fun work => pivotMagnitudeWithin work pivotIndex)
    (ZeroTrailingDiagonalsFrom pivotIndex height width)
    (fun work invHolds pivotMag0 =>
      smithZeroPivotImpliesFindNone work pivotIndex height width (invHolds pivotMag0) pivotMag0)
    terminalKeepsFindNone
    (fun work invHolds workRect workRowLt workColLt foundPos hFind =>
      foldDescendsOnNonzero work foundPos pivotIndex height width workRect
        (by
          cases Nat.eq_zero_or_pos (work.diagonalEntryAt pivotIndex).natAbs with
          | inl pivotMag0 =>
              exact nomatch (hFind.symm.trans (smithZeroPivotImpliesFindNone work pivotIndex height width
                (invHolds pivotMag0) pivotMag0))
          | inr pivotPos => exact pivotPos)
        hFind)
    foldKeepsZeroTrailing
    (smithMinorAbsSum matrix pivotIndex height width) matrix baseZeroTrailing isRect pRowLt pColLt
    (pivotMagnitudeLeMinorAbsSum matrix pivotIndex height width pRowLt pColLt)

/-! ## Brick 7 — the CORRECT per-pivot statement: seed = fuel-adequacy + off-diagonal half -/

/-- **K1 — fuel-adequacy** (the clearing sweep output reports find-`none`; the DIAGONAL-half source). -/
def SmithClearingOutputFindNone : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    smithFindNonDividingLaterDiagonal
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none

/-- **K2 — the OFF-DIAGONAL half** (the landed pivot divides every off-diagonal cell of the clearing sweep
output's `[pivotIndex+1, ·)²` quadrant).  The irreducible "min-abs Euclid computes the gcd" wall, now
isolated ALONE (a strict sharpening of the whole-sub-block seed `SmithCascadeLandsDivisibleSubBlock`). -/
def SmithClearingOutputOffDiagonalDivides : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    SubBlockOffDiagonalDivisibleFrom
      ((matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).diagonalEntryAt
        pivotIndex)
      (pivotIndex + 1)
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))

/-- **The CORRECT per-pivot statement — the seed from fuel-adequacy + the off-diagonal half.**  The driver
seed `SmithCascadeLandsDivisibleSubBlock` (floor `pivotIndex+1`, off-diagonals INCLUDED) splits into halves
(`matrixEntriesDivisibleByWithinOfHalves`): the DIAGONAL half comes from fuel-adequacy `K1` via the shipped
`subBlockDiagonalDivisibleOfFindNone`, and the OFF-DIAGONAL half IS `K2`.  So the whole-sub-block seed
reduces to (K1) + (K2) — a strict sharpening: K1 is a fuel-counting fact (reduced to
`SmithFoldDescendsOnNonzeroPivot` by `smithClearingOutputFindNoneFromFoldDescent`), leaving K2 the sole deep
residual. -/
theorem seedOfClearingFindNoneAndOffDiagonalResidual
    (fuelAdequacy : SmithClearingOutputFindNone)
    (offDiagonalDivides : SmithClearingOutputOffDiagonalDivides) :
    SmithCascadeLandsDivisibleSubBlock := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  exact matrixEntriesDivisibleByWithinOfHalves
    ((matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width)).diagonalEntryAt
      pivotIndex)
    (pivotIndex + 1)
    (matrix.applyOperations (smithRepairPositionSweepClearing
      (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
    (subBlockDiagonalDivisibleOfFindNone
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      (applyOperationsPreservesRectangular _ matrix isRect)
      pivotIndex
      (fuelAdequacy matrix pivotIndex height width isRect pRowLt pColLt))
    (offDiagonalDivides matrix pivotIndex height width isRect pRowLt pColLt)

/-- **The corrected-driver totality from the SHARPENED residual pair.**  Compose the seed reduction with the
shipped `smithReduceCompleteDriverOfSubBlockSeed`: `SmithReduceCompleteDriverStatement` is inhabited GIVEN
(fuel-adequacy `K1`) + (the off-diagonal half `K2`).  The honest r27 residual pair — strictly sharper than
the whole-sub-block seed, and K1 further reduces to `SmithFoldDescendsOnNonzeroPivot`. -/
theorem smithReduceCompleteDriverOfFindNoneAndOffDiagonal
    (fuelAdequacy : SmithClearingOutputFindNone)
    (offDiagonalDivides : SmithClearingOutputOffDiagonalDivides) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfSubBlockSeed
    (seedOfClearingFindNoneAndOffDiagonalResidual fuelAdequacy offDiagonalDivides)

/-! ## The surviving wall (named IN this file — NOT prose masquerading as a theorem)

This file inhabits NOTHING hypothesis-free.  It CORRECTS r26: the descent measure is `pivotMagnitudeWithin`
(`= |diagonalEntryAt p|`), which strictly DROPS on the exact `diag(15,10,6,4)` fold where r26's
`minNonzeroAbsWithin` STALLED (`smithPivotMagnitudeDescendsWhereMinNonzeroAbsStalls`) and on the adversary
battery, RISES on exactly ONE shape — the zero-pivot bootstrap (`smithPivotMagnitudeRisesOnZeroPivotBootstrap`)
— and that shape is driver-UNREACHABLE (`smithZeroPivotImpliesFindNone`: a zero pivot forces the find-`none`
exit under zero-trailing).  So NO lex refinement is needed: the r26-demanded secondary key is superseded by
scoping the single seam away.  The budget clash (recon Delta2) is dodged because `pivotAbs` is a plain `Nat`
that fits the fuel (`pivotMagnitudeLeMinorAbsSum`), not a lex collapse.

**THE OBLIGATIONS, named EXACTLY [r33: the general keystone they serve —
`SmithCascadeLandedPivotDividesMinor` / K2 — is REFUTED AS STATED (`SmithLandedMagnitudeRefuted`); the
RESTRICTED diagonal / in-driver-image form is OPEN, and the descent measures below remain its lever].**

  * `SmithFoldDescendsOnNonzeroPivot` (r28) — `pivotMagnitudeWithin` strictly descends on every nonzero-pivot
    fold.  Battery-verified TRUE (`smithFoldDescendsHoldsOnBattery`); the general proof is the cascade-inner
    descent induction (compose `smithSingleClearStrictlyDecreasesPivot` + `smithRepairDecreasesPivotSize`
    across the whole `smithCascadeSweep` loop to bound its OUTPUT pivot).  It feeds fuel-adequacy `K1` via
    `smithClearingOutputFindNoneFromFoldDescent`, modulo the zero-trailing invariant preservation
    (`foldKeepsZeroTrailing` / `terminalKeepsFindNone`) — the second r28 handoff.
  * `SmithClearingOutputOffDiagonalDivides` (`K2`) — the OFF-DIAGONAL half.  The irreducible
    "min-abs Euclid computes the gcd" gcd-ideal-invariance wall; NOT reduced further by any measure argument.

`seedOfClearingFindNoneAndOffDiagonalResidual` + `smithReduceCompleteDriverOfFindNoneAndOffDiagonal` reduce
`SmithReduceCompleteDriverStatement` to exactly the pair (`K1`, `K2`) — the CORRECT per-pivot statement, a
strict sharpening of the whole-sub-block seed.  `smithReduceComplete` and the driver stay byte-intact. -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithConfinedColumnDescentInsufficient
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedRestriction

/-! # Smith column-clean one-round descent: refuted, with reachable states violating the guard

The column-clean-guarded single-fold descent gate for the Smith clearing fold is false, and reachable
states violate that guard while the one-round pivot magnitude rises on them.

`smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted` refutes the candidate
`SmithFoldDescendsOnColumnCleanNonzeroPivot`: on the column-clean matrix `[[2,1,0],[0,3,0],[0,0,5]]` at
pivot 0 every precondition holds (rectangular, clean guard, positive pivot, `find = some 1`), yet the fold
`row0 += row1` turns the dirty pivot-row entry `entry(0,1) = 1` into `1 + 3 = 4 = 2*2`, which the cascade
clears against the pivot, so the pivot magnitude stalls `2 -> 2`. The clean guard constrains only the pivot
column below the pivot, not the pivot row, so a dirty pivot-row entry masks the found non-divisibility.

`reachableImpliesBelowColumnCleanIsRefuted` refutes the entry invariant `ReachableImpliesBelowColumnClean`:
the pivot-2 state `[[1,0,0,0],[0,1,0,0],[0,0,66,0],[0,0,132,-99]]` reached from `diag(11,11,9,6)` via a
`ReachableFromPhaseA` witness (`base` then two `step`s) carries `entry(3,2) = 132 = 2*66`, violating
confinement, so reachable states do not enter the clean guard. On that same state the driver-selected fold
pulls `entry(3,2)` into the pivot row and raises the one-round measure `66 -> 99`; a hand-built same-family
witness confirms the rise (`132 -> 198`) by `decide`. The natural repair `belowPivotCrossClean` excludes the
mask but is itself violated by the reachable state, so no structural single-round lever is both satisfied by
the reachable image and sufficient for single-fold descent; a surviving fuel-adequacy argument requires a
multi-round measure. `SmithReduceCompleteDriverStatement` stays uninhabited with zero hypotheses, and the
off-diagonal wall `SmithClearingOutputOffDiagonalDivides` is untouched.

Raw Lean 4 + `Init`, structural only, no axioms; per-declaration audit twin at
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithColumnCleanDescentInsufficient.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## The clean-guard candidate is false (dirty pivot-row mask) -/

/-- The mask witness: clean pivot column below (`entry(1,0)=0`, `entry(2,0)=0`) but a dirty pivot-row entry
`entry(0,1)=1` that, once the found row `[0,3,0]` is folded in, becomes `4 = 2*2` and is cleared without
exposing the non-divisible `d1=3`. -/
def smithColumnCleanFoldMaskWitness : IntMatrix := IntMatrix.mk [[2, 1, 0], [0, 3, 0], [0, 0, 5]]

/-- The mask witness is a `3 x 3` matrix. -/
theorem smithColumnCleanFoldMaskWitnessRectangular :
    smithColumnCleanFoldMaskWitness.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The mask witness satisfies the confinement conjunct: `|entry(1,0)| = 0 <= 2 = |pivot|`. -/
theorem smithColumnCleanFoldMaskWitnessConfined :
    belowPivotColumnConfined smithColumnCleanFoldMaskWitness 0 := by
  unfold belowPivotColumnConfined; decide

/-- The mask witness satisfies the deep-column-zero conjunct: the only in-range deeper pivot-column entry is
`entry(2,0) = 0`.  Structural: the `1 < laterRow < 3` window forces `laterRow = 2`. -/
theorem smithColumnCleanFoldMaskWitnessColumnZeroDeep :
    belowPivotColumnZeroDeep smithColumnCleanFoldMaskWitness 0 3 := by
  intro laterRow pivotSuccLtLater laterLtHeight
  have laterIsTwo : laterRow = 2 := Nat.le_antisymm (Nat.le_of_lt_succ laterLtHeight) pivotSuccLtLater
  subst laterIsTwo; decide

/-- The mask witness satisfies the full clean guard, so the descent candidate is genuinely applicable here. -/
theorem smithColumnCleanFoldMaskWitnessColumnClean :
    belowPivotColumnClean smithColumnCleanFoldMaskWitness 0 3 :=
  ⟨smithColumnCleanFoldMaskWitnessConfined, smithColumnCleanFoldMaskWitnessColumnZeroDeep⟩

/-- The pivot is positive (`|d0| = 2 > 0`). -/
theorem smithColumnCleanFoldMaskWitnessPivotPositive :
    0 < (smithColumnCleanFoldMaskWitness.diagonalEntryAt 0).natAbs := by decide

/-- The find-scan reports `some 1` (`d0 = 2` does not divide `d1 = 3`). -/
theorem smithColumnCleanFoldMaskWitnessFindsSome :
    smithFindNonDividingLaterDiagonal smithColumnCleanFoldMaskWitness 0
      (Nat.min 3 3 - (0 + 1)) (0 + 1) = some 1 := by decide

/-- The fold `row0 += row1` and cascade land pivot magnitude `2`, equal to the input, so the candidate's
strict-descent conclusion `2 < 2` is false: the dirty `entry(0,1) = 1` combines with the non-dividing
`d1 = 3` into `4 = 2*2`, divisible by the pivot and cleared to `0`. -/
theorem smithColumnCleanFoldMaskWitnessFoldStalls :
    ¬ (pivotMagnitudeWithin
          (smithClearingFoldStep smithColumnCleanFoldMaskWitness 1 0 3 3) 0
        < pivotMagnitudeWithin smithColumnCleanFoldMaskWitness 0) := by decide

/-- `SmithFoldDescendsOnColumnCleanNonzeroPivot` is false: on the mask witness at pivot 0 all preconditions
hold (rectangular, clean guard, positive pivot, `find = some 1`) yet the fold stalls, because the clean
column guard does not constrain the pivot row and a dirty pivot-row entry masks the found non-divisibility. -/
theorem smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted :
    ¬ SmithFoldDescendsOnColumnCleanNonzeroPivot := by
  intro foldDescends
  exact smithColumnCleanFoldMaskWitnessFoldStalls
    (foldDescends smithColumnCleanFoldMaskWitness 1 0 3 3
      smithColumnCleanFoldMaskWitnessRectangular
      smithColumnCleanFoldMaskWitnessColumnClean
      smithColumnCleanFoldMaskWitnessPivotPositive
      smithColumnCleanFoldMaskWitnessFindsSome)

/-! ## A reachable pivot-2 state from a concrete input

The trajectory is `base` at the Phase-A output `diag(6,9,11,11)`, one `step` at pivot 0, one `step` at
pivot 1.  Each `def` is the matrix the `ReachableFromPhaseA` constructor produces, so the reachability
witness is definitional. -/

/-- The generating input `diag(11,11,9,6)`, a `4 x 4` whose driver trajectory reaches a
confinement-violating pivot-2 state. -/
def smithReachableConfinementInput : IntMatrix := IntMatrix.mk [[11,0,0,0],[0,11,0,0],[0,0,9,0],[0,0,0,6]]

/-- The Phase-A output `diag(6,9,11,11)`, the `base` of `ReachableFromPhaseA` at pivot 0. -/
def smithReachablePhaseAState : IntMatrix :=
  smithReachableConfinementInput.applyOperations
    (smithReduceTotal smithReachableConfinementInput 4 4).operations

/-- The state after the pivot-0 position sweep (`step` once), at pivot 1. -/
def smithReachablePivotZeroState : IntMatrix :=
  smithReachablePhaseAState.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum smithReachablePhaseAState 0 4 4)
      smithReachablePhaseAState 0 4 4)

/-- The reachable pivot-2 state `[[1,0,0,0],[0,1,0,0],[0,0,66,0],[0,0,132,-99]]` (`step` twice).  At pivot 2
it carries `entry(3,2) = 132 = 2*66`, violating confinement. -/
def smithReachablePivotTwoState : IntMatrix :=
  smithReachablePivotZeroState.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum smithReachablePivotZeroState 1 4 4)
      smithReachablePivotZeroState 1 4 4)

/-- The generating input is a `4 x 4` matrix. -/
theorem smithReachableConfinementInputRectangular :
    smithReachableConfinementInput.IsRectangular 4 4 := ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- The Phase-A output is rectangular (operations preserve shape). -/
theorem smithReachablePhaseAStateRectangular :
    smithReachablePhaseAState.IsRectangular 4 4 :=
  applyOperationsPreservesRectangular _ smithReachableConfinementInput
    smithReachableConfinementInputRectangular

/-- The pivot-0-sweep output is rectangular. -/
theorem smithReachablePivotZeroStateRectangular :
    smithReachablePivotZeroState.IsRectangular 4 4 :=
  applyOperationsPreservesRectangular _ smithReachablePhaseAState smithReachablePhaseAStateRectangular

/-- The pivot-2 state is rectangular. -/
theorem smithReachablePivotTwoStateRectangular :
    smithReachablePivotTwoState.IsRectangular 4 4 :=
  applyOperationsPreservesRectangular _ smithReachablePivotZeroState
    smithReachablePivotZeroStateRectangular

/-- The pivot-2 state is reachable: `ReachableFromPhaseA 4 4 _ 2`, built by `base` (Phase-A output) then two
`step`s (pivot-0 and pivot-1 sweeps).  The constructor chain is definitional. -/
theorem smithReachablePivotTwoStateIsReachable :
    ReachableFromPhaseA 4 4 smithReachablePivotTwoState 2 :=
  ReachableFromPhaseA.step smithReachablePivotZeroState 1
    (ReachableFromPhaseA.step smithReachablePhaseAState 0
      (ReachableFromPhaseA.base smithReachableConfinementInput
        smithReachableConfinementInputRectangular))

/-! ## The reachable state violates the guard and the fold rises -/

/-- The reachable pivot-2 state violates confinement: `|entry(3,2)| = 132 > 66 = |pivot|`, computed through
the full driver trajectory. -/
theorem smithReachablePivotTwoStateNotConfined :
    ¬ belowPivotColumnConfined smithReachablePivotTwoState 2 := by
  unfold belowPivotColumnConfined; decide

/-- The find-scan fires at the reachable state: `some 3` (`d2 = 66` does not divide `d3 = -99`). -/
theorem smithReachablePivotTwoStateFindsSome :
    smithFindNonDividingLaterDiagonal smithReachablePivotTwoState 2
      (Nat.min 4 4 - (2 + 1)) (2 + 1) = some 3 := by decide

/-- The one-round measure rises on the reachable fold: `row2 += row3` pulls `entry(3,2) = 132` into the pivot
row and lands `pivotMagnitudeWithin` `66 -> 99`, so the strict-descent inequality `99 < 66` is false. -/
theorem smithReachablePivotTwoStateFoldRises :
    ¬ (pivotMagnitudeWithin
          (smithClearingFoldStep smithReachablePivotTwoState 3 2 4 4) 2
        < pivotMagnitudeWithin smithReachablePivotTwoState 2) := by decide

/-- The proposition that every reachable state enters the clean guard.  Refuted below. -/
def ReachableImpliesBelowColumnClean : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    belowPivotColumnClean matrix pivotIndex height

/-- `ReachableImpliesBelowColumnClean` is false: the reachable pivot-2 state violates the confinement
conjunct of the clean guard, so reachable states do not enter it.  The prefix-settled invariant constrains
only columns below `pivotIndex`; column `pivotIndex` below, where the `2*pivot` fill-in lives, is exactly
what fails. -/
theorem reachableImpliesBelowColumnCleanIsRefuted :
    ¬ ReachableImpliesBelowColumnClean := by
  intro entryLeg
  exact smithReachablePivotTwoStateNotConfined
    (entryLeg smithReachablePivotTwoState 2 4 4 smithReachablePivotTwoStateIsReachable
      smithReachablePivotTwoStateRectangular (by decide) (by decide)).1

/-! ## A trajectory-independent fold-rise witness -/

/-- A hand-built `4x4` in the same confinement-violating family (`entry(3,2) = 264 > 132 = |pivot|`) whose
fold `row2 += row3` raises `pivotMagnitudeWithin` `132 -> 198`, independent of the reachability trajectory. -/
def smithConfinementViolatingFoldRiseWitness : IntMatrix :=
  IntMatrix.mk [[2,0,0,0],[0,2,0,0],[0,0,132,0],[0,0,264,-198]]

/-- The witness fires the fold: `find = some 3` (`132` does not divide `198`). -/
theorem smithConfinementViolatingFoldRiseWitnessFindsSome :
    smithFindNonDividingLaterDiagonal smithConfinementViolatingFoldRiseWitness 2
      (Nat.min 4 4 - (2 + 1)) (2 + 1) = some 3 := by decide

/-- The backup witness RISES `pivotMagnitudeWithin` `132 -> 198` under the fold. -/
theorem smithConfinementViolatingFoldRiseWitnessRises :
    ¬ (pivotMagnitudeWithin
          (smithClearingFoldStep smithConfinementViolatingFoldRiseWitness 3 2 4 4) 2
        < pivotMagnitudeWithin smithConfinementViolatingFoldRiseWitness 2) := by decide

/-! ## Brick 5 — the natural repair `belowPivotCrossClean`, RECORDED and shown NON-COMPOSABLE -/

/-- **The pivot-row-right-zero conjunct** — every pivot-row entry strictly RIGHT of the pivot, within
`width`, vanishes.  This is exactly what the graveyard-A mask violates (`entry(0,1) = 1 != 0`) and what would
be needed to block the dirty-pivot-row mask. -/
def belowPivotRowRightZero (matrix : IntMatrix) (pivotIndex width : Nat) : Prop :=
  ∀ laterCol, pivotIndex < laterCol → laterCol < width → matrix.entryAt pivotIndex laterCol = 0

/-- **The cross-clean lever** — the pivot-row-right-zero PLUS the r40 column-clean guard.  This EXCLUDES the
graveyard-A mask (its pivot row is dirty).  Recorded only; NOT proved as a descent lever, because it is
violated by reachable states at entry (`smithCrossCleanViolatedAtReachableEntry`) and so cannot be
composed. -/
def belowPivotCrossClean (matrix : IntMatrix) (pivotIndex height width : Nat) : Prop :=
  belowPivotRowRightZero matrix pivotIndex width ∧ belowPivotColumnClean matrix pivotIndex height

/-- **Cross-clean would EXCLUDE the graveyard-A mask.**  `¬ belowPivotRowRightZero
smithColumnCleanFoldMaskWitness 0 3`: the pivot-row entry `entry(0,1) = 1 != 0` (witnessed at the in-range
`laterCol = 1`).  So the natural repair fixes the descent side of graveyard A. -/
theorem smithCrossCleanExcludesFoldMask :
    ¬ belowPivotRowRightZero smithColumnCleanFoldMaskWitness 0 3 := by
  intro rowRightZero
  exact absurd (rowRightZero 1 (by decide) (by decide)) (by decide)

/-- **But cross-clean is VIOLATED by the reachable state at entry.**  `¬ belowPivotCrossClean
smithReachablePivotTwoState 2 4 4`: its column-clean conjunct's confinement fails
(`smithReachablePivotTwoStateNotConfined`).  So the natural repair that fixes graveyard A cannot be composed
with reachability — no structural single-round lever survives both sides. -/
theorem smithCrossCleanViolatedAtReachableEntry :
    ¬ belowPivotCrossClean smithReachablePivotTwoState 2 4 4 := by
  intro crossClean
  exact smithReachablePivotTwoStateNotConfined crossClean.2.1

/-! ## The H2-SMITH r41 ledger — GRAVEYARD round; the mandate does NOT fire; the D3 discharge census

**What r41 ships (zero-axiom, additive; the r18-r40 world byte-intact).**  Two new graveyards plus the
one-round-measure death on the reachable image:

  * GRAVEYARD A `smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted`: the r40 candidate
    `SmithFoldDescendsOnColumnCleanNonzeroPivot` is machine-FALSE — a column-clean 3x3
    (`[[2,1,0],[0,3,0],[0,0,5]]`) STALLS the fold `2 -> 2` because a dirty pivot-row entry masks the found
    non-divisibility (`1 + 3 = 4 = 2*2`).
  * GRAVEYARD B `reachableImpliesBelowColumnCleanIsRefuted`: leg 3 is machine-FALSE — the genuinely reachable
    pivot-2 state from `diag(11,11,9,6)` (`[[1,0,0,0],[0,1,0,0],[0,0,66,0],[0,0,132,-99]]`, carried by a
    machine-checked `ReachableFromPhaseA` witness) VIOLATES confinement (`|entry(3,2)| = 132 > 66`).
  * The one-round measure RISES on that reachable fold (`smithReachablePivotTwoStateFoldRises`, `66 -> 99`);
    the same-family `smithConfinementViolatingFoldRiseWitnessRises` (`132 -> 198`) confirms by plain `decide`.
  * The natural repair `belowPivotCrossClean` is RECORDED and shown non-composable
    (`smithCrossCleanExcludesFoldMask` fixes A; `smithCrossCleanViolatedAtReachableEntry` breaks at entry).

**The D3 discharge census** (for `smithClearingOutputFindNoneFromColumnCleanFoldDescent`,
`SmithConfinedColumnDescentInsufficient`, r40).  The corrected driver consumes three hypotheses over the
invariant `ZeroTrailingDiagonalsFrom AND belowPivotColumnClean`, plus a base `baseClean`:

  * `foldDescends` (= the r40 candidate in the driver's shape) — now KNOWN-FALSE.  GRAVEYARD A refutes the
    standalone candidate; the reachable fold RISE (GRAVEYARD B) refutes it on the very states the driver
    visits.  This hypothesis CANNOT be discharged by a single-fold argument.
  * `foldKeepsInvariant` — its CLEAN conjuncts (confinement + deep-zero) are still discharged for free by
    r40's `smithClearingFoldStepColumnClean` (that structural theorem stands); the zero-trailing conjunct
    remains a small handoff.  But this preservation is now MOOT: the invariant it preserves is unsatisfiable
    at the base.
  * `terminalKeepsFindNone` — unaffected; the terminal cascade preserves find-none regardless.
  * `baseClean` (`belowPivotColumnClean matrix pivotIndex height` at the driver start) — UNSATISFIABLE on the
    reachable image.  `reachableImpliesBelowColumnCleanIsRefuted` shows a genuine reachable state fails the
    clean guard, so no reachability-sourced instantiation supplies `baseClean`.  This is the leg the r40 wall
    called "a genuinely NEW r41 trajectory invariant" — it is FALSE, not open.

Net: of the four r40 legs, leg 1 (L1', the clean descent) and leg 3 (`reachableImpliesBelowColumnClean`) are
now REFUTED; leg 2 (zero-trailing preservation) is moot; leg 4 (K2) is untouched.

**Honest mandate distance — unchanged and large, K2 included.**  `SmithReduceCompleteDriverStatement` needs
BOTH a restricted-K1 (the one-round descent route is dead on the reachable image; a surviving K1 requires a
lexicographic / multi-round `Nat.rec` measure, NOT round-sized) AND a restricted-K2
(`SmithClearingOutputOffDiagonalDivides`, the off-diagonal gcd-ideal wall — a separate number-theoretic arc,
witnessed live and non-vacuous by the surviving interior fill-in, unchanged by any K1 work).  Even a perfect
K1 closure leaves K2 standing; the r40 wall's "K2 stands even after K1 closure" is confirmed at the def
level.  The mandate is NOT claimable this round or next.

The round-level divisor chain `pivot(n+1) | pivot(n)` stays machine-REFUTED (not stated, not proven).  No
descent measure is fabricated; no flip is invented.  The r18-r40 world, `smithReduceComplete`, and the
refutation certificates stay byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra

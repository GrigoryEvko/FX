import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithConfinedColumnDescentInsufficient
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedRestriction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithColumnCleanDescentInsufficient — the r40-corrected
    `belowPivotColumnClean`-guarded one-round descent is STILL FALSE, AND reachable states VIOLATE the
    clean guard while the fold RISES on them (H2-SMITH r41)

## The move

r40 (`SmithConfinedColumnDescentInsufficient`) refuted the r39 `belowPivotColumnConfined` descent gate
(a confined-but-deep-dirty 3x3 STALLS the fold) and proposed the strictly-sharper lever
`belowPivotColumnClean` (`belowPivotColumnConfined AND belowPivotColumnZeroDeep`).  It shipped the corrected
candidate `SmithFoldDescendsOnColumnCleanNonzeroPivot` (a `def ... : Prop`, NOT proved) and recorded four
open legs to the mandate: L1' (the clean one-round descent), the zero-trailing preservation, leg 3
`reachableImpliesBelowColumnClean` (reachable states ENTER the clean guard), and K2 (the off-diagonal
gcd-ideal wall).

**r41 WIDE TRUTH-PROBE REFUTES the clean gate TOO, and its natural entry-invariant besides.**  This is a
GRAVEYARD round, one column position deeper than r39/r40: the one-round `pivotMagnitudeWithin` descent is
dead on the reachable image, no structural single-round lever survives, and the mandate does NOT fire.

### GRAVEYARD A — the r40 candidate `SmithFoldDescendsOnColumnCleanNonzeroPivot` is machine-FALSE

The clean lever `belowPivotColumnClean` constrains only the pivot COLUMN below the pivot; it says NOTHING
about the pivot ROW to the right.  A dirty pivot-row entry MASKS the found non-divisibility: on the
3x3 witness

```
smithColumnCleanFoldMaskWitness = [[2,1,0],[0,3,0],[0,0,5]]    -- pivotIndex 0
```

`belowPivotColumnClean ... 0 3` HOLDS (`entry(1,0)=0` confined, `entry(2,0)=0` deep-zero), the pivot is
positive (`|2| > 0`), and `find = some 1` (`d0=2` does not divide `d1=3`).  Yet the fold
`row0 += row1` makes `entry(0,1) = 1 + 3 = 4`, which the cascade Euclid-reduces against `d0=2` to `0`
(`4 = 2*2`): the non-divisible `3` was masked by the dirty `1`, so the fold STALLS the pivot magnitude
`2 -> 2` (`smithColumnCleanFoldMaskWitnessFoldStalls`).  Hence
`smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted : ¬ SmithFoldDescendsOnColumnCleanNonzeroPivot`
(zero axioms) — the r40 candidate is FALSE, the THIRD graveyard of the arc.

### GRAVEYARD B — reachable states VIOLATE the clean guard at entry, and the fold RISES on them

Leg 3 (`reachableImpliesBelowColumnClean`) is not new-and-open: it is machine-FALSE.  The concrete input
`diag(11,11,9,6)` drives the CORRECTED driver's trajectory (Phase-A output `diag(6,9,11,11)`, then the
pivot-0 sweep, then the pivot-1 sweep) to the genuinely reachable pivot-2 state

```
smithReachablePivotTwoState = [[1,0,0,0],[0,1,0,0],[0,0,66,0],[0,0,132,-99]]    -- ReachableFromPhaseA 4 4 _ 2
```

carried by a machine-checked `ReachableFromPhaseA` witness built from `base` + two `step`s
(`smithReachablePivotTwoStateIsReachable`, zero axioms — the constructor chain is definitional, no
in-kernel trajectory recomputation).  At pivot 2 this state has `entry(3,2) = 132 = 2*66`, so
`|entry(3,2)| = 132 > 66 = |pivot|` — CONFINEMENT VIOLATED
(`smithReachablePivotTwoStateNotConfined`), hence `¬ belowPivotColumnClean` at a genuine reachable state:
`reachableImpliesBelowColumnCleanIsRefuted : ¬ ReachableImpliesBelowColumnClean` (the FOURTH graveyard).

The SAME reachable state kills the one-round measure directly: `find = some 3`
(`smithReachablePivotTwoStateFindsSome`) fires the fold, which pulls `entry(3,2)=132` into the pivot row and
lands `pivotMagnitudeWithin` `66 -> 99` — the measure RISES on the driver-chosen fold at a genuinely
reachable state (`smithReachablePivotTwoStateFoldRises`).  This is the r31-recorded "the measure rises on
folds," now witnessed on a reachable, fireable, driver-selected fold rather than an out-of-image seed.

### The decisive adjudication — no structural single-round lever survives

Confinement is NECESSARY for descent (the clean guard's whole purpose; the mask graveyard A shows even the
COLUMN-clean form is insufficient without a row condition) but is VIOLATED by reachable states (graveyard B),
and on the violating reachable states the fold RISES.  The natural repair `belowPivotCrossClean` (add the
pivot-row-right-zero conjunct that EXCLUDES the graveyard-A mask) is itself violated by the reachable state
at entry (its confinement conjunct fails) — recorded here, non-composable.  Therefore no structural
single-round lever can be simultaneously (a) satisfied by the reachable image and (b) sufficient for
single-fold `pivotMagnitudeWithin` descent.  The K1-via-single-fold-descent route is dead on the reachable
image; a surviving K1 needs a lexicographic / multi-round measure (NOT round-sized).

## What this module ships (positive, additive, zero-axiom)

  * **GRAVEYARD A** — `smithColumnCleanFoldMaskWitness` + rectangularity / clean / positive-pivot / find-some
    pins and `smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted`: the r40 candidate is machine-FALSE
    (dirty-pivot-row mask under a clean column).
  * **GRAVEYARD B** — the genuine reachable state `smithReachablePivotTwoState`, its machine-checked
    `ReachableFromPhaseA` witness, the confinement violation, the find-fire, the fold RISE, the leg-3 Prop
    `ReachableImpliesBelowColumnClean`, and `reachableImpliesBelowColumnCleanIsRefuted`.
  * **`smithConfinementViolatingFoldRiseWitness`** — a same-family 4x4 fold-rise backup (`132 -> 198`), pure
    `decide`, independent of the trajectory.
  * **`belowPivotRowRightZero` / `belowPivotCrossClean`** — the natural repair, RECORDED (not proved), with
    `smithCrossCleanExcludesFoldMask` (it would reject the mask) and `smithCrossCleanViolatedAtReachableEntry`
    (it is violated by the reachable state) — so it cannot be composed.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the mandate
does NOT fire.  This is a GRAVEYARD round: the r40 clean descent candidate is machine-REFUTED (the column
guard misses the masking pivot row), leg 3 is machine-REFUTED (reachable states violate confinement), and the
one-round `pivotMagnitudeWithin` measure RISES on the reachable image.  K2
(`SmithClearingOutputOffDiagonalDivides`) stands UNCHANGED and orthogonal (see the D3 census footer).  The
round-level divisor chain stays machine-REFUTED (not stated).  The r18-r40 world, `smithReduceComplete`, and
the refutation certificates stay BYTE-INTACT (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (no recursion introduced; the reachability is the shipped inductive's
`base`/`step`).  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithColumnCleanDescentInsufficient.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Brick 1 — GRAVEYARD A: the r40 `SmithFoldDescendsOnColumnCleanNonzeroPivot` candidate is FALSE

The clean guard constrains the pivot COLUMN below only; a dirty pivot ROW right of the pivot masks the found
non-divisibility.  `[[2,1,0],[0,3,0],[0,0,5]]` at pivot 0: clean column below, but the fold
`row0 += row1` turns `entry(0,1) = 1` into `1 + 3 = 4 = 2*2`, divisible by the pivot, so the cascade
clears it and the pivot magnitude STALLS `2 -> 2`. -/

/-- The refuting matrix for graveyard A: clean pivot column below (`entry(1,0)=0`, `entry(2,0)=0`) but a
dirty pivot-row entry `entry(0,1)=1` that, once the found row `[0,3,0]` is folded in, becomes `4 = 2*2` and
is cleared without exposing the non-divisible `d1=3`. -/
def smithColumnCleanFoldMaskWitness : IntMatrix := IntMatrix.mk [[2, 1, 0], [0, 3, 0], [0, 0, 5]]

/-- The mask witness is a genuine `3 x 3` matrix. -/
theorem smithColumnCleanFoldMaskWitnessRectangular :
    smithColumnCleanFoldMaskWitness.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The mask witness satisfies the r39 confinement conjunct: `|entry(1,0)| = 0 <= 2 = |pivot|`. -/
theorem smithColumnCleanFoldMaskWitnessConfined :
    belowPivotColumnConfined smithColumnCleanFoldMaskWitness 0 := by
  unfold belowPivotColumnConfined; decide

/-- The mask witness satisfies the r40 deep-column-zero conjunct: the only in-range deeper pivot-column entry
`entry(2,0) = 0`.  Structural (the `1 < laterRow < 3` window forces `laterRow = 2`); no `interval_cases`. -/
theorem smithColumnCleanFoldMaskWitnessColumnZeroDeep :
    belowPivotColumnZeroDeep smithColumnCleanFoldMaskWitness 0 3 := by
  intro laterRow pivotSuccLtLater laterLtHeight
  have laterIsTwo : laterRow = 2 := Nat.le_antisymm (Nat.le_of_lt_succ laterLtHeight) pivotSuccLtLater
  subst laterIsTwo; decide

/-- **The mask witness satisfies the FULL r40 clean guard** — the point of graveyard A: the corrected r40
lever HOLDS here, so the clean-guarded descent candidate is genuinely applicable, and yet it fails. -/
theorem smithColumnCleanFoldMaskWitnessColumnClean :
    belowPivotColumnClean smithColumnCleanFoldMaskWitness 0 3 :=
  ⟨smithColumnCleanFoldMaskWitnessConfined, smithColumnCleanFoldMaskWitnessColumnZeroDeep⟩

/-- The pivot is positive (`|d0| = 2 > 0`). -/
theorem smithColumnCleanFoldMaskWitnessPivotPositive :
    0 < (smithColumnCleanFoldMaskWitness.diagonalEntryAt 0).natAbs := by decide

/-- The find-scan reports `some 1` (`d0=2` divides nothing above but `d0 = 2` does not divide `d1 = 3`). -/
theorem smithColumnCleanFoldMaskWitnessFindsSome :
    smithFindNonDividingLaterDiagonal smithColumnCleanFoldMaskWitness 0
      (Nat.min 3 3 - (0 + 1)) (0 + 1) = some 1 := by decide

/-- **The fold STALLS on the mask witness** — the fold `row0 += row1` + cascade lands pivot magnitude `2`,
EQUAL to the input pivot magnitude `2`, so the candidate's conclusion `pivotMagnitudeWithin (fold) <
pivotMagnitudeWithin work` (`2 < 2`) is FALSE here.  The dirty `entry(0,1) = 1` combines with the
non-dividing `d1 = 3` into `4 = 2*2`, which is divisible by the pivot and cleared to `0`. -/
theorem smithColumnCleanFoldMaskWitnessFoldStalls :
    ¬ (pivotMagnitudeWithin
          (smithClearingFoldStep smithColumnCleanFoldMaskWitness 1 0 3 3) 0
        < pivotMagnitudeWithin smithColumnCleanFoldMaskWitness 0) := by decide

/-- **THE GRAVEYARD A — the r40 candidate `SmithFoldDescendsOnColumnCleanNonzeroPivot` is FALSE.**  It fails
at `work = smithColumnCleanFoldMaskWitness`, `foundPos = 1`, `pivotIndex = 0`, `height = width = 3`: all
preconditions hold (rectangular, clean guard, positive pivot, `find = some 1`), yet the conclusion is refuted
(the fold STALLS).  The clean COLUMN guard does not constrain the pivot ROW, and a dirty pivot-row entry
masks the found non-divisibility.  Machine-checked, zero axioms.  The corrected lever would have to add a
pivot-row condition (brick 5 records it and shows it non-composable). -/
theorem smithFoldDescendsOnColumnCleanNonzeroPivotIsRefuted :
    ¬ SmithFoldDescendsOnColumnCleanNonzeroPivot := by
  intro foldDescends
  exact smithColumnCleanFoldMaskWitnessFoldStalls
    (foldDescends smithColumnCleanFoldMaskWitness 1 0 3 3
      smithColumnCleanFoldMaskWitnessRectangular
      smithColumnCleanFoldMaskWitnessColumnClean
      smithColumnCleanFoldMaskWitnessPivotPositive
      smithColumnCleanFoldMaskWitnessFindsSome)

/-! ## Brick 2 — the genuine reachable state at pivot 2: the driver trajectory from `diag(11,11,9,6)`

The corrected driver's trajectory: `base` at the Phase-A output (`diag(6,9,11,11)`), one `step` at pivot 0,
one `step` at pivot 1.  Each `def` is the byte-exact matrix the `ReachableFromPhaseA` constructor produces,
so the reachability witness is definitional (no in-kernel trajectory recomputation). -/

/-- The generating input `diag(11,11,9,6)` — a rectangular `4 x 4` whose corrected-driver trajectory reaches
a confinement-violating pivot-2 state. -/
def smithReachableConfinementInput : IntMatrix := IntMatrix.mk [[11,0,0,0],[0,11,0,0],[0,0,9,0],[0,0,0,6]]

/-- The Phase-A output — the `base` matrix of `ReachableFromPhaseA` at pivot 0 (`diag(6,9,11,11)`). -/
def smithReachablePhaseAState : IntMatrix :=
  smithReachableConfinementInput.applyOperations
    (smithReduceTotal smithReachableConfinementInput 4 4).operations

/-- After the pivot-0 position sweep — the `step`-once matrix at pivot 1. -/
def smithReachablePivotZeroState : IntMatrix :=
  smithReachablePhaseAState.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum smithReachablePhaseAState 0 4 4)
      smithReachablePhaseAState 0 4 4)

/-- **The genuinely reachable pivot-2 state** `[[1,0,0,0],[0,1,0,0],[0,0,66,0],[0,0,132,-99]]` — the
`step`-twice matrix at pivot 2.  At pivot 2 it carries `entry(3,2) = 132 = 2*66`, VIOLATING confinement. -/
def smithReachablePivotTwoState : IntMatrix :=
  smithReachablePivotZeroState.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum smithReachablePivotZeroState 1 4 4)
      smithReachablePivotZeroState 1 4 4)

/-- The generating input is a genuine `4 x 4` matrix. -/
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

/-- **The pivot-2 state is genuinely REACHABLE** — `ReachableFromPhaseA 4 4 _ 2`, built by `base` (Phase-A
output) then two `step`s (pivot-0 and pivot-1 sweeps).  The constructor chain is definitional; zero axioms,
no in-kernel trajectory recomputation. -/
theorem smithReachablePivotTwoStateIsReachable :
    ReachableFromPhaseA 4 4 smithReachablePivotTwoState 2 :=
  ReachableFromPhaseA.step smithReachablePivotZeroState 1
    (ReachableFromPhaseA.step smithReachablePhaseAState 0
      (ReachableFromPhaseA.base smithReachableConfinementInput
        smithReachableConfinementInputRectangular))

/-! ## Brick 3 — GRAVEYARD B: the reachable state VIOLATES the clean guard, and the fold RISES on it -/

/-- **The reachable pivot-2 state VIOLATES confinement** — `|entry(3,2)| = 132 > 66 = |pivot|`, so
`¬ belowPivotColumnConfined`.  Kernel-computed through the full driver trajectory; zero axioms. -/
theorem smithReachablePivotTwoStateNotConfined :
    ¬ belowPivotColumnConfined smithReachablePivotTwoState 2 := by
  unfold belowPivotColumnConfined; decide

/-- The find-scan fires at the reachable pivot-2 state: `some 3` (`d2 = 66` does not divide `d3 = -99`). -/
theorem smithReachablePivotTwoStateFindsSome :
    smithFindNonDividingLaterDiagonal smithReachablePivotTwoState 2
      (Nat.min 4 4 - (2 + 1)) (2 + 1) = some 3 := by decide

/-- **The one-round measure RISES on the reachable fold** — the driver-selected fold `row2 += row3` pulls
`entry(3,2) = 132` into the pivot row and lands `pivotMagnitudeWithin` `66 -> 99`, so `pivotMagnitudeWithin
(fold) < pivotMagnitudeWithin work` (`99 < 66`) is FALSE.  The r31-recorded "measure rises on folds," now on
a genuinely reachable, fireable, driver-chosen fold. -/
theorem smithReachablePivotTwoStateFoldRises :
    ¬ (pivotMagnitudeWithin
          (smithClearingFoldStep smithReachablePivotTwoState 3 2 4 4) 2
        < pivotMagnitudeWithin smithReachablePivotTwoState 2) := by decide

/-- **Leg 3 as a Prop** — that every reachable state ENTERS the r40 clean guard.  This is the "genuinely NEW
r41 trajectory invariant" the r40 wall proposed as the fourth leg.  It is machine-FALSE below. -/
def ReachableImpliesBelowColumnClean : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    belowPivotColumnClean matrix pivotIndex height

/-- **THE GRAVEYARD B — leg 3 `ReachableImpliesBelowColumnClean` is FALSE.**  The genuinely reachable
pivot-2 state (`smithReachablePivotTwoStateIsReachable`) violates the confinement conjunct of the clean guard
(`smithReachablePivotTwoStateNotConfined`), so reachable states do NOT enter the clean guard.  r36's
`reachableImpliesPrefixSettled` settles only the prefix column `< pivotIndex`; column `pivotIndex` below —
where the `2*pivot` fill-in lives — is exactly what is violated.  Machine-checked, zero axioms.  Together
with graveyard A and the fold RISE, this kills the one-round `pivotMagnitudeWithin` descent on the reachable
image. -/
theorem reachableImpliesBelowColumnCleanIsRefuted :
    ¬ ReachableImpliesBelowColumnClean := by
  intro entryLeg
  exact smithReachablePivotTwoStateNotConfined
    (entryLeg smithReachablePivotTwoState 2 4 4 smithReachablePivotTwoStateIsReachable
      smithReachablePivotTwoStateRectangular (by decide) (by decide)).1

/-! ## Brick 4 — a same-family fold-rise backup (pure `decide`, trajectory-independent) -/

/-- A hand-built 4x4 in the same confinement-violating family (`entry(3,2) = 264 > 132 = |pivot|`): the fold
`row2 += row3` RISES `pivotMagnitudeWithin` `132 -> 198`.  Independent of the reachability trajectory —
confirms the fold-rise phenomenon by plain `decide`. -/
def smithConfinementViolatingFoldRiseWitness : IntMatrix :=
  IntMatrix.mk [[2,0,0,0],[0,2,0,0],[0,0,132,0],[0,0,264,-198]]

/-- The backup witness fires the fold: `find = some 3` (`132` does not divide `198`). -/
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

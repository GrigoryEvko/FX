import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutReduceCompletePort

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBezoutFindNoneToChainSeed — the word-agnostic ARC-C
    seed reduction + the sub-block ideal lo-monotonicity, plus the recorded ARC-A residuals (α)/(β)
    (H2-SMITH r49, #2261)

## ★★★★★ MANDATE STATUS: NOT FIRED — HONEST CUT (ARC-A walled; the exact sub-obligations named for r50) ★★★★★

`SmithReduceCompleteBezoutDriverStatement` and `SmithReduceCompleteInBlockDriverStatement` stay
UNINHABITED and BYTE-INTACT.  The #2261 gate `SmithBezoutRepairInvariantsStatement`
(`SmithBezoutReduceCompletePort`) is NOT inhabited this round: it requires BOTH arcs to land, and ARC-A
does not.  The `smithReduceCompleteBezoutMandateReducesToInvariants` reduction (r48, shipped) fires the
mandate the instant that gate is inhabited — but nothing here inhabits it, and NOTHING here inhabits a
weakened variant.

  * **ARC-A** (`SmithBezoutRepairPositionSweepReachesFindNoneStatement`, r48-recorded) needs the fueled
    Bezout position sweep to REACH find-`none`.  Its two open sub-obligations — the positivity-maintenance
    (α) and the trailing-cascade-preserves-`none` (β) — are EMPIRICALLY CONFIRMED here (machine-checked
    `decide` pins on the recon's probe states) but are NOT closeable as GENERAL theorems in r49: no shipped
    lever gives a LOWER bound / non-vanishing on the cascade output pivot (the shipped
    `smithCascadeSweepOutputPivotBounded` is an UPPER bound only), and the neighbouring
    `smithCascadeLandsDivisibleSubBlockIsRefuted` shows the min-abs cascade's sub-block behaviour is
    delicate.  Both are recorded as named residual Props for r50.
  * **ARC-C** the crisp cut: the Bezout chain SEED is WORD-AGNOSTIC.
    `smithBezoutFindNoneImpliesLandsDivisibleSubBlock` (shipped below, GENERAL, CONDITIONAL on the ARC-A
    find-`none`) turns the landed find-`none` DIRECTLY into
    `MatrixEntriesDivisibleByWithin (landed diag) (pivotIndex+1) landed` via the r45 iff bridge
    `smithFindNonDividingInBlockNoneIffDivisibleWithin` + the new lo-monotonicity
    `matrixEntriesDivisibleByWithinLoMonotone` (both shipped below).  This SKIPS the refuted min-abs seed
    route entirely, so r50's ARC-C only needs the NODE-A propagation PORT
    (`chainWindowedThroughPivots` over the Bezout word), not a new gcd-ideal-invariance wall.

## What r49 ships (all additive; consumes r18-r48 levers; zero fabrication)

  * **`matrixEntriesDivisibleByWithinLoMonotone`** — the `[lo, ·)²` sub-block ideal predicate weakens as
    `lo` rises (a super-block divisor still divides the smaller sub-block).  ~1 line, general.
  * **`smithBezoutFindNoneImpliesLandsDivisibleSubBlock`** — GENERAL, CONDITIONAL: IF the Bezout position
    sweep's landed pivot has whole-block find-`none` (the loop's OWN termination test, = ARC-A) THEN the
    landed pivot divides the STRICTLY-ADVANCED sub-block `[pivotIndex+1, ·)²`.  The word-agnostic ARC-C
    seed — the r45 bridge + lo-monotonicity, no gcd-ideal wall.
  * **The recorded ARC-A residuals** `SmithBezoutRepairRoundLandsPivotPositiveStatement` (α) and
    `SmithBezoutTrailingCascadePreservesFindNoneStatement` (β) — the two named r50 targets, UNINHABITED.
  * **The corpus** — the recon's probe seeds as named `IntMatrix` defs, `#eval` census tuples, and
    machine-checked `decide` theorems confirming (α) (a zero-pivot round lands a POSITIVE pivot and
    re-establishes a CLEAN cross) and (β) (the standalone trailing cascade PRESERVES find-`none`) on every
    probe.  The empirical honesty witnesses for the walled arc.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  ADDITIVE only — the r18-r48 world is byte-intact.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutFindNoneToChainSeed.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## Brick 1 — the sub-block ideal predicate is monotone in `lo` (a super-block divisor divides the
    smaller sub-block) -/

/-- **`MatrixEntriesDivisibleByWithin` weakens as the window floor `lo` rises** — if `divisor` divides
every entry of the `[loLower, ·)²` sub-block and `loLower ≤ loUpper`, it divides every entry of the
smaller `[loUpper, ·)²` sub-block (a subset of cells).  Both coordinate guards weaken by
`Nat.le_trans loLe`.  The ~1-line general utility ARC-C needs to advance the divisibility seed from the
pivot `pivotIndex` to the STRICTLY-later block `pivotIndex + 1`. -/
theorem matrixEntriesDivisibleByWithinLoMonotone (divisor : Int) (loLower loUpper : Nat)
    (matrix : IntMatrix) (loLe : loLower ≤ loUpper)
    (divisibleLower : MatrixEntriesDivisibleByWithin divisor loLower matrix) :
    MatrixEntriesDivisibleByWithin divisor loUpper matrix := by
  intro rowIndex rowGe colIndex colGe
  exact divisibleLower rowIndex (Nat.le_trans loLe rowGe) colIndex (Nat.le_trans loLe colGe)

/-! ## Brick 2 — the word-agnostic ARC-C seed reduction: landed find-`none` ⟹ divisible ADVANCED sub-block -/

/-- **The Bezout sweep's landed find-`none` seeds the STRICTLY-ADVANCED sub-block chain** (GENERAL,
CONDITIONAL on the ARC-A find-`none`).  IF the Bezout position sweep's landed pivot has whole-block
find-`none` (the loop's OWN `none`-branch termination test on the LANDED state — exactly the ARC-A
`SmithBezoutRepairPositionSweepReachesFindNoneStatement`) THEN the landed pivot divides every entry of the
strictly-advanced sub-block `[pivotIndex + 1, ·)²`.  Route: the r45 iff bridge
`smithFindNonDividingInBlockNoneIffDivisibleWithin` (mp) turns the landed find-`none` into
`MatrixEntriesDivisibleByWithin (landed diag) pivotIndex landed`; the new `matrixEntriesDivisibleByWithin
LoMonotone` restricts the window floor to `pivotIndex + 1`.  This is the WORD-AGNOSTIC seed — unlike the
REFUTED min-abs seed `SmithCascadeLandsDivisibleSubBlock` it follows DIRECTLY from find-`none` with NO
gcd-ideal-invariance wall — so r50's ARC-C only needs the NODE-A propagation port over the Bezout word. -/
theorem smithBezoutFindNoneImpliesLandsDivisibleSubBlock
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (landedFindNone :
      smithFindNonDividingInBlock
          (matrix.applyOperations
            (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          pivotIndex height width = none) :
    MatrixEntriesDivisibleByWithin
        ((matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
        (pivotIndex + 1)
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)) := by
  have landedRect :
      (matrix.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).IsRectangular height width :=
    applyOperationsPreservesRectangular _ matrix isRect
  have divisibleAtPivot :
      MatrixEntriesDivisibleByWithin
        ((matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
        pivotIndex
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)) :=
    (smithFindNonDividingInBlockNoneIffDivisibleWithin
        (matrix.applyOperations
          (smithBezoutRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width landedRect).mp landedFindNone
  exact matrixEntriesDivisibleByWithinLoMonotone _ pivotIndex (pivotIndex + 1) _
    (Nat.le_succ pivotIndex) divisibleAtPivot

/-! ## Brick 3 — the recorded ARC-A residuals (α) and (β) — the exact r50 sub-obligations (UNINHABITED)

Both are GENERAL statements over the reachable class.  They are EMPIRICALLY CONFIRMED by the `decide`
pins below, but NOT closeable in r49: (α) needs a NEW cascade-output LOWER bound / non-vanishing lever
(the shipped `smithCascadeSweepOutputPivotBounded` is an upper bound only); (β) needs a NEW
"cascade preserves whole-block divisibility" lever (no such lever is shipped, and the min-abs cascade's
sub-block behaviour is delicate per `smithCascadeLandsDivisibleSubBlockIsRefuted`).  They are NEVER
inhabited by a weakened variant. -/

/-- **(α) positivity-maintenance (recorded, UNINHABITED)** — on every rectangular, in-range,
whole-block-find-`some` state (the reachable class), one Bezout-drop round lands a POSITIVE pivot
magnitude.  Feeds the two-phase fuel adequacy: from a zero pivot ONE round lands a positive pivot (and
re-establishes the clean cross), after which K1 `smithBezoutRoundStrictlyDescendsOnCleanCross` takes over.
The r50 target for (α). -/
def SmithBezoutRepairRoundLandsPivotPositiveStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    (smithFindNonDividingInBlock matrix pivotIndex height width).isSome = true →
    0 < pivotMagnitudeWithin (smithBezoutRepairRound matrix pivotIndex height width) pivotIndex

/-- **(β) trailing-cascade-preserves-`none` (recorded, UNINHABITED)** — on every rectangular, in-range
state where the pivot ALREADY divides the whole block (find-`none`), applying the standalone trailing
`smithCascadeSweep` (the `none`-branch of `smithBezoutRepairPositionSweep`) leaves find-`none` intact.
This is the trailing letter the ARC-A residual's actual sweep output ends with.  The r50 target for (β). -/
def SmithBezoutTrailingCascadePreservesFindNoneStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    smithFindNonDividingInBlock matrix pivotIndex height width = none →
    smithFindNonDividingInBlock
        (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
            height width))
        pivotIndex height width = none

/-! ## Brick 4 — the corpus: the recon's probe seeds, `#eval` census tuples, and `decide` honesty pins -/

/-- (α) probe: the r46 zero-pivot seed `[[0,0],[0,4]]` — a clean cross with a ZERO pivot (K1's positivity
guard excludes it; the recon's `probeZP`). -/
def alphaZeroPivotSeed : IntMatrix := IntMatrix.mk [[0, 0], [0, 4]]

/-- (α) probe: the wide zero-pivot seed `[[0,0,0],[0,6,0],[0,0,10]]` — the recon's `probeZP3`, where the
K1 measure RISES then descends (`0 -> 6 -> 2`). -/
def alphaZeroPivotWideSeed : IntMatrix := IntMatrix.mk [[0, 0, 0], [0, 6, 0], [0, 0, 10]]

/-- (β) probe: a divided diagonal `[[2,0],[0,4]]` — find-`none` (`2 ∣ 4`); the recon's `probeFN1`. -/
def betaFindNoneDiagSeed : IntMatrix := IntMatrix.mk [[2, 0], [0, 4]]

/-- (β) probe: a single-pivot state `[[4,0],[0,0]]` — find-`none` (all block entries `0`); the recon's
`probeFN2`. -/
def betaFindNoneSingletonSeed : IntMatrix := IntMatrix.mk [[4, 0], [0, 0]]

/-- (β) probe: a divided triple diagonal `[[1,0,0],[0,2,0],[0,0,6]]` — find-`none` (`1 ∣ everything`);
the recon's `probeFN3`. -/
def betaFindNoneTripleSeed : IntMatrix := IntMatrix.mk [[1, 0, 0], [0, 2, 0], [0, 0, 6]]

/-! (α) census: `(inputPivotMag, roundOutputPivotMag, crossCleanBefore, crossCleanAfter, findBefore)` —
a zero-pivot round RISES the K1 measure off the floor (`0 -> 4`, `0 -> 6`) yet lands a POSITIVE pivot AND
re-establishes the clean cross, exactly the (α) two-phase base. -/
#eval (pivotMagnitudeWithin alphaZeroPivotSeed 0,
  pivotMagnitudeWithin (smithBezoutRepairRound alphaZeroPivotSeed 0 2 2) 0,
  smithCrossIsClear alphaZeroPivotSeed 0 2 2,
  smithCrossIsClear (smithBezoutRepairRound alphaZeroPivotSeed 0 2 2) 0 2 2,
  smithFindNonDividingInBlock alphaZeroPivotSeed 0 2 2)
#eval (pivotMagnitudeWithin alphaZeroPivotWideSeed 0,
  pivotMagnitudeWithin (smithBezoutRepairRound alphaZeroPivotWideSeed 0 3 3) 0,
  smithCrossIsClear alphaZeroPivotWideSeed 0 3 3,
  smithCrossIsClear (smithBezoutRepairRound alphaZeroPivotWideSeed 0 3 3) 0 3 3,
  smithFindNonDividingInBlock alphaZeroPivotWideSeed 0 3 3)

/-! (β) census: `(findBefore.isNone, findAfterTrailingCascade.isNone)` — the standalone trailing cascade
preserves find-`none` on every probe (`(true, true)`). -/
#eval ((smithFindNonDividingInBlock betaFindNoneDiagSeed 0 2 2).isNone,
  (smithFindNonDividingInBlock (betaFindNoneDiagSeed.applyOperations
    (smithCascadeSweep (smithMinorAbsSum betaFindNoneDiagSeed 0 2 2) betaFindNoneDiagSeed 0 2 2))
    0 2 2).isNone)
#eval ((smithFindNonDividingInBlock betaFindNoneSingletonSeed 0 2 2).isNone,
  (smithFindNonDividingInBlock (betaFindNoneSingletonSeed.applyOperations
    (smithCascadeSweep (smithMinorAbsSum betaFindNoneSingletonSeed 0 2 2) betaFindNoneSingletonSeed 0 2 2))
    0 2 2).isNone)
#eval ((smithFindNonDividingInBlock betaFindNoneTripleSeed 0 3 3).isNone,
  (smithFindNonDividingInBlock (betaFindNoneTripleSeed.applyOperations
    (smithCascadeSweep (smithMinorAbsSum betaFindNoneTripleSeed 0 3 3) betaFindNoneTripleSeed 0 3 3))
    0 3 3).isNone)

/-! ## (α) honesty theorems — a zero-pivot round lands a POSITIVE pivot + re-establishes a CLEAN cross -/

/-- **(α), narrow probe** — one Bezout-drop round from the zero-pivot `[[0,0],[0,4]]` lands a POSITIVE
pivot magnitude (`0 -> 4 > 0`).  The (α) base-case witness: even off the K1 measure floor the round lands
a positive pivot.  `decide`, zero axioms. -/
theorem alphaZeroPivotRoundLandsPivotPositive :
    0 < pivotMagnitudeWithin (smithBezoutRepairRound alphaZeroPivotSeed 0 2 2) 0 := by decide

/-- **(α), narrow probe** — the same round re-establishes a CLEAN cross (the K1 loop-invariant guard). -/
theorem alphaZeroPivotRoundReEstablishesCleanCross :
    smithCrossIsClear (smithBezoutRepairRound alphaZeroPivotSeed 0 2 2) 0 2 2 = true := by decide

/-- **(α), wide probe** — one Bezout-drop round from `[[0,0,0],[0,6,0],[0,0,10]]` lands a POSITIVE pivot
(`0 -> 6 > 0`) despite the K1 measure RISING off the floor.  The two-phase (α) is real precisely here. -/
theorem alphaZeroPivotWideRoundLandsPivotPositive :
    0 < pivotMagnitudeWithin (smithBezoutRepairRound alphaZeroPivotWideSeed 0 3 3) 0 := by decide

/-- **(α), wide probe** — the wide round likewise re-establishes a CLEAN cross. -/
theorem alphaZeroPivotWideRoundReEstablishesCleanCross :
    smithCrossIsClear (smithBezoutRepairRound alphaZeroPivotWideSeed 0 3 3) 0 3 3 = true := by decide

/-! ## (β) honesty theorems — the standalone trailing cascade PRESERVES find-`none` -/

/-- **(β), diagonal probe, before** — `[[2,0],[0,4]]` has find-`none` (`2 ∣ 4`). -/
theorem betaFindNoneDiagBefore :
    (smithFindNonDividingInBlock betaFindNoneDiagSeed 0 2 2).isNone = true := by decide

/-- **(β), diagonal probe** — the standalone trailing `smithCascadeSweep` PRESERVES find-`none`. -/
theorem betaFindNoneDiagTrailingCascadePreservesFindNone :
    (smithFindNonDividingInBlock (betaFindNoneDiagSeed.applyOperations
        (smithCascadeSweep (smithMinorAbsSum betaFindNoneDiagSeed 0 2 2) betaFindNoneDiagSeed 0 2 2))
        0 2 2).isNone = true := by decide

/-- **(β), singleton probe, before** — `[[4,0],[0,0]]` has find-`none` (all block entries `0`). -/
theorem betaFindNoneSingletonBefore :
    (smithFindNonDividingInBlock betaFindNoneSingletonSeed 0 2 2).isNone = true := by decide

/-- **(β), singleton probe** — the standalone trailing cascade PRESERVES find-`none`. -/
theorem betaFindNoneSingletonTrailingCascadePreservesFindNone :
    (smithFindNonDividingInBlock (betaFindNoneSingletonSeed.applyOperations
        (smithCascadeSweep (smithMinorAbsSum betaFindNoneSingletonSeed 0 2 2) betaFindNoneSingletonSeed 0 2 2))
        0 2 2).isNone = true := by decide

/-- **(β), triple probe, before** — `[[1,0,0],[0,2,0],[0,0,6]]` has find-`none` (`1 ∣ everything`). -/
theorem betaFindNoneTripleBefore :
    (smithFindNonDividingInBlock betaFindNoneTripleSeed 0 3 3).isNone = true := by decide

/-- **(β), triple probe** — the standalone trailing cascade PRESERVES find-`none`. -/
theorem betaFindNoneTripleTrailingCascadePreservesFindNone :
    (smithFindNonDividingInBlock (betaFindNoneTripleSeed.applyOperations
        (smithCascadeSweep (smithMinorAbsSum betaFindNoneTripleSeed 0 3 3) betaFindNoneTripleSeed 0 3 3))
        0 3 3).isNone = true := by decide

/-! ## The ARC-C seed reduction is NON-VACUOUS — its antecedent holds on a corpus seed

The conditional `smithBezoutFindNoneImpliesLandsDivisibleSubBlock` is not vacuous: on the divided seed
`betaFindNoneDiagSeed` the FULL Bezout position sweep output already has whole-block find-`none`, so the
seed reduction genuinely delivers the advanced-sub-block divisibility there. -/
theorem betaFindNoneDiagBezoutSweepLandedFindNone :
    (smithFindNonDividingInBlock (betaFindNoneDiagSeed.applyOperations
        (smithBezoutRepairPositionSweep (smithMinorAbsSum betaFindNoneDiagSeed 0 2 2)
          betaFindNoneDiagSeed 0 2 2))
        0 2 2).isNone = true := by decide

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedFixtures — the seed's magnitude body
    kernel-checked TRUE on the NON-diagonal ADVANCED matrices the repair phase actually threads
    (H2-SMITH r34, #2261 — the corrected-route round)

## What this module adds (positive, additive, non-redundant)

The corrected total driver `smithReduceComplete` reduces (r20–r22) to the single per-phase seed
`SmithCascadeLandsDivisibleSubBlock` (`SmithWindowedChainReduction`): at each pivot the landed diagonal
divides the WHOLE later sub-block of the advanced matrix.  Two facts were already machine-checked in
prior rounds:

  * **The general `∀`-seed is REFUTED** on the OUT-OF-IMAGE seed `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]`
    (`smithCascadeLandsDivisibleSubBlockIsRefuted`, `SmithLandedMagnitudeRefuted`, r33), together with a
    battery of cross-clear / negative / non-square / anti-diagonal out-of-image refuters.
  * **The RAW-INPUT diagonal magnitude identity holds** — `|landed| = gcd(minor)` pinned by `decide` on
    the raw diagonal inputs at various pivots (`landedMagnitudeEqMinorGcdOnKillerSeed…`,
    `SmithLandedMagnitudeEquivalence`, r32).

What NEITHER of those pins is the object `chainWindowedThroughPivots` (`SmithWindowedChainReduction`,
`:453`) actually feeds the seed at pivots `≥ 1`: the **advanced matrix**
`matrix.applyOperations (smithRepairPositionSweepClearing (smithMinorAbsSum matrix 0 …) matrix 0 …)` —
the pivot-`0` repair position-sweep output.  That matrix is genuinely NON-diagonal (it carries the
interior fill-in r24/r33 flagged as the wall — e.g. the `-20` inside the pivot-`1` window
`[1, ·)²` of `diag(15, 10, 6, 4)`, `smithDiagonalInputPivotOneInputNotWindowDiagonal`,
`SmithDiagonalInputSpecialization`).  This module pins, `decide`-kernel-checked and zero-axiom, that the
seed's magnitude body `|landed@1| = gcd(minor@1)` holds ON THOSE ADVANCED MATRICES across a hostile
spread (`3×3`, `4×4`, non-square, negative, coprime, with genuine interior fill-in).  It is the first
machine-check of the IN-DRIVER-IMAGE (reachable-set) form on the ACTUAL non-diagonal objects the wiring
threads — the positive evidence that the restricted (reachable) seed, the honest surviving open content,
holds precisely where r33 could only assert it in prose.

## What this module does NOT claim (honesty banner)

This module inhabits NOTHING hypothesis-free.  `SmithReduceCompleteDriverStatement`
(`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the mandate does NOT fire.  The general
`∀`-seed is REFUTED (above); these fixtures are evidence for the RESTRICTED reachable-image form, NOT a
proof of any `∀`-statement.  The honest OPEN content is the reachable-image keystone — a multi-round arc
(the reachable-trajectory induction re-parameterizing `chainWindowedThroughPivots` off the unrestricted
seed, plus the restricted min-abs descent `|landed| ≤ gcd`, the r11+ wall).  The diagonal-INPUT
restriction is a DEAD route (it discharges only pivot `0`, `smithDiagonalInputPivotOneInputNotWindowDiagonal`);
the correct carrier is the reachable IMAGE, which these fixtures evidence.  The r18–r33 world and
`smithReduceComplete` stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedFixtures.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The advanced matrix — the exact object `chainWindowedThroughPivots` threads at pivot `1` -/

/-- **The pivot-`0` repair position-sweep advance** — the matrix `chainWindowedThroughPivots` carries
into its pivot-`1` step (`SmithWindowedChainReduction`, `:521`).  On a diagonal it is genuinely
NON-diagonal: the Euclid fold plants interior fill-in inside the `[1, ·)²` window (the objects r24/r33
called the wall). -/
def matrixAdvancedByPivotZeroSweep (matrix : IntMatrix) (height width : Nat) : IntMatrix :=
  matrix.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix 0 height width) matrix 0 height width)

/-- **The landed-pivot magnitude** — `|d_pivot|` after the pivot's own clearing position sweep. -/
def landedMagnitudeAt (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  ((matrix.applyOperations
      (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs

/-- **The minor-gcd magnitude** — `|gcd(minor)|` of the `[pivot, ·)²` window. -/
def minorGcdMagnitudeAt (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  (minorGcdWithin matrix pivotIndex height width).natAbs

/-! ## The advanced matrix carries genuine interior fill-in (the NON-diagonal object)

Two concrete structural pins: the advanced matrix is not window-diagonal — it carries a nonzero
off-diagonal entry INSIDE the pivot-`1` window `[1, ·)²`, the very fill-in the seed must divide. -/

set_option maxRecDepth 32000 in
/-- **The re-plumb advance carries `-20` inside `[1, ·)²`.**  The pivot-`0` sweep of `diag(15, 10, 6, 4)`
lands `[[1,0,0,0],[0,-20,0,0],[0,0,6,0],[0,-20,0,-30]]` — nonzero off-diagonal `-20` at `(3, 1)` inside
the pivot-`1` window (the exact object `smithDiagonalInputPivotOneInputNotWindowDiagonal` refutes as
window-diagonal).  So the seed at pivot `1` is genuinely tested on a NON-diagonal advanced matrix. -/
theorem advancedMatrixCarriesInteriorFillInReplumb :
    (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4).rows
      = [[1, 0, 0, 0], [0, -20, 0, 0], [0, 0, 6, 0], [0, -20, 0, -30]] := by
  decide

set_option maxRecDepth 16000 in
/-- **The `3×3` advance carries `60` inside `[1, ·)²`.**  The pivot-`0` sweep of `diag(30, 20, 12)` lands
`[[2,0,0],[0,60,0],[0,60,-60]]` — nonzero off-diagonal `60` at `(2, 1)` inside the pivot-`1` window. -/
theorem advancedMatrixCarriesInteriorFillInThree :
    (matrixAdvancedByPivotZeroSweep { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 3 3).rows
      = [[2, 0, 0], [0, 60, 0], [0, 60, -60]] := by
  decide

/-! ## The seed's magnitude body TRUE on the advanced matrices — `|landed@1| = gcd(minor@1)`

Each pins the seed's magnitude content `|landed| = gcd(minor)` at pivot `1` on the NON-diagonal advanced
matrix `matrixAdvancedByPivotZeroSweep D` — the in-driver-image object.  Both sides are computed and
compared; no literal is hard-coded.  All `decide` (kernel reduction), all at or below the `4×4` defeq
ceiling. -/

set_option maxRecDepth 16000 in
/-- `diag(6, 10, 8)` — advance at pivot `1` lands magnitude `2 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedSixTenEight :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 16000 in
/-- `diag(12, 18, 30)` — advance at pivot `1` lands magnitude `6 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirty :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0], [0, 18, 0], [0, 0, 30]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0], [0, 18, 0], [0, 0, 30]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 16000 in
/-- `diag(30, 20, 12)` — advance at pivot `1` (with the `60` fill-in) lands magnitude `60 = gcd`.  The
identity holds on a genuinely NON-diagonal advanced matrix. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedThirtyTwentyTwelve :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 16000 in
/-- `diag(9, 6, 4)` — advance at pivot `1` lands magnitude `6 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedNineSixFour :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[9, 0, 0], [0, 6, 0], [0, 0, 4]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[9, 0, 0], [0, 6, 0], [0, 0, 4]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 16000 in
/-- `diag(-12, -18, -30)` — advance at pivot `1` lands magnitude `6 = gcd`.  The identity survives
negative entries through the fold. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedNegativeTwelveEighteenThirty :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[-12, 0, 0], [0, -18, 0], [0, 0, -30]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[-12, 0, 0], [0, -18, 0], [0, 0, -30]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 16000 in
/-- `diag(3, 5, 7)` (coprime) — advance at pivot `1` collapses to the unit `1 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedCoprimeThreeFiveSeven :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[3, 0, 0], [0, 5, 0], [0, 0, 7]] } 3 3) 1 3 3
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[3, 0, 0], [0, 5, 0], [0, 0, 7]] } 3 3) 1 3 3 := by
  decide

set_option maxRecDepth 32000 in
/-- `diag(15, 10, 6, 4)` (`4×4`, coprime, with the `-20` fill-in) — advance at pivot `1` lands magnitude
`2 = gcd`.  The heaviest kernel pin: the seed holds on the exact re-plumb object. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedReplumbFifteenTenSixFour :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4) 1 4 4
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4) 1 4 4 := by
  decide

set_option maxRecDepth 32000 in
/-- `diag(12, 18, 30, 42)` (`4×4`) — advance at pivot `1` lands magnitude `6 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirtyFortyTwo :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0, 0], [0, 18, 0, 0], [0, 0, 30, 0], [0, 0, 0, 42]] } 4 4) 1 4 4
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0, 0], [0, 18, 0, 0], [0, 0, 30, 0], [0, 0, 0, 42]] } 4 4) 1 4 4 := by
  decide

set_option maxRecDepth 16000 in
/-- Non-square `3×2` `diag(6, 10)` — advance at pivot `1` lands magnitude `30 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedNonSquareThreeByTwo :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[6, 0], [0, 10], [0, 0]] } 3 2) 1 3 2
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[6, 0], [0, 10], [0, 0]] } 3 2) 1 3 2 := by
  decide

set_option maxRecDepth 16000 in
/-- Non-square `2×4` `diag(12, 18)` — advance at pivot `1` lands magnitude `36 = gcd`. -/
theorem landedMagnitudeEqMinorGcdOnAdvancedNonSquareTwoByFour :
    landedMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0, 0], [0, 18, 0, 0]] } 2 4) 1 2 4
      = minorGcdMagnitudeAt (matrixAdvancedByPivotZeroSweep { rows := [[12, 0, 0, 0], [0, 18, 0, 0]] } 2 4) 1 2 4 := by
  decide

/-! ## The r34 ledger (H2-SMITH r34, #2261) — the corrected-route round

**What r34 ships (all zero-axiom, additive; the r18–r33 world byte-intact).**  The first POSITIVE
machine-check of the reachable-image seed on the ACTUAL non-diagonal advanced matrices
`chainWindowedThroughPivots` threads: two structural pins that the advance carries interior fill-in
(`advancedMatrixCarriesInteriorFillIn…`), and ten `|landed@1| = gcd(minor@1)` fixtures across a hostile
spread (`3×3`, `4×4`, non-square, negative, coprime, with genuine fill-in).  These refute the r33 prose
that the seed "bottoms out" on the advanced matrices — it does not; it holds, everywhere in image tested.

**What r34 does NOT ship.**  No hypothesis-free inhabitant of `SmithReduceCompleteDriverStatement` — the
mandate does NOT fire.  The refuting seed `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]` is the REFUTER
(`smithCascadeLandsDivisibleSubBlockIsRefuted`, `SmithLandedMagnitudeRefuted`), NOT a witness; the general
`∀`-seed stays REFUTED.  The honest open content is the reachable-image keystone: (i) re-parameterize
`chainWindowedThroughPivots` to thread a reachability witness (retiring the unrestricted seed hypothesis);
(ii) the restricted min-abs descent `|landed| ≤ gcd` on the reachable set (the r11+ wall).  Each is a
standalone multi-round arc; neither is r34-sized.  No flip is fabricated. -/

end FX1Poly.ComputerAlgebra

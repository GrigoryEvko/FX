import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBlockFindRepairDriver
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPivotMagnitudeDescent
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBlockRoundDescentRefuted — the CORRECTED whole-block
    round's per-round pivot-magnitude descent is FALSE (H2-SMITH r46, #2261)

r45 (`SmithBlockFindRepairDriver`) shipped the CORRECTED whole-block repair loop
`smithRepairPositionSweepClearingInBlock` and NAMED two residuals for r46, hypothesis-free:
`SmithReduceCompleteInBlockDriverStatement` (the mandate object) and its fuel-adequacy half
`SmithBlockRepairReachesFindNone`.  The r45 footer proposed to discharge adequacy by the CoqEAL
Euclidean-norm route (`sdvd_Bezout_step` + `ltn_enorm`): each firing round supposedly lands a strict
divisor of the pivot, so `|new pivot| < |old pivot|` (the `sdvd` shape).  The footer asserted this was
"probed 15/15 with no rise".

**r46 WIDE-PROBE (28 trajectories) REFUTES the per-round descent, and the 15/15 claim is FALSE.**  The
CORRECTED round is `fold the found ROW into the pivot row, then re-fire the min-abs Euclid cascade at the
pivot`.  On a DIRTY pivot column its fold+min-abs-cascade is byte-identical to the OLD diagonal round's
(r31), so the OLD counterexample transfers VERBATIM.  On `smithBlockRoundCounterexample = [[2,0],[4,3]]`
(pivot `2`, whole-block find `= some` at the off-diagonal `3`): one corrected round folds `row0 += row1`
to `[[6,3],[4,3]]`, the cascade brings the min-abs `3` to the pivot and clears its cross to
`[[3,0],[0,-2]]`, and STOPS — landing pivot magnitude `3`, strictly ABOVE the input `2`.  So the
per-round conclusion `pivotMagnitudeWithin (round) < pivotMagnitudeWithin work` is FALSE here
(`smithBlockRoundRaisesPivotOnDirtyColumn`, `decide`, zero axioms).  The rise is not pathological: the
probe found it on square 2x2 / 3x3 / 4x4, on a WIDE non-square 2x3, and on a deep multi-fire seed.

**The zero-pivot bootstrap independently kills the measure floor.**  On `[[0,0],[0,4]]` the pivot
magnitude is `0` (the minimum of any `Nat` measure) yet the whole-block find is `some` and one corrected
round RISES to `4` (`smithBlockRoundZeroPivotBootstrapRises`).  So "measure `0` implies find-`none`" — the
base case of any magnitude-well-foundedness argument — is also false.

**Every prior single-Nat magnitude refutation TRANSFERS to the corrected round.**  r22 machine-refuted
`smithMinorAbsSum` (rises), r26 found `minNonzeroAbsWithin` STALLS, r31 refuted `pivotMagnitudeWithin`
(the very `[[2,0],[4,3]]` used here).  Because the corrected round's fold+min-abs-cross-clear descent is
the SAME shape as the old round's, all three transfer.  The CoqEAL `sdvd` invariant (`new pivot | old
pivot`) does NOT hold for FX's round: the cascade selects the MIN-ABS block entry, not a gcd-preserving
Bezout combination, so it neither divides the old pivot (`3` does not divide `2`) nor is bounded by
`gcd(pivot, offender)`.

**What IS true — and why the mandate still does not fire.**  Adequacy holds EMPIRICALLY: on all 28 probe
trajectories the fuelled corrected loop REACHES a whole-block find-`none` state and lands
`|pivot| = |minorGcd|` (`smithBlockRoundCounterexampleFullLoopReachesFindNone`,
`...FullLoopLandsMinorGcd`).  So `SmithBlockRepairReachesFindNone` is TRUE — but its termination is NOT a
per-round magnitude descent; it is the gcd-ideal content, on the same footing as the off-diagonal chain
half.  The magnitude-descent route to adequacy (the only lever r46 hypothesised) is DEAD.  Hence
`SmithReduceCompleteInBlockDriverStatement` stays UNINHABITED hypothesis-free; the #2261 mandate is
honestly WALLED, and this file is the r46 (eighth) graveyard entry — a refutation, not the mandate.

The r47 bill: (K1) `SmithBlockRepairReachesFindNone` — TRUE, gcd-ideal-hard, no magnitude measure works;
(K2) the corrected-word chain twins of `minorGcdDividesLanded` + `landedDividesInputBlockImpliesAbs
EqMinorGcd`; and the UNPORTED driver reduction `smithReduceCompleteInBlockDriverOfRepairInvariants` (the
corrected-round twin of the shipped `smithReduceCompleteDriverOfRepairInvariants`), which — even ported —
only reduces the mandate to `K1 and K2`, never fires it.

Additive only: `smithReduceComplete`, the corrected driver, and the r18-r45 world stay byte-intact.  Raw
Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`/`WellFounded.fix`.  ASCII identifiers.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockRoundDescentRefuted.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## One corrected whole-block round + the landed loop state -/

/-- **One CORRECTED whole-block repair round** on the `[pivotIndex, ..)` square block: the corrected
repair word at `fuel = 1` (fold the found row into the pivot row, then the min-abs Euclid cascade)
applied to `work`.  At `fuel = 1` the recursive tail is empty, so when the whole-block find fires this is
exactly one firing round. -/
def smithBlockRoundOnce (work : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  work.applyOperations (smithRepairPositionSweepClearingInBlock 1 work pivotIndex height width)

/-- **The corrected loop's LANDED state** under the shipped `smithMinorAbsSum` fuel seed — the exact
state whose whole-block find-`none` is `SmithBlockRepairReachesFindNone`. -/
def smithBlockRepairLandedState (work : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  work.applyOperations
    (smithRepairPositionSweepClearingInBlock (smithMinorAbsSum work pivotIndex height width)
      work pivotIndex height width)

/-! ## The dirty-pivot-column counterexample (the r31 matrix, transferred to the corrected round) -/

/-- The refuting matrix: pivot `2` divides `2, 0, 4` but NOT the off-diagonal `3`, so the whole-block
find fires; the dirty pivot column (`entry(1,0) = 4`) makes the fold+cascade land magnitude `3 > 2`. -/
def smithBlockRoundCounterexample : IntMatrix := IntMatrix.mk [[2, 0], [4, 3]]

/-- The counterexample is a genuine `2 x 2` matrix. -/
theorem smithBlockRoundCounterexampleIsRectangular :
    smithBlockRoundCounterexample.IsRectangular 2 2 := ⟨rfl, rfl, rfl, trivial⟩

/-- The pivot magnitude is positive (`|2| = 2 > 0`, the descent property's guard). -/
theorem smithBlockRoundCounterexamplePivotPositive :
    0 < pivotMagnitudeWithin smithBlockRoundCounterexample 0 := by decide

set_option maxRecDepth 100000 in
/-- The whole-block find fires on the counterexample (`some`, not `none` — the descent property's third
guard genuinely holds). -/
theorem smithBlockRoundCounterexampleFindsSome :
    (smithFindNonDividingInBlock smithBlockRoundCounterexample 0 2 2).isSome = true := by decide

set_option maxRecDepth 100000 in
/-- **The corrected round LANDS pivot magnitude `3`** on the counterexample (`[[2,0],[4,3]]` fold to
`[[6,3],[4,3]]`, cascade to `[[3,0],[0,-2]]`).  `decide`, zero axioms. -/
theorem smithBlockRoundLandsPivotThree :
    pivotMagnitudeWithin (smithBlockRoundOnce smithBlockRoundCounterexample 0 2 2) 0 = 3 := by decide

set_option maxRecDepth 100000 in
/-- **The corrected round RAISES the pivot magnitude** — `3 < 2` is false, so the per-round descent
conclusion fails on the counterexample.  The corrected-round twin of r31's
`smithFoldStepRaisesPivotOnCounterexample`, over the WHOLE-BLOCK find. -/
theorem smithBlockRoundRaisesPivotOnDirtyColumn :
    ¬ (pivotMagnitudeWithin (smithBlockRoundOnce smithBlockRoundCounterexample 0 2 2) 0
        < pivotMagnitudeWithin smithBlockRoundCounterexample 0) := by decide

/-! ## Adequacy HOLDS on the counterexample — but not via magnitude descent -/

set_option maxRecDepth 100000 in
/-- **The full corrected loop DOES reach whole-block find-`none`** on the counterexample (adequacy holds
here: `SmithBlockRepairReachesFindNone` at this input).  The loop rises `2 -> 3` mid-flight yet still
lands — termination is the gcd-ideal content, NOT the refuted per-round measure. -/
theorem smithBlockRoundCounterexampleFullLoopReachesFindNone :
    smithFindNonDividingInBlock (smithBlockRepairLandedState smithBlockRoundCounterexample 0 2 2) 0 2 2
      = none := by decide

set_option maxRecDepth 100000 in
/-- **The full corrected loop lands `|pivot| = |minorGcd| = 1`** on the counterexample — the C3 landing
conclusion holds where the per-round descent does not. -/
theorem smithBlockRoundCounterexampleFullLoopLandsMinorGcd :
    pivotMagnitudeWithin (smithBlockRepairLandedState smithBlockRoundCounterexample 0 2 2) 0
      = (minorGcdWithin smithBlockRoundCounterexample 0 2 2).natAbs := by decide

/-! ## The zero-pivot bootstrap — the magnitude measure has no floor -/

/-- The zero-pivot seed: pivot magnitude `0`, yet the whole-block find fires on the off-diagonal `4`. -/
def smithBlockRoundZeroPivotSeed : IntMatrix := IntMatrix.mk [[0, 0], [0, 4]]

/-- The zero-pivot seed is a genuine `2 x 2` matrix. -/
theorem smithBlockRoundZeroPivotSeedIsRectangular :
    smithBlockRoundZeroPivotSeed.IsRectangular 2 2 := ⟨rfl, rfl, rfl, trivial⟩

/-- The pivot magnitude at the zero-pivot seed is `0` (the minimum of any `Nat` measure). -/
theorem smithBlockRoundZeroPivotSeedPivotMagnitudeZero :
    pivotMagnitudeWithin smithBlockRoundZeroPivotSeed 0 = 0 := by decide

set_option maxRecDepth 100000 in
/-- **Measure `0` does NOT imply find-`none`** — at the zero-pivot seed the whole-block find still fires,
so the base case of any magnitude-well-foundedness argument is violated. -/
theorem smithBlockRoundZeroPivotSeedFindsSome :
    (smithFindNonDividingInBlock smithBlockRoundZeroPivotSeed 0 2 2).isSome = true := by decide

set_option maxRecDepth 100000 in
/-- **The zero-pivot bootstrap RISES `0 -> 4`** — from the measure floor, one corrected round produces a
LARGER-magnitude pivot.  A second, independent obstruction to a `Nat`-magnitude descent. -/
theorem smithBlockRoundZeroPivotBootstrapRises :
    pivotMagnitudeWithin (smithBlockRoundOnce smithBlockRoundZeroPivotSeed 0 2 2) 0 = 4 := by decide

/-! ## The headline refutation -/

/-- **The corrected whole-block round's per-round pivot-magnitude descent.**  Exactly the property a
`pivotMagnitudeWithin`-descent proof of `SmithBlockRepairReachesFindNone` would consume: on every
rectangular firing state (positive pivot magnitude, whole-block find `= some`), one corrected round
strictly lowers the pivot magnitude.  Refuted below. -/
def SmithBlockRoundDescendsPerRound : Prop :=
  ∀ (work : IntMatrix) (pivotIndex height width : Nat),
    work.IsRectangular height width →
    0 < pivotMagnitudeWithin work pivotIndex →
    (smithFindNonDividingInBlock work pivotIndex height width).isSome = true →
    pivotMagnitudeWithin (smithBlockRoundOnce work pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-- **THE HEADLINE — the corrected block round's per-round descent is FALSE.**
`SmithBlockRoundDescendsPerRound` fails at `work = smithBlockRoundCounterexample`, `pivotIndex = 0`,
`height = width = 2`: all three guards hold (rectangular, `|2| > 0`, find `= some`), yet the conclusion
`3 < 2` is refuted.  So no per-round `pivotMagnitudeWithin` descent can discharge the fuel-adequacy
residual `SmithBlockRepairReachesFindNone` — the #2261 mandate stays WALLED.  Machine-checked, zero
axioms. -/
theorem smithBlockRoundDescendsPerRoundIsRefuted : ¬ SmithBlockRoundDescendsPerRound := by
  intro roundDescends
  exact smithBlockRoundRaisesPivotOnDirtyColumn
    (roundDescends smithBlockRoundCounterexample 0 2 2
      smithBlockRoundCounterexampleIsRectangular
      smithBlockRoundCounterexamplePivotPositive
      smithBlockRoundCounterexampleFindsSome)

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPivotMagnitudeDescent

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithFoldDescentRefuted — the r27/r28 single-fold descent
    obligation `SmithFoldDescendsOnNonzeroPivot` is FALSE (H2-SMITH r31, #2261)

r27 (`SmithPivotMagnitudeDescent`) named `SmithFoldDescendsOnNonzeroPivot` as the r28 obligation whose
proof would discharge the fuel-adequacy keystone half `K1 = SmithClearingOutputFindNone` (via
`smithClearingOutputFindNoneFromFoldDescent`).  r30 (`SmithCascadeOutputBound`) proposed to prove it by
composing the never-raises invariant with a single Euclid step on the folded matrix.

**r31 TRUTH-PROBE REFUTES the obligation as stated.**  `SmithFoldDescendsOnNonzeroPivot` quantifies over
ARBITRARY rectangular `work` (only `IsRectangular` + `0 < |diag pivot|` + `find = some`).  It is FALSE:
`smithClearingFoldStep`'s inner `smithCascadeSweep` clears only the pivot's CROSS (row-right + col-below)
and stops as soon as that cross is clean — it does NOT descend into the deeper `[pivot+1, ·)²` minor and
does NOT compute the sub-block gcd.  So on `work = [[2,0],[4,3]]` (pivot `0`, `find = some 1`) the fold
`row0 += row1` yields `afterFold = [[6,3],[4,3]]`, whose cascade brings the min-abs `3` to the pivot,
clears its cross to `[[3,0],[0,-2]]`, finds the cross clean, and STOPS — landing pivot magnitude `3`,
which is LARGER than the input pivot magnitude `2`.  The obligation's conclusion `|fold| < |work|`
(`3 < 2`) is false.  Machine-checked below (`smithFoldDescendsOnNonzeroPivotIsRefuted`), zero axioms.

**Why the r30 route cannot rescue it.**  The fold `addRowMultiple foundPos pivotIndex 1` sets
`afterFold.entryAt pivotIndex pivotIndex = work.entryAt pivotIndex pivotIndex + work.entryAt foundPos
pivotIndex`.  r30's never-raises + witness bounds the cascade output only against the AFTERFOLD pivot,
not the ORIGINAL `work` pivot.  These coincide iff the found-column entry `work.entryAt foundPos
pivotIndex` is `0` (`smithFoldAfterFoldPivotEqOfFoundColumnZero` below).  When it is NONZERO (the pivot
column below is dirty), the afterFold pivot differs and the r30 bound is against the wrong quantity, so
strict descent below the original pivot is a deeper (gcd-ideal) fact, not an r30 consequence.

**The driver itself crosses the boundary.**  The dirty-found-column shape is not a pathological
non-driver input: on the diagonal seed `diag(4,6,9,7)` the corrected driver's repair phase reaches, at
pivot `2`, the sweep-start matrix `[[1,0,0,0],[0,1,0,0],[0,0,-126,0],[0,0,-126,-12]]`, where
`find = some 3` AND the found-column entry `entry(3,2) = -126 ≠ 0`
(`smithDirtyFoundColumnIsFindSomeReachable`, decidable; provenance = the r31 read-only driver-walk eval).
So even a window-diagonal / found-column-zero SCOPING of the obligation would not be satisfied by the
driver's own fold inputs — the guarded-node-D invariant `smithClearingOutputFindNoneFromFoldDescent`
would need is FALSE at driver-reachable pivot-≥1 states.

**Consequence for the corrected-driver totality.**  `smithClearingOutputFindNoneFromFoldDescent` takes
`SmithFoldDescendsOnNonzeroPivot` as a hypothesis; that hypothesis is uninhabitable, so this wiring can
never discharge `K1` unconditionally.  `K1` is TRUE (the sweep does reach find-`none` on every fixture),
but its termination is NOT a per-fold `pivotMagnitudeWithin` descent — no simple per-fold measure works
(r22 machine-refuted `smithMinorAbsSum`, r26 found `minNonzeroAbsWithin` STALLS, r31 refutes
`pivotMagnitudeWithin`).  So `K1` (fuel-adequacy) is gcd-ideal-hard, on the same footing as the
off-diagonal half `K2`, NOT the "mechanical fuel-counting fact" the r27 framing suggested.
`SmithReduceCompleteDriverStatement` stays UNINHABITED hypothesis-free; the mandate is NOT reached.

Additive only: `smithReduceComplete`, its refutation, the r18–r30 world, and the (now-known-vacuous)
r27 wiring stay byte-intact.  Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/
`Quot.sound`/`Classical`/`omega`/`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithFoldDescentRefuted.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The counterexample -/

/-- The refuting matrix: `d0 = 2` does not divide the later diagonal `d1 = 3` (so `find = some 1`), and
the below-diagonal entry `(1,0) = 4` makes the fold's cascade land pivot magnitude `3 > 2`. -/
def smithFoldDescentCounterexample : IntMatrix := IntMatrix.mk [[2, 0], [4, 3]]

/-- The counterexample is a genuine `2 x 2` matrix (the obligation's first precondition). -/
theorem smithFoldDescentCounterexampleIsRectangular :
    smithFoldDescentCounterexample.IsRectangular 2 2 := ⟨rfl, rfl, rfl, trivial⟩

/-- The pivot is positive (`|d0| = 2 > 0`, the obligation's second precondition). -/
theorem smithFoldDescentCounterexamplePivotPositive :
    0 < (smithFoldDescentCounterexample.diagonalEntryAt 0).natAbs := by decide

set_option maxRecDepth 100000 in
/-- The find-scan reports `some 1` (`d0 = 2` does not divide `d1 = 3`, the obligation's third
precondition — so all three preconditions genuinely hold). -/
theorem smithFoldDescentCounterexampleFindsSome :
    smithFindNonDividingLaterDiagonal smithFoldDescentCounterexample 0 (Nat.min 2 2 - (0 + 1)) (0 + 1)
      = some 1 := by decide

set_option maxRecDepth 100000 in
/-- **The fold RAISES the pivot magnitude on the counterexample** — the fold+cascade lands pivot
magnitude `3`, strictly ABOVE the input pivot magnitude `2`, so the obligation's conclusion
`pivotMagnitudeWithin (fold) < pivotMagnitudeWithin work` is FALSE here.  The inner cascade clears only
the pivot cross (`[[6,3],[4,3]] -> [[3,0],[0,-2]]`, cross clean) and stops, leaving `-2` outside the
cross — it never computes the deeper gcd. -/
theorem smithFoldStepRaisesPivotOnCounterexample :
    ¬ (pivotMagnitudeWithin (smithClearingFoldStep smithFoldDescentCounterexample 1 0 2 2) 0
        < pivotMagnitudeWithin smithFoldDescentCounterexample 0) := by decide

/-- **THE HEADLINE — the r27/r28 obligation is FALSE.**  `SmithFoldDescendsOnNonzeroPivot` fails at
`work = smithFoldDescentCounterexample`, `foundPos = 1`, `pivotIndex = 0`, `height = width = 2`: all
three preconditions hold, yet the conclusion is refuted.  Machine-checked, zero axioms.  Hence
`smithClearingOutputFindNoneFromFoldDescent` (which consumes this obligation as a hypothesis) can never
discharge the fuel-adequacy keystone half `K1` unconditionally. -/
theorem smithFoldDescendsOnNonzeroPivotIsRefuted : ¬ SmithFoldDescendsOnNonzeroPivot := by
  intro foldDescends
  exact smithFoldStepRaisesPivotOnCounterexample
    (foldDescends smithFoldDescentCounterexample 1 0 2 2
      smithFoldDescentCounterexampleIsRectangular
      smithFoldDescentCounterexamplePivotPositive
      smithFoldDescentCounterexampleFindsSome)

/-! ## The boundary hinge — the fold preserves the pivot exactly when the found column is clean -/

/-- **The fold preserves the pivot iff the found-column entry is zero.**  `addRowMultiple foundPos
pivotIndex 1` reads the new on-target-row entry `old(pivotIndex, pivotIndex) + 1 * old(foundPos,
pivotIndex)`; when the found-column entry `old(foundPos, pivotIndex)` is `0` the afterFold pivot EQUALS
the input pivot.  This isolates the exact boundary: only here does r30's afterFold-pivot bound become a
bound on the ORIGINAL pivot.  Outside it (dirty pivot column) the obligation is refuted above. -/
theorem smithFoldAfterFoldPivotEqOfFoundColumnZero {height width : Nat} (work : IntMatrix)
    (isRect : work.IsRectangular height width) (foundPos pivotIndex : Nat)
    (foundNePivot : foundPos ≠ pivotIndex)
    (foundInRange : foundPos < height) (pivotRowInRange : pivotIndex < height)
    (pivotColInRange : pivotIndex < width)
    (foundColumnZero : work.entryAt foundPos pivotIndex = 0) :
    (work.applyOperations
        [ ElementaryOperation.rowOperation
            (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]).diagonalEntryAt pivotIndex
      = work.diagonalEntryAt pivotIndex :=
  (addRowMultipleEntryOnTargetRow work isRect foundPos pivotIndex pivotIndex 1 foundNePivot
      foundInRange pivotRowInRange pivotColInRange).trans
    ((congrArg (fun foundColumnEntry => work.entryAt pivotIndex pivotIndex + 1 * foundColumnEntry)
        foundColumnZero).trans
      ((congrArg (work.entryAt pivotIndex pivotIndex + ·) (intOneMul 0)).trans
        (intAddZero (work.entryAt pivotIndex pivotIndex))))

/-! ## The driver crosses the boundary -/

/-- The pivot-`2` sweep-start matrix the corrected driver reaches on the seed `diag(4,6,9,7)` (recovered
by the r31 read-only driver walk of `smithReduceComplete`'s repair phase). -/
def smithDirtyFoundColumnDriverWitness : IntMatrix :=
  IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -126, 0], [0, 0, -126, -12]]

/-- **A driver-reachable `find = some` state with a NONZERO found-column entry.**  At pivot `2` the scan
reports `some 3` (`-126` does not divide `-12`) while the found-column entry `entry(3, 2) = -126 ≠ 0`.
So the fold's pivot column is dirty exactly where a fold fires — a found-column-zero (or window-diagonal)
scoping of the obligation is NOT satisfied by the driver's own fold inputs, and cannot re-close `K1`. -/
theorem smithDirtyFoundColumnIsFindSomeReachable :
    smithFindNonDividingLaterDiagonal smithDirtyFoundColumnDriverWitness 2
        (Nat.min 4 4 - (2 + 1)) (2 + 1) = some 3
    ∧ smithDirtyFoundColumnDriverWitness.entryAt 3 2 ≠ 0 := by decide

end FX1Poly.ComputerAlgebra

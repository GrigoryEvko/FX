import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedRestriction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachablePrefixConfinement — the confinement
    invariant of the reachable trajectory, proven by trajectory induction (H2-SMITH r36)

## The move

r35 (`SmithReachableImageSeedRestriction`) re-parameterized the corrected driver off the RESTRICTED seed
`SmithCascadeLandsDivisibleSubBlockReachable`, quantified over the trajectory predicate
`ReachableFromPhaseA`, and excluded the r33 refuter.  Its honesty banner named the residual's structural
half `reachablePivotCrossClearInteriorConfined` (reachable states have a clean pivot cross, off-diagonal
content confined to a sub-block) and called it "a standalone multi-round arc, NOT r35-sized".

This module discharges that structural half.  It is NOT a multi-round arc: the confinement invariant is
the SHIPPED predicate `SmithPrefixSettled` (`SmithCascadeTermination`, the `[pivotIndex, ·)²` sub-block
form), and its base + per-op-class single step are already proven UNCONDITIONALLY
(`smithPrefixSettledZero`, `smithRepairClearingStepSettlesHolds`).  The reachable induction closes it with
one trajectory-induction wrapper.

## Off-by-one correction (machine-refuted)

The r35 footer wrote the confinement block as the strict `[p+1, ·)²` sub-block.  That is off-by-one under
the natural convention (`p` = the state's reachability/pivot index).  A `#eval` truth-probe over the
GENUINE reachable trajectories `diag(100,75,30,14)` and `diag(4,6,9,7)` shows, at index `2`, a legitimate
pivot-column fill-in at `(3, 2)` (= `(pivotIndex+1, pivotIndex)`, equal in value to the current pivot,
cleared by the NEXT sweep).  So the state is settled at `[2, ·)²` (`SmithPrefixSettled ... 2`) but NOT at
`[3, ·)²` (`SmithPrefixSettled ... 3` FALSE — the `(3,2)` residue violates it).  The current pivot's own
cross is NOT clean; only the PROCESSED prefix `< pivotIndex` is.  The exact, machine-checked confinement
form is therefore `SmithPrefixSettled matrix pivotIndex height width`, NOT the `[p+1, ·)²` prose.

## What this module ships (positive, additive, zero-axiom)

  * **`reachableImpliesRectangular`** — every state reachable from a rectangular input stays rectangular.
    Trajectory induction: base transports `input.IsRectangular` through the Phase-A word; step transports
    the IH through the repair word (`applyOperationsPreservesRectangular` at both).

  * **`reachableImpliesPrefixSettled`** — THE confinement invariant: every reachable state at an in-window
    pivot `pivotIndex` (`pivotIndex ≤ height`, `pivotIndex ≤ width`) is `SmithPrefixSettled` there — the
    processed prefix `< pivotIndex` carries no off-diagonal content.  Trajectory induction: base is the
    vacuous `smithPrefixSettledZero`; step is the UNCONDITIONAL, per-op-class-assembled
    `smithRepairClearingStepSettlesHolds` (fed the derived rectangularity and the IH), whose range side
    conditions `pivotIndex < height/width` come free from the successor range hypotheses.  NO seed.

  * **`reachableAtMinIsWindowDiagonal`** — the seed-free terminal corollary: a state reachable at the
    terminal index `Nat.min height width` is FULLY window-diagonal (`IsWindowDiagonal ... 0`).  The
    off-diagonal-clearing half of Smith completeness holds on the reachable image with ZERO hypotheses
    beyond reachability — the seed is needed ONLY for the divisibility chain, never for diagonality.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the
mandate does NOT fire.  The EXACT remaining hypothesis is the restricted seed

    SmithCascadeLandsDivisibleSubBlockReachable

whose OPEN content is the DIVISIBILITY half, NOT the confinement half discharged here.  Per the H2-SMITH
r36 descent reconnaissance, the seed factors as

    SmithCascadeLandsDivisibleSubBlockReachable
      ⟸ reachableImpliesPrefixSettled           -- SHIPPED here (the confinement invariant)
      + K1_reachable  (the diagonal half: find-none ⟹ pivot divides every later diagonal)
      + K2_reachable  (the off-diagonal half: pivot divides every later off-diagonal combination)

Both K1 and K2 rest on ONE genuinely-open fact — that min-abs Euclid on a `SmithPrefixSettled` block LANDS
the block gcd generator at the pivot (the classical `improve_pivot_rec_spec` / `f ∣ every entry of H`
invariant of CoqEAL / Isabelle-AFP / jreaso).  This is gcd-IDEAL-INVARIANCE, NOT a per-fold Nat measure:
the per-fold `|pivot|` descent is REFUTED (`smithFoldDescendsOnNonzeroPivotIsRefuted`), and the min-abs /
minor-abs-sum measures are dead (r22/r26/r31).  So K1 and K2 collapse into a single gcd-ideal wall that is
a ≥2-round arc, NOT round-sized.  It is honestly walled here; no descent measure is fabricated, no flip
is invented.  The r18–r35 world and `smithReduceComplete` stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (trajectory induction on the reachability witness — no
`WellFounded.fix`).  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachablePrefixConfinement.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Rectangularity is preserved along the whole trajectory -/

/-- **Every reachable state is rectangular.**  Trajectory induction on the reachability witness: the `base`
constructor's matrix is the Phase-A word applied to the rectangular input
(`applyOperationsPreservesRectangular`); the `step` constructor transports the IH rectangularity through the
repair word.  No range hypothesis needed. -/
theorem reachableImpliesRectangular (height width : Nat) :
    ∀ (matrix : IntMatrix) (pivotIndex : Nat),
      ReachableFromPhaseA height width matrix pivotIndex →
      matrix.IsRectangular height width := by
  intro matrix pivotIndex reached
  induction reached with
  | base input isRect =>
      exact applyOperationsPreservesRectangular
        (smithReduceTotal input height width).operations input isRect
  | step innerMatrix innerPivot _reachedInner ih =>
      exact applyOperationsPreservesRectangular
        (smithRepairPositionSweepClearing (smithMinorAbsSum innerMatrix innerPivot height width)
          innerMatrix innerPivot height width)
        innerMatrix ih

/-! ## The confinement invariant — the reachable trajectory keeps the processed prefix settled -/

/-- **THE CONFINEMENT INVARIANT.**  Every state reachable from the Phase-A output at an in-window pivot
`pivotIndex` (`pivotIndex ≤ height`, `pivotIndex ≤ width`) is `SmithPrefixSettled` at `pivotIndex` — no
off-diagonal cell whose row OR column is `< pivotIndex` is nonzero (the processed prefix is clean; the
current pivot cross and the trailing sub-block are unconstrained).  Trajectory induction on the reachability
witness: the `base` state at pivot `0` is vacuously settled (`smithPrefixSettledZero`); the `step` state at
pivot `innerPivot + 1` is settled by the UNCONDITIONAL per-op-class single-step
`smithRepairClearingStepSettlesHolds`, whose range side conditions `innerPivot < height/width` are exactly
the successor range hypotheses `innerPivot + 1 ≤ height/width`, and whose rectangularity input is
`reachableImpliesRectangular` on the inner witness.  NO seed hypothesis. -/
theorem reachableImpliesPrefixSettled (height width : Nat) :
    ∀ (matrix : IntMatrix) (pivotIndex : Nat),
      ReachableFromPhaseA height width matrix pivotIndex →
      pivotIndex ≤ height → pivotIndex ≤ width →
      SmithPrefixSettled matrix pivotIndex height width := by
  intro matrix pivotIndex reached
  induction reached with
  | base input isRect =>
      intro _pivotRowLe _pivotColLe
      exact smithPrefixSettledZero
        (input.applyOperations (smithReduceTotal input height width).operations) height width
  | step innerMatrix innerPivot reachedInner ih =>
      intro succRowLe succColLe
      have pivotRowLt : innerPivot < height := succRowLe
      have pivotColLt : innerPivot < width := succColLe
      have innerSettled : SmithPrefixSettled innerMatrix innerPivot height width :=
        ih (Nat.le_of_lt pivotRowLt) (Nat.le_of_lt pivotColLt)
      have innerRect : innerMatrix.IsRectangular height width :=
        reachableImpliesRectangular height width innerMatrix innerPivot reachedInner
      exact smithRepairClearingStepSettlesHolds innerMatrix innerPivot height width
        innerRect pivotRowLt pivotColLt innerSettled

/-! ## Seed-free terminal corollary — reachable at `Nat.min` ⟹ fully window-diagonal -/

/-- **The off-diagonal-clearing half of Smith completeness, seed-free.**  A state reachable at the terminal
index `Nat.min height width` is fully window-diagonal (`IsWindowDiagonal ... 0`): the confinement invariant
at `pivotIndex = Nat.min height width` (in range by `natMinLeLeft`/`natMinLeRight`) IS the full window
diagonal (`smithPrefixSettledAtMinIsWindowDiagonal`).  This needs NO seed — only the divisibility chain
does.  It cleanly isolates what IS proven (diagonality) from what remains open (the gcd chain). -/
theorem reachableAtMinIsWindowDiagonal (height width : Nat) (matrix : IntMatrix)
    (reached : ReachableFromPhaseA height width matrix (Nat.min height width)) :
    IsWindowDiagonal matrix 0 height width :=
  fun rowIndex colIndex _zeroLeRow rowLtHeight _zeroLeCol colLtWidth rowNeCol =>
    smithPrefixSettledAtMinIsWindowDiagonal matrix height width
      (reachableImpliesPrefixSettled height width matrix (Nat.min height width) reached
        (natMinLeLeft height width) (natMinLeRight height width))
      rowIndex colIndex rowLtHeight colLtWidth rowNeCol

/-! ## The H2-SMITH r36 ledger — the confinement half discharged; the gcd descent honestly walled

**What r36 ships (zero-axiom, additive; the r18–r35 world byte-intact).**  The three trajectory results
above: `reachableImpliesRectangular` (reachable ⟹ rectangular), `reachableImpliesPrefixSettled` (THE
confinement invariant — the reachable trajectory keeps the processed prefix `< pivotIndex` settled, the
CORRECTED `[pivotIndex, ·)²` form, machine-truth-probed per-step before proving), and
`reachableAtMinIsWindowDiagonal` (the seed-free terminal corollary — reachable at `Nat.min` ⟹ fully
window-diagonal).  The r35 claim that `reachablePivotCrossClearInteriorConfined` is "a standalone
multi-round arc" is RETIRED — it is one trajectory-induction wrapper over the shipped
`smithRepairClearingStepSettlesHolds`.  The `[p+1, ·)²` prose is corrected to `[p, ·)²` (off-by-one,
machine-refuted via the `(pivotIndex+1, pivotIndex)` pivot-column fill-in).

**What r36 does NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`.  `smithReduceCompleteDriverOfSubBlockSeedReachable` still consumes the
RESTRICTED seed `SmithCascadeLandsDivisibleSubBlockReachable`, the EXACT remaining hypothesis.  With the
confinement half now discharged, the seed's ONLY open content is the DIVISIBILITY half: that min-abs Euclid
on a `SmithPrefixSettled` block lands the block gcd generator at the pivot (K1 diagonal + K2 off-diagonal,
both fed by the SAME gcd-ideal-invariance fact).  The per-fold `|pivot|` measure is REFUTED
(`smithFoldDescendsOnNonzeroPivotIsRefuted`); no per-fold Nat measure works (r22/r26/r31).  That is a
≥2-round gcd-ideal arc, NOT round-sized — honestly walled.  No descent measure is fabricated; no flip is
invented. -/

end FX1Poly.ComputerAlgebra

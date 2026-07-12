import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeEquivalence
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithClearingHalvesFromKeystone

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeRefuted — the general per-phase keystone
    is FALSE as stated, and the corrected-driver seed with it (H2-SMITH r33, #2261)

## The decision, brutally

r32 framed the single surviving corrected-driver residual — the per-phase keystone
`SmithCascadeLandedPivotDividesMinor`, equivalently the magnitude identity
`MinAbsEuclidLandsMinorGcdMagnitude` (`|landed| = gcd(minor)`) — as an OPEN wall "TRUE where it is
hardest to see", and pinned it TRUE on hostile DIAGONAL seeds.  A truth-probe on a NON-diagonal seed
REFUTES it.  On

    `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]`   (pivot 0)

the min-abs clearing cascade brings the min-abs `6` (at column 1) to the pivot by a column swap, finds
the pivot-0 CROSS already clean, and STOPS — landing `d_0 = 6`.  But the pivot minor `{6, 10}` has
`gcd = 2`, and `6 ∤ 10`.  So `|landed| = 6 ≠ 2 = gcd(minor)`, and the landed pivot does NOT divide the
whole minor.  The `10` at `(1, 2)` sits off the pivot cross, in the `[1, ·)²` interior the cross-clear
terminator never inspects.

This refutes ALL THREE forms of the wall, machine-checked below (zero axioms, at or below the 4x4 defeq
ceiling — the counterexample is 3x3):

  * `minAbsEuclidLandsMinorGcdMagnitudeIsRefuted` — `¬ MinAbsEuclidLandsMinorGcdMagnitude` (the crisp
    magnitude identity r32 sharpened the wall to).
  * `smithCascadeLandedPivotDividesMinorIsRefuted` — `¬ SmithCascadeLandedPivotDividesMinor` (the r22
    keystone), via the shipped `keystoneIffLandedMagnitudeEqMinorGcd`.
  * `smithCascadeLandsDivisibleSubBlockIsRefuted` — `¬ SmithCascadeLandsDivisibleSubBlock`, the SOLE
    hypothesis of the shipped seed-conditional driver totality `smithReduceCompleteDriverOfSubBlockSeed`
    (`SmithWindowedChainReduction`).  This is the load-bearing refutation: the whole shipped route from
    the corrected driver to `SmithReduceCompleteDriverStatement` runs through this one seed, and the
    seed is uninhabitable.  So the mandate route is DEAD AS STATED — `smithReduceComplete` may still be
    correct, but this particular seed cannot witness it.

`smithReduceComplete`, its refutation, and the entire r18–r32 world stay byte-intact (additive only).

## What actually survives OPEN — the RESTRICTED (in-driver-image) form

The refuting seeds are all OUT-OF-IMAGE: they are not matrices the corrected driver's repair phase
actually feeds the keystone.  The driver feeds the repair sweep the Phase-A output, which is provably
window-diagonal at floor 0 (`phaseAOutputIsWindowDiagonalAtZero`,
`SmithDiagonalInputSpecialization`), and then the repair trajectory `M_0 · sweep_0 · sweep_1 · …`.  On
DIAGONAL inputs the same cascade DOES land the gcd — witnessed here by
`landedMagnitudeEqMinorGcdOnDiagonalWindowContrast` and by the r32 diagonal battery
(`landedMagnitudeEqMinorGcdOnKillerSeed*`, `...OnCoprimeSeed`, `...OnFillInSeedPivotOne`,
`SmithLandedMagnitudeEquivalence`).  So the honest OPEN content is NOT the general `∀`-keystone (refuted
here) but the RESTRICTED keystone over the driver's own repair-trajectory image — a genuine
re-architecture, NOT a one-round scoping.  Two obstacles, both already machine-established:

  * The restriction cannot be `IsWindowDiagonal`: the diagonal restriction was already machine-refuted
    for the chain by `smithDiagonalInputPivotOneInputNotWindowDiagonal` (`diag(15,10,6,4)·sweep_0`
    carries `-20` off-diagonal at floor 1) — the repair sweep's own pivot-≥1 intermediates are not
    window-diagonal, and diagonality is never re-established mid-sweep.
  * The restriction cannot be "cross-clear": the counterexamples here (cross-clear
    `[[6,0,0],[0,0,10],[0,0,0]]`, anti-diagonal `[[2,0,0],[0,0,3],[0,3,0]]`) are all cross-0-clear yet
    still refute — the cross-clear terminator ignores the interior.

The true restriction is the inductively-generated reachable set, threaded as the NODE-A induction
invariant — a standalone multi-round arc that still bottoms out on the unshipped lex-refined
`minNonzeroAbsWithin` descent (r22 `smithMinorAbsSum` RISES on folds, r26 `minNonzeroAbsWithin` STALLS,
r31 `pivotMagnitudeWithin` RISES).  NOT r33-sized; NOT flipped.  `SmithReduceCompleteDriverStatement`
stays UNINHABITED hypothesis-free.

## Robustness battery

The refutation is not a single-seed fluke: the magnitude mismatch is reproduced on a cross-clear seed, a
negative-entry seed, a non-square (2x3) seed, and an anti-diagonal seed below — every hostile shape the
mandate criteria name.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeRefuted.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The counterexample seed — a non-diagonal 3x3 where the cascade overshoots the minor gcd -/

/-- The refuting seed: the min-abs `6` sits at `(0, 1)`, the off-cross `10` at `(1, 2)`.  The cascade
swaps `6` to the pivot, finds the pivot-0 cross clean, and stops at `d_0 = 6`; but `gcd(6, 10) = 2` and
`6 ∤ 10`, so the landed pivot neither has magnitude `gcd(minor)` nor divides the whole minor.  A genuine
`3x3` matrix (within the 4x4 defeq ceiling), with a trailing zero row. -/
def landedExceedsMinorGcdSeed : IntMatrix := { rows := [[0, 6, 0], [0, 0, 10], [0, 0, 0]] }

/-- The counterexample is a genuine `3 x 3` matrix (the keystone's rectangularity precondition).  A
structural `∧`-witness, not `decide` — `IsRectangular` is a plain `Prop`, not `Decidable`. -/
theorem landedExceedsMinorGcdSeedIsRectangular :
    landedExceedsMinorGcdSeed.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

set_option maxRecDepth 16000 in
/-- **The landed magnitude misses the minor gcd on the seed** — `|landed| = 6 ≠ 2 = gcd(minor)`.  The
`MinAbsEuclidLandsMinorGcdMagnitude` `∀`-body, kernel-refuted at the seed by `decide`. -/
theorem landedMagnitudeNeMinorGcdOnSeed :
    ((landedExceedsMinorGcdSeed.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum landedExceedsMinorGcdSeed 0 3 3)
          landedExceedsMinorGcdSeed 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin landedExceedsMinorGcdSeed 0 3 3).natAbs := by decide

/-- **THE MAGNITUDE IDENTITY IS FALSE.**  `MinAbsEuclidLandsMinorGcdMagnitude` fails at the seed, pivot
`0`, `height = width = 3`: rectangularity and both in-range preconditions hold, yet the magnitude body
is refuted.  So the crispest form of the r32 wall is uninhabitable. -/
theorem minAbsEuclidLandsMinorGcdMagnitudeIsRefuted : ¬ MinAbsEuclidLandsMinorGcdMagnitude := by
  intro magnitudeIdentity
  exact landedMagnitudeNeMinorGcdOnSeed
    (magnitudeIdentity landedExceedsMinorGcdSeed 0 3 3 landedExceedsMinorGcdSeedIsRectangular
      (by decide) (by decide))

/-- **THE r22 KEYSTONE IS FALSE.**  `SmithCascadeLandedPivotDividesMinor` is equivalent to the magnitude
identity (`keystoneIffLandedMagnitudeEqMinorGcd`, shipped); the identity is refuted above, so the
keystone is too. -/
theorem smithCascadeLandedPivotDividesMinorIsRefuted : ¬ SmithCascadeLandedPivotDividesMinor := by
  intro keystone
  exact minAbsEuclidLandsMinorGcdMagnitudeIsRefuted
    (keystoneIffLandedMagnitudeEqMinorGcd.mp keystone)

set_option maxRecDepth 16000 in
/-- **THE DRIVER'S SOLE HYPOTHESIS IS FALSE — the load-bearing refutation.**
`SmithCascadeLandsDivisibleSubBlock` is the one hypothesis the shipped
`smithReduceCompleteDriverOfSubBlockSeed` consumes to inhabit `SmithReduceCompleteDriverStatement`.  At
the seed, pivot `0`, the seed would force the landed pivot to divide the swept `[1, ·)²` sub-block, in
particular the swept entry `(1, 2) = 10`.  But `smithPivotDividesEntry (landed) 10 = false`, and by the
shipped encode bridge `smithPivotDividesEntryEncode` any genuine `dividesExactly (landed) 10` would make
that test `true` — contradiction.  So the mandate route through this seed is DEAD AS STATED. -/
theorem smithCascadeLandsDivisibleSubBlockIsRefuted : ¬ SmithCascadeLandsDivisibleSubBlock := by
  intro seed
  have landedDividesSweptEntry :=
    matrixEntriesDivisibleByWithinAt
      (seed landedExceedsMinorGcdSeed 0 3 3 landedExceedsMinorGcdSeedIsRectangular
        (by decide) (by decide)) 1 2 (by decide) (by decide)
  exact absurd (smithPivotDividesEntryEncode _ _ landedDividesSweptEntry) (by decide)

/-! ## Robustness battery — the mismatch reproduces on every hostile shape -/

set_option maxRecDepth 16000 in
/-- **Cross-clear seed** — `[[6, 0, 0], [0, 0, 10], [0, 0, 0]]` is already pivot-0-cross-clean, yet the
cascade lands `6` while `gcd(6, 10) = 2`.  The cross-clear terminator ignores the off-cross interior, so
a "cross-clear" scoping of the keystone would not rescue it. -/
theorem landedMagnitudeNeMinorGcdOnCrossClearSeed :
    ((({ rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)
          { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- **Negative-entry seed** — `[[0, -6, 0], [0, 0, 10], [0, 0, 0]]` lands magnitude `6` against
`gcd = 2`; the refutation survives sign. -/
theorem landedMagnitudeNeMinorGcdOnNegativeSeed :
    ((({ rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)
          { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- **Non-square seed** — the `2 x 3` matrix `[[0, 6, 0], [0, 0, 10]]` lands magnitude `6` against
`gcd = 2`; the refutation is not an artifact of squareness. -/
theorem landedMagnitudeNeMinorGcdOnNonSquareSeed :
    ((({ rows := [[0, 6, 0], [0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3)
          { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- **Anti-diagonal seed** — `[[2, 0, 0], [0, 0, 3], [0, 3, 0]]` is cross-0-clean with an off-cross
anti-diagonal `3`; the cascade lands `2` against `gcd(2, 3, 3) = 1`.  Off-cross anti-diagonal structure
breaks the keystone exactly as the trailing-zero seed does. -/
theorem landedMagnitudeNeMinorGcdOnAntiDiagonalSeed :
    ((({ rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3)
          { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3).natAbs := by decide

/-! ## The restricted form HOLDS — the surviving open content is TRUE on diagonal inputs -/

set_option maxRecDepth 16000 in
/-- **On a diagonal window the same cascade LANDS the gcd** — on `diag(6, 10)` the pivot-`0` cascade
lands `|landed| = 2 = gcd(6, 10)`.  The contrast with the seeds above localises the failure: it is the
NON-diagonal (off-cross) interior, not the cascade, that breaks the general keystone.  The RESTRICTED
(in-driver-image / diagonal) keystone is the honest surviving OPEN content — see the r32 diagonal
battery in `SmithLandedMagnitudeEquivalence`. -/
theorem landedMagnitudeEqMinorGcdOnDiagonalWindowContrast :
    ((({ rows := [[6, 0], [0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0], [0, 10]] } 0 2 2)
          { rows := [[6, 0], [0, 10]] } 0 2 2)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin { rows := [[6, 0], [0, 10]] } 0 2 2).natAbs := by decide

end FX1Poly.ComputerAlgebra

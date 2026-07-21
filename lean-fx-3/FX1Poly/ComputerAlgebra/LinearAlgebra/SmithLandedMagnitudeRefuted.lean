import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeEquivalence
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithClearingHalvesFromKeystone

/-! # SmithLandedMagnitudeRefuted — the general per-phase keystone is false as stated

The per-phase keystone `SmithCascadeLandedPivotDividesMinor` — equivalently the magnitude identity
`MinAbsEuclidLandsMinorGcdMagnitude` (`|landed| = gcd(minor)`) — is refuted on the non-diagonal seed
`[[0,6,0],[0,0,10],[0,0,0]]` at pivot 0: the min-abs cascade swaps the min-abs `6` to the pivot, finds
the pivot-0 cross already clean, and stops at `d_0 = 6`, whereas `gcd(6,10) = 2` and `6 ∤ 10`.  The `10`
at `(1,2)` lies off the pivot cross, in the `[1, ·)²` interior the cross-clear terminator never inspects.

Three forms of the wall fall, machine-checked below (counterexample is 3x3, at or below the 4x4 defeq
ceiling): the magnitude identity (`minAbsEuclidLandsMinorGcdMagnitudeIsRefuted`); the keystone itself
(`smithCascadeLandedPivotDividesMinorIsRefuted`, via `keystoneIffLandedMagnitudeEqMinorGcd`); and the
driver's sole hypothesis `SmithCascadeLandsDivisibleSubBlock`
(`smithCascadeLandsDivisibleSubBlockIsRefuted`).  The last is load-bearing: the shipped seed-conditional
route `smithReduceCompleteDriverOfSubBlockSeed` runs through that one seed, which is uninhabitable, so the
route is dead as stated (`smithReduceComplete` may still be correct — this seed cannot witness it).

What survives open is the restricted, in-driver-image keystone: on diagonal inputs the same cascade does
land the gcd (`landedMagnitudeEqMinorGcdOnDiagonalWindowContrast`, plus the diagonal battery in
`SmithLandedMagnitudeEquivalence`).  The restriction cannot be `IsWindowDiagonal` (already refuted for the
chain by `smithDiagonalInputPivotOneInputNotWindowDiagonal`) nor "cross-clear" (the counterexamples here
are all cross-0-clear yet still refute).  The true restriction is the reachable set, a standalone
multi-round arc bottoming out on the unshipped descent (`smithMinorAbsSum` rises, `minNonzeroAbsWithin`
stalls, `pivotMagnitudeWithin` rises); `SmithReduceCompleteDriverStatement` stays uninhabited
hypothesis-free.  The robustness battery reproduces the mismatch on cross-clear, negative-entry,
non-square, and anti-diagonal seeds.

Raw Lean 4 + `Init`, structural only; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `omega`,
`native_decide`.  Gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The counterexample seed -/

/-- The refuting seed: min-abs `6` at `(0,1)`, off-cross `10` at `(1,2)`.  The cascade swaps `6` to the
pivot, finds the pivot-0 cross clean, and stops at `d_0 = 6`, but `gcd(6,10) = 2` and `6 ∤ 10`, so the
landed pivot neither has magnitude `gcd(minor)` nor divides the whole minor. -/
def landedExceedsMinorGcdSeed : IntMatrix := { rows := [[0, 6, 0], [0, 0, 10], [0, 0, 0]] }

/-- The counterexample is a genuine `3 x 3` matrix.  A structural witness, not `decide` — `IsRectangular`
is a plain `Prop`. -/
theorem landedExceedsMinorGcdSeedIsRectangular :
    landedExceedsMinorGcdSeed.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

set_option maxRecDepth 16000 in
/-- The landed magnitude misses the minor gcd on the seed: `|landed| = 6 ≠ 2 = gcd(minor)`, the
`MinAbsEuclidLandsMinorGcdMagnitude` body kernel-refuted by `decide`. -/
theorem landedMagnitudeNeMinorGcdOnSeed :
    ((landedExceedsMinorGcdSeed.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum landedExceedsMinorGcdSeed 0 3 3)
          landedExceedsMinorGcdSeed 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin landedExceedsMinorGcdSeed 0 3 3).natAbs := by decide

/-- The magnitude identity is false: `MinAbsEuclidLandsMinorGcdMagnitude` fails at the seed, pivot `0`,
`height = width = 3` — rectangularity and both in-range preconditions hold, yet the body is refuted. -/
theorem minAbsEuclidLandsMinorGcdMagnitudeIsRefuted : ¬ MinAbsEuclidLandsMinorGcdMagnitude := by
  intro magnitudeIdentity
  exact landedMagnitudeNeMinorGcdOnSeed
    (magnitudeIdentity landedExceedsMinorGcdSeed 0 3 3 landedExceedsMinorGcdSeedIsRectangular
      (by decide) (by decide))

/-- The keystone is false: `SmithCascadeLandedPivotDividesMinor` is equivalent to the magnitude identity
(`keystoneIffLandedMagnitudeEqMinorGcd`), which is refuted above. -/
theorem smithCascadeLandedPivotDividesMinorIsRefuted : ¬ SmithCascadeLandedPivotDividesMinor := by
  intro keystone
  exact minAbsEuclidLandsMinorGcdMagnitudeIsRefuted
    (keystoneIffLandedMagnitudeEqMinorGcd.mp keystone)

set_option maxRecDepth 16000 in
/-- The driver's sole hypothesis is false — the load-bearing refutation.
`SmithCascadeLandsDivisibleSubBlock` is the one hypothesis `smithReduceCompleteDriverOfSubBlockSeed`
consumes to inhabit `SmithReduceCompleteDriverStatement`.  At the seed, pivot `0`, it would force the
landed pivot to divide the swept entry `(1,2) = 10`; but `smithPivotDividesEntry (landed) 10 = false`, and
by `smithPivotDividesEntryEncode` any genuine `dividesExactly (landed) 10` would make that test `true`. -/
theorem smithCascadeLandsDivisibleSubBlockIsRefuted : ¬ SmithCascadeLandsDivisibleSubBlock := by
  intro seed
  have landedDividesSweptEntry :=
    matrixEntriesDivisibleByWithinAt
      (seed landedExceedsMinorGcdSeed 0 3 3 landedExceedsMinorGcdSeedIsRectangular
        (by decide) (by decide)) 1 2 (by decide) (by decide)
  exact absurd (smithPivotDividesEntryEncode _ _ landedDividesSweptEntry) (by decide)

/-! ## Robustness battery -/

set_option maxRecDepth 16000 in
/-- Cross-clear seed `[[6,0,0],[0,0,10],[0,0,0]]` is already pivot-0-cross-clean, yet the cascade lands
`6` while `gcd(6,10) = 2` — a "cross-clear" scoping would not rescue the keystone. -/
theorem landedMagnitudeNeMinorGcdOnCrossClearSeed :
    ((({ rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)
          { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- Negative-entry seed `[[0,-6,0],[0,0,10],[0,0,0]]` lands magnitude `6` against `gcd = 2`; the
refutation survives sign. -/
theorem landedMagnitudeNeMinorGcdOnNegativeSeed :
    ((({ rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)
          { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[0, -6, 0], [0, 0, 10], [0, 0, 0]] } 0 3 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- Non-square seed: the `2 x 3` matrix `[[0,6,0],[0,0,10]]` lands magnitude `6` against `gcd = 2`; the
refutation is not an artifact of squareness. -/
theorem landedMagnitudeNeMinorGcdOnNonSquareSeed :
    ((({ rows := [[0, 6, 0], [0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3)
          { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[0, 6, 0], [0, 0, 10]] } 0 2 3).natAbs := by decide

set_option maxRecDepth 16000 in
/-- Anti-diagonal seed `[[2,0,0],[0,0,3],[0,3,0]]` is cross-0-clean with an off-cross anti-diagonal `3`;
the cascade lands `2` against `gcd(2,3,3) = 1`, breaking the keystone as the trailing-zero seed does. -/
theorem landedMagnitudeNeMinorGcdOnAntiDiagonalSeed :
    ((({ rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3)
          { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3)).diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] } 0 3 3).natAbs := by decide

/-! ## The restricted form holds on diagonal inputs -/

set_option maxRecDepth 16000 in
/-- On the diagonal window `diag(6,10)` the pivot-`0` cascade lands `|landed| = 2 = gcd(6,10)`.  The
contrast with the seeds above localises the failure to the non-diagonal interior, not the cascade: the
restricted (in-driver-image / diagonal) keystone is the surviving open content, see the diagonal battery
in `SmithLandedMagnitudeEquivalence`. -/
theorem landedMagnitudeEqMinorGcdOnDiagonalWindowContrast :
    ((({ rows := [[6, 0], [0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0], [0, 10]] } 0 2 2)
          { rows := [[6, 0], [0, 10]] } 0 2 2)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin { rows := [[6, 0], [0, 10]] } 0 2 2).natAbs := by decide

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedDivisibility

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithWindowGcdInvariance — the gcd-ideal CONVERSE:
    every common divisor of the input minor divides the landed pivot (H2-SMITH r25, #2261)

The corrected keystone `SmithCascadeLandedPivotDividesMinor`
(`SmithWindowedChainReduction.lean`) is the ONE open Prop the corrected-driver totality rests on:
*the landed pivot `g := M'.diagonalEntryAt p` divides every entry of the input `[p, ·) × [p, ·)`
minor* — i.e. `g` is a COMMON DIVISOR of the whole minor (its magnitude is the minor gcd).

This module ships the **CONVERSE half** of that gcd-ideal statement, which is a pure composition of
the SHIPPED forward tower:

  * `commonDivisorOfInputMinorDividesLandedPivot` — for ANY `divisor` that divides every entry of the
    input `[pivotIndex, ·) × [pivotIndex, ·)` minor, `divisor` divides the LANDED pivot
    `(M.applyOperations (repair sweep)).diagonalEntryAt pivotIndex`.  Read off the confined forward
    tower (`applyOperationsPreservesEntriesDivisibleWithin` +
    `smithRepairPositionSweepClearingBoundedBelow` at floor `lo := pivotIndex`) at the on-diagonal
    slot `(p, p)` (`matrixEntriesDivisibleByWithinAt`; `diagonalEntryAt p = entryAt p p` is defeq).

**HONEST SIZING — this is the CONVERSE and does NOT flip the driver.**  It proves
`gcd(input minor) ∣ g` ("`g` lies in the minor's gcd-ideal"); the keystone needs the OPPOSITE,
`g ∣ every input minor entry` ("`g` is ITSELF a common divisor").  Together they force
`|g| = gcd(minor)`, but `g ∣ gcd` ⟺ the keystone (circular).  The genuinely-missing content — that
the min-abs Euclid descent LANDS a common divisor / `g` is minimal — is untouched by any
gcd-invariance argument.  The surviving wall is named at the foot of this file.

Truth-probed BEFORE proving by `decide`/kernel reduction (all instances at or below the 3x3/4x4 defeq
ceiling):
  * the exit scan on the coprime `diag(15,10,6,4)` window does NOT exit (`15 ∤ 10`), and on a dividing
    `diag(2,4,8)` window it DOES exit (`none`);
  * the scalar gcd-invariance holds on a concrete Euclid rotation (`gcd(6,10) = gcd(6, 10 + 6·(-1))`);
  * the common divisor `2` divides the landed pivot on the non-coprime `diag(6,10,8)` window AND on a
    hostile all-even NON-diagonal seed;
  * the coprime `diag(15,10,6,4)` sweep leaves a nonzero interior off-diagonal cell `(3,1) = -20` (the
    residual the keystone's minimality wall — not this converse — must clear).

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowGcdInvariance.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Truth-probes (kernel-checked concrete instances, established BEFORE the general brick) -/

/-- **Exit scan does NOT exit on a coprime diagonal window** — on `diag(15,10,6,4)` the pivot-`0`
find-loop hits `15 ∤ 10` immediately and returns `some 1` (the non-dividing later diagonal), so the
per-pivot recursion does NOT reach its `none` terminal.  The hostile witness the exit-scan inversion
`smithFindNonDividingLaterDiagonalNoneDividesAll` (shipped r18) is vacuous on. -/
theorem smithExitScanDoesNotExitOnCoprimeDiagonalWindow :
    smithFindNonDividingLaterDiagonal
      { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0
      (Nat.min 4 4 - (0 + 1)) (0 + 1) = some 1 := by
  decide

/-- **Exit scan DOES exit on a dividing diagonal window** — on `diag(2,4,8)` the pivot-`0` find-loop
sees `2 ∣ 4` and `2 ∣ 8`, exhausts the scan, and returns `none` (the genuine terminal that feeds the
diagonal half of the seed). -/
theorem smithExitScanExitsOnDividingDiagonalWindow :
    smithFindNonDividingLaterDiagonal
      { rows := [[2, 0, 0], [0, 4, 0], [0, 0, 8]] } 0
      (Nat.min 3 3 - (0 + 1)) (0 + 1) = none := by
  decide

/-- **Scalar gcd-invariance on a concrete Euclid rotation** — `gcd(6,10) = gcd(6, 10 + 6·(-1)) =
gcd(6,4) = 2`.  A kernel-checked instance of `intGcdInvariantUnderAddScaledLeft` (the invariant every
min-abs Euclid clear inside the cascade rides): folding a multiple of the pivot into the later entry
leaves their gcd fixed. -/
theorem intGcdInvariantOnConcreteEuclidRotation :
    intGcd 6 10 = intGcd 6 (10 + 6 * (-1)) := by
  decide

set_option maxRecDepth 8000 in
/-- **The common divisor `2` divides the landed pivot on a non-coprime diagonal window** — on
`diag(6,10,8)` (every entry even), the pivot-`0` clearing sweep lands `g = 2` at the pivot, and
`2 ∣ 2`.  A non-vacuous positive instance of `commonDivisorOfInputMinorDividesLandedPivot` (the input
minor is `2`-divisible, so the brick predicts `2 ∣ g`). -/
theorem commonDivisorTwoDividesLandedPivotOnNonCoprimeDiagonalWindow :
    smithPivotDividesEntry 2
      ((({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3)
          { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3)).diagonalEntryAt 0) = true := by
  decide

set_option maxRecDepth 8000 in
/-- **The common divisor `2` divides the landed pivot on a HOSTILE non-diagonal seed** — on the fully
non-diagonal all-even `[[6,2,4],[8,10,2],[2,6,8]]`, the pivot-`0` clearing sweep lands an even pivot
(`2`), and `2 ∣ 2`.  Confirms the brick's premise machinery (the forward tower over a confined sweep)
does NOT rely on diagonality of the input — the genuinely non-diagonal case the seed is stated on. -/
theorem commonDivisorTwoDividesLandedPivotOnHostileNonDiagonalSeed :
    smithPivotDividesEntry 2
      ((({ rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } 0 3 3)
          { rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } 0 3 3)).diagonalEntryAt 0) = true := by
  decide

set_option maxRecDepth 8000 in
/-- **The coprime-window sweep leaves a nonzero interior off-diagonal cell** — on `diag(15,10,6,4)`
the pivot-`0` clearing sweep output has `(3,1) = -20 ≠ 0`.  The escaping residual: this converse brick
reads ONLY the on-diagonal slot `(p,p)`; the off-diagonal minor entries the keystone's minimality wall
must clear are NOT sub-block-diagonal after one sweep (route (i) refuted, NODE E). -/
theorem smithSweepLeavesInteriorNonzeroOnCoprimeWindow :
    (({ rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } : IntMatrix).applyOperations
      (smithRepairPositionSweepClearing
        (smithMinorAbsSum { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)
        { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)).entryAt 3 1
      = -20 := by
  decide

/-! ## The brick — the gcd-ideal CONVERSE (forward-tower read-off at the diagonal slot) -/

/-- **Every common divisor of the input minor divides the landed pivot.**  If `divisor` divides every
entry of the input matrix's `[pivotIndex, ·) × [pivotIndex, ·)` minor, then `divisor` divides the
LANDED pivot `(M.applyOperations (clearing repair sweep)).diagonalEntryAt pivotIndex`.  Proof: the
pivot-`pivotIndex` clearing repair sweep is confined below `pivotIndex`
(`smithRepairPositionSweepClearingBoundedBelow` at `lo := pivotIndex`), so the SHIPPED forward tower
`applyOperationsPreservesEntriesDivisibleWithin` carries the whole-minor divisor across it; read off the
resulting `MatrixEntriesDivisibleByWithin` at the on-diagonal slot `(pivotIndex, pivotIndex)` via
`matrixEntriesDivisibleByWithinAt` (`diagonalEntryAt p = entryAt p p` is defeq).

This is the CONVERSE of the keystone `SmithCascadeLandedPivotDividesMinor` and does NOT inhabit it —
see the residual note at the foot of the file. -/
theorem commonDivisorOfInputMinorDividesLandedPivot
    (matrix : IntMatrix) (pivotIndex height width : Nat) (divisor : Int)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (dividesMinor : MatrixEntriesDivisibleByWithin divisor pivotIndex matrix) :
    dividesExactly divisor
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex) :=
  matrixEntriesDivisibleByWithinAt
    (applyOperationsPreservesEntriesDivisibleWithin
      (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width)
      matrix
      (smithRepairPositionSweepClearingBoundedBelow pivotIndex
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
        pRowLt pColLt (Nat.le_refl pivotIndex))
      dividesMinor)
    pivotIndex pivotIndex (Nat.le_refl pivotIndex) (Nat.le_refl pivotIndex)

/-! ## SURVIVING WALL (H2-SMITH r25, #2261)

`commonDivisorOfInputMinorDividesLandedPivot` delivers ONLY the ideal-CONTAINMENT direction
(`divisor ∣ minor ⇒ divisor ∣ g`, i.e. `gcd(minor) ∣ g`).  The corrected-driver keystone
`SmithCascadeLandedPivotDividesMinor` (owned by `SmithWindowedChainReduction.lean`, the file that
carries the wall) needs the OPPOSITE, `g ∣ every input-minor entry` (`g` is itself a common divisor,
`g ∣ gcd(minor)`).  That direction — *the min-abs Euclid descent LANDS a common divisor / `g` is
minimal in the gcd-ideal* — is the r11+ "min-abs Euclid computes the gcd" wall and is NOT closed by any
gcd-invariance argument.  Probe-TRUE (`smithClearingSweepLandsMinorGcdOnConcreteWindow`,
`SmithWindowedChainReduction.lean`: `diag(6,10,8)` lands `2 = gcd`) but a standalone multi-round arc;
`smithSweepLeavesInteriorNonzeroOnCoprimeWindow` above exhibits exactly the off-diagonal residual that
direction must clear.  `SmithReduceCompleteDriverStatement` therefore stays UNINHABITED hypothesis-free
after r25; the driver is inhabited GIVEN the keystone via
`smithReduceCompleteDriverOfLandedPivotDividesMinor` (already wired). -/

end FX1Poly.ComputerAlgebra

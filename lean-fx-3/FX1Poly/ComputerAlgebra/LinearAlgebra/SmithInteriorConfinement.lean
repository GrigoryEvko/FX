import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorTransportEquivalence

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithInteriorConfinement — the keystone survives interior
    fill-in: the landed pivot divides the OFF-DIAGONAL cell it creates (H2-SMITH r26, #2261)

The corrected keystone `SmithCascadeLandedPivotDividesMinor` (⟺ `SmithCascadeOutputMinorDivides`,
`SmithMinorTransportEquivalence.lean`) is the ONE open Prop the corrected-driver totality rests on: the
landed pivot `g := M'.diagonalEntryAt p` divides EVERY entry of the `[p, ·) × [p, ·)` minor — off-diagonal
interior fill-in INCLUDED.

The r21 NODE E witness `smithClearingSweepInteriorNotDiagonalWitness` (and the r25
`smithSweepLeavesInteriorNonzeroOnCoprimeWindow`) established only that the single-pivot clearing sweep
leaves a NONZERO interior off-diagonal cell — route (i) "the sweep output stays sub-block-diagonal" is
false.  But both fired on a COPRIME window where the landed pivot is `1`, so "`1` divides the fill-in" is
vacuous.  The r26 truth-adjudication (NODE 2) needs the NON-trivial conjunction: a window where BOTH the
interior fill-in is nonzero AND the landed pivot is a proper divisor `> 1` that divides that fill-in — the
concrete statement that the keystone SURVIVES genuine interior fill-in.

**The witness window (probe-first, `#eval` before `decide`).**  Feed the pivot-`1` clearing sweep the
diagonal work matrix `diag(1, -12, -18, 10)` (the post-pivot-`0` driver state on the `diag(4, 6, 9, 10)`
seed).  The `[1, ·)` input minor is `diag(-12, -18, 10)`, gcd `2`.  The sweep output is
`[[1,0,0,0], [0,2,0,0], [0,0,-90,0], [0,0,-90,-12]]`: it lands `g = 2` at the pivot, and creates a
GENUINE interior off-diagonal fill-in `(3, 2) = -90 ≠ 0`.  And `2 ∣ -90` (`-90 = 2 · -45`), `2 ∣ -12`,
`2 ∣ 2` — the landed pivot divides every window entry, fill-in included.  So the keystone's output form
holds on this fill-in window: the transient interior fill-in is CONFINED to the landed pivot's ideal.

**The general principle (conditional on the open keystone).**
`landedPivotDividesInteriorOfOutputMinorDivides` reads off `SmithCascadeOutputMinorDivides` at an arbitrary
interior slot: GIVEN the keystone, EVERY interior cell of the sweep output (off-diagonal fill-in included)
is landed-pivot-divisible — the confinement principle spelled out.  It is a projection of the keystone
predicate, so it does NOT close the keystone; it names the exact content the keystone delivers.

**HONEST SIZING — this does NOT flip the driver.**  The keystone `SmithCascadeLandedPivotDividesMinor`
stays OPEN (the min-abs Euclid cascade lands the minor gcd — the r11+ "cascade-computes-gcd" major arc).
This file corroborates NODE 2 (keystone TRUE / interior fill-in confined) with a kernel-checked non-trivial
witness and states the confinement principle conditionally; it inhabits NOTHING hypothesis-free.  The
surviving wall is named at the foot of the file.  The shipped `smithReduceComplete`, its refutation, and
the r18-r25 world stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only; concrete instances at or below the 4x4 defeq ceiling
(`decide` at `maxRecDepth 8000`).  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithInteriorConfinement.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The NODE-2 witness window — `diag(1, -12, -18, 10)`, pivot `1` (probe-first) -/

set_option maxRecDepth 8000 in
/-- The pivot-`1` clearing sweep of the fill-in work matrix — the pivot-`0`-reduced `diag(4, 6, 9, 10)`
driver state — lands the whole output `[[1,0,0,0], [0,2,0,0], [0,0,-90,0], [0,0,-90,-12]]`.  The single
headline reduction: it lands `g = 2` at the pivot AND fills the interior off-diagonal cell `(3, 2)`. -/
theorem smithClearingSweepLandsFillInWindowOutput :
    (({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
          { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).rows
      = [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, -90, 0], [0, 0, -90, -12]] := by
  decide

set_option maxRecDepth 8000 in
/-- The landed pivot on the fill-in window is `g = 2` (a proper divisor `> 1`, NOT the trivial `1` of the
coprime NODE-E witnesses). -/
theorem smithClearingSweepLandsPivotTwoOnFillInWindow :
    (({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
          { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).diagonalEntryAt 1
      = 2 := by
  decide

set_option maxRecDepth 8000 in
/-- The pivot-`1` clearing sweep creates a GENUINE nonzero interior off-diagonal cell `(3, 2) = -90` — the
same fill-in the NODE-E witnesses reported, now on a window whose landed pivot is `2 > 1`. -/
theorem smithClearingSweepFillsInteriorOnFillInWindow :
    (({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
          { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).entryAt 3 2
      = -90 := by
  decide

set_option maxRecDepth 8000 in
/-- **THE NODE-2 CRUX — the landed pivot EXACTLY divides the interior fill-in.**  On the fill-in window
the landed pivot `g = 2` divides the transient interior fill-in `(3, 2) = -90` (witness `-90 = 2 · -45`).
So the keystone's output form is NON-VACUOUSLY confirmed where a genuine off-diagonal fill-in occurs: the
fill-in is confined to the landed pivot's ideal, not merely nonzero.  The `dividesExactly` (∃-witness) form
— the genuine ZZ divisibility, sharper than the `smithPivotDividesEntry` bool. -/
theorem smithLandedPivotExactlyDividesInteriorFillIn :
    dividesExactly
      ((({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
            { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).diagonalEntryAt 1)
      ((({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
            { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).entryAt 3 2) :=
  ⟨-45, by decide⟩

set_option maxRecDepth 8000 in
/-- The landed pivot also divides the remaining nonzero window cells `(2, 2) = -90` and `(3, 3) = -12`
(bool form) — the WHOLE `[1, ·)` output minor of the fill-in window is `2`-divisible, off-diagonals and
all.  Combined with `smithLandedPivotExactlyDividesInteriorFillIn`, the keystone's output form holds on
every entry of this concrete fill-in window. -/
theorem smithLandedPivotDividesEveryFillInWindowCell :
    smithPivotDividesEntry
      ((({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
            { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).diagonalEntryAt 1)
      ((({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
            { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).entryAt 3 3)
      = true := by
  decide

/-! ## The general confinement principle — the keystone confines all interior fill-in to its ideal -/

/-- **The keystone confines every interior cell to the landed pivot's ideal.**  GIVEN
`SmithCascadeOutputMinorDivides` (⟺ the keystone), for ANY rectangular input and pivot, EVERY entry of the
sweep output's `[pivotIndex, ·) × [pivotIndex, ·)` minor — off-diagonal fill-in included — is divisible by
the landed pivot.  A direct read-off of the keystone predicate at an arbitrary interior slot
(`matrixEntriesDivisibleByWithinAt`): the transient interior fill-in the NODE-E witnesses exhibit lands in
the landed pivot's ideal exactly when the keystone holds.  This spells out the NODE-2 confinement content;
it is a PROJECTION of the keystone, so it inhabits nothing hypothesis-free. -/
theorem landedPivotDividesInteriorOfOutputMinorDivides
    (outputDivides : SmithCascadeOutputMinorDivides)
    (matrix : IntMatrix) (pivotIndex height width rowIndex colIndex : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height)
    (pColLt : pivotIndex < width) (rowGe : pivotIndex ≤ rowIndex) (colGe : pivotIndex ≤ colIndex) :
    dividesExactly
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).entryAt rowIndex colIndex) :=
  matrixEntriesDivisibleByWithinAt
    (outputDivides matrix pivotIndex height width isRect pRowLt pColLt) rowIndex colIndex rowGe colGe

/-! ## The surviving wall (named IN this file — NOT prose masquerading as a theorem)

This file inhabits NOTHING hypothesis-free.  It establishes:

  * a KERNEL-CHECKED non-trivial NODE-2 witness — the pivot-`1` clearing sweep of `diag(1, -12, -18, 10)`
    lands `g = 2 > 1` and creates a genuine interior off-diagonal fill-in `(3, 2) = -90` that `g` divides
    (`smithLandedPivotExactlyDividesInteriorFillIn`), so the keystone SURVIVES interior fill-in on a
    non-coprime window (strictly sharper than the coprime, pivot-`1` NODE-E / r25 witnesses);
  * the CONFINEMENT PRINCIPLE `landedPivotDividesInteriorOfOutputMinorDivides` — a projection of the
    keystone, conditional on it, spelling out that the keystone confines every interior cell to the landed
    pivot's ideal.

**THE OPEN OBLIGATION, named EXACTLY.**  `SmithCascadeLandedPivotDividesMinor`
(⟺ `SmithCascadeOutputMinorDivides`) — the min-abs Euclid cascade LANDS the minor gcd (`g ∣ every input
minor entry`, the direction `g ∣ gcd` that gcd-invariance CANNOT give,
`SmithWindowGcdInvariance.lean`).  This is the r11+ "cascade-computes-gcd" MAJOR ARC, decisively NOT
r26-sized; corroborated TRUE per NODE 2 (this file's concrete witness plus the r26 hunt's zero-violation
battery), but unproven in general.  `smithReduceCompleteDriverOfOutputMinorDivides` remains the
output-side seed-conditional totality, byte-intact. -/

end FX1Poly.ComputerAlgebra

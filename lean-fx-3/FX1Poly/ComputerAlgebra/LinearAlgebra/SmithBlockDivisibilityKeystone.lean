import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithBlockDivisibilityKeystone — the keystone is
    STATE-LOCAL under the WHOLE-BLOCK landing condition, and the OPERATIONAL landing condition is
    strictly weaker (H2-SMITH r44, #2261)

## The re-factoring, adjudicated

The corrected-driver totality residual (since r22/r29) is the magnitude identity `|landed| = gcd(minor)`
on the landed pivot.  As an UNRESTRICTED claim over the actual sweep it is REFUTED (r33,
`SmithLandedMagnitudeRefuted`): the seed

    `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]`   (pivot 0)

lands `6` while `gcd(6, 10) = 2` and `6 ∤ 10` — the off-cross `10` at `(1, 2)` escapes the pivot cross.
r33 concluded the surviving open content is the RESTRICTED keystone on the sweep's reachable image.

The CoqEAL / Isabelle / Mathlib formalizations of Smith normal form thread this DIFFERENTLY.  Their
`improve_pivot` postcondition is `∀ i j, pivot ∣ block[i][j]` — the pivot divides the WHOLE block — a
purely STATE-LOCAL predicate carrying NO reachability history.  Under it, "the pivot is an entry AND
divides all" gives `|pivot| = gcd` by antisymmetry (shape (a); the Bezout descent lives inside the
improvement loop, not at the landing).  This module ports that factoring and adjudicates the gap:

  * The keystone IS state-local — under the CORRECT (whole-block) landing condition
    (`blockDivisibilityImpliesAbsEqMinorGcd`, `landedDividesInputBlockImpliesAbsEqMinorGcd`); the r33
    refuter is EXCLUDED because it genuinely FAILS whole-block divisibility (`6 ∤ 10`), not by a
    reachability test and not by fiat.
  * The OPERATIONAL landing condition the sweep actually uses — nonzero pivot ∧ `smithCrossIsClear` ∧
    `smithFindNonDividingLaterDiagonal = none` — is STRICTLY WEAKER: it is DIAGONAL-only.  The KILLER
    seed `[[6, 0, 0], [0, 0, 10], [0, 0, 0]]` (and the anti-diagonal `[[2, 0, 0], [0, 0, 3], [0, 3, 0]]`)
    satisfy ALL THREE operational conjuncts on the injected state ITSELF, yet miss the gcd
    (`operationallyLandedYetMissesMinorGcd`) and do NOT divide their block
    (`offCrossEntryEscapesDiagonalFind`: `6 ∤ 10` at the off-cross `(1, 2)` the diagonal-only scan never
    inspects).

## What ships (all zero-axiom, additive; the r18–r43 world byte-intact)

  * `oneDividesEntireBlock` — `1` divides every entry of any `[lo, ·)²` block (the unit witness).
  * `blockDivisibilityImpliesAbsEqMinorGcd` — STATE-LOCAL keystone: if the pivot at `(p, p)` divides
    every entry of the `[p, ·)²` block, then `|pivot| = gcd(block)`.  Unconditional given the whole-block
    hypothesis; the CoqEAL `improve_pivot`-postcondition ⟹ gcd, shape (a).  Proof: `pivot ∣ gcd`
    (`minorGcdWithinGreatest`) ∧ `gcd ∣ pivot` (`minorGcdWithinDividesWithin` at `(p, p)`), then
    `natDividesAntisymm` on magnitudes.
  * `unitPivotForcesBlockGcdOne` — non-vacuity: a concrete unit-pivot matrix has block gcd `1`, proved
    THROUGH the keystone (`oneDividesEntireBlock` discharges the hypothesis).
  * `landedDividesInputBlockImpliesAbsEqMinorGcd` — the DRIVER-LOCALIZED keystone: if the sweep's landed
    pivot divides every entry of the INPUT `[p, ·)²` block, then `|landed| = gcd(input minor)`.  Discharges
    the `gcd ∣ landed` half with the SHIPPED hypothesis-free `minorGcdDividesLanded`; the localized form of
    `landedMagnitudeEqMinorGcdOfKeystone` (a STATE-LOCAL whole-block hypothesis, not the global keystone).
  * `operationallyLandedYetMissesMinorGcd` — the INSUFFICIENCY CERTIFICATE: a matrix that is operationally
    landed (nonzero pivot ∧ cross clear ∧ diagonal-find-none, all on the injected state) yet `|pivot| ≠
    gcd`.  Sharpens r33 from "the sweep overshoots on non-diagonal input" to "even the repair's OWN
    termination predicate (find-none) reports done on a state that misses the gcd".
  * `offCrossEntryEscapesDiagonalFind` — the located gap: the pivot does not divide the off-cross `(1, 2)`
    entry, which the diagonal-only find never inspects — operational landing ⇏ whole-block divisibility.
  * `antiDiagonalKillerOperationallyLandedYetMissesMinorGcd` — the second killer (anti-diagonal, `2 ≠ 1`).

## HONEST SIZING — the driver stays WALLED hypothesis-free

`blockDivisibilityImpliesAbsEqMinorGcd` and `landedDividesInputBlockImpliesAbsEqMinorGcd` are
HYPOTHESIS-BOUND: each consumes the whole-block divisibility of the (landed) state.  Neither inhabits
`SmithReduceCompleteDriverStatement` hypothesis-free.  The insufficiency certificate proves the sweep's
OPERATIONAL landing predicate does NOT establish that whole-block hypothesis.  So the surviving open
content is precisely "operational (diagonal-only) landing ⟹ whole-block divisibility of the landed
state ON THE REACHABLE IMAGE" — the K1 (fuel-adequacy / round-pair descent; single-round `pivotMagnitudeWithin`
RISES, r41) ∧ K2 (off-diagonal gcd-ideal) multi-round wall, NOT same-round reachable and NOT r44-sized.
The r33 unrestricted refutation, `smithReduceComplete`, and the r18–r43 world stay byte-intact
(additive only).

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBlockDivisibilityKeystone.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

set_option maxRecDepth 100000

/-! ## The whole-block landing condition is the gcd condition (state-local) -/

/-- **`1` divides every entry of any `[lo, ·)²` block** — the unit `MatrixEntriesDivisibleByWithin`
witness (factor is the entry itself, `entry = 1 * entry`).  Non-vacuity fuel for the keystone below. -/
theorem oneDividesEntireBlock (matrix : IntMatrix) (lo : Nat) :
    MatrixEntriesDivisibleByWithin 1 lo matrix :=
  fun rowIndex _ colIndex _ =>
    ⟨matrix.entryAt rowIndex colIndex, (Int.one_mul (matrix.entryAt rowIndex colIndex)).symm⟩

/-- **STATE-LOCAL keystone** — if the pivot at `(pivotIndex, pivotIndex)` divides EVERY entry of the
`[pivotIndex, ·)²` block (`MatrixEntriesDivisibleByWithin (diagonalEntryAt pivotIndex) pivotIndex
matrix`, the CoqEAL `improve_pivot` postcondition), then `|pivot| = gcd(block)`.  Unconditional given
that whole-block hypothesis — no sweep, no reachability.  `pivot ∣ gcd` from `minorGcdWithinGreatest`
(the pivot is a common divisor of the block); `gcd ∣ pivot` from `minorGcdWithinDividesWithin` read at
the pivot slot `(pivotIndex, pivotIndex)` (`diagonalEntryAt p = entryAt p p` is defeq); antisymmetry on
`natAbs` via `natDividesAntisymm`.  The r33 refuter is excluded because it FAILS the hypothesis (`6 ∤
10`), not by fiat. -/
theorem blockDivisibilityImpliesAbsEqMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotDividesBlock :
      MatrixEntriesDivisibleByWithin (matrix.diagonalEntryAt pivotIndex) pivotIndex matrix) :
    (matrix.diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs :=
  natDividesAntisymm
    (natDividesNatAbsOfIntDivides
      (minorGcdWithinGreatest matrix pivotIndex height width
        (matrix.diagonalEntryAt pivotIndex) pivotDividesBlock))
    (natDividesNatAbsOfIntDivides
      (matrixEntriesDivisibleByWithinAt
        (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)
        pivotIndex pivotIndex (Nat.le_refl pivotIndex) (Nat.le_refl pivotIndex)))

/-- A concrete `3 x 3` matrix with a unit pivot at `(0, 0)`. -/
def unitPivotSeed : IntMatrix := { rows := [[1, 7, 3], [2, 5, 9], [4, 8, 6]] }

theorem unitPivotSeedIsRectangular : unitPivotSeed.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **Non-vacuity, proved THROUGH the keystone** — the unit pivot divides the whole block
(`oneDividesEntireBlock`), so `blockDivisibilityImpliesAbsEqMinorGcd` fires and the block gcd magnitude
is `|1| = 1`.  A machine witness that the state-local hypothesis is satisfiable and the conclusion
non-trivially discharges. -/
theorem unitPivotForcesBlockGcdOne : (minorGcdWithin unitPivotSeed 0 3 3).natAbs = 1 :=
  (blockDivisibilityImpliesAbsEqMinorGcd unitPivotSeed 0 3 3 unitPivotSeedIsRectangular
      (oneDividesEntireBlock unitPivotSeed 0)).symm.trans (by decide)

/-! ## The driver-localized keystone (landed pivot vs the INPUT block) -/

/-- **DRIVER-LOCALIZED keystone** — if the sweep's landed pivot divides every entry of the INPUT
`[pivotIndex, ·)²` block, then `|landed| = gcd(input minor)`.  The `landed ∣ gcd` half is
`minorGcdWithinGreatest`; the `gcd ∣ landed` half is the SHIPPED, hypothesis-free `minorGcdDividesLanded`
(the r25/r29 converse).  This is the STATE-LOCAL form of `landedMagnitudeEqMinorGcdOfKeystone`: it
consumes only the whole-block divisibility of THIS landed state, not the global keystone
`SmithCascadeLandedPivotDividesMinor`.  It is exactly the driver residual #10–#12 shape, localized —
and still HYPOTHESIS-BOUND (does not inhabit the driver hypothesis-free). -/
theorem landedDividesInputBlockImpliesAbsEqMinorGcd (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height)
    (pColLt : pivotIndex < width)
    (landedDividesInputBlock :
      MatrixEntriesDivisibleByWithin
        ((matrix.applyOperations
            (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
        pivotIndex matrix) :
    ((matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs :=
  natDividesAntisymm
    (natDividesNatAbsOfIntDivides
      (minorGcdWithinGreatest matrix pivotIndex height width _ landedDividesInputBlock))
    (natDividesNatAbsOfIntDivides
      (minorGcdDividesLanded matrix pivotIndex height width isRect pRowLt pColLt))

/-! ## The operational landing condition is strictly weaker — the insufficiency certificate -/

/-- The KILLER seed: nonzero pivot `6` at `(0, 0)`, off-cross `10` at `(1, 2)`.  Pivot-cross clean, later
diagonals `0` (so the diagonal-only find reports done), yet `gcd(6, 10) = 2` and `6 ∤ 10`. -/
def operationallyLandedKillerSeed : IntMatrix := { rows := [[6, 0, 0], [0, 0, 10], [0, 0, 0]] }

theorem operationallyLandedKillerSeedIsRectangular :
    operationallyLandedKillerSeed.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **THE INSUFFICIENCY CERTIFICATE** — there is a matrix that is OPERATIONALLY LANDED (nonzero pivot ∧
`smithCrossIsClear` ∧ `smithFindNonDividingLaterDiagonal = none`, all on the INJECTED state itself) whose
`|pivot| ≠ gcd(block)`.  So the sweep's own operational landing predicate does NOT imply `|landed| =
gcd` — reachability (or, equivalently, the stronger whole-block divisibility) is genuinely load-bearing.
This SHARPENS r33 (which only showed the sweep overshoots on non-diagonal input): here the repair's OWN
diagonal termination test passes on a state that still misses the gcd.  An EXISTENTIAL (a witnessed
refutation of the implication), never a refuted universal proved. -/
theorem operationallyLandedYetMissesMinorGcd :
    ∃ (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width ∧ pivotIndex < height ∧ pivotIndex < width ∧
      (matrix.diagonalEntryAt pivotIndex).natAbs ≠ 0 ∧
      smithCrossIsClear matrix pivotIndex height width = true ∧
      smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none ∧
      (matrix.diagonalEntryAt pivotIndex).natAbs
        ≠ (minorGcdWithin matrix pivotIndex height width).natAbs :=
  ⟨operationallyLandedKillerSeed, 0, 3, 3, operationallyLandedKillerSeedIsRectangular,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **THE LOCATED GAP** — on the killer, the pivot `6` does NOT divide the off-cross `(1, 2)` entry `10`
(`smithPivotDividesEntry … = false`), the entry the DIAGONAL-only `smithFindNonDividingLaterDiagonal`
never inspects.  This is why operational landing ⇏ whole-block divisibility (the hypothesis of
`blockDivisibilityImpliesAbsEqMinorGcd`): the operational predicate is under-quantified. -/
theorem offCrossEntryEscapesDiagonalFind :
    smithPivotDividesEntry (operationallyLandedKillerSeed.diagonalEntryAt 0)
        (operationallyLandedKillerSeed.entryAt 1 2) = false := by decide

/-- The anti-diagonal KILLER: nonzero pivot `2`, off-cross anti-diagonal `3`. -/
def operationallyLandedAntiDiagonalKillerSeed : IntMatrix :=
  { rows := [[2, 0, 0], [0, 0, 3], [0, 3, 0]] }

theorem operationallyLandedAntiDiagonalKillerSeedIsRectangular :
    operationallyLandedAntiDiagonalKillerSeed.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- **Second insufficiency witness** — the anti-diagonal killer is operationally landed (nonzero pivot ∧
cross clear ∧ diagonal-find-none) yet `|pivot| = 2 ≠ 1 = gcd(2, 3, 3)`.  The refutation is not a single
shape: off-cross structure of either kind (trailing zero or anti-diagonal) breaks the operational
predicate identically. -/
theorem antiDiagonalKillerOperationallyLandedYetMissesMinorGcd :
    operationallyLandedAntiDiagonalKillerSeed.IsRectangular 3 3 ∧
    (operationallyLandedAntiDiagonalKillerSeed.diagonalEntryAt 0).natAbs ≠ 0 ∧
    smithCrossIsClear operationallyLandedAntiDiagonalKillerSeed 0 3 3 = true ∧
    smithFindNonDividingLaterDiagonal operationallyLandedAntiDiagonalKillerSeed 0
        (Nat.min 3 3 - 1) 1 = none ∧
    (operationallyLandedAntiDiagonalKillerSeed.diagonalEntryAt 0).natAbs
      ≠ (minorGcdWithin operationallyLandedAntiDiagonalKillerSeed 0 3 3).natAbs :=
  ⟨operationallyLandedAntiDiagonalKillerSeedIsRectangular, by decide, by decide, by decide, by decide⟩

/-! ## SURVIVING WALL (H2-SMITH r44, #2261)

The keystone `|landed| = gcd(minor)` is STATE-LOCAL under the WHOLE-BLOCK landing condition
(`blockDivisibilityImpliesAbsEqMinorGcd`, `landedDividesInputBlockImpliesAbsEqMinorGcd`) — the CoqEAL
`improve_pivot`-postcondition factoring, with the r33 refuter `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]`
excluded because it genuinely FAILS whole-block divisibility (`6 ∤ 10`), not by fiat.  But the sweep's
ACTUAL termination predicate is OPERATIONAL — nonzero pivot ∧ cross clear ∧ DIAGONAL-only find-none — and
`operationallyLandedYetMissesMinorGcd` proves that predicate strictly weaker: the killer
`[[6, 0, 0], [0, 0, 10], [0, 0, 0]]` (and the anti-diagonal `[[2, 0, 0], [0, 0, 3], [0, 3, 0]]`) are
operationally landed on the injected state yet miss the gcd, because the off-cross entry
(`offCrossEntryEscapesDiagonalFind`, `6 ∤ 10` at `(1, 2)`) escapes the diagonal-only scan.

The surviving open content is therefore "operational (diagonal-only) landing ⟹ whole-block divisibility
of the landed state ON THE REACHABLE IMAGE" — K1 (fuel-adequacy / round-pair descent; the single-round
`pivotMagnitudeWithin` RISES per r41, so K1 needs a lexicographic / two-round measure) ∧ K2 (the
off-diagonal gcd-ideal).  Both bottom out on the same min-abs-Euclid-computes-the-sub-block-gcd core; it
is a standalone MULTI-ROUND descent arc, NOT same-round reachable, NOT r44-sized.  Nothing here inhabits
`SmithReduceCompleteDriverStatement` hypothesis-free: it stays inhabited only GIVEN the whole-block /
keystone hypothesis (via `landedDividesInputBlockImpliesAbsEqMinorGcd` composed with the shipped
`keystoneIffLandedDividesMinorGcd.mpr` and `smithReduceCompleteDriverOfLandedPivotDividesMinor`).  The
#2261 mandate does NOT fire; the driver is honestly WALLED. -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithMinNonzeroAbsDescent — the corrected `foldDescends`
    measure candidate: `minNonzeroAbs` beats `minorAbsSum` but STALLS (H2-SMITH r26, #2261)

The r21 NODE D reduces the seed's diagonal half to `foldDescends` — a strict drop of some descent
`measure` on each genuine fold of the clearing cascade — plus a fuel-budget fit.  r22 machine-REFUTED the
naive budget-fitting candidate: `smithMinorAbsSumRaisesOnFoldWitness` shows `smithMinorAbsSum` (the
fuel/budget) RISES `24 → 40` on the `diag(6, 10, 8)` pivot-`0` fold, so it is NOT a descent measure.

The r26 hunt's descent probe proposed `minNonzeroAbs(minor)` — the minimum magnitude among the NONZERO
entries of the `[p, ·) × [p, ·)` minor — as the corrected measure.  This module ships that measure and
its machine-checked behaviour.  **The probe's headline "strictly descends on every nonzero-pivot fold" is
CORRECTED here: `minNonzeroAbs` never RISES, and it strictly descends exactly where `minorAbsSum` rises,
but it STALLS on two fold classes** (already-minimal, and the zero-pivot bootstrap) — so `minNonzeroAbs`
ALONE is not a strict descent measure; `foldDescends` needs a lex refinement, and the two stall classes
are the named seam.

**Machine-checked (probe-first `#eval`, then `decide`; all at or below the 4x4 defeq ceiling).**

  * `smithMinNonzeroAbsDescendsWhereMinorAbsSumRises` — on the EXACT `diag(6, 10, 8)` pivot-`0` fold where
    `smithMinorAbsSumRaisesOnFoldWitness` shows `minorAbsSum` rises `24 → 40`, `minNonzeroAbs` strictly
    DESCENDS `6 → 2`.  The corrected measure beats the naive one on the naive one's failure case.
  * `smithMinNonzeroAbsDescendsOnCoprimeSeed` — a second strict descent, `diag(6, 9, 10)` pivot-`0`
    (`6 → 3`).
  * `smithMinNonzeroAbsStallsOnAlreadyMinimalFold` — on `diag(15, 10, 6, 4)` pivot-`0` the fold's landed
    magnitude equals a value ALREADY present in the minor, so `minNonzeroAbs` STALLS `4 = 4`.  A genuine
    NONZERO-pivot fold where `minNonzeroAbs` does NOT strictly descend — the machine-checked correction to
    the recon's "strictly descends on every nonzero-pivot fold".
  * `smithMinNonzeroAbsStallsOnZeroPivotBootstrap` — on `diag(0, 4)` the pivot is `0`, the fold jumps
    `|pivot| 0 → 4`, yet `minNonzeroAbs` STALLS `4 = 4` (the `4` was the sole nonzero entry all along).
    The zero-pivot bootstrap seam (recon Δ2), isolated as its own fold class.

**HONEST SIZING — this does NOT close `foldDescends` or the keystone.**  It CORRECTS the r26 recon's
measure claim and PINS the exact residual: `minNonzeroAbs` is non-increasing across folds (strictly better
than `minorAbsSum`, which rises) but stalls on the two named classes, so a strict measure must lex-refine
it (secondary key breaking the stalls) — and proving that refinement descends IS the "cascade-computes-gcd"
major arc the keystone `SmithCascadeLandedPivotDividesMinor` rests on.  Inhabits NOTHING hypothesis-free.
The shipped `smithMinorAbsSum`, `smithClearingFoldStep`, the driver, and the r18-r25 world stay byte-intact
(additive only).

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinNonzeroAbsDescent.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The corrected measure — `minNonzeroAbs` over the `[pivotIndex, ·) × [pivotIndex, ·)` minor -/

/-- Combine a running minimum-of-nonzero-magnitudes accumulator with one candidate magnitude.  A `0`
candidate is SKIPPED (zeros are not in the minimum); a `0` accumulator means "no nonzero seen yet", so the
first nonzero candidate seeds it.  The `0` sentinel is unambiguous — every nonzero magnitude is `≥ 1`. -/
def natMinNonzero (current candidate : Nat) : Nat :=
  match candidate with
  | 0 => current
  | _ + 1 =>
      match current with
      | 0 => candidate
      | _ + 1 => Nat.min current candidate

/-- Fold `natMinNonzero` across one row's `colCount` magnitudes from `colStart` (mirrors
`smithRowAbsSum`'s shape, taking min-of-nonzero instead of sum). -/
def rowMinNonzeroFrom (matrix : IntMatrix) (rowIndex : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | colCount + 1, colStart =>
      natMinNonzero (rowMinNonzeroFrom matrix rowIndex colCount (colStart + 1))
        (matrix.entryAt rowIndex colStart).natAbs

/-- Fold `natMinNonzero` over `rowCount` rows from `rowStart`, each `colCount` columns from `colStart`
(mirrors `smithMinorAbsSumRows`). -/
def minorMinNonzeroRows (matrix : IntMatrix) (colStart colCount : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | rowCount + 1, rowStart =>
      natMinNonzero (minorMinNonzeroRows matrix colStart colCount rowCount (rowStart + 1))
        (rowMinNonzeroFrom matrix rowStart colCount colStart)

/-- **The corrected descent measure** — the minimum magnitude among the NONZERO entries of the
`[pivotIndex, ·) × [pivotIndex, ·)` minor (`0` iff the minor is entirely zero).  The r26-recommended
replacement for `smithMinorAbsSum` as the `foldDescends` witness measure — mirrors `smithMinorAbsSum`'s
iteration exactly, taking min-of-nonzero rather than sum. -/
def minNonzeroAbsWithin (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  minorMinNonzeroRows matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex

/-! ## The measure's fold behaviour — strict descent where `minorAbsSum` rises, and the two STALL classes -/

set_option maxRecDepth 8000 in
/-- **The corrected measure DESCENDS where the naive one RISES.**  On the exact `diag(6, 10, 8)` pivot-`0`
fold where `smithMinorAbsSumRaisesOnFoldWitness` shows `smithMinorAbsSum` rises `24 → 40`,
`minNonzeroAbsWithin` strictly DESCENDS `6 → 2`.  So `minNonzeroAbs` beats `minorAbsSum` precisely on the
fold that refutes `minorAbsSum` as a measure — the r26 de-risking payoff. -/
theorem smithMinNonzeroAbsDescendsWhereMinorAbsSumRises :
    minNonzeroAbsWithin
        (smithClearingFoldStep { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 1 0 3 3) 0 3 3
      < minNonzeroAbsWithin { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3 := by
  decide

set_option maxRecDepth 8000 in
/-- **A second strict descent** — `diag(6, 9, 10)` pivot-`0`: the fold drops `minNonzeroAbs` `6 → 3`. -/
theorem smithMinNonzeroAbsDescendsOnCoprimeSeed :
    minNonzeroAbsWithin
        (smithClearingFoldStep { rows := [[6, 0, 0], [0, 9, 0], [0, 0, 10]] } 1 0 3 3) 0 3 3
      < minNonzeroAbsWithin { rows := [[6, 0, 0], [0, 9, 0], [0, 0, 10]] } 0 3 3 := by
  decide

set_option maxRecDepth 8000 in
/-- **STALL class 1 — an already-minimal nonzero-pivot fold.**  On `diag(15, 10, 6, 4)` pivot-`0` the
fold lands magnitude `4`, a value ALREADY present in the minor, so `minNonzeroAbsWithin` STALLS `4 = 4` —
a genuine nonzero-pivot fold on which `minNonzeroAbs` does NOT strictly descend.  This machine-CORRECTS the
r26 recon's "`minNonzeroAbs` strictly descends on every nonzero-pivot fold": it does not, so the measure
alone is non-strict and `foldDescends` needs a lex refinement. -/
theorem smithMinNonzeroAbsStallsOnAlreadyMinimalFold :
    minNonzeroAbsWithin
        (smithClearingFoldStep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 1 0 4 4)
        0 4 4
      = minNonzeroAbsWithin { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4 := by
  decide

set_option maxRecDepth 8000 in
/-- **STALL class 2 — the zero-pivot bootstrap.**  On `diag(0, 4)` the pivot is `0`; the fold jumps the
pivot magnitude `0 → 4` (`|pivot|` is not monotone), yet `minNonzeroAbsWithin` STALLS `4 = 4` (the `4` was
the sole nonzero minor entry all along).  Both the pivot-zero premise and the measure stall are stated so
the zero-pivot seam (recon Δ2) is pinned as its own fold class — the second obstruction a lex refinement
of `minNonzeroAbs` must break. -/
theorem smithMinNonzeroAbsStallsOnZeroPivotBootstrap :
    ({ rows := [[0, 0], [0, 4]] } : IntMatrix).diagonalEntryAt 0 = 0 ∧
    ((smithClearingFoldStep { rows := [[0, 0], [0, 4]] } 1 0 2 2).diagonalEntryAt 0).natAbs = 4 ∧
    minNonzeroAbsWithin (smithClearingFoldStep { rows := [[0, 0], [0, 4]] } 1 0 2 2) 0 2 2
      = minNonzeroAbsWithin { rows := [[0, 0], [0, 4]] } 0 2 2 := by
  decide

/-! ## The surviving wall (named IN this file — NOT prose masquerading as a theorem)

This file inhabits NOTHING hypothesis-free.  It ships the corrected measure `minNonzeroAbsWithin` and
machine-checks that it (a) strictly DESCENDS on the `diag(6, 10, 8)` fold where `smithMinorAbsSum` RISES,
and on `diag(6, 9, 10)`, but (b) STALLS on `diag(15, 10, 6, 4)` (already-minimal) and `diag(0, 4)`
(zero-pivot bootstrap) — so it is non-increasing but NOT strictly monotone.

**THE OPEN OBLIGATION, named EXACTLY.**  [r33: the general keystone this measure serves —
`SmithCascadeLandedPivotDividesMinor` — is REFUTED AS STATED (`SmithLandedMagnitudeRefuted`); the descent
measure below remains the OPEN lever for the RESTRICTED diagonal / in-driver-image form.]  `foldDescends`
(the r21 NODE D per-fold strict drop) needs a lex
refinement `(minNonzeroAbsWithin, secondaryKey)` whose secondary key strictly descends on the two stall
classes above; proving THAT descends across the whole min-abs Euclid cascade IS the "cascade-computes-gcd"
major arc underlying the keystone `SmithCascadeLandedPivotDividesMinor` (`SmithWindowedChainReduction.lean`
NODE D; `smithReduceCompleteDriverOfLandedPivotDividesMinor` remains the seed-conditional totality,
byte-intact).  Decisively NOT r26-sized. -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithFoldDescentRefuted
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachablePrefixConfinement

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithPrefixSettledDescentInsufficient — the
    `SmithPrefixSettled`-guarded one-round descent is STILL FALSE; the corrected lever is the
    below-pivot-column confinement (H2-SMITH r39, #2261)

## The move

r38 (`SmithReachableMagnitudeResidual`) sharpened the corrected-driver residual to the reachable
magnitude equality `|landed| = gcd(minor)`, whose only open half is the one-sided min-abs no-overshoot
descent `|landed| ≤ gcd`.  Its footer proposed the lever "a `Nat.rec` strong induction on a `natAbs`
bound fed by `SmithPrefixSettled`/reachable states" — the per-round `pivotMagnitudeWithin` descent, gated
so that the r31 refuter (`smithFoldDescendsOnNonzeroPivotIsRefuted`, raw `SmithFoldDescendsOnNonzeroPivot`
FALSE) is excluded.  The natural candidate gate is the SHIPPED confinement invariant `SmithPrefixSettled`
(`reachableImpliesPrefixSettled`, r36).

**r39 TRUTH-PROBE REFUTES that gate.**  `SmithPrefixSettled matrix pivotIndex height width` is VACUOUS at
`pivotIndex = 0` — it constrains only off-diagonal cells whose row OR column is `< pivotIndex`, and there
are none below `0` (`smithPrefixSettledZero` holds for EVERY matrix).  So the exact r31 counterexample
`[[2,0],[4,3]]` IS `SmithPrefixSettled … 0 2 2` (vacuously), yet the fold RAISES `pivotMagnitudeWithin`
`2 → 3` (`smithFoldStepRaisesPivotOnCounterexample`).  Hence the `SmithPrefixSettled`-guarded one-round
descent obligation is FALSE — refuted by the SAME r31 counterexample the raw form was
(`smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted`, machine-checked, zero axioms).  **The design's
proposed guard does not gate the descent.**

## The corrected lever (trace-table-confirmed, machine-verified separation)

The `#eval` truth-probe over the reachable trajectory pins the ACTUAL taming condition: on the reachable
carrier the below-pivot pivot-column fill-in `entry(pivotIndex+1, pivotIndex)` has MAGNITUDE `≤` the pivot
(the r36 off-by-one confinement fill-in — `|entry(3,2)| = 126 = |pivot|` on the driver-reachable
`diag(4,6,9,7)` pivot-`2` state), whereas the r31 refuter has `|entry(1,0)| = 4 > 2 = |pivot|`.  So the
predicate `belowPivotColumnConfined` (`|entry(p+1,p)| ≤ |pivot|`) SEPARATES them: the reachable driver
witness satisfies it and DESCENDS (`126 → 12`, `smithConfinedFoldDescendsOnDriverWitness`); the r31 refuter
VIOLATES it (`smithConfinedGuardExcludesRefuter`).  This is strictly SHARPER than `SmithPrefixSettled` —
`SmithPrefixSettled` says nothing about column `pivotIndex` below the pivot, which is exactly where the
fill-in lives.

## What this module ships (positive, additive, zero-axiom)

  * **`belowPivotColumnConfined`** — the corrected lever `|entry(pivotIndex+1, pivotIndex)| ≤ |pivot|`, the
    load-bearing below-pivot-column magnitude confinement (decidable at every concrete instance).
  * **`SmithFoldDescendsOnPrefixSettledNonzeroPivot`** — the design's PROPOSED r39 gate (the raw fold
    obligation `+ SmithPrefixSettled`).  A `def … : Prop`.
  * **`smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted`** — THE GRAVEYARD: that gate is FALSE at the
    r31 counterexample (`SmithPrefixSettled … 0 2 2` holds VACUOUSLY via `smithPrefixSettledZero`, all other
    preconditions hold, yet the fold raises).  Machine-checked, zero axioms.  Sharpens the r38 footer.
  * **`smithConfinedGuardExcludesRefuter`** — the corrected guard rejects the r31 refuter (`¬
    belowPivotColumnConfined [[2,0],[4,3]] 0`, `4 ≤ 2` false); the guard `SmithPrefixSettled` admitted it.
  * **`smithDriverWitnessConfined`** — the driver-reachable dirty-found-column state
    (`smithDirtyFoundColumnDriverWitness`, `find = some 3`, `entry(3,2) ≠ 0`) SATISFIES the corrected guard
    (`126 ≤ 126`).
  * **`smithConfinedFoldDescendsOnDriverWitness`** — the descent CONCLUSION holds on that reachable state
    (`pivotMagnitudeWithin` `126 → 12`): the corrected candidate's conclusion is TRUE precisely on the
    exact r31 dirty-column obstruction state, once the state is confined.
  * **`SmithFoldDescendsOnConfinedNonzeroPivot`** — the CORRECTED one-round candidate (the trace-table
    statement): the `belowPivotColumnConfined`-guarded strict `pivotMagnitudeWithin` descent.  A `def …
    : Prop`, NOT proved (see the wall); battery-verified on the reachable witness above.
  * **`smithClearingOutputFindNoneFromConfinedFoldDescent`** — the D3 INSTANTIATION: the shipped generic
    `Nat.rec`-on-fuel driver `smithClearingSweepReachesFindNoneOfGuardedDescent` fixed with
    `measure := pivotMagnitudeWithin · pivotIndex` and `invariant := ZeroTrailingDiagonalsFrom ∧
    belowPivotColumnConfined`; the zero-pivot base discharged by brick-4 (`smithZeroPivotImpliesFindNone`),
    the budget by `pivotMagnitudeLeMinorAbsSum`.  Consumes the corrected confined-fold-descent + the
    confinement-preservation invariant as HYPOTHESES — the named r40 residuals.  No `WellFounded.fix`: the
    strong induction is the shipped structural one.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the
mandate does NOT fire.  This is a GATE-CORRECTION + GRAVEYARD round: the r38-proposed
`SmithPrefixSettled` descent gate is machine-REFUTED (vacuous at pivot 0), the load-bearing lever is
`belowPivotColumnConfined` (machine-verified to separate reachable from refuter), and the D3 instantiation
is wired MODULO two open r40 legs — (i) `SmithFoldDescendsOnConfinedNonzeroPivot` (the confined one-round
descent, the cascade-output-magnitude content) and (ii) the confinement-PRESERVATION invariant (that the
fold keeps `belowPivotColumnConfined`, which `reachableImpliesPrefixSettled` does NOT supply: it settles
only the prefix `< pivotIndex`, leaving column `pivotIndex` below UNCONSTRAINED — precisely where the
fill-in lives).  Both feed fuel-adequacy `K1`; `K2` (`SmithClearingOutputOffDiagonalDivides`) remains the
standalone gcd-ideal wall, UNCHANGED.  The round-level divisor chain stays machine-REFUTED (not stated).
The r18–r38 world, `smithReduceComplete`, and the refutation certificates stay BYTE-INTACT (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (no recursion introduced; the induction is the shipped driver's).
ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithPrefixSettledDescentInsufficient.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Brick 1 — the corrected lever + the GRAVEYARD: the `SmithPrefixSettled` gate is FALSE -/

/-- **The corrected lever** — the below-pivot pivot-column magnitude confinement: the fill-in entry
`(pivotIndex+1, pivotIndex)` never exceeds the pivot in magnitude.  On the reachable carrier this holds
with equality (the r36 confinement fill-in `|entry(p+1,p)| = |pivot|`); the r31 refuter violates it
(`4 > 2`).  Strictly sharper than `SmithPrefixSettled`, which says nothing about column `pivotIndex`. -/
def belowPivotColumnConfined (matrix : IntMatrix) (pivotIndex : Nat) : Prop :=
  (matrix.entryAt (pivotIndex + 1) pivotIndex).natAbs ≤ (matrix.diagonalEntryAt pivotIndex).natAbs

/-- **The design's PROPOSED r39 gate** — the raw single-fold `pivotMagnitudeWithin` descent obligation
`SmithFoldDescendsOnNonzeroPivot` (`SmithPivotMagnitudeDescent`, `:258`) additionally guarded by the
SHIPPED confinement invariant `SmithPrefixSettled`.  The r38 footer proposed feeding the descent "by
`SmithPrefixSettled`/reachable states"; this is that proposal made precise.  A `Prop`, refuted below. -/
def SmithFoldDescendsOnPrefixSettledNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    SmithPrefixSettled work pivotIndex height width →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-- **THE GRAVEYARD — the `SmithPrefixSettled` gate is FALSE.**  `SmithPrefixSettled work pivotIndex …` is
VACUOUS at `pivotIndex = 0` (`smithPrefixSettledZero` holds for every matrix), so the r31 counterexample
`[[2,0],[4,3]]` satisfies the gate together with all other preconditions (rectangular, positive pivot
`|2| > 0`, `find = some 1`), yet the fold RAISES the magnitude `2 → 3`
(`smithFoldStepRaisesPivotOnCounterexample`).  The gate therefore fails to exclude the refuter — the same
`[[2,0],[4,3]]` that killed the raw obligation kills the `SmithPrefixSettled`-guarded one.  Machine-checked,
zero axioms; the r38-proposed lever needs the strictly-sharper `belowPivotColumnConfined` (brick 2). -/
theorem smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted :
    ¬ SmithFoldDescendsOnPrefixSettledNonzeroPivot := by
  intro foldDescends
  exact smithFoldStepRaisesPivotOnCounterexample
    (foldDescends smithFoldDescentCounterexample 1 0 2 2
      smithFoldDescentCounterexampleIsRectangular
      (smithPrefixSettledZero smithFoldDescentCounterexample 2 2)
      smithFoldDescentCounterexamplePivotPositive
      smithFoldDescentCounterexampleFindsSome)

/-! ## Brick 2 — the corrected lever SEPARATES the refuter from the reachable driver witness -/

/-- **The corrected guard rejects the r31 refuter.**  `¬ belowPivotColumnConfined [[2,0],[4,3]] 0`: the
below-pivot entry `(1,0) = 4` exceeds the pivot `|2| = 2` in magnitude (`4 ≤ 2` is false).  So where the
vacuous `SmithPrefixSettled` ADMITTED the refuter (brick 1), the confinement lever EXCLUDES it — the
descent-raising shape is out of scope of the corrected candidate. -/
theorem smithConfinedGuardExcludesRefuter :
    ¬ belowPivotColumnConfined smithFoldDescentCounterexample 0 := by
  unfold belowPivotColumnConfined; decide

/-- **The driver-reachable dirty-found-column state SATISFIES the corrected guard.**  On
`smithDirtyFoundColumnDriverWitness` (the pivot-`2` sweep-start state the corrected driver reaches on
`diag(4,6,9,7)`, with `find = some 3` and the NONZERO fill-in `entry(3,2) = -126`;
`smithDirtyFoundColumnIsFindSomeReachable`), the fill-in magnitude equals the pivot magnitude
(`|-126| ≤ |-126|`), so `belowPivotColumnConfined … 2` holds — the reachable carrier is confined even where
the pivot column is dirty. -/
theorem smithDriverWitnessConfined :
    belowPivotColumnConfined smithDirtyFoundColumnDriverWitness 2 := by
  unfold belowPivotColumnConfined; decide

set_option maxRecDepth 100000 in
/-- **The descent CONCLUSION holds on the reachable driver witness.**  On the exact r31 dirty-found-column
obstruction state (`smithDirtyFoundColumnDriverWitness`, pivot `2`, `find = some 3`), which SATISFIES the
corrected confinement guard (`smithDriverWitnessConfined`), the fold strictly DESCENDS
`pivotMagnitudeWithin` `126 → 12`.  So the corrected candidate's conclusion is TRUE precisely where the raw
obligation was refuted (the dirty found column) once the state is confined — evidence the corrected
candidate is TRUE on the reachable carrier; NOT a proof of the universal. -/
theorem smithConfinedFoldDescendsOnDriverWitness :
    pivotMagnitudeWithin (smithClearingFoldStep smithDirtyFoundColumnDriverWitness 3 2 4 4) 2
      < pivotMagnitudeWithin smithDirtyFoundColumnDriverWitness 2 := by decide

/-! ## Brick 3 — the CORRECTED one-round candidate (the trace-table-confirmed statement) -/

/-- **THE CORRECTED r39 candidate** — the `belowPivotColumnConfined`-guarded single-fold
`pivotMagnitudeWithin` descent.  This is the trace-table-confirmed one-round statement: on every confined
nonzero-pivot fold, `pivotMagnitudeWithin` strictly descends.  Unlike the `SmithPrefixSettled` gate (brick
1, refuted) the confinement lever EXCLUDES the r31 refuter (`smithConfinedGuardExcludesRefuter`) and holds
on the reachable dirty-column carrier (`smithDriverWitnessConfined` + `smithConfinedFoldDescendsOnDriverWitness`).
A `Prop`, NOT proved here: its universal proof is the cascade-output-magnitude descent under confinement —
the r40 gcd-ideal arc; the r30 output bound reaches only `|landed| ≤ min-abs entry`, and the gap to `gcd`
is the multi-round Euclid reduction the r31 dirty-found-column obstruction forbids collapsing. -/
def SmithFoldDescendsOnConfinedNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    belowPivotColumnConfined work pivotIndex →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-! ## Brick 4 — the D3 instantiation: the shipped `Nat.rec` driver fixed to the corrected invariant -/

/-- **The D3 instantiation on the corrected confined invariant.**  Instantiates the shipped GUARDED-NODE-D
strong induction `smithClearingSweepReachesFindNoneOfGuardedDescent` (`SmithPivotMagnitudeDescent`, `:295`,
`induction fuel` — the `Nat.rec` strong recursion on the `natAbs` budget, NEVER `WellFounded.fix`) with
`measure := pivotMagnitudeWithin · pivotIndex` and `invariant := ZeroTrailingDiagonalsFrom pivotIndex
height width ∧ belowPivotColumnConfined · pivotIndex`.  The zero-pivot base is discharged inline by brick 4
(`smithZeroPivotImpliesFindNone`, via the zero-trailing conjunct), the budget by `pivotMagnitudeLeMinorAbsSum`.
The clearing sweep output reports find-`none` (fuel-adequacy `K1`) GIVEN: the CORRECTED confined one-round
descent (`foldDescends`, = `SmithFoldDescendsOnConfinedNonzeroPivot` in the driver's shape) and the
confinement + zero-trailing PRESERVATION invariant (`foldKeepsInvariant`) and the terminal-cascade
preservation (`terminalKeepsFindNone`).  These are the r40 handoffs; both open legs are named.  The
`SmithPrefixSettled`-guarded route (brick 1) is refuted, so this confined route is its replacement. -/
theorem smithClearingOutputFindNoneFromConfinedFoldDescent
    (pivotIndex height width : Nat)
    (foldDescends : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
            < pivotMagnitudeWithin work pivotIndex)
    (foldKeepsInvariant : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          (ZeroTrailingDiagonalsFrom pivotIndex height width
              (smithClearingFoldStep work foundPos pivotIndex height width)
            ∧ belowPivotColumnConfined (smithClearingFoldStep work foundPos pivotIndex height width)
                pivotIndex))
    (terminalKeepsFindNone : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (matrix : IntMatrix)
    (baseZeroTrailing : ZeroTrailingDiagonalsFrom pivotIndex height width matrix)
    (baseConfined : belowPivotColumnConfined matrix pivotIndex)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithFindNonDividingLaterDiagonal
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none :=
  smithClearingSweepReachesFindNoneOfGuardedDescent pivotIndex height width
    (fun work => pivotMagnitudeWithin work pivotIndex)
    (fun work => ZeroTrailingDiagonalsFrom pivotIndex height width work
      ∧ belowPivotColumnConfined work pivotIndex)
    (fun work invHolds pivotMag0 =>
      smithZeroPivotImpliesFindNone work pivotIndex height width (invHolds.1 pivotMag0) pivotMag0)
    terminalKeepsFindNone
    foldDescends
    foldKeepsInvariant
    (smithMinorAbsSum matrix pivotIndex height width) matrix ⟨baseZeroTrailing, baseConfined⟩
    isRect pRowLt pColLt
    (pivotMagnitudeLeMinorAbsSum matrix pivotIndex height width pRowLt pColLt)

/-! ## The H2-SMITH r39 ledger — the `SmithPrefixSettled` descent gate is REFUTED; the lever is confinement

**What r39 ships (zero-axiom, additive; the r18–r38 world byte-intact).**  The GRAVEYARD
`smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted`: the r38-proposed descent gate `SmithPrefixSettled`
is machine-FALSE — vacuous at `pivotIndex = 0`, it re-admits the exact r31 refuter `[[2,0],[4,3]]` that
raises `pivotMagnitudeWithin` `2 → 3`.  The corrected lever `belowPivotColumnConfined` (`|entry(p+1,p)| ≤
|pivot|`) is machine-verified to SEPARATE the refuter (`smithConfinedGuardExcludesRefuter`, `4 > 2`) from
the reachable dirty-found-column driver witness (`smithDriverWitnessConfined` + the `126 → 12` descent
`smithConfinedFoldDescendsOnDriverWitness`).  The corrected one-round candidate
`SmithFoldDescendsOnConfinedNonzeroPivot` and the D3 instantiation
`smithClearingOutputFindNoneFromConfinedFoldDescent` (the shipped `Nat.rec` driver fixed to `measure :=
pivotMagnitudeWithin`, `invariant := zero-trailing ∧ confined`, zero-pivot base discharged) complete the
corrected wiring MODULO the two named r40 legs.

**What r39 does NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`.  The corrected fuel-adequacy route now rests on exactly two OPEN r40
legs, both named in `smithClearingOutputFindNoneFromConfinedFoldDescent`:

  1. `SmithFoldDescendsOnConfinedNonzeroPivot` — the confined one-round `pivotMagnitudeWithin` descent (the
     `foldDescends` shape).  The cascade-output-magnitude content; the r30 output bound reaches only
     `|landed| ≤ min-abs entry`, and the gap `min-abs → gcd` is the multi-round Euclid reduction.

  2. the confinement-PRESERVATION invariant — that the fold KEEPS `belowPivotColumnConfined` along the
     sweep (the `foldKeepsInvariant` confined conjunct).  Crucially this is NOT `reachableImpliesPrefixSettled`
     (r36): `SmithPrefixSettled` settles only the prefix `< pivotIndex`, leaving column `pivotIndex` below —
     where the fill-in lives — UNCONSTRAINED.  Establishing the below-pivot-column confinement as a
     reachable-trajectory invariant (and its fold-preservation) is a NEW r40 prerequisite, strictly beyond
     the shipped confinement invariant.

Both feed fuel-adequacy `K1`; the off-diagonal half `K2` (`SmithClearingOutputOffDiagonalDivides`) remains
the standalone gcd-ideal wall, UNCHANGED.  The round-level divisor chain `pivot(n+1) ∣ pivot(n)` stays
machine-REFUTED (`smithFoldDescendsOnNonzeroPivotIsRefuted` + probe); it is NOT stated here and NOT proven.
No descent measure is fabricated; no flip is invented.  The r18–r38 world, `smithReduceComplete`, and the
refutation certificates stay byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra

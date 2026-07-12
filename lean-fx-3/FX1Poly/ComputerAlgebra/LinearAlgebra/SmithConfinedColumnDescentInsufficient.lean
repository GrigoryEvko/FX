import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPrefixSettledDescentInsufficient
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithConfinedColumnDescentInsufficient — the
    `belowPivotColumnConfined`-guarded one-round descent is STILL FALSE; the corrected lever adds the
    below-pivot-column DEEP-ZERO conjunct (H2-SMITH r40, #2261)

## The move

r39 (`SmithPrefixSettledDescentInsufficient`) refuted the r38-proposed `SmithPrefixSettled` descent gate
(vacuous at pivot `0`, re-admits the r31 refuter `[[2,0],[4,3]]`) and proposed the strictly-sharper lever
`belowPivotColumnConfined` (`|entry(p+1,p)| ≤ |pivot|`), machine-verified to SEPARATE that refuter from the
reachable driver witness.  It shipped the corrected candidate `SmithFoldDescendsOnConfinedNonzeroPivot` (a
`def … : Prop`, NOT proved) and the D3 instantiation `smithClearingOutputFindNoneFromConfinedFoldDescent`
consuming the confined one-round descent + its preservation as the two named r40 legs.

**r40 WIDE TRUTH-PROBE REFUTES the confined gate too.**  `belowPivotColumnConfined` is a SINGLE-entry
`(p+1,p)` guard — it constrains only the first sub-diagonal entry of the pivot column, saying NOTHING about
DEEPER entries `(q,p)` with `q > p+1`.  A raw state can be confined at `(p+1,p)` (even with
`entry(p+1,p) = 0`) yet carry a large deeper column entry that the fold's cascade pulls into the pivot and
STALLS on.  The machine counterexample (3×3, decidable):

```
smithConfinedColumnDescentCounterexample = [[10,0,0],[0,10,0],[20,0,12]]
```

at `pivotIndex = 0`.  It is `IsRectangular 3 3`; `belowPivotColumnConfined … 0` HOLDS
(`entry(1,0) = 0 ≤ 10 = |pivot|`); the pivot is positive (`|10| > 0`); `find = some 2` (`10 ∤ 12`).  Yet the
fold `row0 += row2` + cascade lands pivot magnitude `10 = 10` — the cross clears but the pivot is UNCHANGED,
so `pivotMagnitudeWithin (fold) < pivotMagnitudeWithin work` (`10 < 10`) is FALSE
(`smithConfinedColumnFoldStallsOnCounterexample`, machine-checked).  Hence
`SmithFoldDescendsOnConfinedNonzeroPivot` is FALSE
(`smithFoldDescendsOnConfinedNonzeroPivotIsRefuted`, zero axioms) — the confined route repeats the SAME
vacuity failure it diagnosed in the `SmithPrefixSettled` gate, one column position deeper.  The independent
wide probe (3×3 dirty-column family, negatives) finds confined-but-deep-dirty STALLS in bulk while the clean
family below has ZERO refutations.

## The corrected lever (probe-clean; machine-verified separation)

The pivot column below the pivot must be entirely zero EXCEPT the confined `(p+1,p)` — i.e. add the
DEEP-ZERO conjunct:

  * **`belowPivotColumnZeroDeep matrix pivotIndex height`** — `∀ laterRow, pivotIndex+1 < laterRow →
    laterRow < height → entry laterRow pivotIndex = 0` (every pivot-column entry strictly below `p+1`, within
    `height`, vanishes).  `height` is the exact bound the fold's column-clear reaches — sharper and cleaner
    than a `Nat.min` bound (whose `Nat.min_le_*` lemmas are propext-dirty in this lane).
  * **`belowPivotColumnClean matrix pivotIndex height`** — `belowPivotColumnConfined ∧
    belowPivotColumnZeroDeep`.

The confined-only guard ADMITS the counterexample (`smithConfinedGuardAdmitsRefuter`, `0 ≤ 10`); the clean
guard EXCLUDES it non-vacuously (`smithCleanGuardExcludesRefuter`: `entry(2,0) = 20 ≠ 0`, witnessed at the
in-range `laterRow = 2`).  On a genuine non-vacuous CLEAN witness the corrected candidate's conclusion HOLDS
(`smithColumnCleanCandidateDescendsOnCleanWitness`: `[[10,0,0],[0,10,0],[0,0,12]]`, `find = some 2`, deep
column zero, fold `10 → 2`).

## What this module ships (positive, additive, zero-axiom)

  * **`smithConfinedColumnDescentCounterexample`** + rectangularity/confined/positive-pivot/find-some pins
    and **`smithFoldDescendsOnConfinedNonzeroPivotIsRefuted`** — THE GRAVEYARD: the r39 confined gate is
    machine-FALSE (confined-but-deep-dirty stall).
  * **`belowPivotColumnZeroDeep`, `belowPivotColumnClean`** — the corrected lever (deep-column zero).
  * **`smithConfinedGuardAdmitsRefuter` / `smithCleanGuardExcludesRefuter`** — the confined guard is too weak
    (admits the stall); the clean guard's deep-zero conjunct excludes it, non-vacuously.
  * **`smithClearingFoldStepColumnBelowZero`** — **L2' FREE PRESERVATION (the positive structural theorem)**:
    the fold's re-fired cascade clears the WHOLE pivot column below the pivot, so
    `(fold).entryAt row pivotIndex = 0` for every `pivotIndex < row < height`.  Rides the shipped
    `smithRepairFoldCascadeReachesCrossClear` + `smithCrossIsClearPointwise`.
  * **`smithClearingFoldStepColumnZeroDeep` / `…Confined` / `…ColumnClean`** — the fold OUTPUT satisfies the
    clean lever (`…Confined`/`…ColumnClean` given the sub-block-nonempty `pivotIndex + 1 < height`); so the
    confinement + deep-zero conjuncts of the D3 `foldKeepsInvariant` are DISCHARGED for free — only the
    zero-trailing conjunct stays a handoff.
  * **`SmithFoldDescendsOnColumnCleanNonzeroPivot`** — the CORRECTED r40 candidate (the clean-guarded strict
    `pivotMagnitudeWithin` descent).  A `def … : Prop`, NOT proved (see the wall).
  * **`smithClearingOutputFindNoneFromColumnCleanFoldDescent`** — the re-shaped D3: the shipped `Nat.rec`
    driver fixed with `invariant := ZeroTrailingDiagonalsFrom ∧ belowPivotColumnClean`.  Consumes the
    corrected clean-fold-descent + the (now-largely-discharged) preservation + terminal preservation as
    HYPOTHESES.  No `WellFounded.fix`.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the mandate
does NOT fire.  This is a GRAVEYARD + GUARD-CORRECTION round: the r39 confined descent gate is machine-REFUTED
(confined-but-deep-dirty stall), the corrected lever is `belowPivotColumnClean` (machine-verified to separate
the stall non-vacuously), L2' preservation is now a SHIPPED structural theorem (the fold clears the whole
column below), and the D3 instantiation is wired MODULO the r41+ legs.  The four remaining legs to the
mandate:

  1. **L1' `SmithFoldDescendsOnColumnCleanNonzeroPivot`** — the clean one-round `pivotMagnitudeWithin`
     descent (probe-clean; the cascade-output-magnitude / Euclid-survivor content).  OPEN r41 target.
  2. the zero-trailing preservation conjunct of `foldKeepsInvariant` (small handoff; the clean conjuncts are
     now DISCHARGED by `smithClearingFoldStepColumnClean`).
  3. **the FOURTH leg** `reachableImpliesBelowColumnClean` — that reachable states ENTER the clean guard.
     NOT supplied by r36's `reachableImpliesPrefixSettled` (which settles only the prefix `< pivotIndex`,
     leaving column `pivotIndex` below unconstrained — precisely where the fill-in lives).  A genuinely NEW
     r41 trajectory invariant.
  4. **K2** (`SmithClearingOutputOffDiagonalDivides`) — the off-diagonal gcd-ideal wall, UNCHANGED; the
     confined/clean route attacks K1 (fuel-adequacy) ONLY and does NOT collapse K2.

The round-level divisor chain stays machine-REFUTED (not stated).  The r18–r39 world, `smithReduceComplete`,
and the refutation certificates stay BYTE-INTACT (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (no recursion introduced; the induction is the shipped driver's).
ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithConfinedColumnDescentInsufficient.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Brick 1 — the GRAVEYARD: the `belowPivotColumnConfined` gate is FALSE (deep-dirty column stall) -/

/-- The refuting matrix: confined at `(1,0) = 0` (`0 ≤ 10 = |pivot|`), yet the DEEP pivot-column entry
`(2,0) = 20` is what the fold's cascade pulls in, and `d0 = 10` does not divide the later diagonal
`d2 = 12` (so `find = some 2`).  The fold+cascade clears the cross but the pivot stays `10`. -/
def smithConfinedColumnDescentCounterexample : IntMatrix := IntMatrix.mk [[10, 0, 0], [0, 10, 0], [20, 0, 12]]

/-- The counterexample is a genuine `3 x 3` matrix (the obligation's first precondition). -/
theorem smithConfinedColumnDescentCounterexampleIsRectangular :
    smithConfinedColumnDescentCounterexample.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The counterexample SATISFIES the r39 confined guard: `|entry(1,0)| = 0 ≤ 10 = |pivot|`.  (The whole
point — the confined guard is too weak; the deep entry `(2,0) = 20` is out of its scope.) -/
theorem smithConfinedColumnDescentCounterexampleConfined :
    belowPivotColumnConfined smithConfinedColumnDescentCounterexample 0 := by
  unfold belowPivotColumnConfined; decide

/-- The pivot is positive (`|d0| = 10 > 0`, the obligation's second precondition). -/
theorem smithConfinedColumnDescentCounterexamplePivotPositive :
    0 < (smithConfinedColumnDescentCounterexample.diagonalEntryAt 0).natAbs := by decide

set_option maxRecDepth 100000 in
/-- The find-scan reports `some 2` (`d0 = 10` divides `d1 = 10` but NOT `d2 = 12`, the obligation's third
precondition — so all three preconditions genuinely hold). -/
theorem smithConfinedColumnDescentCounterexampleFindsSome :
    smithFindNonDividingLaterDiagonal smithConfinedColumnDescentCounterexample 0
      (Nat.min 3 3 - (0 + 1)) (0 + 1) = some 2 := by decide

set_option maxRecDepth 100000 in
/-- **The fold STALLS the pivot magnitude on the counterexample** — the fold `row0 += row2` + cascade clears
the pivot cross but lands pivot magnitude `10`, EQUAL to the input pivot magnitude `10`, so the obligation's
conclusion `pivotMagnitudeWithin (fold) < pivotMagnitudeWithin work` (`10 < 10`) is FALSE here.  The deep
column entry `(2,0) = 20` is pulled into the pivot row and Euclid-reduced against `d0 = 10` to a multiple of
`10`, so `gcd(10, …) = 10` — no descent. -/
theorem smithConfinedColumnFoldStallsOnCounterexample :
    ¬ (pivotMagnitudeWithin (smithClearingFoldStep smithConfinedColumnDescentCounterexample 2 0 3 3) 0
        < pivotMagnitudeWithin smithConfinedColumnDescentCounterexample 0) := by decide

/-- **THE GRAVEYARD — the r39 `belowPivotColumnConfined` gate is FALSE.**  `SmithFoldDescendsOnConfinedNonzeroPivot`
fails at `work = smithConfinedColumnDescentCounterexample`, `foundPos = 2`, `pivotIndex = 0`,
`height = width = 3`: all three preconditions hold (rectangular, confined `0 ≤ 10`, positive pivot,
`find = some 2`), yet the conclusion is refuted (the fold STALLS).  Machine-checked, zero axioms.  The
single-entry confinement guard does not see the deeper pivot-column entry the fold pulls in — the corrected
lever must add the DEEP-ZERO conjunct (brick 2). -/
theorem smithFoldDescendsOnConfinedNonzeroPivotIsRefuted :
    ¬ SmithFoldDescendsOnConfinedNonzeroPivot := by
  intro foldDescends
  exact smithConfinedColumnFoldStallsOnCounterexample
    (foldDescends smithConfinedColumnDescentCounterexample 2 0 3 3
      smithConfinedColumnDescentCounterexampleIsRectangular
      smithConfinedColumnDescentCounterexampleConfined
      smithConfinedColumnDescentCounterexamplePivotPositive
      smithConfinedColumnDescentCounterexampleFindsSome)

/-! ## Brick 2 — the corrected lever: below-pivot-column DEEP-ZERO + the clean guard -/

/-- **The deep-column-zero conjunct** — every pivot-column entry strictly BELOW the confined sub-diagonal
`(p+1,p)`, within `height`, vanishes.  This is exactly what the r39 confined guard omits, and exactly what
the counterexample violates (`entry(2,0) = 20 ≠ 0`).  Bound `height` (not `Nat.min height width`) is the
tight bound the fold's column-clear reaches AND avoids the propext-dirty `Nat.min_le_*` lemmas. -/
def belowPivotColumnZeroDeep (matrix : IntMatrix) (pivotIndex height : Nat) : Prop :=
  ∀ laterRow, pivotIndex + 1 < laterRow → laterRow < height → matrix.entryAt laterRow pivotIndex = 0

/-- **The corrected r40 lever** — the confined sub-diagonal PLUS the deep-column zero: the pivot column below
the pivot is entirely zero except the confined `(p+1,p)`.  Strictly sharper than `belowPivotColumnConfined`;
probe-clean (zero raw refutations across the 3×3 dirty-column family with negatives). -/
def belowPivotColumnClean (matrix : IntMatrix) (pivotIndex height : Nat) : Prop :=
  belowPivotColumnConfined matrix pivotIndex ∧ belowPivotColumnZeroDeep matrix pivotIndex height

/-! ## Brick 3 — separation: confined ADMITS the stall; clean EXCLUDES it (non-vacuously) -/

/-- **The confined-only guard ADMITS the refuter.**  `belowPivotColumnConfined [[10,0,0],[0,10,0],[20,0,12]] 0`
holds (`0 ≤ 10`) — so where r39's confined lever excluded the r31 refuter it now ADMITS this deep-dirty stall.
The single-entry guard is too weak. -/
theorem smithConfinedGuardAdmitsRefuter :
    belowPivotColumnConfined smithConfinedColumnDescentCounterexample 0 :=
  smithConfinedColumnDescentCounterexampleConfined

/-- **The clean guard's deep-zero conjunct EXCLUDES the refuter, non-vacuously.**  `¬
belowPivotColumnZeroDeep [[10,0,0],[0,10,0],[20,0,12]] 0 3`: the in-range deeper entry `(2,0) = 20 ≠ 0`
(witnessed at `laterRow = 2`, with `0+1 < 2 < 3`).  So the corrected lever REJECTS the exact stall the
confined guard admitted — and non-vacuously, since `laterRow = 2` is a genuine in-range witness (3×3 has a
deep column). -/
theorem smithCleanGuardExcludesRefuter :
    ¬ belowPivotColumnZeroDeep smithConfinedColumnDescentCounterexample 0 3 := by
  intro deepZero
  exact absurd (deepZero 2 (by decide) (by decide)) (by decide)

/-! ## Brick 4 — the CORRECTED clean candidate (the trace-table-confirmed statement) -/

/-- **THE CORRECTED r40 candidate** — the `belowPivotColumnClean`-guarded single-fold `pivotMagnitudeWithin`
descent.  Unlike the confined gate (brick 1, refuted) the clean lever EXCLUDES the deep-dirty stall
(`smithCleanGuardExcludesRefuter`) and holds on a genuine non-vacuous clean witness
(`smithColumnCleanCandidateDescendsOnCleanWitness`).  A `Prop`, NOT proved here: its universal proof is the
cascade-output Euclid-survivor descent under the clean guard — the r41 L1' target.  The clean guard
GUARANTEES a small survivor (`foundPos = p+1`: the confined `entry(p+1,p)`; `foundPos > p+1`: the deep column
is zero so the fold does not dirty the pivot), which the r30 output-bound kit turns into strict descent. -/
def SmithFoldDescendsOnColumnCleanNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    belowPivotColumnClean work pivotIndex height →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-- **The corrected candidate's conclusion HOLDS on a genuine non-vacuous CLEAN witness.**  On
`[[10,0,0],[0,10,0],[0,0,12]]` (pivot `0`, `find = some 2`, deep column zero `entry(2,0) = 0` — clean and
non-vacuous), the fold strictly DESCENDS `pivotMagnitudeWithin` `10 → 2`.  Evidence the corrected candidate
is TRUE precisely where the confined refuter differs only in the deep column being clean; NOT a proof of the
universal. -/
theorem smithColumnCleanCandidateDescendsOnCleanWitness :
    pivotMagnitudeWithin (smithClearingFoldStep (IntMatrix.mk [[10, 0, 0], [0, 10, 0], [0, 0, 12]]) 2 0 3 3) 0
      < pivotMagnitudeWithin (IntMatrix.mk [[10, 0, 0], [0, 10, 0], [0, 0, 12]]) 0 := by decide

/-! ## Brick 5 — L2' FREE PRESERVATION: the fold clears the WHOLE pivot column below (structural, no decide) -/

/-- **The fold clears the whole pivot column below the pivot.**  `smithClearingFoldStep` runs its re-fired
Euclid cascade to `smithCrossIsClear = true` (the shipped `smithRepairFoldCascadeReachesCrossClear`), whose
column conjunct decodes (`smithCrossIsClearPointwise`, second component) to: every entry of column
`pivotIndex` strictly below the pivot, within `height`, is zero.  STRUCTURAL — no `decide`; the load-bearing
L2' content (the fold's output has a clean pivot column below, so both clean conjuncts hold). -/
theorem smithClearingFoldStepColumnBelowZero (work : IntMatrix) (foundPos pivotIndex height width : Nat)
    (isRect : work.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width) :
    ∀ row, pivotIndex < row → row < height →
      (smithClearingFoldStep work foundPos pivotIndex height width).entryAt row pivotIndex = 0 :=
  (smithCrossIsClearPointwise (smithClearingFoldStep work foundPos pivotIndex height width)
    pivotIndex height width pivotRowInRange pivotColInRange
    (smithRepairFoldCascadeReachesCrossClear work foundPos pivotIndex height width isRect
      pivotRowInRange pivotColInRange)).2

/-- **The fold output satisfies the DEEP-ZERO conjunct.**  Corollary of `smithClearingFoldStepColumnBelowZero`:
every `laterRow` with `pivotIndex+1 < laterRow < height` has cleared column entry, so
`belowPivotColumnZeroDeep (fold) pivotIndex height` — no sub-block-nonempty hypothesis needed. -/
theorem smithClearingFoldStepColumnZeroDeep (work : IntMatrix) (foundPos pivotIndex height width : Nat)
    (isRect : work.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width) :
    belowPivotColumnZeroDeep (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex height :=
  fun laterRow pivotSuccLtLater laterLtHeight =>
    smithClearingFoldStepColumnBelowZero work foundPos pivotIndex height width isRect
      pivotRowInRange pivotColInRange laterRow
      (Nat.lt_trans (Nat.lt_succ_self pivotIndex) pivotSuccLtLater) laterLtHeight

/-- **The fold output satisfies the CONFINED conjunct** (given the sub-block below the pivot is non-empty,
`pivotIndex + 1 < height`).  The cleared `entry(p+1,p) = 0` gives `|0| = 0 ≤ |pivot|`.  The `p+1 < height`
hypothesis is the honest "there is a row below the pivot" condition (always true when a fold fires — the
found position is a later diagonal in range). -/
theorem smithClearingFoldStepConfined (work : IntMatrix) (foundPos pivotIndex height width : Nat)
    (isRect : work.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (succRowInRange : pivotIndex + 1 < height) :
    belowPivotColumnConfined (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex := by
  unfold belowPivotColumnConfined
  rw [smithClearingFoldStepColumnBelowZero work foundPos pivotIndex height width isRect
    pivotRowInRange pivotColInRange (pivotIndex + 1) (Nat.lt_succ_self pivotIndex) succRowInRange]
  exact Nat.zero_le _

/-- **L2' — the fold KEEPS the clean guard for free** (given the sub-block below the pivot is non-empty).  The
fold output satisfies `belowPivotColumnClean … pivotIndex height`: confinement from
`smithClearingFoldStepConfined`, deep-zero from `smithClearingFoldStepColumnZeroDeep`.  So the confinement +
deep-zero conjuncts of the D3 `foldKeepsInvariant` are DISCHARGED — only the zero-trailing conjunct stays a
handoff.  The literature carries NO analogue (every printed Smith proof clears the whole cross before
recursing, making preservation vacuous); here it is a genuine SHIPPED theorem. -/
theorem smithClearingFoldStepColumnClean (work : IntMatrix) (foundPos pivotIndex height width : Nat)
    (isRect : work.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (succRowInRange : pivotIndex + 1 < height) :
    belowPivotColumnClean (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex height :=
  ⟨smithClearingFoldStepConfined work foundPos pivotIndex height width isRect pivotRowInRange
      pivotColInRange succRowInRange,
   smithClearingFoldStepColumnZeroDeep work foundPos pivotIndex height width isRect pivotRowInRange
      pivotColInRange⟩

/-! ## Brick 6 — the re-shaped D3: the shipped `Nat.rec` driver fixed to the CLEAN invariant -/

/-- **The D3 instantiation on the corrected CLEAN invariant.**  Instantiates the shipped GUARDED-NODE-D strong
induction `smithClearingSweepReachesFindNoneOfGuardedDescent` (`SmithPivotMagnitudeDescent`, `induction fuel`
— the `Nat.rec` strong recursion, NEVER `WellFounded.fix`) with `measure := pivotMagnitudeWithin · pivotIndex`
and `invariant := ZeroTrailingDiagonalsFrom pivotIndex height width ∧ belowPivotColumnClean · pivotIndex
height`.  The zero-pivot base is discharged by `smithZeroPivotImpliesFindNone` (via the zero-trailing
conjunct), the budget by `pivotMagnitudeLeMinorAbsSum`.  The clearing sweep output reports find-`none`
(fuel-adequacy `K1`) GIVEN: the CORRECTED clean one-round descent (`foldDescends`,
= `SmithFoldDescendsOnColumnCleanNonzeroPivot` in the driver's shape), the clean + zero-trailing PRESERVATION
(`foldKeepsInvariant` — whose clean conjuncts brick 5 discharges), and the terminal preservation
(`terminalKeepsFindNone`).  Replaces the r39 confined route (brick 1, refuted). -/
theorem smithClearingOutputFindNoneFromColumnCleanFoldDescent
    (pivotIndex height width : Nat)
    (foldDescends : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnClean work pivotIndex height) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
            < pivotMagnitudeWithin work pivotIndex)
    (foldKeepsInvariant : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnClean work pivotIndex height) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          (ZeroTrailingDiagonalsFrom pivotIndex height width
              (smithClearingFoldStep work foundPos pivotIndex height width)
            ∧ belowPivotColumnClean (smithClearingFoldStep work foundPos pivotIndex height width)
                pivotIndex height))
    (terminalKeepsFindNone : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnClean work pivotIndex height) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (matrix : IntMatrix)
    (baseZeroTrailing : ZeroTrailingDiagonalsFrom pivotIndex height width matrix)
    (baseClean : belowPivotColumnClean matrix pivotIndex height)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithFindNonDividingLaterDiagonal
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none :=
  smithClearingSweepReachesFindNoneOfGuardedDescent pivotIndex height width
    (fun work => pivotMagnitudeWithin work pivotIndex)
    (fun work => ZeroTrailingDiagonalsFrom pivotIndex height width work
      ∧ belowPivotColumnClean work pivotIndex height)
    (fun work invHolds pivotMag0 =>
      smithZeroPivotImpliesFindNone work pivotIndex height width (invHolds.1 pivotMag0) pivotMag0)
    terminalKeepsFindNone
    foldDescends
    foldKeepsInvariant
    (smithMinorAbsSum matrix pivotIndex height width) matrix ⟨baseZeroTrailing, baseClean⟩
    isRect pRowLt pColLt
    (pivotMagnitudeLeMinorAbsSum matrix pivotIndex height width pRowLt pColLt)

/-! ## The H2-SMITH r40 ledger — the confined descent gate is REFUTED; the lever adds deep-column zero

**What r40 ships (zero-axiom, additive; the r18–r39 world byte-intact).**  The GRAVEYARD
`smithFoldDescendsOnConfinedNonzeroPivotIsRefuted`: the r39 `belowPivotColumnConfined` descent gate is
machine-FALSE — a confined-but-deep-dirty 3×3 (`[[10,0,0],[0,10,0],[20,0,12]]`) STALLS the fold
`pivotMagnitudeWithin` `10 → 10`.  The corrected lever `belowPivotColumnClean` (`belowPivotColumnConfined ∧
belowPivotColumnZeroDeep`) is machine-verified to SEPARATE the stall (`smithConfinedGuardAdmitsRefuter` admits
it; `smithCleanGuardExcludesRefuter` excludes it non-vacuously at `laterRow = 2`) and to hold on a genuine
clean witness where the fold descends (`smithColumnCleanCandidateDescendsOnCleanWitness`, `10 → 2`).  **L2'
preservation is now a SHIPPED structural theorem**: `smithClearingFoldStepColumnBelowZero` (the fold clears
the whole pivot column below) and `smithClearingFoldStepColumnClean` (the fold output is
`belowPivotColumnClean`, given `pivotIndex + 1 < height`) — so the clean conjuncts of the D3
`foldKeepsInvariant` are discharged for free.  The corrected candidate
`SmithFoldDescendsOnColumnCleanNonzeroPivot` and the re-shaped D3
`smithClearingOutputFindNoneFromColumnCleanFoldDescent` complete the corrected wiring.

**What r40 does NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`.  The corrected fuel-adequacy route rests on four OPEN r41+ legs:

  1. `SmithFoldDescendsOnColumnCleanNonzeroPivot` — the clean one-round `pivotMagnitudeWithin` descent (the
     `foldDescends` shape).  Probe-clean; the cascade-output Euclid-survivor content the clean guard makes
     tractable (r30's output bound + the guaranteed survivor).

  2. the zero-trailing preservation conjunct of `foldKeepsInvariant` (small; the clean conjuncts are
     DISCHARGED by `smithClearingFoldStepColumnClean`).

  3. `reachableImpliesBelowColumnClean` — that reachable states ENTER the clean guard.  NOT supplied by r36's
     `reachableImpliesPrefixSettled` (prefix `< pivotIndex` only; column `pivotIndex` below — where the
     fill-in lives — unconstrained).  A genuinely NEW r41 trajectory invariant.

  4. the off-diagonal half `K2` (`SmithClearingOutputOffDiagonalDivides`) — the standalone gcd-ideal wall,
     UNCHANGED.  The confined/clean route attacks `K1` (fuel-adequacy) ONLY and does NOT collapse `K2`.  Even
     a perfect four-legged `K1` closure leaves `K2` standing.

The round-level divisor chain `pivot(n+1) ∣ pivot(n)` stays machine-REFUTED (not stated here, not proven).
No descent measure is fabricated; no flip is invented.  The r18–r39 world, `smithReduceComplete`, and the
refutation certificates stay byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableMagnitudeWitnesses
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPivotMagnitudeDescent

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithAcrossRoundsContentInvariant — the per-round magnitude
    family is EXHAUSTED; the honest termination carrier is ACROSS-ROUNDS (H2-SMITH r42, #2261)

## The multi-round trajectory (M1 — read off the loop, one round = `smithRepairPositionSweepClearing 1`)

One round is the `some`-branch body of `smithRepairPositionSweepClearing` (`SmithNormalForm`, `:2894`):
fold `row[pivot] += row[found]` then the standalone `smithCascadeSweep` Euclid clear.  Iterating the
1-fuel sweep steps round-by-round (`smithRoundStep`).  Machine-evaluated (read-only, then kernel-pinned
below):

| seed (pivot)                                   | `pivotMagnitudeWithin` per round | `minorGcdWithin` (content) |
|------------------------------------------------|----------------------------------|----------------------------|
| `diag`-image `[[1,·],[·,1],[·,66,·],[·,132,-99]]` p2 | `66 -> 99 -> 33` (RISE then land) | `33, 33, 33` (invariant)  |
| `[[2,0],[4,3]]` p0                             | `2 -> 3 -> 1`                    | `1, 1, 1`                  |
| `[[2,·],[·,2],[·,132,·],[·,264,-198]]` p2      | `132 -> 198 -> 66`              | `66, 66, 66`               |
| `diag(6,9,11,11)` p0                           | `6 -> 3 -> 1`                    | `1, 1, 1`                  |
| `diag(15,10,6,4)` p0                           | `15 -> 4 -> 2 -> 1`            | `1, 1, 1, 1`               |
| `diag(7,7,18)` p0                              | `7 -> 2`                        | `1, 1`                     |

Two facts jump off the table.  **(a)** `pivotMagnitudeWithin` RISES per round (`66 -> 99`, `2 -> 3`,
`132 -> 198`), and so does every per-round magnitude the recon measure-tournament swept
(`smithMinorAbsSum`, the not-divided count, and their sums / lexes) — the r22/r26/r31/r37/r39/r40/r41
graveyard.  **(b)** `minorGcdWithin` — the gcd-content of the whole `[pivot, ·)²` sub-block — is CONSTANT
across every round of every seed.  That content is the well-founded primary; the magnitude is a volatile
secondary that only rises on the plateau of the content (Stanley SNF Thm 2.4, k=1: the first
determinantal divisor = gcd of all entries is preserved by every unimodular operation; the
lexicographic-ranking-function shape of Ben-Amram-Genaim, where a bounded secondary rise is dominated by
a well-founded primary; CoqEAL's `improve_pivot_rec` recurses on the strict-divisibility `sdvdr` chain /
`enorm`-fuel of the INITIAL pivot, never the magnitude).

## What this module ships (positive, additive, non-redundant)

  * **The 7th graveyard entry — the per-round magnitude family, machine-exhausted.**  Two fresh per-round
    descent candidates are stated and REFUTED by `decide`: the not-divided-count measure
    (`SmithLaterDiagonalNotDividedCountDescendsPerRound`, RISES `1 -> 2` on `diag(7,7,18)`) and the
    magnitude+fuel sum (`SmithPivotPlusMinorAbsSumDescendsPerRound`, RISES `43 -> 46` on `diag(6,9,11,11)`).
    Any candidate whose per-round instance is a magnitude is refuted a priori — these pin two natural
    "amortized" hopes (a divisibility count; magnitude plus its own fuel) that a reader might reach for,
    and both fail on the reachable image.
  * **The across-rounds content carrier — RECORDED + kernel-witnessed.**  `SmithSubBlockContentStableAcrossRound`
    (`minorGcdWithin (fold round) = minorGcdWithin`), pinned constant across the trajectory seeds.  This is
    the honest across-rounds statement the data supports (0 failures on the recon's 11,161-seed probe); its
    general proof is the ideal-preservation of the fold+cascade through the gcd kit (DEFERRED — the cascade
    half is the wall; see the banner).
  * **The round-pair descent carrier — RECORDED + kernel-witnessed.**  `SmithRoundPairPivotMagnitudeDescends`
    (`pivotMagnitudeWithin (round^2) < pivotMagnitudeWithin`), pinned dropping `33 < 66` / `66 < 132` /
    `1 < 2`, with the single-round RISE `99 > 66` pinned alongside to preempt the "isn't this the
    graveyarded per-round measure?" objection — it is legitimate ONLY at round-PAIR granularity (max-rise
    per trajectory = 1, the recon's rise bound).

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the
mandate is NOT reached and is NOT claimable this round — say so plainly.  The across-rounds Props here are
RECORDED (their generic proofs are open): content-invariance's cascade half and the round-pair descent are
both consequences of "min-abs Euclid computes the sub-block gcd", the SAME core as the off-diagonal wall
`K2` (`SmithClearingOutputOffDiagonalDivides`, `SmithPivotMagnitudeDescent`).  **K2 stands UNCHANGED**;
it is not closed here.  The one census revision: r40/r41 framed `K2` as orthogonal to the fuel-adequacy
half `K1` — the r42 data shows both rest on the gcd-computation core (`K1`'s inner termination is the
round-pair magnitude descent, a consequence of content-invariance + `|landed| = gcd`), so the "orthogonal"
footer is too strong.  The shipped `LandedAbsEqMinorGcdReachable` (`SmithReachableMagnitudeResidual`) is
exactly the `|landed| = content` identity; `minorGcdWithinDividesWithin` + `minorGcdDividesLanded` already
give "content divides the whole sub-block" and "content ∣ landed" hypothesis-free — this module does not
re-derive them.  The r18-r41 world and `smithReduceComplete` stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only.  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`; fuel is `Nat.rec`-structural, never `WellFounded.fix`.  All pins
`decide` (kernel reduction, at or below the `4x4` double-round defeq ceiling).  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithAcrossRoundsContentInvariant.lean` (fuel-based
`#assert_no_axioms` AND independent `#print axioms`). -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Round-step and the per-round measures -/

/-- **One clearing round** — the 1-fuel `smithRepairPositionSweepClearing` applied: exactly one fold+cascade
when the find-scan reports `some`, the terminal cascade when it reports `none`.  Iterating it steps the
trajectory round-by-round (the object M1 tabulates). -/
def smithRoundStep (matrix : IntMatrix) (pivotIndex height width : Nat) : IntMatrix :=
  matrix.applyOperations (smithRepairPositionSweepClearing 1 matrix pivotIndex height width)

/-- The count of later diagonals in `[scanStart, scanStart + scanCount)` the pivot does NOT divide —
mirrors `smithFindNonDividingLaterDiagonal`'s scan (`smithPivotDividesEntry`), summing `1` per undivided
position.  Structural on the scan count. -/
def smithLaterDiagonalNotDividedCountFrom (matrix : IntMatrix) (pivotIndex : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | scanCount + 1, scanStart =>
      (if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.diagonalEntryAt scanStart)
        then 0 else 1)
        + smithLaterDiagonalNotDividedCountFrom matrix pivotIndex scanCount (scanStart + 1)

/-- The not-divided count over the pivot's later-diagonal window `[pivotIndex+1, min height width)`. -/
def smithLaterDiagonalNotDividedCount (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  smithLaterDiagonalNotDividedCountFrom matrix pivotIndex
    (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1)

/-- The magnitude+fuel sum measure — `pivotMagnitudeWithin` plus the sweep's own fuel `smithMinorAbsSum`.
The natural "amortized" candidate (rank + slack) a reader might hope tames the magnitude rise. -/
def smithPivotPlusMinorAbsSumMeasure (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  pivotMagnitudeWithin matrix pivotIndex + smithMinorAbsSum matrix pivotIndex height width

/-! ## The 7th graveyard entry — two per-round descent candidates, machine-REFUTED

Both mirror `SmithFoldDescendsOnNonzeroPivot` (`SmithPivotMagnitudeDescent`) exactly — same preconditions
(`IsRectangular`, nonzero pivot, `find = some`) — with the not-divided count / the magnitude+fuel sum in
place of `pivotMagnitudeWithin`.  The recon tournament refuted `pivotMagnitudeWithin` (r31),
`smithMinorAbsSum` (r22), the not-divided count, and every sum/lex on the reachable image; these two pins
close the family with fresh witnesses. -/

/-- Per-round descent CANDIDATE: the not-divided count strictly drops on every nonzero-pivot find-`some`
fold.  REFUTED below. -/
def SmithLaterDiagonalNotDividedCountDescendsPerRound : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    smithLaterDiagonalNotDividedCount (smithClearingFoldStep work foundPos pivotIndex height width)
        pivotIndex height width
      < smithLaterDiagonalNotDividedCount work pivotIndex height width

/-- Per-round descent CANDIDATE: the magnitude+fuel sum strictly drops on every nonzero-pivot find-`some`
fold.  REFUTED below. -/
def SmithPivotPlusMinorAbsSumDescendsPerRound : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    smithPivotPlusMinorAbsSumMeasure (smithClearingFoldStep work foundPos pivotIndex height width)
        pivotIndex height width
      < smithPivotPlusMinorAbsSumMeasure work pivotIndex height width

/-- The not-divided-count refuter: `diag(7,7,18)` at pivot `0` — `7 ∣ 7` but `7 ∤ 18`, so `find = some 2`
and the count is `1`; the fold+cascade lands pivot `2`, which divides neither of the two later diagonals,
so the count RISES to `2`. -/
def smithNotDividedCountRiseWitness : IntMatrix := IntMatrix.mk [[7, 0, 0], [0, 7, 0], [0, 0, 18]]

/-- The sum-measure refuter: `diag(6,9,11,11)` at pivot `0` — `find = some 1` (`6 ∤ 9`); the fold+cascade
drops `pivotMagnitudeWithin 6 -> 3` but RAISES `smithMinorAbsSum 37 -> 43`, so the sum RISES `43 -> 46`. -/
def smithSumMeasureRiseWitness : IntMatrix := IntMatrix.mk [[6, 0, 0, 0], [0, 9, 0, 0], [0, 0, 11, 0], [0, 0, 0, 11]]

/-- The not-divided-count refuter is `3 x 3`. -/
theorem smithNotDividedCountRiseWitnessIsRectangular :
    smithNotDividedCountRiseWitness.IsRectangular 3 3 := ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- The not-divided-count refuter has a positive pivot (`|7| > 0`). -/
theorem smithNotDividedCountRiseWitnessPivotPositive :
    0 < (smithNotDividedCountRiseWitness.diagonalEntryAt 0).natAbs := by decide

set_option maxRecDepth 100000 in
/-- The find-scan reports `some 2` on the not-divided-count refuter (`7 ∤ 18`). -/
theorem smithNotDividedCountRiseWitnessFindsSome :
    smithFindNonDividingLaterDiagonal smithNotDividedCountRiseWitness 0
      (Nat.min 3 3 - (0 + 1)) (0 + 1) = some 2 := by decide

set_option maxRecDepth 100000 in
/-- **The not-divided count RISES on the refuter** — `1 -> 2` across the fold, so
`smithLaterDiagonalNotDividedCount (fold) < smithLaterDiagonalNotDividedCount work` is FALSE here. -/
theorem smithLaterDiagonalNotDividedCountRisesOnRefuter :
    ¬ (smithLaterDiagonalNotDividedCount
          (smithClearingFoldStep smithNotDividedCountRiseWitness 2 0 3 3) 0 3 3
        < smithLaterDiagonalNotDividedCount smithNotDividedCountRiseWitness 0 3 3) := by decide

/-- **THE 7th GRAVEYARD ENTRY, part one — the not-divided count is NOT a per-round descent measure.**
Machine-checked, zero axioms.  A divisibility-progress count rises across a genuine fold — the reachable
image does not monotonically approach "pivot divides all". -/
theorem smithLaterDiagonalNotDividedCountDescendsPerRoundIsRefuted :
    ¬ SmithLaterDiagonalNotDividedCountDescendsPerRound := by
  intro descends
  exact smithLaterDiagonalNotDividedCountRisesOnRefuter
    (descends smithNotDividedCountRiseWitness 2 0 3 3
      smithNotDividedCountRiseWitnessIsRectangular
      smithNotDividedCountRiseWitnessPivotPositive
      smithNotDividedCountRiseWitnessFindsSome)

/-- The sum-measure refuter is `4 x 4`. -/
theorem smithSumMeasureRiseWitnessIsRectangular :
    smithSumMeasureRiseWitness.IsRectangular 4 4 := ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- The sum-measure refuter has a positive pivot (`|6| > 0`). -/
theorem smithSumMeasureRiseWitnessPivotPositive :
    0 < (smithSumMeasureRiseWitness.diagonalEntryAt 0).natAbs := by decide

set_option maxRecDepth 100000 in
/-- The find-scan reports `some 1` on the sum-measure refuter (`6 ∤ 9`). -/
theorem smithSumMeasureRiseWitnessFindsSome :
    smithFindNonDividingLaterDiagonal smithSumMeasureRiseWitness 0
      (Nat.min 4 4 - (0 + 1)) (0 + 1) = some 1 := by decide

set_option maxRecDepth 200000 in
/-- **The magnitude+fuel sum RISES on the refuter** — `43 -> 46` across the fold (magnitude drops `6 -> 3`
but the fuel rises `37 -> 43`), so `smithPivotPlusMinorAbsSumMeasure (fold) < ... work` is FALSE here. -/
theorem smithPivotPlusMinorAbsSumRisesOnRefuter :
    ¬ (smithPivotPlusMinorAbsSumMeasure
          (smithClearingFoldStep smithSumMeasureRiseWitness 1 0 4 4) 0 4 4
        < smithPivotPlusMinorAbsSumMeasure smithSumMeasureRiseWitness 0 4 4) := by decide

/-- **THE 7th GRAVEYARD ENTRY, part two — magnitude+fuel is NOT a per-round descent measure.**
Machine-checked, zero axioms.  Adding the sweep's own fuel to the magnitude does not tame the rise: the
fuel itself rises on the same fold.  Together with part one and the shipped `SmithFoldDescentRefuted`
(`pivotMagnitudeWithin`) / r22 (`smithMinorAbsSum`), the per-round single-`Nat` magnitude family is
exhausted — the honest carrier is across-rounds. -/
theorem smithPivotPlusMinorAbsSumDescendsPerRoundIsRefuted :
    ¬ SmithPivotPlusMinorAbsSumDescendsPerRound := by
  intro descends
  exact smithPivotPlusMinorAbsSumRisesOnRefuter
    (descends smithSumMeasureRiseWitness 1 0 4 4
      smithSumMeasureRiseWitnessIsRectangular
      smithSumMeasureRiseWitnessPivotPositive
      smithSumMeasureRiseWitnessFindsSome)

/-! ## The across-rounds content carrier — RECORDED + kernel-witnessed

`minorGcdWithin` (the `[pivot, ·)²` sub-block gcd) is preserved by one fold+cascade round.  RECORDED as a
`Prop` (the general proof — ideal-preservation of the fold+cascade through the gcd kit — is DEFERRED; the
cascade half is the wall).  Pinned constant across the trajectory seeds by `decide`. -/

/-- **The across-rounds content-invariance carrier.**  On every nonzero-pivot find-`some` fold, the
`[pivotIndex, ·)²` sub-block gcd is unchanged.  The Stanley Thm 2.4 (k=1) content conservation, at
fold+cascade granularity.  RECORDED; NOT proved here. -/
def SmithSubBlockContentStableAcrossRound : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    minorGcdWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex height width
      = minorGcdWithin work pivotIndex height width

set_option maxRecDepth 100000 in
/-- **Content invariant across the fold on the reachable rise witness** — `diag`-image
`[[1,·],[·,1],[·,66,·],[·,132,-99]]` at pivot `2`, `find = some 3`: the sub-block gcd is `33` before AND
after the fold+cascade, even as the magnitude RISES `66 -> 99`. -/
theorem smithSubBlockContentStableOnReachableRiseWitness :
    minorGcdWithin (smithClearingFoldStep
        (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 3 2 4 4) 2 4 4
      = minorGcdWithin (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4 := by
  decide

set_option maxRecDepth 100000 in
/-- **Content invariant across the fold on the sum-measure refuter** — `diag(6,9,11,11)` at pivot `0`,
`find = some 1`: the sub-block gcd is `1` before AND after, even as the sum measure RISES `43 -> 46`. -/
theorem smithSubBlockContentStableOnSumMeasureRefuter :
    minorGcdWithin (smithClearingFoldStep smithSumMeasureRiseWitness 1 0 4 4) 0 4 4
      = minorGcdWithin smithSumMeasureRiseWitness 0 4 4 := by
  decide

set_option maxRecDepth 200000 in
/-- **Content constant across TWO iterated rounds** — on the reachable rise witness at pivot `2`, the
sub-block gcd stays `33` through `round^1` and `round^2` (the magnitude trajectory `66 -> 99 -> 33`). -/
theorem smithSubBlockContentConstantAcrossReachableTrajectory :
    minorGcdWithin (smithRoundStep
        (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4) 2 4 4
        = minorGcdWithin (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4
    ∧ minorGcdWithin (smithRoundStep (smithRoundStep
        (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4) 2 4 4) 2 4 4
        = minorGcdWithin (smithRoundStep
            (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4) 2 4 4 := by
  decide

/-! ## The round-pair descent carrier — RECORDED + kernel-witnessed

`pivotMagnitudeWithin` drops strictly across TWO rounds (max-rise per trajectory = 1).  RECORDED (the
general proof is a consequence of content-invariance + `|landed| = gcd`, the K2 core — DEFERRED).  The
single-round RISE is pinned alongside so the round-PAIR granularity is unmistakable: the per-round instance
IS the graveyarded `pivotMagnitudeWithin` and is refuted a priori; only the gap-2 statement survives. -/

/-- **The round-pair pivot-magnitude descent carrier.**  When two consecutive rounds both fire (both
find-`some`), the pivot magnitude after the pair is strictly below the start.  RECORDED; NOT proved here.
It is NOT the graveyarded per-round `pivotMagnitudeWithin` descent — that RISES once per trajectory
(pinned below); this is strictly a round-PAIR / whole-trajectory statement. -/
def SmithRoundPairPivotMagnitudeDescends : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat), matrix.IsRectangular height width →
    0 < (matrix.diagonalEntryAt pivotIndex).natAbs →
    (smithFindNonDividingLaterDiagonal matrix pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1)).isSome = true →
    (smithFindNonDividingLaterDiagonal (smithRoundStep matrix pivotIndex height width) pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1)).isSome = true →
    pivotMagnitudeWithin
        (smithRoundStep (smithRoundStep matrix pivotIndex height width) pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin matrix pivotIndex

set_option maxRecDepth 100000 in
/-- **The GRAVEYARD GUARD — the pivot magnitude RISES in a single round.**  On the reachable rise witness
at pivot `2`, one round takes the magnitude `66 -> 99` (`99 > 66`).  So the per-round `pivotMagnitudeWithin`
descent is FALSE — only the round-PAIR statement below survives. -/
theorem smithPivotMagnitudeRisesInOneRoundOnReachableWitness :
    pivotMagnitudeWithin (smithRoundStep
        (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4) 2 = 99
    ∧ pivotMagnitudeWithin (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 = 66 := by
  decide

set_option maxRecDepth 300000 in
/-- **Round-pair magnitude descent, kernel-witnessed on the reachable rise witness** — the pivot magnitude
after `round^2` is `33`, strictly below the start `66` (the full trajectory `66 -> 99 -> 33`). -/
theorem smithRoundPairPivotMagnitudeDropsOnReachableWitness :
    pivotMagnitudeWithin (smithRoundStep (smithRoundStep
        (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 4 4) 2 4 4) 2
      < pivotMagnitudeWithin (IntMatrix.mk [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 66, 0], [0, 0, 132, -99]]) 2 := by
  decide

set_option maxRecDepth 300000 in
/-- **Round-pair magnitude descent on the backup reachable rise witness** — `diag`-image
`[[2,·],[·,2],[·,132,·],[·,264,-198]]` at pivot `2`: `round^2` lands `66`, strictly below the start `132`
(trajectory `132 -> 198 -> 66`). -/
theorem smithRoundPairPivotMagnitudeDropsOnBackupWitness :
    pivotMagnitudeWithin (smithRoundStep (smithRoundStep
        (IntMatrix.mk [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 132, 0], [0, 0, 264, -198]]) 2 4 4) 2 4 4) 2
      < pivotMagnitudeWithin (IntMatrix.mk [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 132, 0], [0, 0, 264, -198]]) 2 := by
  decide

set_option maxRecDepth 100000 in
/-- **Round-pair magnitude descent on the small dirty seed** — `[[2,0],[4,3]]` at pivot `0`: `round^2`
lands `1`, strictly below the start `2` (trajectory `2 -> 3 -> 1`). -/
theorem smithRoundPairPivotMagnitudeDropsOnSmallDirtySeed :
    pivotMagnitudeWithin (smithRoundStep (smithRoundStep
        (IntMatrix.mk [[2, 0], [4, 3]]) 0 2 2) 0 2 2) 0
      < pivotMagnitudeWithin (IntMatrix.mk [[2, 0], [4, 3]]) 0 := by
  decide

/-! ## The r42 ledger (H2-SMITH r42, #2261) — the honest across-rounds refounding

**What this module ships (zero-axiom, additive; the r18-r41 world byte-intact).**  (1) The 7th graveyard
entry: two per-round descent candidates — the not-divided count and the magnitude+fuel sum — machine-
REFUTED (`diag(7,7,18)` count `1 -> 2`; `diag(6,9,11,11)` sum `43 -> 46`); with the shipped r31
(`pivotMagnitudeWithin`) / r22 (`smithMinorAbsSum`) refuters, the per-round single-`Nat` magnitude family
is exhausted.  (2) The across-rounds content carrier `SmithSubBlockContentStableAcrossRound` (RECORDED),
pinned constant (`minorGcdWithin` unchanged across folds and across two rounds — content `33`/`1` while the
magnitude rises).  (3) The round-pair carrier `SmithRoundPairPivotMagnitudeDescends` (RECORDED), pinned
dropping (`33 < 66`, `66 < 132`, `1 < 2`) with the single-round RISE `99 > 66` pinned as the graveyard
guard.

**What this module does NOT ship — the mandate does NOT fire (plainly).**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`; the recorded Props are not proved generically.  K2
(`SmithClearingOutputOffDiagonalDivides`) stands UNCHANGED and is not closed.  The census revision: `K1`
and `K2` are NOT orthogonal — both rest on "min-abs Euclid computes the sub-block gcd" (content-invariance
+ `|landed| = gcd`, the shipped `LandedAbsEqMinorGcdReachable`); `K1`'s inner termination IS the round-pair
magnitude descent, a consequence of that core.  Literature anchors: Stanley SNF Thm 2.4 (k=1 content =
gcd of all entries, unimodular-invariant); Ben-Amram-Genaim lexicographic ranking (bounded secondary rise
under a well-founded primary); CoqEAL `improve_pivot_rec` (structural fuel = `enorm`/`sdvdr` of the INITIAL
pivot, never `WellFounded.fix`).  No flip is fabricated. -/

end FX1Poly.ComputerAlgebra

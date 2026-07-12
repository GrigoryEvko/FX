import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedFixtures
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableMagnitudeResidual

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeWitnesses — the r38 magnitude residual's
    body kernel-checked on the COVERAGE-PROBE decision seeds, and the K2 non-vacuity witnessed
    (H2-SMITH r38, #2261)

## What this module adds (positive, additive, non-redundant)

The r38 residual `LandedAbsEqMinorGcdReachable` (`SmithReachableMagnitudeResidual`) is the decidable `Nat`
equality `|landed| = gcd(minor)` on the reachable image.  Its body cannot be `decide`d as a guarded `∀`,
but it CAN be pinned at concrete reachable states.  r32/r34 already pinned it on the killer/coprime/hostile
and pivot-`1` advanced seeds; this module pins it on the states the mandated COVERAGE PROBE surfaced as
decision-relevant and NOT yet covered — headlined by the **r31 divisor-chain REFUTER seed**
`diag(100, 75, 30, 14)` — and, crucially, WITNESSES the recon's central empirical finding: **K2 (the
off-diagonal divisibility) is genuinely non-vacuous** — the clearing sweep does NOT window-diagonalise the
trailing block; a deep-interior fill-in survives at exit, and the landed pivot divides it PURELY via the
gcd-ideal, never because it was cleared.

  * **The divisor-chain refuter still lands the gcd magnitude.**  `diag(100, 75, 30, 14)` is the seed on
    which the round-level divisor chain `pivot(n+1) ∣ pivot(n)` is machine-REFUTED (the cascade swaps the
    far entry `14` into the pivot, so `pivot(1) = 14 ∤ 100`; `SmithReachableKeystoneReduction` docstring,
    `smithFoldDescendsOnNonzeroPivotIsRefuted`).  Yet at the FIXED POINT `|landed@0| = 1 = gcd` — the
    round-level chain is refuted, the fixed-point equality survives.  This is the exact residual body on the
    exact refuter.

  * **K2 non-vacuity, kernel-witnessed.**  Advancing `diag(15, 10, 6, 4)` at pivot `0`, then running the
    pivot-`1` clearing sweep, lands the exit `[[1,0,0,0],[0,2,0,0],[0,0,60,0],[0,0,-60,-30]]`: a nonzero
    deep-interior fill-in `-60` SURVIVES at `(3, 2)` (strictly inside `[2, ·)²`, off pivot `1`'s cross),
    while pivot `1`'s own cross entry `(3, 1)` IS cleared to `0`.  The landed pivot `2` divides the survivor
    `-60` exactly (`-60 = 2 · (-30)`) — so K2 holds on the interior ONLY through `landed = gcd ∣ interior`,
    the r38 residual's content, never through clearing.

## What this module does NOT claim (honesty banner)

This module inhabits NOTHING hypothesis-free.  `SmithReduceCompleteDriverStatement` (`SmithNormalForm`)
stays UNINHABITED with zero hypotheses; the mandate does NOT fire.  The general `∀`-keystone is REFUTED
(`SmithLandedMagnitudeRefuted`, seed `[[0,6,0],[0,0,10],[0,0,0]]`); these fixtures are POSITIVE evidence
for the RESTRICTED reachable-image residual `LandedAbsEqMinorGcdReachable`, NOT a proof of any
`∀`-statement.  The honest OPEN half is the one-sided min-abs no-overshoot descent `|landed| ≤ gcd` (the
r38+ wall, `SmithReachableMagnitudeResidual` footer).  The r18–r37 world and `smithReduceComplete` stay
byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  All pins `decide` (kernel reduction, at or below the `4×4` defeq ceiling; the K2 witness
is a `4×4` DOUBLE sweep).  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeWitnesses.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The residual body `|landed| = gcd(minor)` on the COVERAGE-PROBE decision seeds (raw, pivot 0)

Each pins `LandedAbsEqMinorGcdReachable`'s body at a concrete input/pivot — both sides computed and
compared, no literal hard-coded (`landedMagnitudeAt` / `minorGcdMagnitudeAt`, `SmithReachableImageSeedFixtures`). -/

set_option maxRecDepth 100000 in
/-- **The divisor-chain REFUTER seed lands the gcd magnitude.**  On `diag(100, 75, 30, 14)` — the seed on
which the round-level chain `pivot(n+1) ∣ pivot(n)` is machine-refuted (`14` swaps into the pivot) — the
pivot-`0` cascade lands `|landed| = 1 = gcd(100, 75, 30, 14)`.  The chain is refuted; the fixed-point
equality survives. -/
theorem landedAbsEqMinorGcdOnDivisorChainRefuterSeed :
    landedMagnitudeAt { rows := [[100, 0, 0, 0], [0, 75, 0, 0], [0, 0, 30, 0], [0, 0, 0, 14]] } 0 4 4
      = minorGcdMagnitudeAt { rows := [[100, 0, 0, 0], [0, 75, 0, 0], [0, 0, 30, 0], [0, 0, 0, 14]] } 0 4 4 := by
  decide

set_option maxRecDepth 32000 in
/-- On `diag(6, 10, 8)` the pivot-`0` cascade lands `|landed| = 2 = gcd(6, 10, 8)` (probe state 9). -/
theorem landedAbsEqMinorGcdOnProbeSixTenEight :
    landedMagnitudeAt { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3
      = minorGcdMagnitudeAt { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 8]] } 0 3 3 := by
  decide

set_option maxRecDepth 32000 in
/-- On `diag(15, 10, 6, 4)` (coprime) the pivot-`0` cascade lands `|landed| = 1 = gcd` (probe state 10). -/
theorem landedAbsEqMinorGcdOnProbeFifteenTenSixFour :
    landedMagnitudeAt { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4
      = minorGcdMagnitudeAt { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4 := by
  decide

set_option maxRecDepth 32000 in
/-- On `diag(30, 20, 12)` the pivot-`0` cascade lands `|landed| = 2 = gcd` (the advance carries a `60`
interior fill-in, `advancedMatrixCarriesInteriorFillInThree`). -/
theorem landedAbsEqMinorGcdOnThirtyTwentyTwelve :
    landedMagnitudeAt { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 0 3 3
      = minorGcdMagnitudeAt { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 0 3 3 := by
  decide

set_option maxRecDepth 32000 in
/-- On `diag(12, 18, 30, 42)` the pivot-`0` cascade lands `|landed| = 6 = gcd`. -/
theorem landedAbsEqMinorGcdOnTwelveEighteenThirtyFortyTwo :
    landedMagnitudeAt { rows := [[12, 0, 0, 0], [0, 18, 0, 0], [0, 0, 30, 0], [0, 0, 0, 42]] } 0 4 4
      = minorGcdMagnitudeAt { rows := [[12, 0, 0, 0], [0, 18, 0, 0], [0, 0, 30, 0], [0, 0, 0, 42]] } 0 4 4 := by
  decide

/-! ## K2 non-vacuity — a surviving deep-interior fill-in, divided by the landed pivot via the gcd-ideal

The pivot-`0` advance of `diag(15, 10, 6, 4)`, then its pivot-`1` clearing sweep.  The exit is NOT
window-diagonal: a nonzero `-60` survives at `(3, 2)` (inside `[2, ·)²`, off pivot `1`'s cross), while
pivot `1`'s cross entry `(3, 1)` is cleared.  The landed pivot `2` divides `-60` exactly. -/

/-- The exact object the driver threads: the pivot-`1` clearing-sweep exit of the pivot-`0`-advanced
`diag(15, 10, 6, 4)`. -/
def pivotOneExitOfAdvancedReplumb : IntMatrix :=
  (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4).applyOperations
    (smithRepairPositionSweepClearing
      (smithMinorAbsSum
        (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4) 1 4 4)
      (matrixAdvancedByPivotZeroSweep { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 4 4) 1 4 4)

set_option maxRecDepth 64000 in
/-- **The exit is NOT window-diagonal, yet pivot `1`'s cross IS cleared.**  The full pivot-`1` exit reads
`[[1,0,0,0],[0,2,0,0],[0,0,60,0],[0,0,-60,-30]]`: the deep-interior fill-in `-60` at `(3, 2)` survives (K2
non-vacuous), pivot `1`'s cross entry `(3, 1)` is `0` (cleared), landed pivot `2` at `(1, 1)`. -/
theorem pivotOneExitCarriesSurvivingInteriorFillIn :
    pivotOneExitOfAdvancedReplumb.rows = [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 60, 0], [0, 0, -60, -30]] := by
  decide

set_option maxRecDepth 64000 in
/-- **The landed pivot divides the surviving interior fill-in — via the gcd-ideal, not clearing.**  The
landed pivot `pivotOneExitOfAdvancedReplumb.diagonalEntryAt 1 = 2` divides the surviving off-diagonal
`pivotOneExitOfAdvancedReplumb.entryAt 3 2 = -60` exactly (cofactor `-30`).  Concrete K2 witness: the
interior is divided ONLY because `landed = gcd(minor) ∣ interior`, never because the sweep cleared it. -/
theorem pivotOneLandedDividesSurvivingInteriorFillIn :
    dividesExactly (pivotOneExitOfAdvancedReplumb.diagonalEntryAt 1) (pivotOneExitOfAdvancedReplumb.entryAt 3 2) :=
  ⟨-30, by decide⟩

/-! ## The r38 witnesses ledger (H2-SMITH r38, #2261)

**What these witnesses ship (zero-axiom, additive; the r18–r37 world byte-intact).**  Five `decide` pins
of the r38 residual body `|landed| = gcd(minor)` on the COVERAGE-PROBE decision seeds (headlined by the
r31 divisor-chain refuter `diag(100,75,30,14)`, `|landed@0| = 1 = gcd`), plus the concrete K2 non-vacuity
witness: the pivot-`1` exit of the advanced `diag(15,10,6,4)` carries a surviving deep-interior fill-in
`-60` at `(3,2)` (NOT window-diagonal) that the landed pivot `2` divides exactly, with pivot `1`'s own
cross cleared.  Together: the min-abs Euclid clearing cascade lands the gcd magnitude even on the
divisor-chain refuter, and its off-diagonal guarantee (K2) is genuinely non-vacuous — delivered purely
by the gcd-ideal, exactly the r38 residual's content.

**What these witnesses do NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`; these pin the residual BODY at concrete reachable states, not the
guarded `∀`.  The open half remains the one-sided min-abs no-overshoot descent `|landed| ≤ gcd` (a ≥2-round
structural `Nat.rec` arc, `SmithReachableMagnitudeResidual` footer).  No flip is fabricated. -/

end FX1Poly.ComputerAlgebra

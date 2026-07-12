import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableKeystoneReduction
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeEquivalence

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeResidual — the reachable residual
    sharpened from a 1-D divisibility `∃` to a decidable `Nat` magnitude EQUALITY (H2-SMITH r38)

## The move

r37 (`SmithReachableKeystoneReduction`) reduced the corrected-driver totality to the crisp reachable
1-D scalar `LandedPivotDividesMinorGcdReachable` (`landed ∣ gcd(minor)` on the reachable image), and
noted that with the SHIPPED hypothesis-free converse `minorGcdDividesLanded` (`gcd ∣ landed`) the leg is
equivalently the magnitude identity `|landed| = gcd(minor)`.  This module makes that equivalence a
theorem: it names the reachable magnitude residual `LandedAbsEqMinorGcdReachable` (a `Nat` EQUALITY, no
`∃`, no 2-D block quantifier, decidable at every concrete instance) and proves it inter-derivable with
the r37 divisibility scalar — then re-routes the r37 driver collapse through it.

This is a pure structural assembly (no kernel evaluation, no descent measure, no new fuel): the whole
open content is repackaged into its tightest shape, the r18–r37 world stays BYTE-INTACT.

## The COVERAGE PROBE governs the SHAPE — equality, not a one-sided bound

The mandated `#eval` truth-probe pins `|landed| = gcd(minor)` EXACTLY on every reachable state tested,
both entry classes.  It does NOT support the weaker one-sided bound `|landed| ≤ gcd` as the residual:
that bound is UNSOUND to bridge to `landed ∣ gcd` on its own — the shipped converse `gcd ∣ landed`
together with `|landed| ≤ gcd` does NOT force `landed ∣ gcd` at the zero pivot (`landed = 0`, `gcd ≠ 0`
satisfies both premises yet `0 ∤ gcd`).  The sound, probe-confirmed residual is the two-sided magnitude
EQUALITY, whose bridge to divisibility is the SHIPPED `dividesExactlyOfNatAbsEq`
(`SmithLandedMagnitudeEquivalence`, `:109`): equal magnitudes divide each other (cofactor `±1`), with no
zero-case gap.

## What this module ships (positive, additive, zero-axiom)

  * **`LandedAbsEqMinorGcdReachable`** — the reachable magnitude residual: `|landed| = gcd(minor).natAbs`
    on the reachable image (`ReachableFromPhaseA`).  A `Nat` equality; the exact `#eval`-probed body.

  * **`landedDividesMinorGcdReachableOfAbsEq`** — the magnitude equality yields the r37 divisibility
    scalar `LandedPivotDividesMinorGcdReachable`, via the SHIPPED reverse bridge `dividesExactlyOfNatAbsEq`
    (`|landed| = |gcd| ⟹ landed ∣ gcd`, cofactor `±1`).  The zero-case-safe direction the recon's
    `≤`-framing could not supply.

  * **`landedAbsEqMinorGcdReachableOfDivides`** — the converse: the r37 divisibility scalar yields the
    magnitude equality, via `natDividesAntisymm` on the two `natAbs` divisibilities (`landed ∣ gcd` from the
    hypothesis, `gcd ∣ landed` from the SHIPPED hypothesis-free `minorGcdDividesLanded`).  The byte-parallel
    of the unrestricted `landedMagnitudeEqMinorGcdOfKeystone` (`SmithMinorGcdReduction`, `:302`).

  * **`landedDividesMinorGcdReachableIffAbsEq`** — the two-way equivalence, certifying the magnitude
    residual is the r37 leg faithfully RESTATED (neither strictly stronger nor weaker, given the shipped
    converse), just in a decidable `Nat`-equality shape.

  * **`smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable`** — the corrected-driver totality on the
    magnitude residual ALONE: compose the bridge with the r37 scalar driver
    `smithReduceCompleteDriverOfLandedDividesMinorGcdReachable`.  `SmithReduceCompleteDriverStatement` is
    inhabited GIVEN `LandedAbsEqMinorGcdReachable` — the exact remaining leg in its crispest arithmetic form.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the
mandate does NOT fire.  Every driver here still consumes a hypothesis.  After r38 the corrected-driver
totality residual is UNCHANGED in strength but SHARPENED to a decidable `Nat` equality — the EXACT
remaining leg is verbatim

    LandedAbsEqMinorGcdReachable
      = ∀ (matrix) (pivotIndex height width),
          ReachableFromPhaseA height width matrix pivotIndex →
          matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
          (landed pivot after the pivot-`pivotIndex` clearing sweep).natAbs
            = (minorGcdWithin matrix pivotIndex height width).natAbs

i.e. the min-abs Euclid clearing cascade lands, on the reachable image, a value whose MAGNITUDE is the
input minor's gcd.  The `#eval` probe confirms this is TRUE on every reachable state tested (both entry
classes; the exit interior is sparse-but-nonzero — the surviving fill-in is divided PURELY via the
gcd-ideal, never because it was cleared), but it is the r38+ WALL: a ≥2-round min-abs no-overshoot
descent — `|landed| ≤ gcd(minor)` — the only OPEN half (its converse `gcd ∣ landed` is SHIPPED
hypothesis-free).  That descent is a structural `Nat.rec` strong induction on a `natAbs` bound fed by
`SmithPrefixSettled`/`ReachableFromPhaseA` (NEVER `WellFounded.fix`); the r30 output bound only reaches
`|landed| ≤ min-abs entry`, and the gap `min-abs → gcd` is the multi-round Euclid reduction the r31
dirty-found-column obstruction forbids collapsing into any naive universal `natAbs` measure.  No descent
measure is fabricated here; no round-level divisor-chain flip is invented (it is machine-REFUTED); the
r18–r37 world and `smithReduceComplete` stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (no recursion introduced here — pure reachability-threading assembly).
ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableMagnitudeResidual.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The reachable magnitude residual — `|landed| = gcd(minor)` on the reachable image -/

/-- **The reachable magnitude residual.**  After the pivot-`pivotIndex` clearing sweep, the landed pivot
has MAGNITUDE equal to the input `[pivotIndex, ·)` minor's gcd magnitude, on the reachable image
(`ReachableFromPhaseA`).  A pure `Nat` equality: no divisibility `∃`, no 2-D block quantifier — the exact
`#eval`-probed body, decidable at every concrete instance.  The reachable transport of
`MinAbsEuclidLandsMinorGcdMagnitude` (`SmithLandedMagnitudeEquivalence`, `:123`). -/
def LandedAbsEqMinorGcdReachable : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    ((matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs

/-! ## The magnitude residual ⟹ the r37 divisibility scalar (the zero-safe forward bridge) -/

/-- **The magnitude equality yields `landed ∣ gcd(minor)`.**  Feed the reachable magnitude equality to the
SHIPPED reverse bridge `dividesExactlyOfNatAbsEq` (`|landed| = |gcd| ⟹ landed ∣ gcd`, cofactor `±1`) to
land the r37 divisibility scalar `LandedPivotDividesMinorGcdReachable`.  This is the direction the recon's
one-sided `|landed| ≤ gcd` framing could NOT supply: `≤` plus the shipped `gcd ∣ landed` leaves the
`landed = 0`, `gcd ≠ 0` case unforced, whereas the two-sided equality closes it with no zero-case gap. -/
theorem landedDividesMinorGcdReachableOfAbsEq
    (absEq : LandedAbsEqMinorGcdReachable) : LandedPivotDividesMinorGcdReachable := by
  intro matrix pivotIndex height width reached isRect pRowLt pColLt
  exact dividesExactlyOfNatAbsEq
    (absEq matrix pivotIndex height width reached isRect pRowLt pColLt)

/-! ## The r37 divisibility scalar ⟹ the magnitude residual (the shipped-converse antisymmetry) -/

/-- **`landed ∣ gcd(minor)` yields the magnitude equality.**  From the r37 divisibility scalar (`landed ∣
gcd`) and the SHIPPED hypothesis-free converse `minorGcdDividesLanded` (`gcd ∣ landed`), descend both to
`natAbs` (`natDividesNatAbsOfIntDivides`) and close by `natDividesAntisymm`.  The byte-parallel of the
unrestricted `landedMagnitudeEqMinorGcdOfKeystone` (`SmithMinorGcdReduction`, `:302`), threaded under the
reachability witness; the reachability guard is spent only on the divisibility-scalar hypothesis (the
converse `minorGcdDividesLanded` needs none). -/
theorem landedAbsEqMinorGcdReachableOfDivides
    (landedDividesGcd : LandedPivotDividesMinorGcdReachable) : LandedAbsEqMinorGcdReachable := by
  intro matrix pivotIndex height width reached isRect pRowLt pColLt
  exact natDividesAntisymm
    (natDividesNatAbsOfIntDivides
      (landedDividesGcd matrix pivotIndex height width reached isRect pRowLt pColLt))
    (natDividesNatAbsOfIntDivides
      (minorGcdDividesLanded matrix pivotIndex height width isRect pRowLt pColLt))

/-- **The magnitude residual is the r37 leg faithfully RESTATED.**  The two-way equivalence: given the
shipped converse `gcd ∣ landed`, the divisibility scalar `landed ∣ gcd` and the magnitude equality
`|landed| = |gcd|` are inter-derivable — neither strictly stronger nor weaker, just a decidable
`Nat`-equality shape for the same open content. -/
theorem landedDividesMinorGcdReachableIffAbsEq :
    LandedPivotDividesMinorGcdReachable ↔ LandedAbsEqMinorGcdReachable :=
  ⟨landedAbsEqMinorGcdReachableOfDivides, landedDividesMinorGcdReachableOfAbsEq⟩

/-! ## The corrected-driver totality on the magnitude residual alone -/

/-- **The corrected-driver totality on the magnitude residual `|landed| = gcd(minor)` alone.**  Compose the
forward bridge `landedDividesMinorGcdReachableOfAbsEq` with the r37 scalar driver
`smithReduceCompleteDriverOfLandedDividesMinorGcdReachable`.  `SmithReduceCompleteDriverStatement` is
inhabited GIVEN `LandedAbsEqMinorGcdReachable` — the exact remaining leg in its crispest arithmetic form
(a decidable `Nat` equality).  Still a hypothesis; the mandate does NOT fire. -/
theorem smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable
    (absEq : LandedAbsEqMinorGcdReachable) : SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfLandedDividesMinorGcdReachable
    (landedDividesMinorGcdReachableOfAbsEq absEq)

/-! ## The H2-SMITH r38 ledger — the reachable leg sharpened to a decidable `Nat` magnitude equality

**What r38 ships (zero-axiom, additive; the r18–r37 world byte-intact).**  The reachable magnitude
residual `LandedAbsEqMinorGcdReachable`; the zero-safe forward bridge to the r37 divisibility scalar
(`landedDividesMinorGcdReachableOfAbsEq`, via the shipped `dividesExactlyOfNatAbsEq`); the antisymmetry
converse (`landedAbsEqMinorGcdReachableOfDivides`, via `minorGcdDividesLanded` + `natDividesAntisymm`); the
two-way equivalence (`landedDividesMinorGcdReachableIffAbsEq`) certifying the residual is the r37 leg
faithfully restated; and the driver collapse onto the magnitude residual
(`smithReduceCompleteDriverOfLandedAbsEqMinorGcdReachable`).  The corrected-driver totality residual is now
the most atomic decidable shape: the `Nat` equality `|landed| = gcd(minor)` on the reachable image.

**What r38 does NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`.  The EXACT remaining leg is `LandedAbsEqMinorGcdReachable` (verbatim
above); with the shipped hypothesis-free converse `gcd ∣ landed` (`minorGcdDividesLanded`) its ONLY open
half is the one-sided min-abs no-overshoot descent `|landed| ≤ gcd(minor)`.  That is the r38+ WALL: a
≥2-round structural `Nat.rec` strong induction on a `natAbs` bound fed by `SmithPrefixSettled`/reachable
states — the r30 output bound reaches only `|landed| ≤ min-abs entry`, and the gap `min-abs → gcd` is the
multi-round Euclid reduction the r31 dirty-found-column obstruction
(`smithDirtyFoundColumnIsFindSomeReachable`) forbids collapsing into any naive universal `natAbs` measure.
The round-level divisor chain `pivot(n+1) ∣ pivot(n)` is machine-REFUTED (probe +
`smithFoldDescendsOnNonzeroPivotIsRefuted`); it is NOT stated here and NOT proven.  No flip is fabricated;
no descent measure is invented. -/

end FX1Poly.ComputerAlgebra

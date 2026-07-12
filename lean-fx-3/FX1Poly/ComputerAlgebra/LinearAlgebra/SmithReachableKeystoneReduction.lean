import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachablePrefixConfinement

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithReachableKeystoneReduction — retire the reachable
    SEED to the reachable KEYSTONE, and sharpen it to the crisp gcd scalar (H2-SMITH r37)

## The move

r35 (`SmithReachableImageSeedRestriction`) re-parameterized the corrected total driver off the RESTRICTED
seed `SmithCascadeLandsDivisibleSubBlockReachable` (the whole-`[pivotIndex+1, ·)²`-sub-block divisibility of
the OUTPUT, guarded by `ReachableFromPhaseA`).  r36 (`SmithReachablePrefixConfinement`) discharged that
seed's STRUCTURAL half (the confinement invariant `reachableImpliesPrefixSettled`).  This module discharges
the seed's ASSEMBLY half: it retires the reachable seed to the strictly SHARPER, more-atomic reachable
KEYSTONE — the landed pivot divides the INPUT `[pivotIndex, ·)` minor — and then to the crispest 1-D scalar
`landed ∣ gcd(minor)`, exactly the r22→r29 shape (`SmithWindowedChainReduction` / `SmithMinorGcdReduction`)
transported under the reachability witness.

This is NODE 2 of the r37 reconnaissance: a pure structural assembly (no kernel evaluation, no descent
measure, no new fuel).  The unrestricted originals stay BYTE-INTACT; every declaration here threads the same
`ReachableFromPhaseA height width matrix pivotIndex` witness the seed already carries.

## The mechanism (web-literature verdict — key on DIVISIBILITY, not magnitude)

CoqEAL (`smithpid.v`, `sdvd_Bezout_step` + `well_founded (@sdvdr R)`), Isabelle-AFP (`diagonal_step_dvd1/2`),
and the classical PID proof (Wikipedia's `δ` = prime-factor count) all agree: the repair mechanism is
gcd-REPLACEMENT (`pivot ↦ gcd(pivot, entry)`), whose termination is the well-founded strict-divisibility
order — NOT a remainder magnitude.  So the honest residual is keyed on divisibility: the landed pivot lies in
the minor's gcd-ideal and divides its gcd generator (`LandedPivotDividesMinorGcdReachable`).  The SHIPPED
converse `gcd(minor) ∣ landed` (`minorGcdDividesLanded`, HYPOTHESIS-FREE, needs no reachability guard) is the
gcd-invariance half; the OPEN half `landed ∣ gcd(minor)` is the min-abs-Euclid gcd-landing wall.

## THE DIVISOR-CHAIN PROBE governs — the round-level chain is REFUTED, never proven

The mandated `#eval` truth-probe over the genuine reachable trajectories REFUTES the round-level divisor
chain `pivot(n+1) ∣ pivot(n)`: on `diag(100,75,30,14)@0` the cascade's `smithFindMinAbsInMinor` swaps the
untouched far entry `14` into the pivot, so `pivot(1) = 14 ∤ 100 = pivot(0)`.  This re-confirms the shipped
refutations `smithFoldDescendsOnNonzeroPivotIsRefuted` (`SmithFoldDescentRefuted`) and the r21
`smithCascadeLandsPivotDividesFoldedPair` refutation.  NO round-level divisor-chain lemma is stated here —
that would be a false lemma.  The ONLY probe-confirmed relation is at the fixed point: `|landed| = gcd(minor)`
holds on every one of the 15 seed/pivot runs, keyed on divisibility (`landed ∣ gcd` AND `gcd ∣ landed`).

## What this module ships (positive, additive, zero-axiom)

  * **`SmithCascadeLandedPivotDividesMinorReachable`** — the reachable KEYSTONE: the verbatim body of the r22
    keystone `SmithCascadeLandedPivotDividesMinor` (`SmithWindowedChainReduction`, `:1138`), guarded by
    `ReachableFromPhaseA`.  A strictly WEAKER residual than the unrestricted keystone (only asked on the
    reachable image).

  * **`seedReachableOfLandedPivotDividesMinorReachable`** — the reachable KEYSTONE ⟹ reachable SEED.  The
    byte-parallel of the shipped `seedOfLandedPivotDividesMinor` (`:1155`): carry the landed-pivot
    divisibility of the INPUT `[pivotIndex, ·)` minor across the pivot-`pivotIndex` clearing sweep (confined
    below `pivotIndex` by `smithRepairPositionSweepClearingBoundedBelow`, forward tower
    `applyOperationsPreservesEntriesDivisibleWithin`), then restrict the floor `pivotIndex → pivotIndex + 1`
    (`matrixEntriesDivisibleByWithinLoMono`).  The reachability witness is threaded straight into the
    keystone hypothesis.

  * **`smithReduceCompleteDriverOfLandedPivotDividesMinorReachable`** — the corrected-driver totality on the
    reachable keystone ALONE.  Compose the reduction with the shipped
    `smithReduceCompleteDriverOfSubBlockSeedReachable` (which consumes ONLY the reachable seed).  The residual
    is now the reachable keystone, strictly sharper than the reachable seed.

  * **`LandedPivotDividesMinorGcdReachable`** — the crisp reachable 1-D scalar: after the pivot-`pivotIndex`
    clearing sweep, the landed pivot divides `minorGcdWithin` of the input `[pivotIndex, ·)` minor.  The
    reachable transport of `LandedPivotDividesMinorGcd` (`SmithMinorGcdReduction`, `:247`).

  * **`keystoneReachableIffLandedDividesMinorGcdReachable`** — the reachable keystone ⟺ the reachable scalar.
    The byte-parallel of `keystoneIffLandedDividesMinorGcd` (`:261`): forward via `minorGcdWithinGreatest`
    (a common divisor divides the gcd), backward via `dividesExactlyTrans` +
    `minorGcdWithinDividesWithin` (`gcd ∣ every minor entry`).  The 2-D whole-minor `∀` collapses to the 1-D
    scalar on the reachable image, retiring the interior-fill-in worry.

  * **`smithReduceCompleteDriverOfLandedDividesMinorGcdReachable`** — the corrected-driver totality on the
    CRISPEST reachable residual `landed ∣ gcd(minor)` alone (compose `.mpr` of the iff with the keystone
    driver).  This is the exact remaining leg, in its most atomic reachable shape.

## What this module does NOT claim (honesty banner — the mandate does NOT fire)

`SmithReduceCompleteDriverStatement` (`SmithNormalForm`) stays UNINHABITED with zero hypotheses; the mandate
does NOT fire.  Every driver here still consumes a hypothesis.  After r37 the corrected-driver totality
residual is UNCHANGED in strength but SHARPENED to its most atomic reachable shape — the EXACT remaining leg
is verbatim

    LandedPivotDividesMinorGcdReachable
      = ∀ (matrix) (pivotIndex height width),
          ReachableFromPhaseA height width matrix pivotIndex →
          matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
          dividesExactly (landed pivot after the pivot-`pivotIndex` clearing sweep)
                         (minorGcdWithin matrix pivotIndex height width)

i.e. the landed pivot DIVIDES the input minor's gcd, on the reachable image.  Its converse `gcd ∣ landed` is
SHIPPED hypothesis-free (`minorGcdDividesLanded`), so — with that half — the leg is equivalently
`|landed| = gcd(minor)` on the reachable image: the min-abs Euclid diagonal descent lands a value whose
magnitude IS the minor gcd.  The `#eval` probe confirms this is TRUE on all 15 reachable runs, but it is the
r38+ WALL: a ≥2-round strong-induction stabilization (structural `Nat.rec` on a `natAbs` bound, NEVER
`WellFounded.fix`) fed by a descent valid on `SmithPrefixSettled`/reachable states — the r31 dirty-found-column
obstruction (`smithDirtyFoundColumnIsFindSomeReachable`) forbids a naive universal `natAbs` descent, so the
descent must consume the confinement structure.  No descent measure is fabricated here; no round-level
divisor-chain flip is invented (it is machine-REFUTED); the r18–r36 world and `smithReduceComplete` stay
byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only (no recursion introduced here — pure reachability-threading assembly).
ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableKeystoneReduction.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The reachable keystone — the r22 keystone body guarded by reachability -/

/-- **The reachable KEYSTONE.**  The verbatim body of the r22 keystone `SmithCascadeLandedPivotDividesMinor`
(`SmithWindowedChainReduction`, `:1138`) — after the pivot-`pivotIndex` clearing position sweep, the landed
pivot diagonal divides EVERY entry of the INPUT's `[pivotIndex, ·) × [pivotIndex, ·)` minor — quantified ONLY
over the matrices actually reachable from the Phase-A output (`ReachableFromPhaseA`).  A strictly WEAKER
residual than the unrestricted keystone: it is asked only on the reachable image, exactly the trajectory the
corrected driver's carrier visits. -/
def SmithCascadeLandedPivotDividesMinorReachable : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix

/-! ## The reachable keystone yields the reachable seed -/

/-- **The reachable KEYSTONE ⟹ the reachable SEED.**  The byte-parallel of the shipped
`seedOfLandedPivotDividesMinor` (`SmithWindowedChainReduction`, `:1155`), threading the reachability witness
into the keystone hypothesis.  GIVEN the reachable keystone, the reachable seed
`SmithCascadeLandsDivisibleSubBlockReachable` holds: carry the landed-pivot divisibility of the INPUT
`[pivotIndex, ·)` minor across the pivot-`pivotIndex` clearing sweep — confined below `pivotIndex` by
`smithRepairPositionSweepClearingBoundedBelow`, so the SHIPPED forward tower
`applyOperationsPreservesEntriesDivisibleWithin` carries it to the OUTPUT `[pivotIndex, ·)` block (interior
fill-in included) — then restrict the floor `pivotIndex → pivotIndex + 1` (`matrixEntriesDivisibleByWithinLoMono`).
A pure structural assembly; no inverse machinery, no kernel evaluation. -/
theorem seedReachableOfLandedPivotDividesMinorReachable
    (landedDivides : SmithCascadeLandedPivotDividesMinorReachable) :
    SmithCascadeLandsDivisibleSubBlockReachable := by
  intro matrix pivotIndex height width reached isRect pRowLt pColLt
  exact matrixEntriesDivisibleByWithinLoMono (Nat.le_succ pivotIndex)
    (applyOperationsPreservesEntriesDivisibleWithin
      (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
        matrix pivotIndex height width)
      matrix
      (smithRepairPositionSweepClearingBoundedBelow pivotIndex
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
        pRowLt pColLt (Nat.le_refl pivotIndex))
      (landedDivides matrix pivotIndex height width reached isRect pRowLt pColLt))

/-- **The corrected-driver totality on the reachable KEYSTONE alone.**  Compose the seed reduction with the
shipped seed-conditional driver totality `smithReduceCompleteDriverOfSubBlockSeedReachable` (which consumes
ONLY the reachable seed).  `SmithReduceCompleteDriverStatement` is now inhabited GIVEN the reachable keystone
— a strictly sharper (more atomic) residual than the reachable seed.  The mandate does NOT fire
hypothesis-free. -/
theorem smithReduceCompleteDriverOfLandedPivotDividesMinorReachable
    (landedDivides : SmithCascadeLandedPivotDividesMinorReachable) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfSubBlockSeedReachable
    (seedReachableOfLandedPivotDividesMinorReachable landedDivides)

/-! ## The reachable keystone sharpened to the 1-D scalar `landed | gcd(minor)` -/

/-- **The crisp reachable 1-D residual.**  After the pivot-`pivotIndex` clearing sweep, the landed pivot
divides the gcd of the input's `[pivotIndex, ·)` minor, on the reachable image.  The reachable transport of
`LandedPivotDividesMinorGcd` (`SmithMinorGcdReduction`, `:247`); the divisibility-keyed form the web
literature endorses (the landed pivot lies in the minor's gcd-ideal). -/
def LandedPivotDividesMinorGcdReachable : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    ReachableFromPhaseA height width matrix pivotIndex →
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    dividesExactly
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (minorGcdWithin matrix pivotIndex height width)

/-- **The reachable keystone ⟺ `landed ∣ gcd(minor)` on the reachable image.**  The byte-parallel of
`keystoneIffLandedDividesMinorGcd` (`SmithMinorGcdReduction`, `:261`), threading the reachability witness.
Forward: the keystone says the landed pivot divides every minor entry, so it is a common divisor, so it
divides the gcd (`minorGcdWithinGreatest`).  Backward: from `landed ∣ gcd` and `gcd ∣ every minor entry`
(`minorGcdWithinDividesWithin`), transitivity (`dividesExactlyTrans`) gives the keystone body.  The 2-D
whole-minor `∀` collapses to the 1-D scalar on the reachable image. -/
theorem keystoneReachableIffLandedDividesMinorGcdReachable :
    SmithCascadeLandedPivotDividesMinorReachable ↔ LandedPivotDividesMinorGcdReachable := by
  constructor
  · intro keystone matrix pivotIndex height width reached isRect pRowLt pColLt
    exact minorGcdWithinGreatest matrix pivotIndex height width
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (keystone matrix pivotIndex height width reached isRect pRowLt pColLt)
  · intro landedDividesGcd matrix pivotIndex height width reached isRect pRowLt pColLt
    intro rowIndex rowGe colIndex colGe
    show dividesExactly
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (matrix.entryAt rowIndex colIndex)
    exact dividesExactlyTrans
      (landedDividesGcd matrix pivotIndex height width reached isRect pRowLt pColLt)
      (minorGcdWithinDividesWithin matrix pivotIndex height width isRect rowIndex rowGe colIndex colGe)

/-- **The corrected-driver totality on the CRISPEST reachable residual `landed ∣ gcd(minor)` alone.**
Compose `.mpr` of the iff (recovering the reachable keystone) with the keystone driver.
`SmithReduceCompleteDriverStatement` is inhabited GIVEN `LandedPivotDividesMinorGcdReachable` — the exact,
most-atomic remaining leg.  Its shipped converse `gcd ∣ landed` (`minorGcdDividesLanded`, hypothesis-free)
makes this leg equivalently `|landed| = gcd(minor)` on the reachable image.  Still a hypothesis; the mandate
does NOT fire. -/
theorem smithReduceCompleteDriverOfLandedDividesMinorGcdReachable
    (landedDividesGcd : LandedPivotDividesMinorGcdReachable) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfLandedPivotDividesMinorReachable
    (keystoneReachableIffLandedDividesMinorGcdReachable.mpr landedDividesGcd)

/-! ## The H2-SMITH r37 ledger — the reachable seed retired to the reachable keystone / gcd scalar

**What r37 ships (zero-axiom, additive; the r18–r36 world byte-intact).**  The reachable KEYSTONE
`SmithCascadeLandedPivotDividesMinorReachable`; its reduction to the reachable SEED
(`seedReachableOfLandedPivotDividesMinorReachable`, the byte-parallel of the shipped
`seedOfLandedPivotDividesMinor` under the reachability witness); the driver collapse onto the reachable
keystone (`smithReduceCompleteDriverOfLandedPivotDividesMinorReachable`); the crisp reachable scalar
`LandedPivotDividesMinorGcdReachable`; the keystone ⟺ scalar equivalence
(`keystoneReachableIffLandedDividesMinorGcdReachable`, the byte-parallel of `keystoneIffLandedDividesMinorGcd`);
and the driver collapse onto the scalar (`smithReduceCompleteDriverOfLandedDividesMinorGcdReachable`).  The
corrected-driver totality residual is now the most atomic reachable shape: the 1-D divisibility scalar
`landed ∣ gcd(minor)` on the reachable image.

**What r37 does NOT ship — the mandate does NOT fire.**  No hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement`.  The EXACT remaining leg is `LandedPivotDividesMinorGcdReachable`
(verbatim above): the landed pivot divides the input minor's gcd on the reachable image — equivalently, with
the SHIPPED converse `minorGcdDividesLanded` (`gcd ∣ landed`, hypothesis-free), `|landed| = gcd(minor)` on the
reachable image.  The `#eval` divisor-chain probe confirms this leg is TRUE on all 15 reachable runs, but it
is the r38+ min-abs-Euclid gcd-landing WALL: a ≥2-round strong-induction stabilization (structural `Nat.rec`
on a `natAbs` bound) fed by a descent valid on `SmithPrefixSettled`/reachable states, the r31
dirty-found-column obstruction blocking any naive universal `natAbs` descent.  The round-level divisor chain
`pivot(n+1) ∣ pivot(n)` is machine-REFUTED (probe + `smithFoldDescendsOnNonzeroPivotIsRefuted`); it is NOT
stated here and NOT proven.  No flip is fabricated; no descent measure is invented. -/

end FX1Poly.ComputerAlgebra

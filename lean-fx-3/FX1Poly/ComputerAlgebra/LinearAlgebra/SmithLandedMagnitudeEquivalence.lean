import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeEquivalence — the open wall in its
    crispest arithmetic form, and its kernel-checked truth on the decision-round hostile seeds
    (H2-SMITH r32, #2261 — THE DECISION ROUND)

## The decision

The user-ordered mandate (#2261) is `SmithReduceCompleteDriverStatement` inhabited with ZERO
hypotheses — "every rectangular integer matrix, any size, zero kernel evaluation; the honest pair
finalized".  r32 DECIDES the shape of the remaining work:

  * **The final-state re-threading route is closed.**  The `∀`-correctness theorem is already stated
    over FINAL-state facts (`repairChainHolds` is `SmithChainPrefix` on the whole repair output, not a
    per-phase object — `smithReduceCompleteDriverOfChain`, `SmithCascadeTermination`).  But discharging
    it from final-state facts ALONE is not possible: at each earlier pivot the forward tower needs the
    pivot to divide the WHOLE later sub-block (off-diagonal fill-in included), whereas the r18 exit-scan
    read-off (`smithFindNonDividingLaterDiagonalNoneDividesAll`) supplies only "pivot divides the later
    DIAGONALS".  The gap is exactly the whole-minor content the keystone carries, so there is no
    keystone-free re-threading.

  * **The single surviving wall is the per-phase keystone** `SmithCascadeLandedPivotDividesMinor`
    (`SmithWindowedChainReduction`), sharpened at r29 to the 1-D scalar `landed | gcd(minor)`
    (`LandedPivotDividesMinorGcd`, `SmithMinorGcdReduction`).  With the shipped converse `gcd | landed`
    (`minorGcdDividesLanded`) it is the symmetric magnitude identity: *the min-abs Euclid clearing
    cascade lands, at every pivot, a value whose magnitude equals the minor gcd* — the classic
    "min-abs Euclid computes the gcd".  This is NOT closed by any gcd-invariance argument (which bounds
    the ideal from one side only) and admits no per-fold `Nat` descent measure (`smithMinorAbsSum` RISES
    on folds — r22, and again on the killer seed below; `minNonzeroAbsWithin` STALLS — r26;
    `pivotMagnitudeWithin` RISES — r31).  It is a standalone multi-round descent arc, NOT r32-sized.

## What r32 ships (all zero-axiom, additive; the r18–r31 world byte-intact)

  1. **The general sharpening — the wall's crispest form.**  r29 shipped only the FORWARD half
     `landedMagnitudeEqMinorGcdOfKeystone : keystone → (|landed| = gcd(minor))`.  This module supplies
     the reverse bridge `dividesExactlyOfNatAbsEq` (magnitude equality ⇒ exact divisibility) and closes
     the loop into the FULL equivalence

         `keystoneIffLandedMagnitudeEqMinorGcd :
             SmithCascadeLandedPivotDividesMinor ↔ MinAbsEuclidLandsMinorGcdMagnitude`

     where `MinAbsEuclidLandsMinorGcdMagnitude` is the crisp `∀`-arithmetic statement "for every
     rectangular input and pivot, `|landed| = gcd(minor)`".  So the ENTIRE corrected-driver totality is
     now inhabited hypothesis-free IFF this single magnitude identity holds for all inputs — the open
     wall stated with no divisibility `∃`, no 2-D block quantifier, just an equation between two
     magnitudes.

  2. **The decisive hostile-seed fixtures — the RHS kernel-checked TRUE where it is hardest.**  The
     `∀`-body `|landed| = gcd(minor)` is pinned by `decide` on the round's decisive seeds (all at or
     below the 4x4 defeq ceiling):
       - `landedMagnitudeEqMinorGcdOnKillerSeedPivotZero` / `...PivotTwo` — on `diag(4, 6, 9, 7)`, the
         seed on which BOTH candidate per-fold measures die (`smithMinorAbsSum` rises 26 → 30,
         `smithMinorAbsSumRisesOnKillerSeedFold`; the obstruction count against the pivot RISES 2 → 3
         across a fold).  `|landed| = gcd = 1`.
       - `landedMagnitudeEqMinorGcdOnFillInSeedPivotOne` — on `diag(1, -12, -18, 10)`, the r26
         confinement seed with genuine interior fill-in and negative entries.  `|landed| = gcd = 2`.
       - `landedMagnitudeEqMinorGcdOnHostileNonDiagonalSeed` — on the fully non-diagonal all-even
         `[[6, 2, 4], [8, 10, 2], [2, 6, 8]]`, strengthening r25's converse-only pin to the SYMMETRIC
         `|landed| = gcd = 2`.
       - `landedMagnitudeEqMinorGcdOnCoprimeSeed` — on `diag(15, 10, 6, 4)` (coprime), `|landed| = gcd
         = 1` — the cascade collapses a coprime window to the unit, off the r18-refuted head.

## Honest sizing

This module inhabits NOTHING hypothesis-free.  It sharpens the residual to its crispest equivalent
form (a magnitude equation) and machine-checks that equation on the decision-round's hardest seeds —
CONFIRMING the wall is TRUE where it is hardest to see, and DECIDING that no mechanical `Nat`-measure
closes it and no final-state route bypasses it.  `SmithReduceCompleteDriverStatement` stays UNINHABITED
hypothesis-free after r32; it is inhabited GIVEN the keystone
(`smithReduceCompleteDriverOfLandedPivotDividesMinor`, r22) or, equivalently, GIVEN
`MinAbsEuclidLandsMinorGcdMagnitude` via `keystoneIffLandedMagnitudeEqMinorGcd.mpr`.  The shipped
`smithReduceComplete`, its refutation, and the r18–r31 world stay byte-intact (additive only).

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeEquivalence.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The reverse magnitude bridge — `natAbs`-equality forces exact divisibility -/

/-- **Equal magnitudes divide each other exactly.**  If `|leftValue| = |rightValue|` then `leftValue`
divides `rightValue` over the integers (cofactor `±1`).  Compose the shipped bridges: promote the
magnitude equality to `NatDivides leftValue.natAbs rightValue.natAbs` (`natDividesOfEq` off
`natDividesRefl`), rise to `Int` divisibility by `Int.ofNat leftValue.natAbs`
(`intDividesOfNatDividesNatAbs`), then sign-normalise the divisor (`intDividesOfNatAbsDivides`).  This
is the reverse of `natDividesNatAbsOfIntDivides` specialised to equal magnitudes — the missing piece
that turns the r29 forward-only magnitude implication into a full equivalence. -/
theorem dividesExactlyOfNatAbsEq {leftValue rightValue : Int}
    (magnitudesEqual : leftValue.natAbs = rightValue.natAbs) :
    dividesExactly leftValue rightValue :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs
      (natDividesOfEq magnitudesEqual.symm (natDividesRefl leftValue.natAbs)))

/-! ## The wall in its crispest form — the landed magnitude equals the minor gcd, for all inputs -/

/-- **The corrected-driver totality's crispest equivalent** — for every rectangular integer input and
in-range pivot, the min-abs Euclid clearing cascade's landed pivot has MAGNITUDE equal to the input
minor's gcd.  A pure equation between two `Nat` magnitudes: no divisibility `∃`, no 2-D block
quantifier.  Equivalent to the keystone `SmithCascadeLandedPivotDividesMinor` by
`keystoneIffLandedMagnitudeEqMinorGcd`. -/
def MinAbsEuclidLandsMinorGcdMagnitude : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    ((matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs

/-- **The keystone ⟺ the magnitude identity.**  Forward: the keystone gives `|landed| = gcd(minor)`
directly (`landedMagnitudeEqMinorGcdOfKeystone`).  Backward: from the magnitude equality,
`dividesExactlyOfNatAbsEq` yields `landed | gcd(minor)`, which is `LandedPivotDividesMinorGcd`, which is
the keystone (`keystoneIffLandedDividesMinorGcd.mpr`).  So the ENTIRE corrected-driver totality is
inhabited hypothesis-free IFF `MinAbsEuclidLandsMinorGcdMagnitude` holds — the open wall as a single
`∀`-quantified magnitude equation.  Completes r29's forward-only
`landedMagnitudeEqMinorGcdOfKeystone`. -/
theorem keystoneIffLandedMagnitudeEqMinorGcd :
    SmithCascadeLandedPivotDividesMinor ↔ MinAbsEuclidLandsMinorGcdMagnitude := by
  constructor
  · intro keystone matrix pivotIndex height width isRect pRowLt pColLt
    exact landedMagnitudeEqMinorGcdOfKeystone keystone matrix pivotIndex height width
      isRect pRowLt pColLt
  · intro magnitudeIdentity
    apply keystoneIffLandedDividesMinorGcd.mpr
    intro matrix pivotIndex height width isRect pRowLt pColLt
    exact dividesExactlyOfNatAbsEq
      (magnitudeIdentity matrix pivotIndex height width isRect pRowLt pColLt)

/-! ## The decision-round fixtures — the RHS body kernel-checked TRUE on the decisive hostile seeds

Each pins the `MinAbsEuclidLandsMinorGcdMagnitude` body `|landed| = gcd(minor)` at a concrete
hostile input/pivot by `decide` (kernel reduction, at or below the 4x4 defeq ceiling).  These are the
decision-round evidence that the open wall is TRUE precisely where it is hardest to see. -/

set_option maxRecDepth 16000 in
/-- **The killer seed at pivot 0.**  On `diag(4, 6, 9, 7)` — the seed on which every candidate per-fold
`Nat` measure dies — the pivot-`0` cascade lands `|landed| = 1 = gcd(4, 6, 9, 7)`.  The full 4x4 sweep,
the most stressful kernel pin. -/
theorem landedMagnitudeEqMinorGcdOnKillerSeedPivotZero :
    ((({ rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 0 4 4)
          { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 0 4 4)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 0 4 4).natAbs := by
  decide

set_option maxRecDepth 16000 in
/-- **The killer seed at an inner pivot.**  On `diag(4, 6, 9, 7)` the pivot-`2` cascade lands
`|landed| = 1 = gcd(9, 7)` — the inner-window instance. -/
theorem landedMagnitudeEqMinorGcdOnKillerSeedPivotTwo :
    ((({ rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 2 4 4)
          { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 2 4 4)).diagonalEntryAt 2).natAbs
      = (minorGcdWithin { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 2 4 4).natAbs := by
  decide

set_option maxRecDepth 16000 in
/-- **The fill-in seed with negatives.**  On `diag(1, -12, -18, 10)` — the r26 confinement seed exhibiting
genuine interior fill-in and negative entries — the pivot-`1` cascade lands `|landed| = 2 = gcd(12, 18,
10)`.  Confirms the magnitude identity survives negative entries and transient fill-in. -/
theorem landedMagnitudeEqMinorGcdOnFillInSeedPivotOne :
    ((({ rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)
          { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4)).diagonalEntryAt 1).natAbs
      = (minorGcdWithin { rows := [[1, 0, 0, 0], [0, -12, 0, 0], [0, 0, -18, 0], [0, 0, 0, 10]] } 1 4 4).natAbs := by
  decide

set_option maxRecDepth 16000 in
/-- **The fully non-diagonal hostile seed.**  On the all-even `[[6, 2, 4], [8, 10, 2], [2, 6, 8]]` the
pivot-`0` cascade lands `|landed| = 2 = gcd(minor)`.  Strengthens r25's converse-only `2 | landed` pin
to the SYMMETRIC magnitude identity, on a genuinely non-diagonal input. -/
theorem landedMagnitudeEqMinorGcdOnHostileNonDiagonalSeed :
    ((({ rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } 0 3 3)
          { rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } 0 3 3)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin { rows := [[6, 2, 4], [8, 10, 2], [2, 6, 8]] } 0 3 3).natAbs := by
  decide

set_option maxRecDepth 16000 in
/-- **The coprime seed.**  On `diag(15, 10, 6, 4)` the pivot-`0` cascade collapses the coprime window to
`|landed| = 1 = gcd(15, 10, 6, 4)` — the unit landing off the r18-refuted head. -/
theorem landedMagnitudeEqMinorGcdOnCoprimeSeed :
    ((({ rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } : IntMatrix).applyOperations
        (smithRepairPositionSweepClearing
          (smithMinorAbsSum { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)
          { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4)).diagonalEntryAt 0).natAbs
      = (minorGcdWithin { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] } 0 4 4).natAbs := by
  decide

set_option maxRecDepth 16000 in
/-- **No per-fold `Nat` measure on the killer seed.**  On `diag(4, 6, 9, 7)` the pivot-`0` clearing fold
RAISES `smithMinorAbsSum` `26 → 30`, so the cheapest budget-fitting descent measure fails on this very
seed — corroborating `smithMinorAbsSumRaisesOnFoldWitness` (r22) on the decision-round's killer seed.
Names WHY the magnitude wall above is not mechanically closeable: the natural `Nat` measure is not even
non-increasing across a genuine fold. -/
theorem smithMinorAbsSumRisesOnKillerSeedFold :
    smithMinorAbsSum { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 0 4 4
      < smithMinorAbsSum
          (smithClearingFoldStep { rows := [[4, 0, 0, 0], [0, 6, 0, 0], [0, 0, 9, 0], [0, 0, 0, 7]] } 1 0 4 4)
          0 4 4 := by
  decide

/-! ## SURVIVING WALL (H2-SMITH r32, #2261)

After r32 the corrected-driver totality residual is UNCHANGED in strength but SHARPENED to its crispest
equivalent: `keystoneIffLandedMagnitudeEqMinorGcd` reduces `SmithReduceCompleteDriverStatement` (given
the r22 collapse) to the single `∀`-magnitude identity `MinAbsEuclidLandsMinorGcdMagnitude` —
`|landed| = gcd(minor)` for every rectangular input.  Both the shipped converse `gcd | landed`
(`minorGcdDividesLanded`) and the forward implication (`landedMagnitudeEqMinorGcdOfKeystone`) are folded
into this one biconditional; the fixtures above kernel-check the identity's `∀`-body TRUE on the
decision-round's hardest seeds (killer, fill-in-with-negatives, hostile non-diagonal, coprime).

**The jam, named exactly.**  The OPEN half is the descent direction: the min-abs Euclid clearing cascade
`smithRepairPositionSweepClearing` lands a value of magnitude NO LARGER than the minor gcd — i.e. the
landed pivot is a MINIMAL nonzero element of the input minor's gcd-ideal (`|landed| ≤ gcd`; combined with
the shipped `gcd | landed`, forcing equality).  This is the "min-abs Euclid diagonal descent reaches the
gcd" wall.  It is NOT closed by any gcd-invariance argument (which bounds the ideal from one side only,
r25) and admits NO per-fold `Nat` descent measure: `smithMinorAbsSum` RISES on folds
(`smithMinorAbsSumRisesOnKillerSeedFold` above; r22), `minNonzeroAbsWithin` STALLS on already-minimal and
zero-pivot-bootstrap folds (r26), `pivotMagnitudeWithin` RISES on the raw fold step (r31).  A strict
measure must lex-refine `minNonzeroAbsWithin` and proving THAT refinement descends across the whole
cascade IS the standalone multi-round "cascade-computes-gcd" arc — decisively NOT r32-sized.  No flip is
fabricated: `SmithReduceCompleteDriverStatement` stays UNINHABITED hypothesis-free, and the honest pair
is `(SmithReduceCompleteDriverStatement ⟸ MinAbsEuclidLandsMinorGcdMagnitude, that identity OPEN)`. -/

end FX1Poly.ComputerAlgebra

import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorGcdReduction

/-! # Smith landed-magnitude equivalence

The general keystone `SmithCascadeLandedPivotDividesMinor`, equivalently
`MinAbsEuclidLandsMinorGcdMagnitude` (`|landed| = gcd(minor)`), is refuted as stated. The non-diagonal
seed `[[0, 6, 0], [0, 0, 10], [0, 0, 0]]` at pivot 0 lands `6` (min-abs at column 1, cross clean, cascade
stops) while the minor `{6, 10}` has `gcd = 2` and `6` does not divide `10`: the `10` sits off the pivot
cross, in the interior the cross-clear terminator never inspects (machine-checked in
`SmithLandedMagnitudeRefuted`). The restricted diagonal / in-driver-image form does hold, and every
fixture pinned true here is diagonal, so those fixtures are evidence for the restricted form only.

The mandate `SmithReduceCompleteDriverStatement` stays uninhabited hypothesis-free; it is inhabited given
the keystone (`smithReduceCompleteDriverOfLandedPivotDividesMinor`) or, equivalently, given
`MinAbsEuclidLandsMinorGcdMagnitude` via `keystoneIffLandedMagnitudeEqMinorGcd.mpr`. This module supplies
the reverse magnitude bridge, closes the keystone into the full magnitude equivalence, and checks that
equation on the hardest seeds; it inhabits nothing hypothesis-free. The final-state re-threading route is
closed (each earlier pivot needs the pivot to divide the whole later sub-block, off-diagonal fill-in
included, whereas the exit-scan read-off supplies only divisibility of the later diagonals), and no
per-fold `Nat` measure closes the descent: `smithMinorAbsSum` rises on folds, `minNonzeroAbsWithin`
stalls, `pivotMagnitudeWithin` rises.

Raw Lean 4 on `Init`, structural only, no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`. Per-declaration zero-axiom gate in the FX1PolyAudit twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The reverse magnitude bridge: natAbs-equality forces exact divisibility -/

/-- If `|leftValue| = |rightValue|` then `leftValue` divides `rightValue` over the integers (cofactor
`1` or `-1`). Composes the bridges: `natDividesOfEq` off `natDividesRefl` gives `NatDivides` on the
magnitudes, `intDividesOfNatDividesNatAbs` raises to `Int`, and `intDividesOfNatAbsDivides`
sign-normalises the divisor. The reverse of `natDividesNatAbsOfIntDivides` at equal magnitudes, turning
the forward-only magnitude implication into a full equivalence. -/
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
hostile input/pivot by `decide` (kernel reduction, at or below the 4x4 defeq ceiling).  These are all
DIAGONAL seeds: evidence that the RESTRICTED (diagonal / in-driver-image) form holds, NOT that the
general keystone is TRUE — the general form is REFUTED (`SmithLandedMagnitudeRefuted`, r33). -/

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

/-! ## SURVIVING WALL (H2-SMITH r32, #2261) — [r33: the GENERAL form is REFUTED; only the RESTRICTED
    diagonal / in-driver-image form survives — see the r33 correction banner above and
    `SmithLandedMagnitudeRefuted`]

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
fabricated: `SmithReduceCompleteDriverStatement` stays UNINHABITED hypothesis-free.  [r33: the honest
pair is now `(SmithReduceCompleteDriverStatement ⟸ MinAbsEuclidLandsMinorGcdMagnitude, that identity
REFUTED in general — `SmithLandedMagnitudeRefuted`)`; the surviving OPEN content is the RESTRICTED
(diagonal / in-driver-image) form, a standalone multi-round arc.] -/

end FX1Poly.ComputerAlgebra

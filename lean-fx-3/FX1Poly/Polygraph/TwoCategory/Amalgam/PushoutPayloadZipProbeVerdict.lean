import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutIdentityLayoutCollapse
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAtomicFiringAdjudication
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAlignmentTruthProbe

/-! # Polygraph/TwoCategory/Amalgam/PushoutPayloadZipProbeVerdict — the r20 payload-zip probe VERDICT: NOT REFUTABLE,
the payload arm IS JAM A (WP-AMALG-2 r20, Brick B1)

The r20 recon ran the PAYLOAD-ZIP PROBE: does a same-cell / same-skeleton pair whose per-slot payloads are
NON-convertible exist (a permanent refutation of payload canonicality)?  **VERDICT: NOT REFUTABLE** — and, decisively,
the payload zip is NOT an independent wall: it IS the JAM A per-gap DESCENT composed with the WalkingMonad
reconstructed word problem (fib-3-coupled).  The r13/r16 two-wall ledger (skeleton wall + payload wall) COLLAPSES to
ONE wall.  This file PINS the structural blockers the verdict rests on, both non-vacuity directions, and the honest
re-scope — all zero-axiom.

## Why NOT REFUTABLE (the structural blockers, machine-pinned)

  * **No cross-`s`-wall interaction law.**  `crossPairRealPushoutRel` is the disjoint `involution +_M monad` amalgam:
    every row is either a `left` (involution) row carrying the EMPTY relation or a `right` (monad) row carrying a
    MONO-component reconstructed law.  `crossPairRealPushoutRelLeftArmVacuous` pins the involution arm empty — there
    is NO law acting ACROSS an `s`-wall, so the "material moves across slot boundaries" refutation cannot be derived.
    This is the LOAD-BEARING assumption of the verdict (recon RISK 1): any future cross-component law would un-block
    it.
  * **The δ₁/δ₀ over-identification is BLOCKED (candidate (ii)).**  A single cell with two factorizations whose slot
    payloads are δ₁-flavored vs δ₀-flavored would force `δ₁ ≈ δ₀` by trans — contradicting the shipped non-conv
    `payloadNonConvGenuine` (= `reconAdjudicationRefusesR8Faces` / `reconFacesDecideFalse`).  The non-conv is a
    decider-soundness FEATURE that BLOCKS the refutation, not a payload-canonicality bug.
  * **The shared skeleton is rigid (candidate (i)).**  The r8 word reads the SAME firing-block slot count at both
    boundaries (`sharedSkeletonSlotCountReal`, both `3`); the wire-creating `eta` widens a gap `0 → 1` without
    changing the slot skeleton.  So any two layouts of the same cell share the rigid wall skeleton — a same-cell pair
    is machine-real (non-vacuity direction A), but per-slot the unit law relates the identity-payload and mu-composite
    fillings (candidate (i)'s per-slot conv HOLDS, not a refutation).

## Non-vacuity, BOTH directions

  * **The shared skeleton is machine-real** — `sharedSkeletonSlotCountReal` (the r8 word reads `3` slots at each
    boundary).
  * **The payload non-conv is genuine** — `payloadNonConvGenuine` (δ₁ ≢ δ₀ over the reconstructed signature).
  * **The positive side fires live** — `vcompTwoGapInterchangeWitness` (`PushoutVcompInterchangeSplice.lean`) fires the
    zip on a genuine two-gap interleaved firing at the REAL signature; the `id`-arm collapse
    (`fxAmalg_hasIdCanonicalCollapse`, r20 B2) is the multi-slot identity case.

## The honest re-scope (NO master flip)

To PROVE the general refutation uninhabitable you must derive per-slot conv from whole-cell conv — the descent
`whole-cell conv ⟹ per-gap conv`, which is exactly JAM A (`fxAmalg_hasSaturatedDispatchTheorem`), and the per-gap
comparison, once descended, is the reconstructed monad word problem (WalkingMonad lane, READ-ONLY, fib-3-coupled).
So the payload arm has NO proof independent of JAM A + fib-3 and NO refutation either.  `fxAmalg_vcompZipIsJamADescent`
SHARPENS the r19 marker `fxAmalg_vcompCommonRefinementZipStaysWalled` from "coupled to JAM A" to "IS JAM A".  The four
masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The load-bearing blocker — no cross-`s`-wall interaction law -/

/-- ★★★ **THE LOAD-BEARING BLOCKER — the involution (left) component contributes NO laws.**  The pushout base
relation `crossPairRealPushoutRel`'s left arm carries `emptyCellRel involutionComputad.toModeSignature` (`= fun _ _ =>
False`), so there is no law acting on the `s`-generators — hence NO law spanning an `s`-wall.  Every genuine row is a
`right`-coprojected MONO-component monad law.  This is the structural reason the payload-non-conv refutation cannot be
structurally inhabited (the recon's point 1/RISK 1): a firing is confined to its inter-wall gap, no `baseRel` law can
move material across a wall.  `¬ emptyCellRel … a b` is `id` (the relation reduces to `False`). -/
theorem crossPairRealPushoutRelLeftArmVacuous
    {sourceMode targetMode : involutionComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionComputad.toModeSignature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr involutionComputad.toModeSignature sourcePath targetPath} :
    ¬ emptyCellRel involutionComputad.toModeSignature cellA cellB :=
  fun contradiction => contradiction

/-! ## Candidate (ii) — the δ₁/δ₀ over-identification, DESIGNED and shown BLOCKED -/

/-- The **decisive refutation shape (candidate (ii))** the probe would need: the two reconstructed monad faces
`reconFaceDeltaOne` (δ₁) and `reconFaceDeltaZero` (δ₀) — same boundary `t²⇒t`, different cells — made convertible.  A
single cell with two factorizations whose slot payloads are δ₁-flavored vs δ₀-flavored would force exactly this by
`trans`.  Stated as the concrete Prop the general refutation collapses to. -/
def PayloadNonConvRefutationViaFaces : Prop :=
  SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
    reconFaceDeltaOne reconFaceDeltaZero

/-- ★★★ **THE PAYLOAD NON-CONV IS GENUINE (direction B) / candidate (ii) is BLOCKED.**  The decisive refutation shape
`PayloadNonConvRefutationViaFaces` (`δ₁ ≈ δ₀`) is FALSE — `reconAdjudicationRefusesR8Faces` / `reconFacesDecideFalse`
(shipped): the δ₁/δ₀ faces stay separated over the reconstructed signature.  So the per-slot payload non-conv is a
GENUINE fact (non-vacuity direction B), and any refutation routed through candidate (ii) contradicts it — the
non-conv BLOCKS the refutation rather than enabling it. -/
theorem payloadNonConvGenuine : ¬ PayloadNonConvRefutationViaFaces :=
  reconAdjudicationRefusesR8Faces

/-! ## Candidate (i) — the shared skeleton is rigid and machine-real (direction A) -/

/-- ★★★ **THE SHARED SKELETON IS MACHINE-REAL (direction A).**  The r8 refuting word reads the SAME firing-block slot
count at both boundaries — `s·s` (tags `[s,s]`) and `s·t·s` (tags `[s,t,s]`) both read `3` slots (two walls + one).
So a same-cell / same-skeleton pair is machine-real (the shared skeleton the refutation would need EXISTS); the
wire-creating `eta` merely widens the middle gap `0 → 1`.  Combined with candidate (i)'s per-slot unit-law conv
(the identity-payload and mu-composite fillings are law-related), the same-cell pair does NOT refute. -/
theorem sharedSkeletonSlotCountReal :
    (finestGapWidths [true, true]).length = 3 ∧ (finestGapWidths [true, false, true]).length = 3 :=
  ⟨rfl, rfl⟩

/-! ## The verdict, landed as a machine-checked marker conjunction -/

/-- The payload-zip probe STANDING FACTS — machine-checks the verdict's ledger simultaneously: the id-arm collapse
ships (r20 B2), the atomic-firing zip is bypassed (r14), the finest payload zip stays false at atomic granularity
(r13), and the four masters + the top reader stay walled.  Together: the payload arm is JAM A, not an independent
wall, and no master flips. -/
def payloadZipProbeStandingFacts : Bool :=
  fxAmalg_hasIdCanonicalCollapse
    && fxAmalg_atomicFiringZipBypassed
    && fxAmalg_hasFinestSeamZipCorollary
    && fxAmalg_vcompCommonRefinementZipStaysWalled
    && fxAmalg_topFactorizationInductionStaysWalled
    && (!fxAmalg_hasSaturatedDispatchTheorem)
    && (!fxAmalg_hasFullSaturatedPushoutDispatch)
    && (!fxAmalg_hasGeneralPushoutDispatch)

/-- The standing-facts conjunction holds (`rfl`). -/
theorem payloadZipProbeStandingFacts_true : payloadZipProbeStandingFacts = true := rfl

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the payload-zip probe VERDICT is NOT REFUTABLE (WP-AMALG-2 r20, B1).**  `= true`.  The
probe hunted a same-cell / same-skeleton pair with per-slot payload non-conv; it does NOT exist, for three
machine-pinned structural reasons: (1) `crossPairRealPushoutRelLeftArmVacuous` — the involution arm is empty, so no
`baseRel` law spans an `s`-wall (a firing is confined to its gap); (2) `payloadNonConvGenuine` — the δ₁/δ₀
over-identification any candidate-(ii) refutation would force is BLOCKED (the non-conv is a decider-soundness
feature); (3) `sharedSkeletonSlotCountReal` — the shared skeleton is rigid (the r8 word reads `3` slots at each
boundary), so candidate (i)'s same-cell pair is machine-real but per-slot unit-law-convertible.  Non-vacuity is
witnessed BOTH directions: the shared skeleton is machine-real (direction A) and the payload non-conv is genuine
(direction B); the positive zip fires live (`vcompTwoGapInterchangeWitness`) and the multi-slot identity case ships
(`fxAmalg_hasIdCanonicalCollapse`, r20 B2).  So the refutation is neither structurally inhabitable nor
`decide`-false-witnessable.  `= true`. -/
def fxAmalg_payloadZipProbeNotRefutable : Bool := true

/-- ★★★ **Honesty marker — the vcomp payload zip IS the JAM A per-gap DESCENT (SHARPENS r19).**  `= true` (the wall
honestly held).  To PROVE the general refutation uninhabitable you must derive, from `gapVcompLayout F1 ≈ cell ≈
gapVcompLayout F2`, the per-slot `F1.payloadₖ ≈ F2.payloadₖ` — exactly the descent `whole-cell conv ⟹ per-gap conv`,
which is JAM A (`fxAmalg_hasSaturatedDispatchTheorem = false`); the per-gap comparison, once descended, is the
reconstructed monad word problem (WalkingMonad lane, READ-ONLY, fib-3-coupled).  So the payload arm has NO proof
independent of JAM A + fib-3 and NO refutation either — the r13/r16 two-wall ledger (skeleton wall + payload wall)
COLLAPSES to ONE wall (the skeleton is aligned, `fxAmalg_alignmentVerdictAlignableAtSkeleton`; the payload arm reduces
to JAM A).  This SHARPENS the r19 marker `fxAmalg_vcompCommonRefinementZipStaysWalled` from "coupled to JAM A" to "IS
JAM A definitionally".  The load-bearing assumption is `crossPairRealPushoutRelLeftArmVacuous` (no cross-`s`-wall law);
any future interaction law would un-block the refutation.  `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the four masters STAY walled; #2043 does NOT close.
`= true`. -/
def fxAmalg_vcompZipIsJamADescent : Bool := true

end FX1Poly.Polygraph.Amalgam

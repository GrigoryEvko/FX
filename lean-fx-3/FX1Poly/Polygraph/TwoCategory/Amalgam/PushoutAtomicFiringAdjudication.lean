import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutReconstructedWordGapSplice
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPayloadZip

/-! # Polygraph/TwoCategory/Amalgam/PushoutAtomicFiringAdjudication — the atomic-firing adjudication: the finest
payload zip is BYPASSED by the reseat/splice route (WP-AMALG-2 r14, Brick B3)

r13 (`PushoutFinestPayloadZip`) named the obstruction: `finestLayout` is the correct common refinement of the 1-cell
SKELETON but NOT of the PAYLOADS — its `finestLetterPair` sets identity payloads, so `gapUpperLayout nil
(finestLayout G)` is (up to free absorption) the IDENTITY on `G`, while a real firing (`mu : t·t ⇒ t` spanning two
letters) is ATOMIC and cannot be re-sliced into per-letter identity slots without destroying it.  The genuine
FINEST payload zip is therefore FALSE at atomic granularity — recorded in place by
`fxAmalg_hasFinestSeamZipCorollary`.

## The adjudication (decisive: the zip is BYPASSED)

The reseat + splice route does NOT consume the coarse-vs-finest payload zip.  Tracing the assembly's ACTUAL
consumption chain (B2):

  * `multiGapShiftedSplice` operates on `ShiftedGapFill`s whose gaps are WHOLE atomic firings — one gap-slot per
    firing, composed across the inert `s`-walls by `hcompCongr`.  It NEVER slices a firing into per-letter slots.
  * the per-gap content `reconWordGapFill` decides/lifts at the WHOLE-word (firing-block) granularity — the whole
    within-gap word stack `word ccL ⊟ word ccR` collapses via the reconstructed word multiplicativity (B1), never
    per-letter.

So the finest payload zip (`pushoutFactorizeVcompSeamFinest`, identity payloads) is the WRONG target and is
genuinely FALSE at atomic granularity — already refuted in place (`fxAmalg_hasFinestSeamZipCorollary` stands).  No
new refutation is required; this file CONFIRMS it stands and marks it dead FOR THIS ROUTE, exactly as the r9 seam
(one shared layout across both halves, cast-free `hcompCongr`) bypassed it.

## The honest self-attack, machine-witnessed

The reseat route is essential-surjectivity CONTENT, not an over-identifying identity-payload zip: it FIRES on the
mergeable and REFUSES the non-mergeable.

  * FIRES: `wordMul_vcompReconstructed_smoke_merge` (B1) — the r8 gap `[t,t]` merge `t²⇒t`.
  * REFUSES: `reconAdjudicationRefusesR8Faces` — the r8 non-mergeable δ₁/δ₀ faces stay separated
    (`reconFacesDecideFalse`, shipped); the reseat, being a lift of `wordMul_vcompGen` which respects
    `composeCounts`, cannot manufacture their equality.

## What STAYS WALLED (no flip)

This adjudicates the zip as BYPASSED — it does NOT close the top factorisation.  What the assembly still needs is a
DIFFERENT object: the TOP firing-block FACTORISATION `pushoutFactorize` (the reader that produces the
`ShiftedGapFill` list off an ARBITRARY cell's boundary — `blockDecompose↔composePath` + `mergeFrameIntoHead/Tail`).
The reseat provides the per-gap generic content, NOT that top reader.  `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`; `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`;
`fxAmalg_hasFinestSeamZipCorollary` STAYS `true` (the zip stays false at atomic granularity — this file records that
the route does not need it).  #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The honest self-attack, machine-witnessed -/

/-- ★★ **The reseat route REFUSES the r8 non-mergeable faces.**  The two reconstructed monad faces
`reconFaceDeltaOne` (δ₁, monotone map `[1]`) and `reconFaceDeltaZero` (δ₀, monotone map `[0]`) are NOT convertible
over the reconstructed signature (`reconFacesDecideFalse`, shipped).  The reseat/splice route, being a lift of
`wordMul_vcompGen` which respects `composeCounts`, therefore cannot manufacture their equality — the honest
non-over-identification that distinguishes essential-surjectivity CONTENT from the FALSE identity-payload finest
zip.  Paired with the FIRING witness `wordMul_vcompReconstructed_smoke_merge` (B1): the route fires on the
mergeable, refuses the non-mergeable. -/
theorem reconAdjudicationRefusesR8Faces :
    ¬ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
        reconFaceDeltaOne reconFaceDeltaZero :=
  reconFacesDecideFalse

/-! ## The adjudication landed as a machine-checked marker conjunction -/

/-- The adjudication CONJUNCTION — machine-checks that all three standing facts hold simultaneously: the reseat
ships (B1), the multi-gap gap-EZ splice on the reseat ships (B2), and the finest payload zip stays false at atomic
granularity (r13, dead for this route).  Together they are the atomic-firing adjudication: the zip is BYPASSED, the
firing-block splice ships, the top factorisation stays walled. -/
def reconAtomicFiringAdjudication : Bool :=
  fxAmalg_hasReconstructedWordVcompReseat
    && fxAmalg_pushoutNormalFormSpliceShips
    && fxAmalg_hasFinestSeamZipCorollary

/-- The adjudication conjunction holds (`rfl`). -/
theorem reconAtomicFiringAdjudication_true : reconAtomicFiringAdjudication = true := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the atomic-firing zip is BYPASSED by the reseat/splice route (WP-AMALG-2 r14, B3).**
`= true`.  Tracing the assembly's actual consumption (B2): `multiGapShiftedSplice` hosts each firing atomically (one
gap-slot per firing, composed by `hcompCongr` across the inert `s`-walls) and `reconWordGapFill` decides/lifts at
the whole-word (firing-block) granularity — the route NEVER slices a firing into per-letter identity slots.  So the
finest payload zip (`pushoutFactorizeVcompSeamFinest`, identity payloads) is the WRONG target and is genuinely FALSE
at atomic granularity — already recorded (`fxAmalg_hasFinestSeamZipCorollary` stands, NOT flipped); this file
confirms it stands and marks it DEAD for this route, exactly as the r9 seam bypassed it.  The route is
essential-surjectivity CONTENT: it FIRES on the mergeable (`wordMul_vcompReconstructed_smoke_merge`, B1) and REFUSES
the non-mergeable (`reconAdjudicationRefusesR8Faces`, the r8 δ₁/δ₀ faces).  The machine-checked
`reconAtomicFiringAdjudication_true` conjoins the three standing facts.

This does NOT close the top factorisation: the assembly still needs the firing-block reader `pushoutFactorize`
(produce the `ShiftedGapFill` list off an ARBITRARY cell), which the reseat does not provide.
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.  `= true`. -/
def fxAmalg_atomicFiringZipBypassed : Bool := true

end FX1Poly.Polygraph.Amalgam

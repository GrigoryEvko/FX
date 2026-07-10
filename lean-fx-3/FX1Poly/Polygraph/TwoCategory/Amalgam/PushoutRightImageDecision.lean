import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageReflect
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecisionGen

/-! # Polygraph/TwoCategory/Amalgam/PushoutRightImageDecision — the TWO-SIDED right-image (single-gap) decider

`PushoutNormalForm.lean` shipped the B2-forward lift `pushoutRightImageCompletenessLift` (reconstructed conv ⟹
pushout conv of right-images); `PushoutRightImageReflect.lean` shipped the B2 CONVERSE `pushoutRightImageConvReflect`
(pushout conv of right-images ⟹ reconstructed conv).  Together they are the two-sided BICONDITIONAL for right-images:

  `SaturatedConvOver pushout crossPairRealPushoutRel (inclRight a) (inclRight b)
     ↔ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed a b`

Since the RHS is `Decidable` via the bespoke-free `monadReconstructedDecisionGen` (the B5 re-founding), the LHS is
`Decidable` too — a genuine TWO-SIDED decision procedure for pushout convertibility of right-coprojection images.

## What this closes and what STAYS OPEN (#2043 does NOT close)

This is the two-sided decision for the RIGHT-IMAGE (single-gap, pure component-2) fragment ONLY.  The FULL
saturated pushout dispatch (`fxAmalg_hasFullSaturatedPushoutDispatch`, `DispatchSaturated.lean`) decides ARBITRARY
interleaved boundaries, which additionally needs the MULTI-GAP SPLICE (`s`-interleaved words, the
`PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled` residual riding the consume-only `wordMul_vcomp`).
That is NOT discharged here, so `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false` and #2043 remains OPEN — the
advance is the single-gap fragment now being TWO-SIDED decidable (previously one-sided in `ReverseCompletenessLeg`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The two-sided right-image decision -/

/-- ★★★ **THE TWO-SIDED RIGHT-IMAGE DECIDER.**  For two reconstructed monad cells, `Decidable` whether their
right-coprojection images are pushout-convertible over the real-law relation `crossPairRealPushoutRel`.  Runs the
bespoke-free reconstructed decider `monadReconstructedDecisionGen`; its `isTrue` verdict lifts to a pushout conv via
the B2-forward `pushoutRightImageCompletenessLift`, its `isFalse` verdict refutes via the B2-converse
`pushoutRightImageConvReflect` (a pushout conv would reflect to a reconstructed conv, contradicting the verdict).
Both directions proof-carrying — the two-sided decision the single-gap fragment awaited. -/
def pushoutRightImageTwoSidedDecision
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) :
    Decidable (SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta)) :=
  match monadReconstructedDecisionGen cellAlpha cellBeta with
  | isTrue reconstructedConv => isTrue (pushoutRightImageCompletenessLift reconstructedConv)
  | isFalse reconstructedNonConv =>
      isFalse (fun pushoutConv => reconstructedNonConv (pushoutRightImageConvReflect pushoutConv))

/-! ## Non-vacuity: the decider decides real convertible / non-convertible right-image pairs -/

/-- The two-sided decider's Bool observability. -/
def pushoutRightImageDecidesTwoSided
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) : Bool :=
  match pushoutRightImageTwoSidedDecision cellAlpha cellBeta with
  | isTrue _ => true
  | isFalse _ => false

/-- ★★ **The two-sided decider DECIDES the associativity foldings' right-images CONVERTIBLE** (`= true`) — the
isTrue side, on a genuinely-different reconstructed pair. -/
theorem pushoutRightImageDecidesTwoSided_assoc :
    pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell = true := by
  simp only [pushoutRightImageDecidesTwoSided, pushoutRightImageTwoSidedDecision]
  cases monadReconstructedDecisionGen reconAssocLeftCell reconAssocRightCell with
  | isTrue _ => rfl
  | isFalse hn => exact absurd reconAssocReflectsTrue hn

/-- ★★ **The two-sided decider DECIDES the two monad faces' right-images NON-convertible** (`= false`) — the isFalse
side, on the separating reconstructed pair δ₁ / δ₀.  The genuine two-sided verdict the single-gap fragment awaited. -/
theorem pushoutRightImageDecidesTwoSided_faces :
    pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero = false := by
  simp only [pushoutRightImageDecidesTwoSided, pushoutRightImageTwoSidedDecision]
  cases monadReconstructedDecisionGen reconFaceDeltaOne reconFaceDeltaZero with
  | isTrue conv => exact absurd conv reconFacesReflectFalse
  | isFalse _ => rfl

/-! ## Observability -/

-- The two-sided decider on the associativity foldings' right-images: expect `true`.
#eval pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell
-- The two-sided decider on the two monad faces' right-images: expect `false`.
#eval pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the TWO-SIDED right-image (single-gap) decision SHIPS.**  `= true`:
`pushoutRightImageTwoSidedDecision` is a genuine `Decidable` for pushout convertibility of right-coprojection images
over `crossPairRealPushoutRel`, assembled from the B2-forward lift `pushoutRightImageCompletenessLift` (isTrue) and
the B2-converse `pushoutRightImageConvReflect` (isFalse), routed off the bespoke-free `monadReconstructedDecisionGen`
(the B5 re-founding).  Both verdicts LIVE: `true` on the associativity foldings' right-images
(`pushoutRightImageDecidesTwoSided_assoc`), `false` on the two monad faces' right-images
(`pushoutRightImageDecidesTwoSided_faces`).  This upgrades the `ReverseCompletenessLeg` ONE-sided leg to a TWO-sided
decision for the single-gap fragment.  `= true`. -/
def fxAmalg_hasRightImageTwoSidedDecision : Bool := true

/-- **Honesty marker — the FULL saturated pushout dispatch STAYS WALLED; #2043 does NOT close.**  `= true` (the wall
is honestly held).  The two-sided decision ships for the RIGHT-IMAGE (single-gap, pure component-2) fragment only.
The FULL dispatch `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) decides ARBITRARY interleaved
boundaries, additionally needing the MULTI-GAP SPLICE for `s`-interleaved words
(`PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled`, riding the consume-only `wordMul_vcomp` owned by the
WalkingMonad lane).  That is NOT discharged here, so `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`,
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`, and #2043 remains OPEN at the shared-generator
scope (WP-AMALG-3).  The advance: the single-gap fragment is now TWO-sided decidable.  No fabricated flip.  `= true`. -/
def fxAmalg_fullPushoutDispatchStaysWalledAfterRightImage : Bool := true

end FX1Poly.Polygraph.Amalgam

import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm

/-! # Polygraph/TwoCategory/Amalgam/ReverseCompletenessLeg — the reverse-completeness leg, driven by the
per-component decider (WP-AMALG-2 r3, B3)

`PushoutNormalForm.lean` (B2) shipped the base-case NF soundness `pushoutRightImageCompletenessLift`: a monad
convertibility of two pre-images transports UNCHANGED to a pushout convertibility of their right-coprojection
images.  This file ASSEMBLES that lift with the shipped TOTAL per-component decider `monadReconstructedDecision`
(`ReconstructedDecision.lean`, the unconditional reconstructed-signature decider) into a LIVE reverse-completeness
leg for the single-gap (right-image) fragment: whatever the monad decider certifies convertible, the pushout
inherits — proof-carrying, driven by the actual decision procedure.

## What lands (each zero-axiom, structural)

  * **`pushoutRightImageDecidesConv`** — the LIVE routing (`Bool`): run `monadReconstructedDecision` on a
    reconstructed pair; `true` iff it certifies them convertible.
  * **`pushoutRightImageConvOfDecided`** — the PROOF extraction: `pushoutRightImageDecidesConv … = true` yields the
    transported pushout convertibility of the right-images (via B2's lift).  Router + extractor = the leg.
  * **`pushoutRightImageDecidesConv_assoc` / `_leftUnit` / `_faces`** — the leg fires on the two associativity
    foldings and the left-unit law (`= true`) and correctly declines the two separating monad faces (`= false`),
    each derived from the shipped conv / non-conv verdicts (NOT kernel-reducing the decider).
  * **`pushoutAssocRightImagesConvViaDecider`** — the DECIDER-DRIVEN pushout convertibility of the associativity
    foldings, extracted through the router.

## What STAYS WALLED — #2043 does NOT close (the honest verdict, every marker named)

This leg is the isTrue (completeness) direction for the SINGLE-GAP fragment only.  The FULL reverse-completeness /
saturated dispatch stays open on THREE residuals, so NO full-dispatch marker flips:

  * **the multi-gap splice** — `s`-interleaved boundaries (walls present) need the gap-EZ splice
    (`PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled`);
  * **the LEFT-image fragment** — the left coprojection `inclusionLeftTwoReal` with real 2-generators does not
    exist (`DispatchLedger.lean` jam); only the thin `inclusionLeftTwo` ships;
  * **the isFalse REFLECTION (conservativity)** — a two-sided right-image decider needs "pushout non-conv of images
    ⟹ monad non-conv of pre-images" (the Nelson-Oppen / Baader-Tinelli purification for the wire-creating
    generators, OR the reconstructed `convOfMapEq` + fold-preservation-under-`mapCellAlong`), neither authored here.

Hence `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) and `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) STAY `false` — HELD, not fabricated — and `fxAmalg_realLawCompletenessStaysWalled`
(`RealLawDispatch.lean`) STAYS `true`.  #2043 remains OPEN; the advance is the single-gap reverse-completeness leg
now being LIVE off the shipped per-component decider.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The LIVE reverse-completeness leg for the single-gap (right-image) fragment -/

/-- ★★ **The LIVE routing (`Bool`).**  Run the shipped TOTAL reconstructed decider `monadReconstructedDecision` on
a reconstructed monad pair; `true` iff it certifies them convertible.  The Bool observability of the per-component
decider feeding the pushout. -/
def pushoutRightImageDecidesConv
    {sourceMode targetMode : Fin monadComputad.modeCount}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) : Bool :=
  match monadReconstructedDecision cellAlpha cellBeta with
  | isTrue _ => true
  | isFalse _ => false

/-- ★★★ **THE REVERSE-COMPLETENESS LEG (B3), driven by the per-component decider.**  When the router certifies a
reconstructed pair convertible (`pushoutRightImageDecidesConv … = true`), the monad convertibility it found is
transported UNCHANGED, via the B2 base-case lift `pushoutRightImageCompletenessLift`, to a pushout convertibility of
the right-coprojection images over the REAL-law relation `crossPairRealPushoutRel`.  Router + this extractor = the
single-gap fragment of the reverse-completeness decision, assembled proof-carrying from B2 + the per-component
decider.  The multi-gap / left-image / isFalse-reflection residuals keep the FULL decision walled (see the file
docstring). -/
theorem pushoutRightImageConvOfDecided
    {sourceMode targetMode : Fin monadComputad.modeCount}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath)
    (certified : pushoutRightImageDecidesConv cellAlpha cellBeta = true) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta) := by
  simp only [pushoutRightImageDecidesConv] at certified
  revert certified
  cases monadReconstructedDecision cellAlpha cellBeta with
  | isTrue conv => intro _; exact pushoutRightImageCompletenessLift conv
  | isFalse _ => intro certified; exact Bool.noConfusion certified

/-! ## The leg fires on real convertible pairs and declines non-convertible ones (non-vacuity) -/

/-- ★★ **The leg fires on associativity** (`= true`) — derived from the shipped decider verdict
`reconAssocReflectsTrue`, so no kernel reduction of the decision procedure. -/
theorem pushoutRightImageDecidesConv_assoc :
    pushoutRightImageDecidesConv reconAssocLeftCell reconAssocRightCell = true := by
  simp only [pushoutRightImageDecidesConv]
  cases monadReconstructedDecision reconAssocLeftCell reconAssocRightCell with
  | isTrue _ => rfl
  | isFalse hn => exact absurd reconAssocReflectsTrue hn

/-- ★★ **The leg fires on left-unit** (`= true`) — derived from the shipped verdict `reconLeftUnitReflectsTrue`. -/
theorem pushoutRightImageDecidesConv_leftUnit :
    pushoutRightImageDecidesConv reconLeftUnitCell reconIdTCell = true := by
  simp only [pushoutRightImageDecidesConv]
  cases monadReconstructedDecision reconLeftUnitCell reconIdTCell with
  | isTrue _ => rfl
  | isFalse hn => exact absurd reconLeftUnitReflectsTrue hn

/-- ★★ **The leg correctly DECLINES the separating monad faces** (`= false`) — the two reconstructed faces δ₁ / δ₀
are non-convertible (`reconFacesReflectFalse`), so the router returns `false`.  The leg is not vacuously positive. -/
theorem pushoutRightImageDecidesConv_faces :
    pushoutRightImageDecidesConv reconFaceDeltaOne reconFaceDeltaZero = false := by
  simp only [pushoutRightImageDecidesConv]
  cases monadReconstructedDecision reconFaceDeltaOne reconFaceDeltaZero with
  | isTrue conv => exact absurd conv reconFacesReflectFalse
  | isFalse _ => rfl

/-- ★★ **The DECIDER-DRIVEN pushout convertibility** — the two associativity foldings' right-images are
pushout-convertible, extracted THROUGH the router (`pushoutRightImageDecidesConv_assoc`), demonstrating the leg is
proof-carrying end-to-end.  Same conclusion as B2's `pushoutAssocGapConv`, but routed through the LIVE decider. -/
theorem pushoutAssocRightImagesConvViaDecider :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconAssocLeftCell)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
        reconAssocRightCell) :=
  pushoutRightImageConvOfDecided reconAssocLeftCell reconAssocRightCell pushoutRightImageDecidesConv_assoc

/-! ## Observability -/

-- The leg fires on the two associativity foldings (a genuinely-different single-gap pair): expect `true`.
#eval pushoutRightImageDecidesConv reconAssocLeftCell reconAssocRightCell
-- The leg fires on the left-unit law: expect `true`.
#eval pushoutRightImageDecidesConv reconLeftUnitCell reconIdTCell
-- The leg does NOT fire on the two separating monad faces δ₁ / δ₀ (non-convertible): expect `false`.
#eval pushoutRightImageDecidesConv reconFaceDeltaOne reconFaceDeltaZero

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the single-gap reverse-completeness leg is LIVE off the per-component decider
(WP-AMALG-2 r3, B3).**  `= true`: `pushoutRightImageDecidesConv` (the router) + `pushoutRightImageConvOfDecided`
(the extractor) assemble the shipped TOTAL reconstructed decider `monadReconstructedDecision` with the B2 base-case
lift `pushoutRightImageCompletenessLift` into a proof-carrying reverse-completeness leg for the single-gap
(right-image) fragment — the per-component decider's positive verdicts transport to pushout convertibilities.  It
FIRES non-vacuously on the two associativity foldings and the left-unit law
(`pushoutRightImageDecidesConv_assoc` / `_leftUnit`, `= true`), yields the actual conv through the router
(`pushoutAssocRightImagesConvViaDecider`), and correctly declines the separating monad faces
(`pushoutRightImageDecidesConv_faces`, `= false`).  This is the reverse-completeness leg the recon named, restricted
to the NF base case.  `= true`. -/
def fxAmalg_hasRightImageReverseCompleteness : Bool := true

/-- **Honesty marker — the FULL reverse-completeness / saturated dispatch STAYS WALLED; #2043 does NOT close.**
`= true` (the wall is honestly held).  The single-gap leg ships (`fxAmalg_hasRightImageReverseCompleteness`), but
the FULL decision stays open on THREE named residuals: (1) the MULTI-GAP splice for `s`-interleaved boundaries
(`fxAmalg_pushoutNormalFormSpliceStaysWalled`, riding the CONSUME-only `wordMul_vcomp`); (2) the LEFT-image
fragment (`inclusionLeftTwoReal` does not exist — `DispatchLedger.lean` jam); (3) the isFalse REFLECTION /
conservativity (pushout non-conv of images ⟹ monad non-conv of pre-images — the Nelson-Oppen / Baader-Tinelli
purification for the wire-creating generators, or reconstructed `convOfMapEq` + fold-preservation-under-
`mapCellAlong`).  So NO full-dispatch marker flips: `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
`fxAmalg_realLawCompletenessStaysWalled` (`RealLawDispatch.lean`) STAYS `true`.  No fabricated flip.  `= true`. -/
def fxAmalg_fullReverseCompletenessStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam

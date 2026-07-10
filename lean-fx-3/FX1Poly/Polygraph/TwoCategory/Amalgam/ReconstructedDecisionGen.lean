import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecision
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen

/-! # Polygraph/TwoCategory/Amalgam/ReconstructedDecisionGen — the GENERIC-PRIMARY reconstructed-signature decider
(the SaturatedOver re-founding, Amalgam-side)

`ReconstructedDecision.lean` shipped the UNCONDITIONAL reconstructed-signature decider `monadReconstructedDecision`,
built on `monadReconstructedDecisionViaReflection`, which internally runs the BESPOKE `monadSaturatedTwoCellDecision`
(bridged by `monadSaturated_iff_generic`).  So the LIVE reverse-completeness decision's constant-closure still
contains the bespoke inductive `MonadSaturatedTwoCellConv` and the bespoke decider `monadSaturatedTwoCellDecision`.

This file re-founds that decision on the BORN-GENERIC native decider.  `decideSaturatedConvOverMonadNative`
(`WalkingMonad/MonadNormalizeGen`) decides `SaturatedConvOver monadModeSignature MonadLawRel` — the SAME signature the
`reseatCell`-images live over — with its ENTIRE constant-closure certified free of `MonadSaturatedTwoCellConv` (the
exhaustive meta-walk).  Crucially, `reseatReflect` (`ReconstructedDecision.lean`) already consumes a GENERIC
`SaturatedConvOver monadModeSignature MonadLawRel` conv, and `monadReconRefutes` (`MonadReseat.lean`) already consumes
a GENERIC refutation — so NO `monadSaturated_iff_generic` bridge is needed at all: the native decider's verdict feeds
both legs directly.

## What ships (each zero-axiom, structural, ASCII-only)

  * **`monadReconstructedDecisionGen`** — the total `DecidableSaturatedConvForRel monadComputad.toModeSignature
    MonadLawRelReconstructed` obtained by running `decideSaturatedConvOverMonadNative` on the `reseatCell`-images:
    isTrue via `reseatReflect` (the reconstructed-signature reflection), isFalse via `monadReconRefutes` (the forward
    transport).  Same total decision as `monadReconstructedDecision`, but with the BESPOKE decider replaced by the
    born-generic native one in the running term.
  * **`monadReconstructedDecisionGen_faces` / `_assoc` / `_leftUnit`** — the gen decider LIVE on real reconstructed
    cells: it declines the two separating monad faces (`= false`) and certifies the associativity foldings and the
    left-unit law (`= true`), read off the shipped reconstructed-level verdicts (NOT kernel-reducing the native
    normalizer).

## The honest wall (the FILE-level import does NOT drop; the re-founding gate stays gated)

Re-pointing the LIVE decision onto `monadReconstructedDecisionGen` drops `monadSaturatedTwoCellDecision` +
`MonadSaturatedTwoCellConv` from the decision's CONSTANT-closure (a real, checkable provenance advance).  It does NOT
drop the FILE-level transitive import of `WalkingMonad/MonadSaturatedConv` / `MonadWordProblem`, which is pinned by
THREE roots untouched here: (1) `SaturatedOver.lean:2` imports `MonadSaturatedConv` to state
`monadSaturated_iff_generic` + `MonadLawRel` (the user-erosion sign-off, `fxAmalg_saturatedOverSignOffStaysGated`);
(2) `DeciderReseat.lean:3` directly imports `MonadWordProblem` for the P4 separation witness; (3)
`SaturatedRelationFamily.monadRelationFamily` uses the bespoke carrier.  Those retirements are named in the ledger.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generic-primary reconstructed-signature decider -/

/-- ★★ **The GENERIC-PRIMARY reconstructed-signature decider.**  A total `DecidableSaturatedConvForRel
monadComputad.toModeSignature MonadLawRelReconstructed` obtained by running the BORN-GENERIC native decider
`decideSaturatedConvOverMonadNative` (bespoke-constant-free) on the `reseatCell`-images.  The isTrue leg via the
reconstructed-signature reflection `reseatReflect` (which already consumes the generic conv), the isFalse leg via the
forward transport `monadReconRefutes` (which already consumes the generic refutation) — so NO `monadSaturated_iff_generic`
bridge is needed.  Same total decision as `monadReconstructedDecision`, with the bespoke `monadSaturatedTwoCellDecision`
replaced by the native decider in the running term. -/
def monadReconstructedDecisionGen :
    DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed :=
  fun cellAlpha cellBeta =>
    match decideSaturatedConvOverMonadNative (reseatCell cellAlpha) (reseatCell cellBeta) with
    | isTrue hgen => isTrue (reseatReflect hgen)
    | isFalse hgen => isFalse (monadReconRefutes hgen)

/-! ## Both verdicts LIVE on real reconstructed cells (non-vacuity) -/

/-- ★★ **The gen decider certifies the reconstructed associativity foldings** (`isTrue`) — routed off the shipped
reconstructed verdict `reconAssocReflectsTrue` (NOT kernel-reducing the native normalizer). -/
theorem monadReconstructedDecisionGen_assoc :
    (match monadReconstructedDecisionGen reconAssocLeftCell reconAssocRightCell with
      | isTrue _ => true | isFalse _ => false) = true := by
  cases monadReconstructedDecisionGen reconAssocLeftCell reconAssocRightCell with
  | isTrue _ => rfl
  | isFalse hn => exact absurd reconAssocReflectsTrue hn

/-- ★★ **The gen decider certifies the reconstructed left-unit law** (`isTrue`) — routed off
`reconLeftUnitReflectsTrue`. -/
theorem monadReconstructedDecisionGen_leftUnit :
    (match monadReconstructedDecisionGen reconLeftUnitCell reconIdTCell with
      | isTrue _ => true | isFalse _ => false) = true := by
  cases monadReconstructedDecisionGen reconLeftUnitCell reconIdTCell with
  | isTrue _ => rfl
  | isFalse hn => exact absurd reconLeftUnitReflectsTrue hn

/-- ★★ **The gen decider DECLINES the two separating reconstructed monad faces** (`isFalse`) — routed off
`reconFacesReflectFalse`, so the decision is not vacuously positive. -/
theorem monadReconstructedDecisionGen_faces :
    (match monadReconstructedDecisionGen reconFaceDeltaOne reconFaceDeltaZero with
      | isTrue _ => true | isFalse _ => false) = false := by
  cases monadReconstructedDecisionGen reconFaceDeltaOne reconFaceDeltaZero with
  | isTrue conv => exact absurd conv reconFacesReflectFalse
  | isFalse _ => rfl

/-! ## Honesty markers -/

/-- ★★ **Honesty marker (`true`) — the GENERIC-PRIMARY reconstructed decider SHIPS.**  `monadReconstructedDecisionGen`
is a total `DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed` whose running term
uses the BORN-GENERIC native decider `decideSaturatedConvOverMonadNative` (bespoke-constant-free) in place of the
bespoke `monadSaturatedTwoCellDecision`, with the isTrue leg via `reseatReflect` and the isFalse leg via
`monadReconRefutes` — neither needing the `monadSaturated_iff_generic` bridge.  Both verdicts LIVE on real
reconstructed cells: isTrue on the associativity foldings and left-unit law (`monadReconstructedDecisionGen_assoc` /
`_leftUnit`), isFalse on the two separating monad faces (`monadReconstructedDecisionGen_faces`).  `= true`. -/
def fxAmalg_hasGenericPrimaryReconstructionDecision : Bool := true

/-- **Honesty marker (`true`) — the FILE-level bespoke import does NOT drop; the SaturatedOver re-founding stays
gated.**  `= true` (the wall is honestly held).  `monadReconstructedDecisionGen` drops the bespoke
`monadSaturatedTwoCellDecision` + `MonadSaturatedTwoCellConv` from the LIVE decision's CONSTANT-closure once the B3
router is re-pointed onto it — a real provenance advance — but the FILE-level transitive import of
`WalkingMonad/MonadSaturatedConv` / `MonadWordProblem` STAYS, pinned by three roots untouched here:
(1) `SaturatedOver.lean` imports `MonadSaturatedConv` to state `monadSaturated_iff_generic` + `MonadLawRel` (the
user-erosion sign-off `fxAmalg_saturatedOverSignOffStaysGated`); (2) `DeciderReseat.lean` directly imports
`MonadWordProblem` for the separation witness; (3) `SaturatedRelationFamily.monadRelationFamily` uses the bespoke
carrier.  Those retirements need the `SaturatedOver` split + the monad-lane `MonadDeltaModel` de-bespoking, named in
the dispatch ledger.  `= true`. -/
def fxAmalg_reFoundingFileImportStaysGated : Bool := true

end FX1Poly.Polygraph.Amalgam

import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/PushoutMultiGapSplice — the multi-gap NF FORWARD assembly (wall-inert splice)

`PushoutNormalForm.lean` shipped the BASE case (single-gap) NF soundness `pushoutRightImageCompletenessLift`, and
`RealLawDispatch.lean`'s `sInterleavedAssocLawConv` witnessed a single REAL law fired inside ONE `s`-wall.  This file
ships the FORWARD assembly of the gap-indexed NF: multiple right-image GAPS, each firing a real monad law, spliced
across FIXED `s`-walls into ONE boundary conv — pure congruence closure over `SaturatedConvOver`, wall-inert.

## The forward assembly is pure congruence closure

The gap-indexed coordinate (`PushoutNormalForm`): a boundary word factors into `s`-WALLS (component-1, inert, fixed
position) and `t`-GAPS (component-2, each a monad sub-cell).  A cell PRESENTED in wall/gap-whiskered form —
gap-images whiskered by the fixed `s`-walls and vertically composed — normalizes GAP-BY-GAP: each gap converts to
its monad NF in place (the base-case lift `pushoutRightImageCompletenessLift`, whiskered into position by the
`SaturatedConvOver` whisker congruences), the walls never move (they are identity whisker contexts).  So the whole
multi-gap boundary conv is assembled from the per-gap convs by the four one-hole congruences + `trans` — NO new
monad lemma, exactly the recon's "forward half".

## Non-vacuity: a THREE-gap, TWO-wall word normalized end-to-end

`threeGapWord` fires the reconstructed LEFT-UNIT law (`mu·(eta|>t) ⇒ id_t`) in THREE `t`-gaps of the interleaved
boundary `t·s·t·s·t` (two `s`-walls at positions 2 and 4), each gap whiskered into place by the surrounding walls.
`threeGapSpliceConv` normalizes it END-TO-END to `threeGapWordNormalForm` (all three gaps collapsed to `id_t`),
splicing the three per-gap left-unit collapses across the two inert `s`-walls — a genuine multi-gap NF-soundness
witness, wall-inert, hypothesis-free.

## The residual, pinned (the FACTORIZATION half)

This is the FORWARD assembly: given a cell ALREADY in wall/gap-whiskered form, it normalizes gap-by-gap.  The
DEEP residual — that an ARBITRARY interleaved pushout cell FACTORS into wall/gap-whiskered form — is the genuine
SPLICE crux, riding the consume-only `WalkingMonad/MonadNormalizeVcomp.wordMul_vcomp` (owned by the monad lane).
That is NOT authored here; it stays named in `PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The three-gap interleaved word and its normal form -/

/-- The real right coprojection at `involution +_M monad`, abbreviated. -/
abbrev multiGapInclRight : ComputadMorphismTwo monadComputad involutionMonadPushout :=
  inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes

/-- The right-image of a reconstructed left-unit gap `mu·(eta|>t) ⇒ id_t` — a pushout 2-cell `t ⇒ t`. -/
abbrev gapLeftUnitImage := mapCellAlong multiGapInclRight reconLeftUnitCell

/-- The right-image of the reconstructed identity gap `id_t` — the normalized gap `t ⇒ t`. -/
abbrev gapIdImage := mapCellAlong multiGapInclRight reconIdTCell

/-- ★★ **The per-gap collapse** — the shipped base-case lift makes the left-unit gap-image pushout-convertible to the
identity gap-image (`reconLeftUnitReflectsTrue` transported).  The single-gap NF collapse the splice replicates. -/
def gapCollapse :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      gapLeftUnitImage gapIdImage :=
  pushoutRightImageCompletenessLift reconLeftUnitReflectsTrue

/-- Fire a gap in position 1 (leftmost `t`), right-whiskered by the wall/gap context `s·t·s·t`. -/
abbrev gapPositionOne (gapCell : RawTwoCellExpr involutionMonadPushout.toModeSignature
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)) :=
  RawTwoCellExpr.whiskerRight
    (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath)))
    gapCell

/-- Fire a gap in position 2 (middle `t`), left-whiskered by `t·s` and right-whiskered by `s·t`. -/
abbrev gapPositionTwo (gapCell : RawTwoCellExpr involutionMonadPushout.toModeSignature
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)) :=
  RawTwoCellExpr.whiskerLeft (composePath monadPushTPath monadPushSPath)
    (RawTwoCellExpr.whiskerRight (composePath monadPushSPath monadPushTPath) gapCell)

/-- Fire a gap in position 3 (rightmost `t`), left-whiskered by the wall/gap context `t·s·t·s`. -/
abbrev gapPositionThree (gapCell : RawTwoCellExpr involutionMonadPushout.toModeSignature
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)
    (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)) :=
  RawTwoCellExpr.whiskerLeft
    (composePath monadPushTPath (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)))
    gapCell

/-- ★ **The THREE-gap interleaved word** — the left-unit law fired in all three `t`-gaps of `t·s·t·s·t`, the three
firings vertically composed.  A genuine two-`s`-wall, three-`t`-gap cell. -/
def threeGapWord :=
  RawTwoCellExpr.vcomp (gapPositionOne gapLeftUnitImage)
    (RawTwoCellExpr.vcomp (gapPositionTwo gapLeftUnitImage) (gapPositionThree gapLeftUnitImage))

/-- ★ **The THREE-gap word's NORMAL FORM** — every gap collapsed to `id_t`, walls unchanged. -/
def threeGapWordNormalForm :=
  RawTwoCellExpr.vcomp (gapPositionOne gapIdImage)
    (RawTwoCellExpr.vcomp (gapPositionTwo gapIdImage) (gapPositionThree gapIdImage))

/-- ★★★ **THE MULTI-GAP FORWARD SPLICE (non-vacuity: a THREE-gap word normalized end-to-end).**  `threeGapWord`
(the left-unit law fired in all three `t`-gaps of the two-`s`-wall boundary `t·s·t·s·t`) is
saturated-pushout-convertible to `threeGapWordNormalForm` (all gaps collapsed to `id_t`): the per-gap collapse
`gapCollapse` is whiskered into each position by the fixed `s`-walls (`whiskerLeftCongr` / `whiskerRightCongr`) and
the three collapses are spliced by the vcomp congruences + `trans` — the walls never move (they are identity whisker
contexts).  Pure congruence closure, wall-inert, hypothesis-FREE — the recon's forward-assembly half, executed on a
genuine multi-gap word. -/
def threeGapSpliceConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      threeGapWord threeGapWordNormalForm :=
  SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft
      (RawTwoCellExpr.vcomp (gapPositionTwo gapLeftUnitImage) (gapPositionThree gapLeftUnitImage))
      (SaturatedConvOver.whiskerRightCongr
        (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath)))
        gapCollapse))
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight (gapPositionOne gapIdImage)
        (SaturatedConvOver.vcompCongrLeft (gapPositionThree gapLeftUnitImage)
          (SaturatedConvOver.whiskerLeftCongr (composePath monadPushTPath monadPushSPath)
            (SaturatedConvOver.whiskerRightCongr (composePath monadPushSPath monadPushTPath) gapCollapse))))
      (SaturatedConvOver.vcompCongrRight (gapPositionOne gapIdImage)
        (SaturatedConvOver.vcompCongrRight (gapPositionTwo gapIdImage)
          (SaturatedConvOver.whiskerLeftCongr
            (composePath monadPushTPath (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)))
            gapCollapse))))

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the multi-gap NF FORWARD assembly SHIPS (non-vacuous on a THREE-gap word).**  `= true`:
`threeGapSpliceConv` normalizes `threeGapWord` (the reconstructed left-unit law fired in all THREE `t`-gaps of the
two-`s`-wall boundary `t·s·t·s·t`) END-TO-END to `threeGapWordNormalForm` (all gaps collapsed to `id_t`), splicing
the three per-gap base-case collapses (`gapCollapse` = the shipped `pushoutRightImageCompletenessLift`) across the
two FIXED `s`-walls by the `SaturatedConvOver` whisker + vcomp congruences.  Pure congruence closure, wall-inert,
hypothesis-FREE — the forward half of the gap-indexed splice, on a genuine multi-gap word (two `s`-walls, three
`t`-gaps).  `= true`. -/
def fxAmalg_hasMultiGapForwardSplice : Bool := true

/-- **Honesty marker — the FACTORIZATION half of the splice STAYS WALLED.**  `= true` (the wall is honestly held).
The FORWARD assembly ships: a cell PRESENTED in wall/gap-whiskered form normalizes gap-by-gap (`threeGapSpliceConv`).
The DEEP residual — that an ARBITRARY interleaved pushout cell FACTORS into wall/gap-whiskered form (so its whole
boundary has one canonical NF) — is the genuine SPLICE crux, riding the consume-only
`WalkingMonad/MonadNormalizeVcomp.wordMul_vcomp` (word-multiplicativity within a gap, owned by the WalkingMonad
lane).  It is NOT authored here; it stays named in `PushoutNormalForm.fxAmalg_pushoutNormalFormSpliceStaysWalled`.
So `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`; #2043 remains OPEN.  No
fabricated flip.  `= true`. -/
def fxAmalg_multiGapFactorizationStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam

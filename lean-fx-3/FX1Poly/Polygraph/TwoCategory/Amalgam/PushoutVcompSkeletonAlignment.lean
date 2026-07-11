import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFiringBlockReader
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompMultiGapSeam

/-! # Polygraph/TwoCategory/Amalgam/PushoutVcompSkeletonAlignment — the vcomp arm's shared-middle skeleton alignment,
now a PROVEN theorem via the B4 general slot invariant (WP-AMALG-2 r17, Brick B3)

r16 (`PushoutVcompMultiGapSeam.lean`) fired the vcomp arm at genuine two-gap granularity, CONSUMING the skeleton share
as the B1 MARKER `fxAmalg_alignmentVerdictAlignableAtSkeleton`.  The r17 recon's B3 wants the vcomp arm's alignment
consumed via the SKELETON INVARIANT: for `vcomp cellUpper cellLower` (`cellUpper : A ⇒ M`, `cellLower : M ⇒ B`), both
halves read the SHARED middle `M` at the SAME canonical firing-block slot count.  B4's general invariant
`finestGapWidths_slotCount_domCod_eq` (the canonical slot count is a dom↔cod invariant for ANY cell) makes that
alignment a THEOREM, not a marker: applied to `cellUpper` it gives `slotCount A = slotCount M`, applied to `cellLower`
it gives `slotCount M = slotCount B`.

## The vcomp slot-count chain (the recon's B3 point), machine-checked

For the r16 two-gap layout `[interleavedAssocGapPair, interleavedLeftUnitGapPair]` at wall `pushoutTrivialWall`, the
UPPER half `gapUpperLayout` (`gapDomLayout ⇒ gapMidLayout`) and the LOWER half `gapLowerLayout`
(`gapMidLayout ⇒ gapCodLayout`) share the middle 1-cell `gapMidLayout pushoutTrivialWall …`.  The B4 invariant applied
to each half proves the two halves read that shared middle at the SAME slot count — the recon's
`slotCount(canonical cellUpper) = wallCount M + 1 = slotCount(canonical cellLower)` chain, now off the general
`wallLetterCount_dom_eq_cod`.

## What the r14 splice does — and does NOT — do here (no conflation)

The recon's honest distinction: the factorization SEAM rides `vcompGapInterchangeSplice` (r7), NOT the r14
`multiGapShiftedSplice`.  The r14 `reconWordGapFill` / `reconWordThreeGapSplice` is the per-gap CONTENT normalizer the
DECISION consumes (comparing two canonical layouts' per-gap right-images), landing at the DECISION, not the
factorization seam.  This file's alignment feeds the seam / the decision's skeleton pre-check; the r14 splice is a
SEPARATE, downstream (decision) ingredient.  Recorded as an honesty marker, NOT wired here.

## What STAYS WALLED (no flip)

This proves the shared-middle slot-count ALIGNMENT (a necessary skeleton precondition) via the B4 invariant, on the r16
two-multi-gap-cell vcomp.  It does NOT supply the per-gap DESCENT (JAM A: `fxAmalg_hasSaturatedDispatchTheorem =
false`, the convex-block projection the wire-creating `eta`/`mu` violate) — the alignment is necessary, NOT sufficient
for the decision.  The masters STAY: `fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch`
`false`, `fxAmalg_topFactorizationInductionStaysWalled` `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  `rfl` / term-mode.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shared-middle skeleton alignment (the B4 invariant consumed) -/

/-- ★★★ **THE VCOMP ARM'S SHARED-MIDDLE SLOT-COUNT ALIGNMENT — a PROVEN theorem.**  For the r16 two-gap layout
`[interleavedAssocGapPair, interleavedLeftUnitGapPair]` at wall `pushoutTrivialWall`, the UPPER half `gapUpperLayout`
(`gapDomLayout ⇒ gapMidLayout`) and the LOWER half `gapLowerLayout` (`gapMidLayout ⇒ gapCodLayout`) read the SHARED
middle 1-cell `gapMidLayout pushoutTrivialWall …` at the SAME canonical firing-block slot count.  The left conjunct is
`finestGapWidths_slotCount_domCod_eq (gapUpperLayout …)` (`slotCount(dom) = slotCount(mid)`), the right is the same
invariant on `gapLowerLayout …` (`slotCount(mid) = slotCount(cod)`).  This is the recon's B3 vcomp slot-count chain —
both halves present the middle at `wallCount M + 1` slots — now off the GENERAL `wallLetterCount_dom_eq_cod`, not a
per-path computation.  The alignment the multi-gap vcomp seam consumes, made a theorem. -/
theorem vcompMultiGapSharedMiddleSlotCountAligns :
    (finestGapWidths (pushoutPathTags
        (gapDomLayout pushoutTrivialWall
          [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length
      = (finestGapWidths (pushoutPathTags
          (gapMidLayout pushoutTrivialWall
            [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length
    ∧ (finestGapWidths (pushoutPathTags
        (gapMidLayout pushoutTrivialWall
          [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length
      = (finestGapWidths (pushoutPathTags
          (gapCodLayout pushoutTrivialWall
            [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length :=
  ⟨finestGapWidths_slotCount_domCod_eq
      (gapUpperLayout pushoutTrivialWall
        [interleavedAssocGapPair, interleavedLeftUnitGapPair]),
   finestGapWidths_slotCount_domCod_eq
      (gapLowerLayout pushoutTrivialWall
        [interleavedAssocGapPair, interleavedLeftUnitGapPair])⟩

/-- ★★ **THE WHOLE-VCOMP dom↔cod slot count agrees.**  The vertical composite
`vcomp (gapUpperLayout …) (gapLowerLayout …)` (the r16 multi-gap vcomp cell) has its domain (`gapDomLayout`) and
codomain (`gapCodLayout`) read the SAME canonical slot count — `finestGapWidths_slotCount_domCod_eq` applied to the
whole vcomp cell.  The end-to-end consequence of the shared-middle alignment: both boundaries of the composed cell key
to the same firing-block skeleton. -/
theorem vcompMultiGapWholeSlotCountAgrees :
    (finestGapWidths (pushoutPathTags
        (gapDomLayout pushoutTrivialWall
          [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length
      = (finestGapWidths (pushoutPathTags
          (gapCodLayout pushoutTrivialWall
            [interleavedAssocGapPair, interleavedLeftUnitGapPair]))).length :=
  finestGapWidths_slotCount_domCod_eq
    (RawTwoCellExpr.vcomp
      (gapUpperLayout pushoutTrivialWall
        [interleavedAssocGapPair, interleavedLeftUnitGapPair])
      (gapLowerLayout pushoutTrivialWall
        [interleavedAssocGapPair, interleavedLeftUnitGapPair]))

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the vcomp arm's shared-middle SKELETON ALIGNMENT is now a THEOREM (WP-AMALG-2 r17, B3).**
`= true`.  `vcompMultiGapSharedMiddleSlotCountAligns` proves — via the B4 general invariant
`finestGapWidths_slotCount_domCod_eq` applied to each half — that the UPPER and LOWER cells of the r16 two-gap vcomp read
the SHARED middle 1-cell at the SAME canonical firing-block slot count (the recon's B3 `slotCount cellUpper = wallCount M
+ 1 = slotCount cellLower` chain), and `vcompMultiGapWholeSlotCountAgrees` closes the whole-vcomp dom↔cod slot equality.
This UPGRADES the r16 consumption (which recorded the skeleton share as the B1 MARKER
`fxAmalg_alignmentVerdictAlignableAtSkeleton`) to a machine-checked THEOREM off the general
`wallLetterCount_dom_eq_cod`.  The shipped multi-gap vcomp seam (`pushoutVcompMultiGapSeamWitness`, `slotCount = 2`,
r16) fires GIVEN the aligned halves; this file proves the alignment they share.  `= true`. -/
def fxAmalg_hasVcompSkeletonAlignmentTheorem : Bool := true

/-- ★★ **Honesty marker — the r14 splice lands at the DECISION, NOT the factorization seam (no conflation) —
WP-AMALG-2 r17, B3.**  `= true` (the honest distinction).  The vcomp factorization SEAM rides
`vcompGapInterchangeSplice` (r7); the shared-middle alignment here is the skeleton precondition it consumes.  The r14
`reconWordGapFill` / `reconWordThreeGapSplice` is the per-gap CONTENT normalizer the DECISION consumes (comparing two
canonical layouts' per-gap right-images) — a SEPARATE, downstream ingredient landing at the decision, NOT wired into the
seam.  The skeleton alignment (this file) is NECESSARY but NOT SUFFICIENT for the decision: the per-gap DESCENT (JAM A,
`fxAmalg_hasSaturatedDispatchTheorem = false`, the convex-block projection the wire-creating `eta`/`mu` violate) STAYS
the residual.  Named node: the per-gap descent.  `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`; `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043
does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_vcompR14SpliceLandsAtDecisionNotSeam : Bool := true

end FX1Poly.Polygraph.Amalgam

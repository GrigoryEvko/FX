import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerLeftJunctionCanonical
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppendFold
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonicalWhiskerRight

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerRightJunctionMerge — the whiskerRight (trailing) direction of the
producer junction merge law, its route-agreement probe, and the honest naming of the whiskerRight junction CONV /
CANONICAL residual (WP-AMALG-2 r21, Brick B2 — arm b')

Arm b (`PushoutWhiskerLeftJunctionCanonical.lean`) SHIPPED the whiskerLeft junction merge (conv + `CanonicalFactorization`).
Arm b' is the whiskerRight DUAL.  The r18 machinery is banked: the full trailing fold `whiskerRight_conv_appendFinalWall`
(`PushoutWhiskerRightAppendFold.lean`, cons-case landed) and the `n → n` canonical merge arm
`pushoutFactorizeWhiskerRightMergeLayout` (`PushoutFactorizeCanonicalWhiskerRight.lean`).

## The producer merge law is DIRECTION-SYMMETRIC (the shared inheritance piece)

The r21 B1 producer law `firingBlockLayout_composePath` splices the SECOND factor's producer run into the FIRST
factor's last block.  For the trailing (whiskerRight) direction the composed 1-cell is `composePath bodyPath oneCell`,
so the law reads directly with `bodyPath` as the frame and `oneCell` as the appended run —
`firingBlockLayout_composePathRight` is the SAME theorem with the roles named for the trailing side.  This is what
WP-AMALG-3 inherits for both whisker directions.

## What is HONESTLY OWED (arm b' conv / canonical — the named residual)

The whiskerRight junction CANONICAL factorization is NOT a syntactic mirror of arm b.  Arm b folds the frame's LAST
block into the body's HEAD WALL (`mergeFrameIntoHead`, count-neutral) and prepends the frame's other blocks.  The
whiskerRight dual must APPEND the frame's blocks past the body's TRAILING WALL (`finalWall`) — and the body's tail is a
WALL, not a block-with-gap, so the tail-append fusion (the body's `finalWall` + the frame's leading block) is a fresh
surgery: fold the frame's FIRST block into `finalWall` (the r18 append), then append `fb_1 … fb_k` as fresh trailing
slots absorbing the accumulated wall into `fb_1`'s wall.  The conv `whiskerRightFiringBlockMerge` and its
`whiskerRightJunctionCanonical` are the named residual below — a distinct tail-append induction over the r18 append,
NOT authored this round.  `fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true` (it flips only when BOTH arm b AND
arm b' ship their `CanonicalFactorization`); #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The producer merge law, trailing (whiskerRight) direction -/

/-- ★★★ **THE PRODUCER MERGE LAW (trailing direction).**  `firingBlockLayout (composePath bodyPath oneCell) =
spliceFrameBlocks (firingBlockLayout bodyPath) oneCell` — the coarse producer on a body-then-frame composite splices
the frame's run into the body's last block (junction fusion at the body/frame seam).  The SAME `firingBlockLayout_composePath`
with `bodyPath` as the leading factor and `oneCell` as the trailing run — the producer law is direction-symmetric; this
is the whiskerRight-side inheritance piece for WP-AMALG-3. -/
theorem firingBlockLayout_composePathRight
    (bodyPath oneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    firingBlockLayout (composePath bodyPath oneCell)
      = spliceFrameBlocks (firingBlockLayout bodyPath) oneCell :=
  firingBlockLayout_composePath bodyPath oneCell

/-- ★★★ **THE TRAILING JUNCTION SPLICE SLOT COUNT.**  `(spliceFrameBlocks (firingBlockLayout bodyPath) oneCell).length
= wallCount(bodyPath) + wallCount(oneCell) + 1` — the canonical spec count for `whiskerRight oneCell body` (domain
`composePath (dom body) oneCell`).  The SAME slot-count law, roles named for the trailing side. -/
theorem spliceFrameBlocks_firingBlockLayout_slotCountRight
    (bodyPath oneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (spliceFrameBlocks (firingBlockLayout bodyPath) oneCell).length
      = pushoutPathWallCount bodyPath + pushoutPathWallCount oneCell + 1 :=
  spliceFrameBlocks_firingBlockLayout_slotCount bodyPath oneCell

/-! ## The route-agreement truth-probe (trailing side) -/

/-- ★★★ **TRUTH-PROBE (trailing route agreement).**  On a `t·t` body followed by an `s·s` frame, the producer directly
on `composePath (t·t) (s·s)` equals the splice of the two runs — the trailing junction merge probed before the
surgery. -/
theorem whiskerRightJunctionMerge_producerRouteAgrees :
    firingBlockLayout (composePath (composePath monadPushTPath monadPushTPath) unitSplitsWallDom)
      = spliceFrameBlocks (firingBlockLayout (composePath monadPushTPath monadPushTPath)) unitSplitsWallDom :=
  firingBlockLayout_composePathRight (composePath monadPushTPath monadPushTPath) unitSplitsWallDom

/-- ★★★ **PROBE (trailing junction slot count on `t·t` body / `s·s` frame) — THREE slots.**  `(spliceFrameBlocks
(firingBlockLayout (t·t)) (s·s)).length = 3` (`rfl`): `wallCount(t·t) + wallCount(s·s) + 1 = 0 + 2 + 1 = 3` — the two
frame walls open two trailing slots, the fused junction is the leading one. -/
theorem whiskerRightJunctionMerge_sliceSlotCount :
    (spliceFrameBlocks (firingBlockLayout (composePath monadPushTPath monadPushTPath))
      unitSplitsWallDom).length = 3 := rfl

/-! ## Observability -/

-- The trailing junction slot count: `t·t` body / `s·s` frame (expect `3`).
#eval (spliceFrameBlocks (firingBlockLayout (composePath monadPushTPath monadPushTPath))
        unitSplitsWallDom).length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the whiskerRight producer merge law (trailing direction) SHIPS (WP-AMALG-2 r21, B2).**
`= true`.  `firingBlockLayout_composePathRight` re-states the direction-symmetric producer merge law for the trailing
seam (`firingBlockLayout (composePath bodyPath oneCell) = spliceFrameBlocks (firingBlockLayout bodyPath) oneCell`), with
its canonical slot count (`spliceFrameBlocks_firingBlockLayout_slotCountRight`) and the trailing route-agreement probe
(`whiskerRightJunctionMerge_producerRouteAgrees`, slot count `3`).  This is the whiskerRight-side producer inheritance
piece; the r18 append machinery (`whiskerRight_conv_appendFinalWall`) + the `n → n` merge arm
(`pushoutFactorizeWhiskerRightMergeLayout`) are already banked.  `= true`. -/
def fxAmalg_hasFiringBlockProducerMergeLawRight : Bool := true

/-- ★★★ **Honesty marker — the whiskerRight junction CONV + CANONICAL FACTORIZATION STAY the NAMED RESIDUAL (WP-AMALG-2
r21, B2).**  `= true` (the wall honestly held).  Arm b shipped `whiskerLeftFiringBlockMerge` + `whiskerLeftJunctionCanonical`
by folding the frame's LAST block into the body's HEAD WALL (count-neutral `mergeFrameIntoHead`) and prepending the
frame's other blocks.  The whiskerRight dual is NOT a syntactic mirror: the body's TAIL is a WALL (`finalWall`), not a
block-with-gap, so the tail-append fusion — fold the frame's FIRST block into `finalWall` (r18 append), then append
`fb_1 … fb_k` as fresh trailing slots absorbing the accumulated wall into `fb_1`'s wall — is a fresh tail-append
induction over the r18 `whiskerRight_conv_appendFinalWall`.  The named node: `whiskerRightFiringBlockMerge`
(`whiskerRight (gapDomLayout nil frameBlocks) (gapVcompLayout finalWall bodyPairs) ≈ castBoundary (…) (tail-append
layout)`, structural on the frame's `AllIdBlocks`, base = r18 append, cons = `whiskerRightComp` peel + IH with updated
`finalWall` + fresh trailing block) and `whiskerRightJunctionCanonical (oneCell) (bodyFact) : CanonicalFactorization
(whiskerRight oneCell body)`.  Until BOTH arm b AND this arm b' ship their `CanonicalFactorization`,
`fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true`; #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_whiskerRightJunctionCanonicalStaysResidual : Bool := true

end FX1Poly.Polygraph.Amalgam

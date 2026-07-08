import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenReadback
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenCastBridgeB
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenFactor

/-! # mode-3 keystone — Piece I STRAIGHTEN producer (i, handedness B): the SEED SPECIALIZATION

`SpineValleyStraightenSeed` connected the abstract handedness-A collapse `mergedSharedLegFramesCollapse` to the
CONCRETE readback bands of a `zigZagSharedLeg` cup·cap pair, discharging the `straightenStepConv` hypothesis for the
LEFT-snake orientation.  This file is the co/op MIRROR — handedness B (the RIGHT snake): it specializes
`mergedSharedLegFramesCollapseB` to the concrete readback bands of a RIGHT-snake shared-leg pair.

The connection is CLEAN — no genuine cast reconciliation:

  * ★ **`pinnedCupBandB_eq_merged` / `pinnedCapBandB_eq_merged`** (`rfl`) — a cup atom pinned to `unit` with LEFT
    context `lc · R` reads back EXACTLY as `mergedCupFrameB lc rc`; a cap atom pinned to `counit` with right context
    `R · rc` reads back EXACTLY as `mergedCapFrameB lc rc`.  DEFINITIONAL.
  * ★ **`pinnedZigZagBandCollapseB`** — `mergedSharedLegFramesCollapseB` fired at the pinned bands; the abstract
    associativity casts and the readback casts relate the SAME endpoints, hence proof-irrelevance-equal (`rfl`).
  * ★ **`zigZagBandCollapseB`** — the generic handedness-B closer: destructure both atoms, pin the two generators,
    read the factorization off `sharedLegFactorHandednessB` (`lcCup = lcCap · R`, `rcCap = R · rcCup`), substitute,
    and fire `mergedSharedLegFramesCollapseB` — everything lands by defeq.

## What this does NOT close (gates stay `false`)

This is handedness B ONLY.  With `zigZagBandCollapseA` (LEFT) already shipped, both arms of the width dichotomy are
now covered; the A/B-dispatching assembly `straightenCellDescentStep` + the oracle swap are the next step (separate
file).  So `CellStraightenStepInput` is NOT yet discharged here.  `convOfMapEq` and the fib-3 gate flags stay
`false`.  This brick reads NO `matchingOf` / `partnerIndexOf` / arc structure.

Raw Lean 4 + Init; the band-merged identity is `rfl`, the cast reconciliation is proof irrelevance, the generic
closer is destructure + generator casing + factorization `subst`; `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The pinned atoms and the band ↔ merged-frame identity -/

/-- A cup atom pinned to the `unit` generator with RIGHT-snake shared-leg left context `leftContext · R`. -/
def pinnedCupAtomB {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget) :
    SpineAtom adjunctionModeSignature overallSource overallTarget :=
  ⟨AdjunctionMode.base, AdjunctionMode.base,
    composePath leftContext (singletonModalityPath AdjunctionModality.right),
    ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base, adjunctionLeftThenRight,
    AdjunctionTwoCell.unit, rightContext⟩

/-- The pinned cup band IS the merged cup frame — DEFINITIONALLY. -/
theorem pinnedCupBandB_eq_merged {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget) :
    readbackBand (pinnedCupAtomB leftContext rightContext)
      = mergedCupFrameB leftContext rightContext := rfl

/-- A cap atom pinned to the `counit` generator with RIGHT-snake shared-leg right context `R · rightContext`. -/
def pinnedCapAtomB {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget) :
    SpineAtom adjunctionModeSignature overallSource overallTarget :=
  ⟨AdjunctionMode.tip, AdjunctionMode.tip, leftContext,
    adjunctionRightThenLeft, ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip,
    AdjunctionTwoCell.counit,
    composePath (singletonModalityPath AdjunctionModality.right) rightContext⟩

/-- The pinned cap band IS the merged cap frame — DEFINITIONALLY. -/
theorem pinnedCapBandB_eq_merged {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget) :
    readbackBand (pinnedCapAtomB leftContext rightContext)
      = mergedCapFrameB leftContext rightContext := rfl

/-! ## The pinned-pair collapse (proof irrelevance handles the casts) -/

/-- ★ **The pinned-pair band collapse (handedness B).**  `mergedSharedLegFramesCollapseB` fired at the pinned
readback bands.  The abstract associativity casts (`mergedFramesAlignB` / `mergedFramesEndpointB`) and the readback
casts (`coh.symm` / `reconnect.symm`) relate the SAME endpoints, hence are equal by proof irrelevance. -/
theorem pinnedZigZagBandCollapseB {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.tip)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base overallTarget)
    (coh : atomFrameTarget (pinnedCupAtomB leftContext rightContext)
      = atomFrameSource (pinnedCapAtomB leftContext rightContext))
    (reconnect : atomFrameSource (pinnedCupAtomB leftContext rightContext)
      = atomFrameTarget (pinnedCapAtomB leftContext rightContext)) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand (pinnedCupAtomB leftContext rightContext))
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm
          (readbackBand (pinnedCapAtomB leftContext rightContext))))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (atomFrameSource (pinnedCupAtomB leftContext rightContext))) := by
  rw [pinnedCupBandB_eq_merged, pinnedCapBandB_eq_merged]
  exact mergedSharedLegFramesCollapseB leftContext rightContext

/-! ## The generic handedness-B band collapse -/

/-- ★★ **The generic handedness-B band collapse.**  For ANY cup·cap pair with the boundary coherence `coh`, the
reconnection `reconnect`, and the width-B verdict, the concrete readback-band collapse holds.  Destructure both
atoms, pin the two generators (`unit` / `counit` — the cross cases refuted by the tags), read off
`sharedLegFactorHandednessB` (`lcCup = lcCap · R`, `rcCap = R · rcCup`), substitute, and fire
`mergedSharedLegFramesCollapseB`.  This discharges `straightenStepConv`'s hypothesis for the RIGHT-snake
orientation. -/
theorem zigZagBandCollapseB {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (widthB : capAtom.leftContext.length + 1 = cupAtom.leftContext.length) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (atomFrameSource cupAtom)) := by
  obtain ⟨lmmCup, rmmCup, lcCup, domCup, codCup, genCup, rcCup⟩ := cupAtom
  obtain ⟨lmmCap, rmmCap, lcCap, domCap, codCap, genCap, rcCap⟩ := capAtom
  cases genCup with
  | counit => nomatch isCup
  | unit =>
    cases genCap with
    | unit => nomatch isCap
    | counit =>
      obtain ⟨lcCupEq, rcCapEq⟩ :=
        sharedLegFactorHandednessB lcCup rcCup lcCap rcCap coh widthB
      subst lcCupEq
      subst rcCapEq
      exact mergedSharedLegFramesCollapseB lcCap rcCup

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the SEED SPECIALIZATION (handedness B) is LANDED; the "cast reconciliation" is a `rfl`.**
The readback band of a pinned RIGHT-snake cup / cap atom IS the abstract merged cup / cap frame DEFINITIONALLY
(`pinnedCupBandB_eq_merged` / `pinnedCapBandB_eq_merged`, `rfl`), and firing `mergedSharedLegFramesCollapseB` at the
pinned bands closes the concrete collapse — proof irrelevance identifies the abstract associativity casts with the
readback casts.  `zigZagBandCollapseB` lifts this to a generic cup·cap pair by pinning the generators off the tags
and substituting `sharedLegFactorHandednessB`.  This DISCHARGES `straightenStepConv`'s band-collapse hypothesis for
the RIGHT-snake (handedness B) orientation — the co/op mirror of `zigZagBandCollapseA`.

  What this marker does NOT close (gates stay `false`): the A/B-dispatching assembly `straightenCellDescentStep` and
  the oracle swap.  So `CellStraightenStepInput` is NOT yet discharged; `convOfMapEq` and the fib-3 gate flags stay
  `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenSeedB : Bool := true

end FX1Poly.Polygraph

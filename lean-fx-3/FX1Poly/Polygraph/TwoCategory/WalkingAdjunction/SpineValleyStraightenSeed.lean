import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenReadback
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenCastBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenFactor

/-! # mode-3 keystone — Piece I STRAIGHTEN producer (i, handedness A): the SEED SPECIALIZATION

`SpineValleyStraightenReadback` reduced the STRAIGHTEN `stepConv` to one HYPOTHESIS: the concrete band collapse
`readbackBand cup ⊟ castBoundary (readbackBand cap) ≈ id`.  `SpineValleyStraightenCastBridge` shipped the ABSTRACT
merged-frame collapse `mergedSharedLegFramesCollapse` (handedness A); `SpineValleyStraightenFactor` shipped the
seed-rigidity factorization `sharedLegFactorHandednessA`.  This file connects them: it SPECIALIZES the abstract
collapse to the CONCRETE readback bands of a `zigZagSharedLeg` cup·cap pair (handedness A), discharging the
`straightenStepConv` hypothesis.

The connection is CLEAN — no genuine cast reconciliation:

  * ★ **`pinnedCupBand_eq_merged` / `pinnedCapBand_eq_merged`** (`rfl`) — a cup atom pinned to the `unit` generator
    with right context `L · rc` reads back EXACTLY as `mergedCupFrame lc rc`; a cap atom pinned to `counit` with
    left context `lc · L` reads back EXACTLY as `mergedCapFrame lc rc`.  DEFINITIONAL — the merged frame IS the
    readback band once the generator and the shared-leg context are pinned.
  * ★ **`pinnedZigZagBandCollapse`** — the pinned-pair collapse: `mergedSharedLegFramesCollapse` fired at the
    pinned bands.  The abstract collapse carries the `composePath`-associativity casts `mergedFramesAlign` /
    `mergedFramesEndpoint`; the readback carries `coh.symm` / `reconnect.symm`.  These cast pairs relate the SAME
    endpoints, so they are DEFINITIONALLY EQUAL by proof irrelevance — the "cast reconciliation" the design
    predicted collapses to a `rfl`.
  * ★ **`zigZagBandCollapseA`** — the generic handedness-A closer: for ANY cup·cap pair (`isCup` / `isCap`) with
    the boundary coherence `coh`, the reconnection `reconnect`, and the width-A verdict (`cupLeft + 1 = capLeft`),
    the concrete band collapse holds.  Proof: destructure both atoms, pin the two generators (`unit` / `counit`,
    the other cases refuted by the tags), read the factorization off `sharedLegFactorHandednessA` (`lcCap = lcCup ·
    L`, `rcCup = L · rcCap`), substitute, and fire `pinnedZigZagBandCollapse` — everything lands by defeq.

## What this does NOT close (gates stay `false`)

This is handedness A ONLY.  The width dichotomy `zigZagSharedLeg_widthDichotomy` is `A ∨ B`, so a total
`straightenCellDescentStep` also needs handedness B — the RIGHT-snake merged cast bridge (mirror of
`SpineValleyStraightenCastBridge`, feeding the shipped iterated-B collapse `generalContextFrameLegsCollapseB`),
NOT built here.  So `CellStraightenStepInput` is NOT yet discharged; the assembly + swap are separate.
`convOfMapEq` and the fib-3 gate flags stay `false`.  This brick reads NO `matchingOf` / `partnerIndexOf` / arc
structure — the shared-leg shape is `sharedLegFactorHandednessA`'s, not the matching's.

Raw Lean 4 + Init; the band-merged identity is `rfl`, the cast reconciliation is proof irrelevance, the generic
closer is destructure + generator casing + factorization `subst`; `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The pinned atoms and the band ↔ merged-frame identity -/

/-- A cup atom pinned to the `unit` generator with shared-leg right context `L · rightContext`. -/
def pinnedCupAtom {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget) :
    SpineAtom adjunctionModeSignature overallSource overallTarget :=
  ⟨AdjunctionMode.base, AdjunctionMode.base, leftContext,
    ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base, adjunctionLeftThenRight,
    AdjunctionTwoCell.unit,
    composePath (singletonModalityPath AdjunctionModality.left) rightContext⟩

/-- The pinned cup band IS the merged cup frame — DEFINITIONALLY. -/
theorem pinnedCupBand_eq_merged {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget) :
    readbackBand (pinnedCupAtom leftContext rightContext)
      = mergedCupFrame leftContext rightContext := rfl

/-- A cap atom pinned to the `counit` generator with shared-leg left context `leftContext · L`. -/
def pinnedCapAtom {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget) :
    SpineAtom adjunctionModeSignature overallSource overallTarget :=
  ⟨AdjunctionMode.tip, AdjunctionMode.tip,
    composePath leftContext (singletonModalityPath AdjunctionModality.left),
    adjunctionRightThenLeft, ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip,
    AdjunctionTwoCell.counit, rightContext⟩

/-- The pinned cap band IS the merged cap frame — DEFINITIONALLY. -/
theorem pinnedCapBand_eq_merged {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget) :
    readbackBand (pinnedCapAtom leftContext rightContext)
      = mergedCapFrame leftContext rightContext := rfl

/-! ## The pinned-pair collapse (proof irrelevance handles the casts) -/

/-- ★ **The pinned-pair band collapse.**  `mergedSharedLegFramesCollapse` fired at the pinned readback bands.  The
abstract collapse's associativity casts (`mergedFramesAlign` / `mergedFramesEndpoint`) and the readback casts
(`coh.symm` / `reconnect.symm`) relate the SAME endpoints, hence are equal by proof irrelevance — the reconciliation
is a `rfl`. -/
theorem pinnedZigZagBandCollapse {overallSource overallTarget : AdjunctionMode}
    (leftContext : ModalityPath adjunctionGraph overallSource AdjunctionMode.base)
    (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip overallTarget)
    (coh : atomFrameTarget (pinnedCupAtom leftContext rightContext)
      = atomFrameSource (pinnedCapAtom leftContext rightContext))
    (reconnect : atomFrameSource (pinnedCupAtom leftContext rightContext)
      = atomFrameTarget (pinnedCapAtom leftContext rightContext)) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand (pinnedCupAtom leftContext rightContext))
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm
          (readbackBand (pinnedCapAtom leftContext rightContext))))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (atomFrameSource (pinnedCupAtom leftContext rightContext))) := by
  rw [pinnedCupBand_eq_merged, pinnedCapBand_eq_merged]
  exact mergedSharedLegFramesCollapse leftContext rightContext

/-! ## The generic handedness-A band collapse -/

/-- ★★ **The generic handedness-A band collapse.**  For ANY cup·cap pair with the boundary coherence `coh`, the
reconnection `reconnect`, and the width-A verdict, the concrete readback-band collapse holds.  Destructure both
atoms, pin the two generators (`unit` / `counit` — the cross cases refuted by the tags), read off
`sharedLegFactorHandednessA` (`lcCap = lcCup · L`, `rcCup = L · rcCap`), substitute, and fire
`pinnedZigZagBandCollapse`.  This discharges `straightenStepConv`'s hypothesis for the LEFT-snake orientation. -/
theorem zigZagBandCollapseA {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (widthA : cupAtom.leftContext.length + 1 = capAtom.leftContext.length) :
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
      obtain ⟨lcCapEq, rcCupEq⟩ :=
        sharedLegFactorHandednessA lcCup rcCup lcCap rcCap coh widthA
      subst lcCapEq
      subst rcCupEq
      exact mergedSharedLegFramesCollapse lcCup rcCap

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the SEED SPECIALIZATION (handedness A) is LANDED; the "cast reconciliation" is a `rfl`.**
The readback band of a pinned cup / cap atom IS the abstract merged cup / cap frame DEFINITIONALLY
(`pinnedCupBand_eq_merged` / `pinnedCapBand_eq_merged`, `rfl`), and firing `mergedSharedLegFramesCollapse` at the
pinned bands closes the concrete collapse — the abstract associativity casts and the readback casts relate the
SAME endpoints, so proof irrelevance identifies them (no genuine transport).  `zigZagBandCollapseA` lifts this to
a generic cup·cap pair by pinning the generators off the tags and substituting `sharedLegFactorHandednessA`.  This
DISCHARGES `straightenStepConv`'s band-collapse hypothesis for the LEFT-snake (handedness A) orientation.

  What this marker does NOT close (gates stay `false`): handedness B — the width dichotomy is `A ∨ B`, so a total
  `straightenCellDescentStep` needs the RIGHT-snake merged cast bridge (mirror of `SpineValleyStraightenCastBridge`,
  feeding the shipped `generalContextFrameLegsCollapseB`) plus the A/B-dispatching assembly + the swap.  So
  `CellStraightenStepInput` is NOT yet discharged; `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenSeed : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeGenCase

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeVcompCase — the `vcomp` case of the top factorization: two
composable cells share ONE gap's vertical split; the seam fires on the r8 composite; the general two-layout
alignment stays the atomic-firing residual (WP-AMALG-2 r15, Brick B3)

The `vcomp` case is the historical crux.  Two shipped pieces bound it: the SEAM `pushoutFactorizeVcompSeam`
(`PushoutVcompSeam.lean`, r9) which assembles `vcomp cellUpper cellLower` GIVEN two half-factorizations sharing ONE
`(finalWall, pairs)` layout, and the r8 composite witness `vcompSplitBlockFactorization` which factors `vcomp
unitSplitsWallCell unitThenFaceLowerCell : s·s ⇒ s·t·t·s` through a SINGLE shared block.  This file ships the BASE
case (two composable cells occupying ONE gap's vertical split) and re-probes the r8 composite.

## The base case — two cells in one gap's vertical split

`vcomp cellUpper cellLower` (`cellUpper : A ⇒ M`, `cellLower : M ⇒ B`) factors as a SINGLE gap whose vertical split
carries the two halves directly: `upper := cellUpper`, `lower := cellLower`, gap middle `M` (the SHARED boundary).
Unlike the trivial `pushoutFactorizeSingleGap` (which buries the whole `vcomp` in `upper`), this respects the
vertical split — the two firings sit in the same gap, `cellUpper` above `cellLower`, sharing the middle 1-cell `M`.
The convertibility is the generic nil-framed gadget reduction `nilFramedGadgetConv` (both `id`-whisker gadgets
stripped by the whisker unitors — cleaner than the `gen` case, no `vcompIdRight` needed).

## What STAYS WALLED (no flip)

This is the vcomp case when the two halves occupy ONE shared gap.  The GENERAL case — align two ARBITRARY multi-gap
IH layouts `(fwU, pairsU)`, `(fwL, pairsL)` to a common FIRING-BLOCK refinement so both halves factor through it —
is the atomic-firing residual (`PushoutFinestPayloadZip.lean:157`: a `mu : t·t ⇒ t` spanning two letters is ATOMIC
and cannot be re-sliced into per-letter identity slots).  The seam CONSUMES a shared layout; PRODUCING it from two
arbitrary layouts is unbuilt.  `fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`)
STAYS `true`; the masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generic nil-framed gadget reduction -/

/-- ★★ **The nil-framed gadget reduction.**  For ANY payload `A ⇒ B`, the doubly-`id`-whiskered gadget
`hcomp (id id) (hcomp payload (id id))` is saturated-convertible to the boundary-cast payload (right-unit cast on
both boundaries).  The leading `id`-whisker strips by `whiskerLeft_conv_hcompIdLeading` + the unitor
`whiskerLeftUnit`; the trailing by `whiskerRight_conv_hcompIdTrailing` + the unitor `whiskerRightUnit`.  This is the
common reduction all single-gap layouts share (both the `gen` and `vcomp` base cases). -/
theorem nilFramedGadgetConv {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (payload : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (ModalityPath.nil oneMode))
        (RawTwoCellExpr.hcomp payload (RawTwoCellExpr.id (ModalityPath.nil oneMode))))
      (RawTwoCellExpr.castBoundary (composePath_identityPath_right sourcePath).symm
        (composePath_identityPath_right targetPath).symm payload) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.symm
        (whiskerLeft_conv_hcompIdLeading (ModalityPath.nil oneMode)
          (RawTwoCellExpr.hcomp payload (RawTwoCellExpr.id (ModalityPath.nil oneMode)))))
      (SaturatedConvOver.ofFull
        (TwoCellConvFull.whiskerLeftUnit
          (RawTwoCellExpr.hcomp payload (RawTwoCellExpr.id (ModalityPath.nil oneMode))))))
    (SaturatedConvOver.trans
      (SaturatedConvOver.symm
        (whiskerRight_conv_hcompIdTrailing (ModalityPath.nil oneMode) payload))
      (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerRightUnit payload)))

/-! ## The `vcomp` base case — two cells in one gap's vertical split -/

/-- The **vcomp single-gap block** — one `VcompGapPair` whose vertical split carries two composable cells directly:
`upper := cellUpper` (`A ⇒ M`), `lower := cellLower` (`M ⇒ B`), gap middle `M` the shared boundary, no wall. -/
def vcompSingleGapPair {signature : ModeSignature} {oneMode : signature.graph.Mode}
    {pathA pathM pathB : ModalityPath signature.graph oneMode oneMode}
    (cellUpper : RawTwoCellExpr signature pathA pathM)
    (cellLower : RawTwoCellExpr signature pathM pathB) : VcompGapPair signature oneMode where
  wall := ModalityPath.nil oneMode
  gapDom := pathA
  gapMid := pathM
  gapCod := pathB
  upper := cellUpper
  lower := cellLower

/-- ★★★ **THE `vcomp` CASE (single shared gap).**  `vcomp cellUpper cellLower` (`cellUpper : A ⇒ M`, `cellLower :
M ⇒ B`) factors as a SINGLE gap whose vertical split carries the two halves directly (`upper = cellUpper`,
`lower = cellLower`, shared middle `M`).  Boundary casts the right-unit `composePath_identityPath_right`,
convertibility `nilFramedGadgetConv` on the payload `vcomp cellUpper cellLower`.  This respects the vertical split —
the two firings share the gap, undivided by walls.  The base case of the `vcomp` alignment. -/
def pushoutFactorizeVcompSingleGap {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    {pathA pathM pathB : ModalityPath signature.graph oneMode oneMode}
    (cellUpper : RawTwoCellExpr signature pathA pathM)
    (cellLower : RawTwoCellExpr signature pathM pathB) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.vcomp cellUpper cellLower) where
  finalWall := ModalityPath.nil oneMode
  pairs := [vcompSingleGapPair cellUpper cellLower]
  domEq := (composePath_identityPath_right pathA).symm
  codEq := (composePath_identityPath_right pathB).symm
  conv := SaturatedConvOver.symm (nilFramedGadgetConv (RawTwoCellExpr.vcomp cellUpper cellLower))

/-! ## Concrete probe — a vertical composite of two pushout gens -/

/-- ★★ **`eta` then `delta_1` factored as one vcomp gap.**  `vcomp eta delta_1 : id ⇒ t·t` (unit then face, sharing
the middle `t`) factors as a single gap whose split carries `eta` (`id ⇒ t`) above `delta_1` (`t ⇒ t·t`).  A concrete
`vcomp`-case factorization at the REAL pushout signature. -/
def pushoutEtaThenFaceVcompFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.vcomp pushoutEta pushoutFaceDeltaOne) :=
  pushoutFactorizeVcompSingleGap crossPairRealPushoutRel pushoutEta pushoutFaceDeltaOne

/-! ## The r8 composite re-probe — the seam fires through ONE shared block -/

/-- ★★ **RE-PROBE (r8 composite) — the seam factors it through ONE shared block.**  The r8 refuting cell composed
with a face firing inside its split block (`vcomp unitSplitsWallCell unitThenFaceLowerCell : s·s ⇒ s·t·t·s`) factors,
via the shipped `vcompSplitBlockFactorization`, through EXACTLY ONE shared `VcompGapPair` (`pairs.length = 1`) — the
seam's alignment succeeds on the r8 shape because the two halves share the middle 1-cell `s·t·s`.  The self-attack
5a, re-confirmed here: what r8 could not zip through a wall scaffold, the seam factors through the shared middle. -/
theorem r8ComposedSeamProbe : vcompSplitBlockFactorization.pairs.length = 1 := rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the `vcomp` base case (single shared gap) SHIPS; the general two-layout alignment STAYS
the atomic-firing residual (WP-AMALG-2 r15, B3).**  `= true`.  `vcomp cellUpper cellLower` factors as a single gap
whose vertical split carries the two halves directly (`pushoutFactorizeVcompSingleGap`, respecting the split — shared
middle `M`, convertibility `nilFramedGadgetConv`).  Non-vacuous at the REAL pushout signature:
`vcomp eta delta_1 : id ⇒ t·t` factors (`pushoutEtaThenFaceVcompFactorization`).  The r8 composite re-probes: the
shipped seam factors `vcomp unitSplitsWallCell unitThenFaceLowerCell` through EXACTLY ONE shared block
(`r8ComposedSeamProbe`, `pairs.length = 1`), self-attack 5a re-confirmed.

This is the `vcomp` case when the two halves occupy ONE shared gap.  It does NOT ship the general alignment: two
ARBITRARY multi-gap IH layouts re-sliced to a common FIRING-BLOCK refinement (the atomic-firing residual — a
`mu : t·t ⇒ t` spanning two letters cannot be re-sliced into per-letter slots, `PushoutFinestPayloadZip.lean:157`).
The seam CONSUMES a shared layout; PRODUCING it from two arbitrary layouts is the unbuilt hard core.
`fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.
No fabricated flip.  `= true`. -/
def fxAmalg_hasVcompSingleGapCase : Bool := true

end FX1Poly.Polygraph.Amalgam

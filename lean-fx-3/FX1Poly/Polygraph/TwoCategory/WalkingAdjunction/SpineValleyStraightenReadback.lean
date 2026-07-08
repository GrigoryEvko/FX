import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenNext
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellLift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackConv

/-! # mode-3 keystone — Piece I STRAIGHTEN producer (iii-b): the readback realization `stepConv`

`SpineValleyStraightenNext` shipped the deleted `next` (the readback of the delete-surgery chain).  COMMUTE got its
`stepConv` free via spine-trace-equivalence (`commuteAtomSwapCellLift`) — a permutation preserves the trace.  But
deletion is NOT trace-preserving (the spine shrinks by two), so STRAIGHTEN's `stepConv : SaturatedTwoCellConv cell
next` is a genuinely NEW obligation: it must be realized THROUGH the readback, straightening the located cup·cap
band-pair away.  This file ships that realization, taking the concrete band-collapse witness `atomFrame cup ⊟
castBoundary (atomFrame cap) ≈ id` as a HYPOTHESIS (piece i supplies it by pinning the seed generators).

  * ★ **`framedChain_readback_consForm`** — the cons-readback form (`rfl` after `cases`): a chain over a cons list
    reads back as its head's `atomFrame` band vertically composed with its tail's readback (up to the source cast
    `framedChain_consSource`).  Applying it at a variable chain avoids the rigid-source indexed inversion.
  * ★ **`framedPairReadbackStraightens`** — the RV middle-four STEP on the readback: a width-2 matched chain
    `cupBand ⊟ (capBand ⊟ tail)` straightens to `tail` (spliced by the reconnection cast), via the shipped
    `snakePrefixStraightens` fed the concrete band collapse — the casts threaded by `vcomp_castBoundaryLeft` +
    cast cancellation.
  * ★ **`framedDeleteChainReadbackConv`** — the RV WIDTH induction on the readback carrier: the deleted-chain
    readback is saturated-convertible to the original chain's readback, by STRUCTURAL recursion on the prefix (each
    prefix atom whiskered through by `vcompCongrRight` under the source cast).  No `WellFounded.fix`, no arc read.
  * ★ **`straightenStepConv`** — the `stepConv`: `cell ≈full cell.cellChain.readback = chain.readback ≈ next`,
    composing `cellChain_readback_convFull`, `castAtoms_readback`, and `framedDeleteChainReadbackConv`.

## What this does NOT close (gates stay `false`)

This ships the `stepConv` GIVEN the concrete band collapse.  Producing that collapse for a `zigZagSharedLeg` redex
(pinning the cup/cap seed generators, instantiating `mergedSharedLegFramesCollapse` (A) / `generalContextFrameLegsCollapseB`
(B), and threading the readback casts) is piece (i), NOT here.  So `CellStraightenStepInput` stays open; the
assembly + swap are separate.  `convOfMapEq` and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; the recursion is structural on the prefix, the casts are `castBoundary_castBoundary` /
`vcomp_castBoundaryLeft` / proof-irrelevance; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`/
`WellFounded.fix`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-atom readback band (the `atomFrame` shape a `cons` emits) -/

/-- The readback band of one atom — the whiskered generator `leftContext ◁ (rightContext ▷ gen generator)` a
`FramedSpineChain.readback` `cons` emits (definitionally `atomFrame` / `spineAtomFrame`). -/
def readbackBand {sourceMode targetMode : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode) :
    RawTwoCellExpr adjunctionModeSignature (atomFrameSource atom) (atomFrameTarget atom) :=
  RawTwoCellExpr.whiskerLeft atom.leftContext
    (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator))

/-! ## The cons-readback form -/

/-- ★ **The cons-readback form.**  A chain over a cons list reads back as its head atom's band vertically composed
with its tail's readback, up to the source cast `framedChain_consSource`.  `rfl` after `cases` on the chain (the
head band IS the readback's `cons` layer). -/
theorem framedChain_readback_consForm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom : SpineAtom signature overallSource overallTarget}
    {restAtoms : List (SpineAtom signature overallSource overallTarget)}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (chain : FramedSpineChain signature sourcePath targetPath (headAtom :: restAtoms)) :
    chain.readback = RawTwoCellExpr.castBoundary (framedChain_consSource chain).symm rfl
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft headAtom.leftContext
            (RawTwoCellExpr.whiskerRight headAtom.rightContext
              (RawTwoCellExpr.gen headAtom.generator)))
          chain.tailChain.readback) := by
  cases chain with
  | cons _ _ => rfl

/-! ## Saturated-conv helpers over casts -/

/-- An equality of cells lifts to a saturated convertibility. -/
theorem saturatedConv_of_eq {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (cellEq : cellAlpha = cellBeta) : SaturatedTwoCellConv cellAlpha cellBeta :=
  cellEq ▸ SaturatedTwoCellConv.refl cellAlpha

/-- Saturated convertibility respects a boundary cast. -/
theorem saturatedConv_castBoundary_congr {sourceMode targetMode : AdjunctionMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath adjunctionGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellAlpha cellBeta) :
    SaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-! ## The RV middle-four step on the readback -/

/-- ★ **The width-2 matched chain straightens on the readback.**  A chain over `cupAtom :: capAtom :: rest` whose
head band-pair collapses (`collapse`) reads back convertible to the delete-surgery chain's readback — the
`snakePrefixStraightens` triangle fired with the readback casts threaded (`vcomp_castBoundaryLeft` + cast
cancellation), then lifted under the source cast. -/
theorem framedPairReadbackStraightens {sourceMode targetMode : AdjunctionMode}
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) (atomFrameSource cupAtom)))
    (rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (chain : FramedSpineChain adjunctionModeSignature sourcePath targetPath
        (cupAtom :: capAtom :: rest)) :
    SaturatedTwoCellConv chain.readback
      (FramedSpineChain.castSource (((framedChain_consSource chain).trans reconnect).symm)
        chain.tailChain.tailChain).readback := by
  have straighten : SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm rfl
          (RawTwoCellExpr.vcomp (readbackBand capAtom) chain.tailChain.tailChain.readback)))
      (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback) := by
    have innerEq :
        RawTwoCellExpr.castBoundary coh.symm rfl
          (RawTwoCellExpr.vcomp (readbackBand capAtom) chain.tailChain.tailChain.readback)
        = RawTwoCellExpr.vcomp
            (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom))
            (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback) := by
      have cancel : ∀ {pathP pathQ : ModalityPath adjunctionGraph sourceMode targetMode}
          (heq : pathP = pathQ) (cellX : RawTwoCellExpr adjunctionModeSignature pathP targetPath),
          RawTwoCellExpr.castBoundary heq.symm rfl
              (RawTwoCellExpr.castBoundary heq rfl cellX) = cellX := by
        intro pathP pathQ heq cellX; cases heq; rfl
      rw [RawTwoCellExpr.vcomp_castBoundaryLeft, cancel]
    rw [innerEq]
    exact snakePrefixStraightens (readbackBand cupAtom)
      (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)) collapse
      (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback)
  have lifted := saturatedConv_castBoundary_congr (framedChain_consSource chain).symm rfl straighten
  rw [RawTwoCellExpr.castBoundary_castBoundary] at lifted
  rw [FramedSpineChain.castSource_readback, framedChain_readback_consForm chain,
      framedChain_readback_consForm chain.tailChain]
  exact lifted

/-! ## The RV width induction on the readback carrier -/

/-- ★ **The delete-surgery chain's readback is saturated-convertible to the original chain's readback.**  By
STRUCTURAL recursion on the prefix: the base is the width-2 straightening (`framedPairReadbackStraightens`); each
prefix atom's band is whiskered through by `vcompCongrRight` under the source cast.  This is RV Prop 3.3.4's width
induction delivered ON the readback carrier, taking the concrete band collapse as a hypothesis. -/
theorem framedDeleteChainReadbackConv {sourceMode targetMode : AdjunctionMode}
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) (atomFrameSource cupAtom)))
    (rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) :
    (prefixCells : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (chain : FramedSpineChain adjunctionModeSignature sourcePath targetPath
        (prefixCells ++ cupAtom :: capAtom :: rest)) →
    SaturatedTwoCellConv chain.readback
      (framedDeletePrefixChain reconnect rest prefixCells chain).readback
  | [], _, _, chain => framedPairReadbackStraightens reconnect coh collapse rest chain
  | prefixHead :: prefixTail, _, _, chain => by
      show SaturatedTwoCellConv chain.readback
        (FramedSpineChain.castSource (framedChain_consSource chain).symm
          (FramedSpineChain.cons prefixHead
            (framedDeletePrefixChain reconnect rest prefixTail chain.tailChain))).readback
      rw [FramedSpineChain.castSource_readback]
      exact (saturatedConv_of_eq (framedChain_readback_consForm chain)).trans
        (saturatedConv_castBoundary_congr (framedChain_consSource chain).symm rfl
          (SaturatedTwoCellConv.vcompCongrRight _
            (framedDeleteChainReadbackConv reconnect coh collapse rest prefixTail chain.tailChain)))

/-! ## The `stepConv` — the full readback realization -/

/-- ★ **The STRAIGHTEN `stepConv`.**  `cell ≈full cell.cellChain.readback = chain.readback ≈ next` — the cell
converts to its own chain's readback (`cellChain_readback_convFull`), which is the located chain's readback
(`castAtoms_readback`), which straightens to the deleted chain's readback = `next`
(`framedDeleteChainReadbackConv`).  The genuinely-NEW STRAIGHTEN conversion (deletion is not trace-preserving),
taking the concrete band collapse as a hypothesis. -/
theorem straightenStepConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (readbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) (atomFrameSource cupAtom)))
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    SaturatedTwoCellConv cell
      (straightenNextCell cell prefixCells rest reconnect sourceSplit) :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.ofFull (RawTwoCellExpr.cellChain_readback_convFull cell))
    (SaturatedTwoCellConv.trans
      (saturatedConv_of_eq
        (FramedSpineChain.castAtoms_readback sourceSplit cell.cellChain).symm)
      (framedDeleteChainReadbackConv reconnect coh collapse rest prefixCells
        (FramedSpineChain.castAtoms sourceSplit cell.cellChain)))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the STRAIGHTEN `stepConv` (producer iii-b) is SHIPPED, modulo the band collapse.**  The
readback realization `cell ≈ cell.cellChain.readback = chain.readback ≈ next` is delivered by
`straightenStepConv`, composing `cellChain_readback_convFull`, `castAtoms_readback`, and the RV width induction on
the readback carrier `framedDeleteChainReadbackConv` (whose middle-four step `framedPairReadbackStraightens` fires
the shipped `snakePrefixStraightens` triangle with the readback casts threaded).  This is the genuinely-NEW
STRAIGHTEN conversion — deletion is not trace-preserving, so unlike COMMUTE it cannot ride `ofSpineTraceEquiv`.

  What this marker does NOT claim (gates stay `false`): the concrete band collapse
  `cupBand ⊟ castBoundary(capBand) ≈ id` is taken as a HYPOTHESIS; producing it for a `zigZagSharedLeg` redex
  (pinning the seed generators + instantiating `mergedSharedLegFramesCollapse` (A) / `generalContextFrameLegsCollapseB`
  (B) + threading the merged-frame casts to the readback casts) is piece (i).  The assembly + swap are separate.
  `CellStraightenStepInput` stays open; `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenReadback : Bool := true

end FX1Poly.Polygraph

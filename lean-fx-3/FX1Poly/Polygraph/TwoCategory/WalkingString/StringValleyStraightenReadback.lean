import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteLift
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSharedLegFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenReadback

/-! # WalkingString — Piece I STRAIGHTEN scaffolding: the readback `stepConv` + the deleted `next` builder, gated on
the band collapse (FC-3 r6, B1)

The walking-adjunction STRAIGHTEN producer factors into (a) the deleted `next` via framed chain surgery
(`straightenNextCell`, `{signature}`-GENERIC — reused directly), (b) the readback realization `stepConv`
(`straightenStepConv`), which is the genuinely-NEW STRAIGHTEN conversion (deletion is NOT trace-preserving, so
unlike COMMUTE it cannot ride `ofSpineTraceEquiv`), and (c) the band collapse `cupBand ⊟ castBoundary capBand ≈ id`
that (b) TAKES AS A HYPOTHESIS.  This file ports (b) and the `StringCellDescentResult` STRAIGHTEN builder to the
three-generator seed's `StringSaturatedTwoCellConv`, reducing the string STRAIGHTEN arm to EXACTLY the band
collapse:

  * ★ **`stringReadbackBand`** — the per-atom readback band (definitionally the head band a
    `FramedSpineChain.readback` `cons` emits).
  * ★ **`stringSnakePrefixStraightens`** — a collapsing frame-pair straightens at the head of a right-nested
    readback chain (`cupBand ⊟ (capBand ⊟ tail) ≈ tail`), via one `vcompAssoc` re-association + the collapse under
    the vcomp congruences.
  * ★ **`stringFramedPairReadbackStraightens`** — the width-2 matched chain straightens on the readback (the RV
    middle-four step), the readback casts threaded (`vcomp_castBoundaryLeft` + cast cancellation).
  * ★ **`stringFramedDeleteChainReadbackConv`** — the RV width induction on the readback carrier: the deleted-chain
    readback is `StringSaturatedTwoCellConv` to the original chain's readback, by STRUCTURAL recursion on the
    prefix (each prefix atom whiskered through by `vcompCongrRight` under the source cast).  No `WellFounded.fix`.
  * ★ **`stringStraightenStepConv`** — the `stepConv`: `cell ≈full cell.cellChain.readback = chain.readback ≈ next`.
  * ★ **`stringCellDescentResult_ofStraightenStep`** — the STRAIGHTEN `StringCellDescentResult` builder, its
    `disorderDrops` discharged by the `{signature}`-GENERIC `spineDisorder_delete_lt`.
  * ★ **`stringStraightenCellDescentStep_ofCollapse`** — the STRAIGHTEN producer for a located `zigZagSharedLeg`
    redex, GIVEN the band collapse: read the boundary coherence off `cell`'s own realized chain, take the
    reconnection from the shipped colour-aware `stringCupCapDeletionReconnects`, realize the `stepConv`, build the
    deleted `next`, and package.  The band collapse is the single remaining input.

## What this does NOT close (the band collapse is the WALL)

The band collapse `stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id` is TAKEN AS A HYPOTHESIS.
Producing it for a `zigZagSharedLeg` string redex is the one genuinely-NEW colour node: the width-only classifier
is colour-BLIND, so it must first refute the MIXED-colour case (a lower cup `η` opening `F·G` next to an upper cap
`ε'` closing `H·G` would demand `F = H`, FALSE — the shipped `stringSharedLegForcesSameColour` handles this at the
RECONNECT level, but the band collapse needs it at the 2-cell level), then fire the matching STRING triangle
(`triangleF`/`triangleGlo`/`triangleGhi`/`triangleH`) whiskered into the general context by the generic whisker
functoriality — a four-generator, two-colour re-derivation of the adjunction's single-colour
`mergedSharedLegFramesCollapse`.  That is a separate multi-file arc; this file reduces the STRAIGHTEN arm to it and
names the exact goal.  So `StringCellDescentStepOracle` stays UN-inhabited and
`fxString_hasAdjointTripleCompleteness` stays `false`.

Raw Lean 4 + Init; the recursion is structural on the prefix, the casts are `castBoundary_castBoundary` /
`vcomp_castBoundaryLeft` / proof-irrelevance.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`/
`WellFounded.fix`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-atom readback band (the `atomFrame` shape a `cons` emits) -/

/-- The readback band of one string atom — the whiskered generator `leftContext ◁ (rightContext ▷ gen generator)` a
`FramedSpineChain.readback` `cons` emits (definitionally the head band). -/
def stringReadbackBand {sourceMode targetMode : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode) :
    RawTwoCellExpr adjointTripleModeSignature (atomFrameSource atom) (atomFrameTarget atom) :=
  RawTwoCellExpr.whiskerLeft atom.leftContext
    (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator))

/-! ## Saturated-conv helpers over casts -/

/-- An equality of cells lifts to a saturated string convertibility. -/
theorem stringSaturatedConv_of_eq {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (cellEq : cellAlpha = cellBeta) : StringSaturatedTwoCellConv cellAlpha cellBeta :=
  cellEq ▸ StringSaturatedTwoCellConv.refl cellAlpha

/-- Saturated string convertibility respects a boundary cast. -/
theorem stringSaturatedConv_castBoundary_congr {sourceMode targetMode : AdjointTripleMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath adjointTripleGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellAlpha cellBeta) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-! ## The STRAIGHTEN per-step lift (prefix) -/

/-- ★ **A collapsing frame-pair straightens at the head of a right-nested readback chain.**  Given the collapse
`cupBand ⊟ capBand ≈ id`, `cupBand ⊟ (capBand ⊟ tail) ≈ tail`: re-associate to `(cupBand ⊟ capBand) ⊟ tail` (free
`vcompAssoc`, reversed), fire the collapse under `vcompCongrLeft`, then `vcompIdLeft`.  The three-generator twin of
`snakePrefixStraightens` (re-derived from primitives — the `generatorCount`-dropping move). -/
theorem stringSnakePrefixStraightens {sourceMode targetMode : AdjointTripleMode}
    {pathLow pathMid pathHigh : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cupFrame : RawTwoCellExpr adjointTripleModeSignature pathLow pathMid)
    (capFrame : RawTwoCellExpr adjointTripleModeSignature pathMid pathLow)
    (collapses : StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp cupFrame capFrame)
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) pathLow))
    (tail : RawTwoCellExpr adjointTripleModeSignature pathLow pathHigh) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp cupFrame (RawTwoCellExpr.vcomp capFrame tail)) tail :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.symm
      (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc cupFrame capFrame tail))))
    (StringSaturatedTwoCellConv.trans
      (StringSaturatedTwoCellConv.vcompCongrLeft tail collapses)
      (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft tail))))

/-! ## The RV middle-four step on the readback -/

/-- ★ **The width-2 matched chain straightens on the readback.**  A chain over `cupAtom :: capAtom :: rest` whose
head band-pair collapses reads back convertible to the delete-surgery chain's readback — the
`stringSnakePrefixStraightens` triangle fired with the readback casts threaded, then lifted under the source cast.
The three-generator twin of `framedPairReadbackStraightens`. -/
theorem stringFramedPairReadbackStraightens {sourceMode targetMode : AdjointTripleMode}
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) (atomFrameSource cupAtom)))
    (rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (chain : FramedSpineChain adjointTripleModeSignature sourcePath targetPath
        (cupAtom :: capAtom :: rest)) :
    StringSaturatedTwoCellConv chain.readback
      (FramedSpineChain.castSource (((framedChain_consSource chain).trans reconnect).symm)
        chain.tailChain.tailChain).readback := by
  have straighten : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm rfl
          (RawTwoCellExpr.vcomp (stringReadbackBand capAtom) chain.tailChain.tailChain.readback)))
      (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback) := by
    have innerEq :
        RawTwoCellExpr.castBoundary coh.symm rfl
          (RawTwoCellExpr.vcomp (stringReadbackBand capAtom) chain.tailChain.tailChain.readback)
        = RawTwoCellExpr.vcomp
            (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom))
            (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback) := by
      have cancel : ∀ {pathP pathQ : ModalityPath adjointTripleGraph sourceMode targetMode}
          (heq : pathP = pathQ) (cellX : RawTwoCellExpr adjointTripleModeSignature pathP targetPath),
          RawTwoCellExpr.castBoundary heq.symm rfl
              (RawTwoCellExpr.castBoundary heq rfl cellX) = cellX := by
        intro pathP pathQ heq cellX; cases heq; rfl
      rw [RawTwoCellExpr.vcomp_castBoundaryLeft, cancel]
    rw [innerEq]
    exact stringSnakePrefixStraightens (stringReadbackBand cupAtom)
      (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)) collapse
      (RawTwoCellExpr.castBoundary reconnect.symm rfl chain.tailChain.tailChain.readback)
  have lifted := stringSaturatedConv_castBoundary_congr (framedChain_consSource chain).symm rfl straighten
  rw [RawTwoCellExpr.castBoundary_castBoundary] at lifted
  rw [FramedSpineChain.castSource_readback, framedChain_readback_consForm chain,
      framedChain_readback_consForm chain.tailChain]
  exact lifted

/-! ## The RV width induction on the readback carrier -/

/-- ★ **The delete-surgery chain's readback is saturated-convertible to the original chain's readback.**  By
STRUCTURAL recursion on the prefix: the base is the width-2 straightening; each prefix atom's band is whiskered
through by `vcompCongrRight` under the source cast.  No `WellFounded.fix`.  The three-generator twin of
`framedDeleteChainReadbackConv`. -/
theorem stringFramedDeleteChainReadbackConv {sourceMode targetMode : AdjointTripleMode}
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) (atomFrameSource cupAtom)))
    (rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) :
    (prefixCells : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (chain : FramedSpineChain adjointTripleModeSignature sourcePath targetPath
        (prefixCells ++ cupAtom :: capAtom :: rest)) →
    StringSaturatedTwoCellConv chain.readback
      (framedDeletePrefixChain reconnect rest prefixCells chain).readback
  | [], _, _, chain => stringFramedPairReadbackStraightens reconnect coh collapse rest chain
  | prefixHead :: prefixTail, _, _, chain => by
      show StringSaturatedTwoCellConv chain.readback
        (FramedSpineChain.castSource (framedChain_consSource chain).symm
          (FramedSpineChain.cons prefixHead
            (framedDeletePrefixChain reconnect rest prefixTail chain.tailChain))).readback
      rw [FramedSpineChain.castSource_readback]
      exact (stringSaturatedConv_of_eq (framedChain_readback_consForm chain)).trans
        (stringSaturatedConv_castBoundary_congr (framedChain_consSource chain).symm rfl
          (StringSaturatedTwoCellConv.vcompCongrRight _
            (stringFramedDeleteChainReadbackConv reconnect coh collapse rest prefixTail chain.tailChain)))

/-! ## The `stepConv` — the full readback realization -/

/-- ★ **The STRAIGHTEN `stepConv`.**  `cell ≈full cell.cellChain.readback = chain.readback ≈ next` — the cell
converts to its own chain's readback (`cellChain_readback_convFull`), which is the located chain's readback
(`castAtoms_readback`), which straightens to the deleted chain's readback = `next`
(`stringFramedDeleteChainReadbackConv`).  The genuinely-NEW STRAIGHTEN conversion, taking the band collapse as a
hypothesis. -/
theorem stringStraightenStepConv {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (collapse : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) (atomFrameSource cupAtom)))
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    StringSaturatedTwoCellConv cell
      (straightenNextCell cell prefixCells rest reconnect sourceSplit) :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.ofFull (RawTwoCellExpr.cellChain_readback_convFull cell))
    (StringSaturatedTwoCellConv.trans
      (stringSaturatedConv_of_eq
        (FramedSpineChain.castAtoms_readback sourceSplit cell.cellChain).symm)
      (stringFramedDeleteChainReadbackConv reconnect coh collapse rest prefixCells
        (FramedSpineChain.castAtoms sourceSplit cell.cellChain)))

/-! ## The STRAIGHTEN `StringCellDescentResult` builder -/

/-- ★ **The STRAIGHTEN `StringCellDescentResult` builder.**  Given a `next` cell saturated-convertible to `cell`
whose spine is `cell`'s with the located cup·cap pair DELETED, package a `StringCellDescentResult cell`:
`disorderDrops` is discharged by the `{signature}`-GENERIC `spineDisorder_delete_lt`.  The three-generator twin of
`cellDescentResult_ofStraightenStep`. -/
def stringCellDescentResult_ofStraightenStep {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (stepConv : StringSaturatedTwoCellConv cell next)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ rest) :
    StringCellDescentResult cell :=
  ⟨next, stepConv, by
    rw [sourceSplit, targetSplit]
    exact spineDisorder_delete_lt prefixCells isCupCup isCapCap rest⟩

/-! ## The STRAIGHTEN producer, GATED on the band collapse -/

/-- ★ **The STRAIGHTEN producer for a located `zigZagSharedLeg` redex, GIVEN the band collapse.**  Reads the
boundary coherence off `cell`'s own realized chain (`framedChain_pairPathCoherence`), takes the reconnection from
the shipped colour-aware `stringCupCapDeletionReconnects` (the LEFT-handedness width relation supplied), realizes
the `stepConv` (`stringStraightenStepConv`, fed the band collapse), builds the deleted `next`, and packages via
`stringCellDescentResult_ofStraightenStep`.  The band collapse is the SINGLE remaining input — the one genuinely-new
colour node the STRAIGHTEN arm reduces to. -/
def stringStraightenCellDescentStep_ofCollapse
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (widthRel : cupAtom.leftContext.length + 1 = capAtom.leftContext.length)
    (collapse :
      (coh : atomFrameTarget cupAtom = atomFrameSource capAtom) →
      (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom) →
      StringSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
          (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)))
        (RawTwoCellExpr.id (signature := adjointTripleModeSignature) (atomFrameSource cupAtom))) :
    StringCellDescentResult cell :=
  let coh : atomFrameTarget cupAtom = atomFrameSource capAtom :=
    framedChain_pairPathCoherence rest prefixCells
      (FramedSpineChain.castAtoms sourceSplit cell.cellChain)
  let reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom :=
    stringCupCapDeletionReconnects cupAtom capAtom isCupCup isCapCap coh widthRel
  let stepConv := stringStraightenStepConv cell prefixCells rest reconnect coh (collapse coh reconnect)
    sourceSplit
  let targetSplit := straightenNextCell_spine cell prefixCells rest reconnect sourceSplit
  stringCellDescentResult_ofStraightenStep stepConv prefixCells rest isCupCup isCapCap sourceSplit
    targetSplit

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the STRAIGHTEN `stepConv` + `next` + builder scaffolding is SHIPPED at the three-generator
seed; the STRAIGHTEN arm is reduced to EXACTLY the band collapse.**  `stringStraightenStepConv` realizes the
genuinely-NEW STRAIGHTEN conversion `cell ≈ cell.cellChain.readback = chain.readback ≈ next` (deletion is not
trace-preserving, so unlike COMMUTE it cannot ride `ofSpineTraceEquiv`), composing `cellChain_readback_convFull`,
`castAtoms_readback`, and the RV width induction on the readback carrier `stringFramedDeleteChainReadbackConv` (whose
middle-four step `stringFramedPairReadbackStraightens` fires `stringSnakePrefixStraightens` with the readback casts
threaded).  The deleted `next` is the `{signature}`-GENERIC `straightenNextCell` (reused).
`stringCellDescentResult_ofStraightenStep` packages the STRAIGHTEN `StringCellDescentResult`, `disorderDrops` by the
generic `spineDisorder_delete_lt`.  `stringStraightenCellDescentStep_ofCollapse` assembles the whole STRAIGHTEN move
GIVEN the band collapse, taking the reconnection from the shipped colour-aware `stringCupCapDeletionReconnects`.
`= true`. -/
def fxString_hasStringValleyStraightenReadback : Bool := true

/-- **★ HONEST WALL RECORD — the band collapse is the one genuinely-new colour node the STRAIGHTEN arm reduces to;
it does NOT flip this round.**  `stringStraightenCellDescentStep_ofCollapse` takes as its SINGLE remaining input the
band collapse `stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id` on the shared boundary.
Producing it for a `zigZagSharedLeg` string redex is a four-generator, two-colour re-derivation of the adjunction's
single-colour `mergedSharedLegFramesCollapse` (`SpineValleyFrameCollapse` + `SpineValleyStraightenCastBridge`): the
width-only classifier is colour-BLIND, so it must first refute the MIXED-colour case at the 2-cell level (the
shipped `stringSharedLegForcesSameColour` handles it at the RECONNECT level — `F ≠ H` via the mode clash — but the
2-cell collapse needs the same refutation lifted), then fire the matching STRING triangle
(`triangleF`/`triangleGlo`/`triangleGhi`/`triangleH`) whiskered into the general context by the generic whisker
functoriality (`TwoCellConvFull.whiskerLeftComp`/`whiskerRightComp`/`whiskerExchange`, which DO exist at the string
signature — verified).  The RIGHT-handedness (`capLeft + 1 = cupLeft`) additionally needs a mirror reconnect (the
shipped `stringCupCapDeletionReconnects` carries only the LEFT width relation).  This is a separate multi-file arc,
NOT a shared-`G` coherence gap (`fxString_hasAdjointTripleCoherenceGap` stays `false`).  So
`StringCellDescentStepOracle` stays UN-inhabited and `fxString_hasAdjointTripleCompleteness` stays `false`.
`= false`. -/
def fxString_hasStringValleyStraightenBandCollapse : Bool := false

end FX1Poly.Polygraph

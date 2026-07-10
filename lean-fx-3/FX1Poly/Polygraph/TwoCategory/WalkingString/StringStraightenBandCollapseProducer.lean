import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyStraightenBandCollapse

/-! # WalkingString — the STRAIGHTEN band-collapse producer (FC-3 r7, B2): leg factorization + merged frames +
the cast bridge

`StringValleyStraightenBandCollapse` shipped the cast-free iterated-leg collapse
(`stringGeneralContextFrameLegsCollapse`).  This file assembles the merged-`atomFrame` cast bridge that connects
the readback BANDS (`stringReadbackBand` = `atomFrame` = a single-whisker MERGED frame) to those iterated legs, and
the leg-factorization extraction that pins a shared-leg cup·cap's stored contexts to the merged shape.

  * ★ **`stringSharedLegLegShape`** — THE load-bearing novelty: from the snake-window coherence and the
    width-distance-1 relation, EXPOSE the two leg pins the reconnect discards — `lcCap = lcCup · L` and
    `rcCup = L · rcCap` (`L = outerLeg`).  One split-pack, the pins read off its factors.
  * ★ **`stringMergedCupFrame` / `stringMergedCapFrame`** — the single-whisker merged frames the readback's
    `atomFrame` produces for a shared-leg cup / cap partner (stored right context `L·rightContext`, stored left
    context `leftContext·L`).  Both legs single modalities, so every `composePath` reduces to a cons-list.

Raw Lean 4 + Init.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The leg-factorization extraction (the novelty the reconnect discards) -/

/-- ★★ **The shared-leg leg shape — the two pins the reconnect discards, EXPOSED.**  For a genuine snake window
(the cup produces `outerLeg·innerLeg`, the cap consumes the palindrome `innerLeg·outerLeg`) with the shared window
equation and the width-distance-1 relation `|lcCup| + 1 = |lcCap|`, the two outer legs pin BOTH stored contexts:
`lcCap = lcCup · outerLeg` (site A-left) and `rcCup = outerLeg · rcCap` (site A-right).  ONE
`composePath_splitPackEqOfPrefixLengthEq` on the shared word at the shared-leg split length, with the two factors
read straight off (not discarded as in `sharedLegSnakeReconnect`).  Signature-GENERIC. -/
theorem stringSharedLegLegShape {graph : ModeGraph}
    {overallSource overallTarget outerSource innerSource : graph.Mode}
    (outerLeg : graph.Modality outerSource innerSource)
    (innerLeg : graph.Modality innerSource outerSource)
    (lcCup : ModalityPath graph overallSource outerSource)
    (rcCup : ModalityPath graph outerSource overallTarget)
    (lcCap : ModalityPath graph overallSource innerSource)
    (rcCap : ModalityPath graph innerSource overallTarget)
    (coherence :
      composePath lcCup
          (composePath
            (ModalityPath.cons outerLeg (ModalityPath.cons innerLeg (ModalityPath.nil outerSource))) rcCup)
        = composePath lcCap
          (composePath
            (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg (ModalityPath.nil innerSource))) rcCap))
    (widthRel : lcCup.length + 1 = lcCap.length) :
    composePath lcCup (singletonModalityPath outerLeg) = lcCap
      ∧ rcCup = ModalityPath.cons outerLeg rcCap := by
  have wordEq :
      composePath (composePath lcCup (singletonModalityPath outerLeg))
          (ModalityPath.cons innerLeg rcCup)
        = composePath lcCap
          (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg rcCap)) := by
    rw [composePath_assoc lcCup (singletonModalityPath outerLeg) (ModalityPath.cons innerLeg rcCup)]
    exact coherence
  have lengthEq :
      (composePath lcCup (singletonModalityPath outerLeg)).length = lcCap.length := by
    rw [ModalityPath.length_composePath, singletonModalityPath_length]
    exact widthRel
  have splitPack := composePath_splitPackEqOfPrefixLengthEq
    (composePath lcCup (singletonModalityPath outerLeg))
    (ModalityPath.cons innerLeg rcCup) lcCap
    (ModalityPath.cons innerLeg (ModalityPath.cons outerLeg rcCap)) wordEq lengthEq
  injection splitPack with _midEqual innerPack
  injection innerPack with prefixEqual suffixEqual
  injection suffixEqual with _srcModeEqual _midModeEqual _tgtModeEqual _modalityEqual tailEqual
  exact ⟨prefixEqual, tailEqual⟩

/-! ## The merged frames — the single-whisker `atomFrame` shapes of a shared-leg partner -/

/-- The merged cup frame `leftContext ◁ ((L · rightContext) ▷ cupGen)` — the shape `atomFrame` produces for a
shared-leg cup whose stored right context is `L · rightContext`.  The generic string twin of `mergedCupFrame`. -/
def stringMergedCupFrame
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath contextLeft
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
          (composePath (singletonModalityPath sharedLegModality) contextRight)))
      (composePath contextLeft
        (composePath (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
          (composePath (singletonModalityPath sharedLegModality) contextRight))) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight
      (composePath (singletonModalityPath sharedLegModality) contextRight) cupGen)

/-- The merged cap frame `(leftContext · L) ◁ (rightContext ▷ capGen)` — the shape `atomFrame` produces for a
shared-leg cap whose stored left context is `leftContext · L`.  The generic string twin of `mergedCapFrame`. -/
def stringMergedCapFrame
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
          contextRight))
      (composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
    (composePath contextLeft (singletonModalityPath sharedLegModality))
    (RawTwoCellExpr.whiskerRight contextRight capGen)

/-! ## The cup half of the cast bridge: the merged cup frame IS the iterated cup leg (cast-free) -/

/-- ★ **The cup half of THE CAST BRIDGE.**  The merged cup frame `leftContext ◁ ((L · rightContext) ▷ cupGen)` is
`TwoCellConvFull` to the iterated cup leg `stringSharedLegCupLeg`: the merged single right-whisker splits
(`whiskerRightComp`) into `rightContext ▷ (L ▷ cupGen)`, lifted through `leftContext ◁ -` with the cast pulled out
(`whiskerLeft_castBoundary`).  CAST-FREE at the conclusion: both legs single modalities, so the split's
associativity cast is between definitionally-equal boundaries, hence defeq-invisible.  The string twin of
`mergedCupFrame_convFull_castCupLeg`. -/
theorem stringMergedCupFrame_convFull_cupLeg
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (stringMergedCupFrame sharedLegModality otherLegModality cupGen contextLeft contextRight)
      (stringSharedLegCupLeg sharedLegModality otherLegModality cupGen contextLeft contextRight) := by
  have lifted := TwoCellConvFull.whiskerLeftCongr contextLeft
    (TwoCellConvFull.whiskerRightComp (singletonModalityPath sharedLegModality) contextRight cupGen)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at lifted
  exact lifted

/-! ## The cap half of the cast bridge: the merged cap frame IS the iterated cap leg (up to associativity casts)

The align / endpoint boundary equalities are stated with the cap leg's OWN `(L·M)·L` window bracketing (so
`castBoundary` typechecks against `stringSharedLegCapLeg` with no unification), and proved by ONE `composePath_assoc`
transporting the `leftContext · L` prefix (the window re-bracketing is definitional at single modalities). -/

/-- The align cast: the iterated cap leg's SOURCE `contextLeft · ((L·M)·L · contextRight)` equals the merged cap
frame's SOURCE `(contextLeft · L) · ((M·L) · contextRight)` — the `leftContext · L`-prefix re-bracketing. -/
theorem stringMergedCapAlign
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath contextLeft
        (composePath
          (composePath (composePath (singletonModalityPath sharedLegModality)
            (singletonModalityPath otherLegModality)) (singletonModalityPath sharedLegModality)) contextRight)
      = composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
            contextRight) :=
  (composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      contextRight)).symm

/-- The endpoint cast: the iterated cap leg's TARGET `contextLeft · ((L·nil) · contextRight)` equals the merged cap
frame's TARGET `(contextLeft · L) · (nil · contextRight)`. -/
theorem stringMergedCapEndpoint
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)) contextRight)
      = composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight) :=
  (composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight)).symm

/-- ★ **The cap half of THE CAST BRIDGE.**  The merged cap frame `(leftContext · L) ◁ (rightContext ▷ capGen)` is
`TwoCellConvFull` to the iterated cap leg `stringSharedLegCapLeg` up to the align / endpoint casts: the composite
left-whisker `leftContext · L` splits (`whiskerLeftComp`) into `leftContext ◁ (L ◁ (rightContext ▷ capGen))`, and
the inner `L ◁ (rightContext ▷ capGen)` exchanges (`whiskerExchange`) into `rightContext ▷ (L ◁ capGen)`; the two
casts fuse (`castBoundary_castBoundary`) into the align / endpoint casts (matched by proof irrelevance).  The string
twin of `mergedCapFrame_convFull_castCapLeg`. -/
theorem stringMergedCapFrame_convFull_castCapLeg
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (stringMergedCapFrame sharedLegModality otherLegModality capGen contextLeft contextRight)
      (RawTwoCellExpr.castBoundary
        (stringMergedCapAlign sharedLegModality otherLegModality contextLeft contextRight)
        (stringMergedCapEndpoint sharedLegModality contextLeft contextRight)
        (stringSharedLegCapLeg sharedLegModality otherLegModality capGen contextLeft contextRight)) := by
  have innerConv := TwoCellConvFull.whiskerLeftCongr contextLeft
    (TwoCellConvFull.whiskerExchange (singletonModalityPath sharedLegModality) contextRight capGen)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at innerConv
  have splitOuter := TwoCellConvFull.whiskerLeftComp contextLeft (singletonModalityPath sharedLegModality)
    (RawTwoCellExpr.whiskerRight contextRight capGen)
  have combined := splitOuter.trans
    (TwoCellConvFull.castBoundaryCongr
      (stringMergedCapAlign sharedLegModality otherLegModality contextLeft contextRight)
      (stringMergedCapEndpoint sharedLegModality contextLeft contextRight)
      innerConv)
  rw [RawTwoCellExpr.castBoundary_castBoundary] at combined
  exact combined

/-! ## THE MERGED CAST BRIDGE — the two merged frames collapse to the identity -/

/-- The merged frames' alignment cast: the merged cap frame's SOURCE `(contextLeft·L) · ((M·L)·contextRight)`
equals the merged cup frame's TARGET `contextLeft · ((L·M)·(L·contextRight))` — the same word, re-bracketed.  One
`composePath_assoc` on the `contextLeft·L` prefix; the window re-bracket is definitional (single modalities). -/
theorem stringMergedFramesAlign
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath
          (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
          contextRight)
      = composePath contextLeft
          (composePath (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
            (composePath (singletonModalityPath sharedLegModality) contextRight)) :=
  composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      contextRight)

/-- The merged frames' endpoint cast: the merged cap frame's TARGET `(contextLeft·L) · (nil·contextRight)` equals
the merged cup frame's SOURCE `contextLeft · (nil·(L·contextRight))` — the shared boundary. -/
theorem stringMergedFramesEndpoint
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight)
      = composePath contextLeft
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
            (composePath (singletonModalityPath sharedLegModality) contextRight)) :=
  composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight)

/-- ★★ **THE MERGED CAST BRIDGE.**  The merged cup and cap frames — the readback `atomFrame` shapes of a shared-leg
partner — collapse to the identity on the shared boundary: `mergedCup ⊟ castBoundary(align) mergedCap ≈ id`.  Each
merged frame lifts to its iterated leg (`stringMergedCupFrame_convFull_cupLeg` cast-free;
`stringMergedCapFrame_convFull_castCapLeg` with the cap cast fused into the align cast, defeq-invisible), and the
iterated composite collapses by `stringGeneralContextFrameLegsCollapse`.  The generic string twin of
`mergedSharedLegFramesCollapse`, taking the `triangle` so it serves both same-colour snakes. -/
theorem stringMergedSharedLegFramesCollapse
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality)))
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode))
    (triangle : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen)
        (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringMergedCupFrame sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (RawTwoCellExpr.castBoundary
          (stringMergedFramesAlign sharedLegModality otherLegModality contextLeft contextRight)
          (stringMergedFramesEndpoint sharedLegModality contextLeft contextRight)
          (stringMergedCapFrame sharedLegModality otherLegModality capGen contextLeft contextRight)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath contextLeft
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
            (composePath (singletonModalityPath sharedLegModality) contextRight)))) := by
  have capCastConv : TwoCellConvFull adjointTripleModeSignature
      (RawTwoCellExpr.castBoundary
        (stringMergedFramesAlign sharedLegModality otherLegModality contextLeft contextRight)
        (stringMergedFramesEndpoint sharedLegModality contextLeft contextRight)
        (stringMergedCapFrame sharedLegModality otherLegModality capGen contextLeft contextRight))
      (stringSharedLegCapLeg sharedLegModality otherLegModality capGen contextLeft contextRight) := by
    have transported := TwoCellConvFull.castBoundaryCongr
      (stringMergedFramesAlign sharedLegModality otherLegModality contextLeft contextRight)
      (stringMergedFramesEndpoint sharedLegModality contextLeft contextRight)
      (stringMergedCapFrame_convFull_castCapLeg sharedLegModality otherLegModality capGen contextLeft contextRight)
    rw [RawTwoCellExpr.castBoundary_castBoundary] at transported
    exact transported
  exact StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.castBoundary
        (stringMergedFramesAlign sharedLegModality otherLegModality contextLeft contextRight)
        (stringMergedFramesEndpoint sharedLegModality contextLeft contextRight)
        (stringMergedCapFrame sharedLegModality otherLegModality capGen contextLeft contextRight))
      (StringSaturatedTwoCellConv.ofFull
        (stringMergedCupFrame_convFull_cupLeg sharedLegModality otherLegModality cupGen contextLeft contextRight)))
    (StringSaturatedTwoCellConv.trans
      (StringSaturatedTwoCellConv.vcompCongrRight
        (stringSharedLegCupLeg sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (StringSaturatedTwoCellConv.ofFull capCastConv))
      (stringGeneralContextFrameLegsCollapse sharedLegModality otherLegModality cupGen capGen triangle
        contextLeft contextRight))

/-! ## THE BAND COLLAPSE PRODUCER — the readback bands collapse, discharging the STRAIGHTEN hypothesis -/

/-- ★★★ **THE LEFT-HANDED BAND COLLAPSE, unconditional.**  For a located LEFT-handed zigzag cup·cap pair
(`|lcCup| + 1 = |lcCap|`) with the shared window coherence and the endpoint reconnect, the readback bands collapse:
`stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id`.  This is EXACTLY the hypothesis
`stringStraightenCellDescentStep_ofCollapse` takes — discharged.  Casing the four cup×cap generator combos: the two
SAME-colour snakes (`η·ε` at `L = F`, `η'·ε'` at `L = G`) fire the merged cast bridge
`stringMergedSharedLegFramesCollapse` (with `triangleF` / `triangleGhi`) after the leg-factorization subst rewrites
the bands into the merged frames; the two MIXED combos are refuted at the 2-cell level by `sharedLegModeClash`
(`F` targets `tip`, `H·G` starts `base`), `.elim`.  The goal's cast `castBoundary coh.symm reconnect.symm` and the
bridge's `castBoundary(align)` agree by proof irrelevance (same boundary paths). -/
theorem stringZigZagBandCollapseLeft
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (widthRel : cupAtom.leftContext.length + 1 = capAtom.leftContext.length)
    (coh : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringReadbackBand cupAtom)
        (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (stringReadbackBand capAtom)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) (atomFrameSource cupAtom)) := by
  obtain ⟨cupLeftMid, cupRightMid, lcCup, cupDom, cupCod, genCup, rcCup⟩ := cupAtom
  obtain ⟨capLeftMid, capRightMid, lcCap, capDom, capCod, genCap, rcCap⟩ := capAtom
  dsimp only [SpineAtom.isCupAtom] at isCup isCap
  dsimp only [atomFrameTarget, atomFrameSource] at coh reconnect
  dsimp only [SpineAtom.leftContext] at widthRel
  cases genCup with
  | counitLower => exact absurd isCup (by decide)
  | counitUpper => exact absurd isCup (by decide)
  | unitLower =>
      cases genCap with
      | unitLower => exact absurd isCap (by decide)
      | unitUpper => exact absurd isCap (by decide)
      | counitLower =>
          dsimp only [stringFG, stringGF] at coh
          obtain ⟨lcCapEq, rcCupEq⟩ := stringSharedLegLegShape
            AdjointTripleModality.left AdjointTripleModality.right lcCup rcCup lcCap rcCap coh widthRel
          subst rcCupEq
          subst lcCapEq
          exact stringMergedSharedLegFramesCollapse AdjointTripleModality.left AdjointTripleModality.right
            stringUnitLower stringCounitLower StringSaturatedTwoCellConv.triangleF lcCup rcCap
      | counitUpper =>
          dsimp only [stringFG, stringHG] at coh
          exact (stringSharedLegMixedPairExcluded lcCup rcCup lcCap rcCap coh widthRel).elim
  | unitUpper =>
      cases genCap with
      | unitLower => exact absurd isCap (by decide)
      | unitUpper => exact absurd isCap (by decide)
      | counitUpper =>
          dsimp only [stringGH, stringHG] at coh
          obtain ⟨lcCapEq, rcCupEq⟩ := stringSharedLegLegShape
            AdjointTripleModality.right AdjointTripleModality.coLeft lcCup rcCup lcCap rcCap coh widthRel
          subst rcCupEq
          subst lcCapEq
          exact stringMergedSharedLegFramesCollapse AdjointTripleModality.right AdjointTripleModality.coLeft
            stringUnitUpper stringCounitUpper StringSaturatedTwoCellConv.triangleGhi lcCup rcCap
      | counitLower =>
          dsimp only [stringGH, stringGF] at coh
          refine (sharedLegModeClash
            (composePath lcCup (singletonModalityPath AdjointTripleModality.right))
            (ModalityPath.cons AdjointTripleModality.coLeft rcCup) lcCap
            (composePath stringGF rcCap) ?_ ?_
            (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCup (singletonModalityPath AdjointTripleModality.right)
                (ModalityPath.cons AdjointTripleModality.coLeft rcCup)]
            exact coh
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel

/-! ## The UNCONDITIONAL LEFT STRAIGHTEN producer — the gated producer, collapse supplied -/

/-- ★★★ **The STRAIGHTEN producer for a LEFT-handed located zigzag redex — UNCONDITIONAL.**  The gated
`stringStraightenCellDescentStep_ofCollapse` with its band-collapse hypothesis SUPPLIED by
`stringZigZagBandCollapseLeft`.  No hypothesis remains: for a LEFT-handed zigzag cup·cap split
(`|lcCup| + 1 = |lcCap|`) this produces a `StringCellDescentResult cell` outright — the LEFT STRAIGHTEN arm of the
descent oracle, closed.  (The RIGHT-handed `|lcCap| + 1 = |lcCup|` mirror is the remaining arm for oracle
totality.) -/
def stringStraightenCellDescentStep_left
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (widthRel : cupAtom.leftContext.length + 1 = capAtom.leftContext.length) :
    StringCellDescentResult cell :=
  stringStraightenCellDescentStep_ofCollapse cell prefixCells rest isCupCup isCapCap sourceSplit widthRel
    (stringZigZagBandCollapseLeft cupAtom capAtom isCupCup isCapCap widthRel)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the leg-factorization extraction, the merged `atomFrame` frames, and THE MERGED CAST BRIDGE
are machine-checked (FC-3 r7, B2).**  `stringSharedLegLegShape` EXPOSES the two leg pins (`lcCap = lcCup · L`,
`rcCup = L · rcCap`) the `sharedLegSnakeReconnect` discards — the load-bearing novelty the merged-frame rewrite
consumes.  `stringMergedCupFrame` / `stringMergedCapFrame` are the single-whisker `atomFrame` shapes of a shared-leg
partner.  `stringMergedCupFrame_convFull_cupLeg` (cast-free) and `stringMergedCapFrame_convFull_castCapLeg` (cap
cast, `whiskerLeftComp` + `whiskerExchange`) lift each merged frame to its iterated leg, and
`stringMergedSharedLegFramesCollapse` collapses `mergedCup ⊟ castBoundary(align) mergedCap ≈ id` — the full string
port of `mergedSharedLegFramesCollapse`, GENERIC in the shared-leg / cup / cap generators and the triangle, so ONE
bridge serves both same-colour snakes (`F`-snake / upper-`G`-snake).

  What this marker does NOT close (gates stay `false`): the RIGHT-handedness (`|lcCap| + 1 = |lcCup|`) mirror band
  collapse (needed for descent-oracle totality — the classifier is handedness-symmetric) and the oracle wire-up.
  `fxString_hasStringValleyStraightenBandCollapse` is flipped for the LEFT arm (see below); the RIGHT arm and
  `fxString_hasAdjointTripleCompleteness` stay `false`.  `= true`. -/
def fxString_hasStringSharedLegLegShape : Bool := true

/-- **★★★ ESTABLISHED — the LEFT-handed STRAIGHTEN BAND COLLAPSE is DISCHARGED unconditionally (FC-3 r7, B2).**
`stringZigZagBandCollapseLeft` proves, with NO band-collapse hypothesis, the exact goal
`stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id` for a LEFT-handed zigzag cup·cap pair
(`|lcCup| + 1 = |lcCap|`): the four generator combos cased, the two SAME-colour snakes firing
`stringMergedSharedLegFramesCollapse` (`triangleF` at `L = F`, `triangleGhi` at `L = G`) after the
`stringSharedLegLegShape` subst, the two MIXED combos refuted by `sharedLegModeClash`.  The cast reconciliation
(`castBoundary coh.symm reconnect.symm` vs the bridge's `castBoundary(align)`) closes by proof irrelevance.
`stringStraightenCellDescentStep_left` then supplies this collapse to the shipped
`stringStraightenCellDescentStep_ofCollapse`, making the LEFT STRAIGHTEN producer UNCONDITIONAL — the exact hypothesis
that gated producer took is now proven.

  Scope (honest): this is the LEFT handedness ONLY.  The descent oracle's zigzag arm is handedness-symmetric
  (`stringZigZagSharedLeg_widthDichotomy` admits both `|lcCup| + 1 = |lcCap|` and `|lcCap| + 1 = |lcCup|`), so the
  RIGHT mirror (`triangleGlo` / `triangleH` RIGHT-snakes + a RIGHT reconnect) is still owed for
  `StringCellDescentStepOracle` totality.  So `StringCellDescentStepOracle` stays UN-inhabited and
  `fxString_hasAdjointTripleCompleteness` stays `false`.  `= true`. -/
def fxString_hasStringZigZagBandCollapseLeft : Bool := true

end FX1Poly.Polygraph

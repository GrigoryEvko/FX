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

/-! ## Honesty marker -/

/-- **★ ESTABLISHED (partial) — the leg-factorization extraction and merged frames are machine-checked (FC-3 r7,
B2 stage 1).**  `stringSharedLegLegShape` EXPOSES the two leg pins (`lcCap = lcCup · L`, `rcCup = L · rcCap`) the
`sharedLegSnakeReconnect` discards — the load-bearing novelty the merged-frame rewrite consumes.  `stringMergedCupFrame`
/ `stringMergedCapFrame` are the single-whisker `atomFrame` shapes of a shared-leg cup / cap partner (both legs
single modalities, so associativity is definitional).

  What this marker does NOT close (gates stay `false`): the merged→iterated cast bridges
  (`whiskerRightComp`/`whiskerLeftComp`/`whiskerExchange`), the merged-frame collapse, and the band-collapse
  producer with its cast reconciliation.  `fxString_hasStringValleyStraightenBandCollapse` stays `false`.
  `= true`. -/
def fxString_hasStringSharedLegLegShape : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingString.StringStraightenBandCollapseProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringStraightenOracleWireUp

/-! # WalkingString — the RIGHT-handed STRAIGHTEN producer (FC-3 r8, B2): the mirror of the LEFT band collapse

`StringStraightenBandCollapseProducer` shipped the LEFT-handed band collapse `stringZigZagBandCollapseLeft`
(`|lcCup| + 1 = |lcCap|`) and the unconditional LEFT producer `stringStraightenCellDescentStep_left`.  The descent
classifier is handedness-SYMMETRIC (`stringZigZagSharedLeg_widthDichotomy` admits both widths), so the RIGHT
handedness `|lcCap| + 1 = |lcCup|` is the remaining arm for `StringCellDescentStepOracle` totality — the SOLE input
`stringDescentDispatch_ofLocatedPair` still takes (`StringRightStraightenProducer`).

This file ships the RIGHT mirror of the entire LEFT band-collapse stack.  Where the LEFT snake right-whiskers the
cup and left-whiskers the cap (`cupGen ▷ L` / `L ◁ capGen`, producing `L·M` / consuming `M·L`), the RIGHT snake
LEFT-whiskers the cup and RIGHT-whiskers the cap (`L ◁ cupGen` / `capGen ▷ L`, producing `M·L` / consuming `L·M`) —
exactly the shape of `triangleGlo` (`(G ◁ η) ⊟ (ε ▷ G)`, `L = G`, `M = F`) and `triangleH`
(`(H ◁ η') ⊟ (ε' ▷ H)`, `L = H`, `M = G`), the two RIGHT snakes.

  * ★ **`stringSharedLegForcesSameColourRight`** / **`stringCupCapDeletionReconnectsRight`** — the RIGHT reconnect:
    the SAME conclusion `atomFrameSource cup = atomFrameTarget cap` at the RIGHT width `|lcCap| + 1 = |lcCup|`.
    The same-colour snakes reuse the GENERIC `sharedLegSnakeReconnect` with the cup·cap roles SWAPPED (`coh.symm`,
    the shorter cap-side leg plays the generic "cup"), the mixed combos reuse `sharedLegModeClash` extending the
    shorter cap side.  No new generic lemma.
  * ★ the RIGHT engine legs / merged frames / cast bridge / general collapse — the whisker-flipped mirror of
    `StringValleyStraightenBandCollapse` + `StringStraightenBandCollapseProducer`.  The generic
    `stringSnakeDoubleWhiskerCollapses` fires unchanged.  The one genuinely-fiddly node is the cast bridge's ROLE
    SWAP: the RIGHT CUP side carries the align/endpoint casts (`whiskerLeftComp` + `whiskerExchange`, mirror of the
    LEFT cap) and the RIGHT CAP side is cast-free (`whiskerRightComp`, mirror of the LEFT cup).
  * ★★★ **`stringZigZagBandCollapseRight`** — the RIGHT band collapse, unconditional; truth-probed on a concrete
    RIGHT redex before the theorem.
  * ★★★ **`stringStraightenCellDescentStep_right : StringRightStraightenProducer`** — the RIGHT producer, closing
    the SOLE remaining input to the per-step oracle dispatch.

Raw Lean 4 + Init.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The RIGHT reconnect — a shared-leg cup·cap at the RIGHT width is SAME-colour -/

/-- ★★ **The RIGHT-handed shared-leg cup·cap is SAME-colour — its OUTER legs reconnect.**  The mirror of
`stringSharedLegForcesSameColour` at the RIGHT width relation `|lcCap| + 1 = |lcCup|`.  Same conclusion
(`atomFrameSource cup = atomFrameTarget cap`); the same-colour snakes reuse the GENERIC `sharedLegSnakeReconnect`
with the cup·cap roles SWAPPED (the shorter cap-side leg plays the generic "cup", `coh.symm`, result `.symm`), the
two MIXED combos are refuted by `sharedLegModeClash` extending the shorter cap side by the cup's leading leg. -/
theorem stringSharedLegForcesSameColourRight {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coherence : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (widthRel : capAtom.leftContext.length + 1 = cupAtom.leftContext.length) :
    atomFrameSource cupAtom = atomFrameTarget capAtom := by
  obtain ⟨cupLeftMid, cupRightMid, lcCup, cupDom, cupCod, genCup, rcCup⟩ := cupAtom
  obtain ⟨capLeftMid, capRightMid, lcCap, capDom, capCod, genCap, rcCap⟩ := capAtom
  dsimp only [atomFrameTarget, atomFrameSource, stringFG, stringGF, stringGH, stringHG] at coherence
  cases genCup with
  | counitLower => nomatch isCup
  | counitUpper => nomatch isCup
  | unitLower =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitLower =>
          show composePath lcCup rcCup = composePath lcCap rcCap
          dsimp only [stringFG, stringGF] at coherence
          exact (sharedLegSnakeReconnect AdjointTripleModality.right AdjointTripleModality.left
            lcCap rcCap lcCup rcCup coherence.symm widthRel).symm
      | counitUpper =>
          dsimp only [stringFG, stringHG] at coherence
          refine (sharedLegModeClash lcCup
            (composePath (ModalityPath.cons AdjointTripleModality.left
              (ModalityPath.cons AdjointTripleModality.right
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))) rcCup)
            (composePath lcCap (singletonModalityPath AdjointTripleModality.coLeft))
            (ModalityPath.cons AdjointTripleModality.right rcCap) ?_ ?_
            (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCap (singletonModalityPath AdjointTripleModality.coLeft)
                (ModalityPath.cons AdjointTripleModality.right rcCap)]
            exact coherence
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel.symm
  | unitUpper =>
      cases genCap with
      | unitLower => nomatch isCap
      | unitUpper => nomatch isCap
      | counitUpper =>
          show composePath lcCup rcCup = composePath lcCap rcCap
          dsimp only [stringGH, stringHG] at coherence
          exact (sharedLegSnakeReconnect AdjointTripleModality.coLeft AdjointTripleModality.right
            lcCap rcCap lcCup rcCup coherence.symm widthRel).symm
      | counitLower =>
          dsimp only [stringGH, stringGF] at coherence
          refine (sharedLegModeClash lcCup
            (composePath (ModalityPath.cons AdjointTripleModality.right
              (ModalityPath.cons AdjointTripleModality.coLeft
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))) rcCup)
            (composePath lcCap (singletonModalityPath AdjointTripleModality.right))
            (ModalityPath.cons AdjointTripleModality.left rcCap) ?_ ?_
            (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCap (singletonModalityPath AdjointTripleModality.right)
                (ModalityPath.cons AdjointTripleModality.left rcCap)]
            exact coherence
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel.symm

/-- ★ **The RIGHT-handed STRAIGHTEN endpoint identification.**  The `stringCupCapDeletionReconnects` twin at the
RIGHT width relation `|lcCap| + 1 = |lcCup|`: `atomFrameSource cup = atomFrameTarget cap`, wrapping the RIGHT
same-colour reconnect. -/
theorem stringCupCapDeletionReconnectsRight {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (coherence : atomFrameTarget cupAtom = atomFrameSource capAtom)
    (widthRel : capAtom.leftContext.length + 1 = cupAtom.leftContext.length) :
    atomFrameSource cupAtom = atomFrameTarget capAtom :=
  stringSharedLegForcesSameColourRight cupAtom capAtom isCup isCap coherence widthRel

/-! ## The RIGHT snake's two generator legs (whisker-flipped: cup LEFT-whiskered, cap RIGHT-whiskered) -/

/-- The RIGHT cup generator leg `L ◁ cupGen` (cupGen produces `M·L`).  The whisker-flipped mirror of
`stringSnakeCupGenLeg`. -/
def stringSnakeCupGenLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality)
        (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode))
      (composePath (singletonModalityPath sharedLegModality)
        (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
    (singletonModalityPath sharedLegModality) cupGen

/-- The RIGHT cap generator leg `capGen ▷ L` (capGen consumes `L·M`), its source restated in the `L·(M·L)`
bracketing so it is SYNTACTICALLY the cup leg's target (defeq — single modalities).  The whisker-flipped mirror of
`stringSnakeCapGenLeg`. -/
def stringSnakeCapGenLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality)
        (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
      (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
        (singletonModalityPath sharedLegModality)) :=
  RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
    (singletonModalityPath sharedLegModality) capGen

/-! ## The iterated-whisker RIGHT shared-leg legs -/

/-- The iterated RIGHT cup leg: `stringSnakeCupGenLegRight` right-whiskered by `contextRight`, then left-whiskered by
`contextLeft`.  The whisker-flipped mirror of `stringSharedLegCupLeg`. -/
def stringSharedLegCupLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)) contextRight))
      (composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
          contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight contextRight
      (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen))

/-- The iterated RIGHT cap leg: `stringSnakeCapGenLegRight` right-whiskered by `contextRight`, then left-whiskered by
`contextLeft`.  The whisker-flipped mirror of `stringSharedLegCapLeg`. -/
def stringSharedLegCapLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
          contextRight))
      (composePath contextLeft
        (composePath
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
            (singletonModalityPath sharedLegModality)) contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight contextRight
      (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen))

/-! ## The RIGHT distribution and general collapse -/

/-- The whiskered RIGHT snake distributes (by the two `whiskerVcomp` laws) into the vcomp of the RIGHT cup and cap
legs.  The whisker-flipped mirror of `stringWhiskeredSnakeDistributesToLegs`. -/
theorem stringWhiskeredSnakeDistributesToLegsRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (RawTwoCellExpr.whiskerLeft contextLeft
        (RawTwoCellExpr.whiskerRight contextRight
          (RawTwoCellExpr.vcomp (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen)
            (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen))))
      (RawTwoCellExpr.vcomp
        (stringSharedLegCupLegRight sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (stringSharedLegCapLegRight sharedLegModality otherLegModality capGen contextLeft contextRight)) :=
  TwoCellConvFull.trans
    (TwoCellConvFull.whiskerLeftCongr contextLeft
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp contextRight
          (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen)
          (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen)))))
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftVcomp contextLeft
      (RawTwoCellExpr.whiskerRight contextRight
        (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen))
      (RawTwoCellExpr.whiskerRight contextRight
        (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen)))))

/-- ★★ **The GENERAL RIGHT shared-leg frame collapse (cast-free).**  `cupLegRight ⊟ capLegRight ≈ id` on the shared
boundary `contextLeft · L · contextRight`.  The vcomp re-folds (by `stringWhiskeredSnakeDistributesToLegsRight`,
reversed) into the whiskered RIGHT snake, which collapses by the GENERIC `stringSnakeDoubleWhiskerCollapses`.  The
whisker-flipped mirror of `stringGeneralContextFrameLegsCollapse`, serving both RIGHT snakes via the supplied
`triangle`. -/
theorem stringGeneralContextFrameLegsCollapseRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (triangle : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen)
        (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (stringSharedLegCupLegRight sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (stringSharedLegCapLegRight sharedLegModality otherLegModality capGen contextLeft contextRight))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath contextLeft
          (composePath (singletonModalityPath sharedLegModality) contextRight))) :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.symm
        (stringWhiskeredSnakeDistributesToLegsRight sharedLegModality otherLegModality cupGen capGen
          contextLeft contextRight)))
    (stringSnakeDoubleWhiskerCollapses (singletonModalityPath sharedLegModality) contextLeft contextRight
      (RawTwoCellExpr.vcomp (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen)
        (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen))
      triangle)

/-! ## The RIGHT merged frames (roles swapped: cup absorbs L LEFT, cap absorbs L RIGHT) -/

/-- The merged RIGHT cup frame `(leftContext · L) ◁ (rightContext ▷ cupGen)` — the shape `atomFrame` produces for a
RIGHT shared-leg cup whose stored left context is `leftContext · L`.  The role-swapped mirror of `stringMergedCapFrame`. -/
def stringMergedCupFrameRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight))
      (composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
        (composePath (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
          contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
    (composePath contextLeft (singletonModalityPath sharedLegModality))
    (RawTwoCellExpr.whiskerRight contextRight cupGen)

/-- The merged RIGHT cap frame `leftContext ◁ ((L · rightContext) ▷ capGen)` — the shape `atomFrame` produces for a
RIGHT shared-leg cap whose stored right context is `L · rightContext`.  The role-swapped mirror of `stringMergedCupFrame`. -/
def stringMergedCapFrameRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath contextLeft
        (composePath (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
          (composePath (singletonModalityPath sharedLegModality) contextRight)))
      (composePath contextLeft
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
          (composePath (singletonModalityPath sharedLegModality) contextRight))) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight
      (composePath (singletonModalityPath sharedLegModality) contextRight) capGen)

/-! ## The cap half of THE RIGHT CAST BRIDGE: the merged cap frame IS the iterated cap leg (cast-FREE) -/

/-- ★ **The cap half of THE RIGHT CAST BRIDGE (cast-free).**  The merged RIGHT cap frame
`leftContext ◁ ((L · rightContext) ▷ capGen)` is `TwoCellConvFull` to the iterated RIGHT cap leg
`stringSharedLegCapLegRight`: the merged single right-whisker splits (`whiskerRightComp`) into
`rightContext ▷ (L ▷ capGen)`, lifted through `leftContext ◁ -` with the cast pulled out.  CAST-FREE at the
conclusion (the split's associativity cast is between definitionally-equal boundaries).  The role-swapped mirror of
`stringMergedCupFrame_convFull_cupLeg`. -/
theorem stringMergedCapFrame_convFull_capLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (stringMergedCapFrameRight sharedLegModality otherLegModality capGen contextLeft contextRight)
      (stringSharedLegCapLegRight sharedLegModality otherLegModality capGen contextLeft contextRight) := by
  have lifted := TwoCellConvFull.whiskerLeftCongr contextLeft
    (TwoCellConvFull.whiskerRightComp (singletonModalityPath sharedLegModality) contextRight capGen)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at lifted
  exact lifted

/-! ## The cup half of THE RIGHT CAST BRIDGE: the merged cup frame IS the iterated cup leg (up to casts) -/

/-- The align cast: the iterated RIGHT cup leg's SOURCE equals the merged RIGHT cup frame's SOURCE — the
`leftContext · L`-prefix re-bracketing.  The role-swapped mirror of `stringMergedCapAlign`. -/
theorem stringMergedCupAlignRight
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

/-- The endpoint cast: the iterated RIGHT cup leg's TARGET equals the merged RIGHT cup frame's TARGET. -/
theorem stringMergedCupEndpointRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
          contextRight)
      = composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
            contextRight) :=
  (composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      contextRight)).symm

/-- ★ **The cup half of THE RIGHT CAST BRIDGE.**  The merged RIGHT cup frame `(leftContext · L) ◁ (rightContext ▷
cupGen)` is `TwoCellConvFull` to the iterated RIGHT cup leg `stringSharedLegCupLegRight` up to the align / endpoint
casts: the composite left-whisker `leftContext · L` splits (`whiskerLeftComp`) into `leftContext ◁ (L ◁ (rightContext
▷ cupGen))`, and the inner `L ◁ (rightContext ▷ cupGen)` exchanges (`whiskerExchange`) into `rightContext ▷ (L ◁
cupGen)`; the two casts fuse (`castBoundary_castBoundary`).  The role-swapped mirror of
`stringMergedCapFrame_convFull_castCapLeg`. -/
theorem stringMergedCupFrame_convFull_castCupLegRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (stringMergedCupFrameRight sharedLegModality otherLegModality cupGen contextLeft contextRight)
      (RawTwoCellExpr.castBoundary
        (stringMergedCupAlignRight sharedLegModality contextLeft contextRight)
        (stringMergedCupEndpointRight sharedLegModality otherLegModality contextLeft contextRight)
        (stringSharedLegCupLegRight sharedLegModality otherLegModality cupGen contextLeft contextRight)) := by
  have innerConv := TwoCellConvFull.whiskerLeftCongr contextLeft
    (TwoCellConvFull.whiskerExchange (singletonModalityPath sharedLegModality) contextRight cupGen)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at innerConv
  have splitOuter := TwoCellConvFull.whiskerLeftComp contextLeft (singletonModalityPath sharedLegModality)
    (RawTwoCellExpr.whiskerRight contextRight cupGen)
  have combined := splitOuter.trans
    (TwoCellConvFull.castBoundaryCongr
      (stringMergedCupAlignRight sharedLegModality contextLeft contextRight)
      (stringMergedCupEndpointRight sharedLegModality otherLegModality contextLeft contextRight)
      innerConv)
  rw [RawTwoCellExpr.castBoundary_castBoundary] at combined
  exact combined

/-! ## THE RIGHT MERGED CAST BRIDGE — the two merged frames collapse to the identity -/

/-- Casting an identity 2-cell by two proofs of the SAME boundary equality is the identity. -/
private theorem stringCastBoundaryIdSame {sourceMode targetMode : AdjointTripleMode}
    {pathP pathQ : ModalityPath adjointTripleGraph sourceMode targetMode} (hsource htarget : pathP = pathQ) :
    RawTwoCellExpr.castBoundary hsource htarget
        (RawTwoCellExpr.id (signature := adjointTripleModeSignature) pathP)
      = RawTwoCellExpr.id (signature := adjointTripleModeSignature) pathQ := by
  cases hsource; rfl

/-- A cup-target cast and cap-source cast that re-anchor the shared middle to the SAME 1-cell fuse out of the
vcomp, leaving the outer source / target casts on the whole composite. -/
private theorem vcompCastFuse {sourceMode targetMode : AdjointTripleMode}
    {pathSource pathMid pathMidCast pathTarget pathOuter : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr adjointTripleModeSignature pathSource pathMid)
    (cellBeta : RawTwoCellExpr adjointTripleModeSignature pathMid pathTarget)
    (hsource : pathSource = pathOuter) (hmiddleOne hmiddleTwo : pathMid = pathMidCast)
    (htarget : pathTarget = pathOuter) :
    RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddleOne cellAlpha)
        (RawTwoCellExpr.castBoundary hmiddleTwo htarget cellBeta)
      = RawTwoCellExpr.castBoundary hsource htarget (RawTwoCellExpr.vcomp cellAlpha cellBeta) := by
  cases hsource; cases hmiddleOne; cases htarget; rfl

/-- The frames' alignment cast: the merged RIGHT cap frame's SOURCE equals the merged RIGHT cup frame's TARGET. -/
theorem stringMergedFramesAlignRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath contextLeft
        (composePath (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
          (composePath (singletonModalityPath sharedLegModality) contextRight))
      = composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath
            (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
            contextRight) :=
  (composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      contextRight)).symm

/-- The frames' endpoint cast: the merged RIGHT cap frame's TARGET equals the merged RIGHT cup frame's SOURCE. -/
theorem stringMergedFramesEndpointRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    composePath contextLeft
        (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
          (composePath (singletonModalityPath sharedLegModality) contextRight))
      = composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight) :=
  (composePath_assoc contextLeft (singletonModalityPath sharedLegModality)
    (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight)).symm

/-- ★★ **THE RIGHT MERGED CAST BRIDGE.**  The merged RIGHT cup and cap frames collapse to the identity on the merged
cup frame's source: `mergedCupRight ⊟ castBoundary(align) mergedCapRight ≈ id`.  The cup frame lifts WITH its cast
(`stringMergedCupFrame_convFull_castCupLegRight`), the cap frame lifts cast-free
(`stringMergedCapFrame_convFull_capLegRight`); the two casts (cup-bridge on the first factor, frames on the second)
are relocated across the vcomp and fuse to identity (all boundary equalities are single-modality assoc between
definitionally-equal endpoints), leaving `vcomp cupLegRight capLegRight`, which collapses by
`stringGeneralContextFrameLegsCollapseRight`.  The role-swapped mirror of `stringMergedSharedLegFramesCollapse`. -/
theorem stringMergedSharedLegFramesCollapseRight
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality)))
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode))
    (triangle : StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (stringSnakeCupGenLegRight sharedLegModality otherLegModality cupGen)
        (stringSnakeCapGenLegRight sharedLegModality otherLegModality capGen))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (singletonModalityPath sharedLegModality)))
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (stringMergedCupFrameRight sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (RawTwoCellExpr.castBoundary
          (stringMergedFramesAlignRight sharedLegModality otherLegModality contextLeft contextRight)
          (stringMergedFramesEndpointRight sharedLegModality contextLeft contextRight)
          (stringMergedCapFrameRight sharedLegModality otherLegModality capGen contextLeft contextRight)))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath (composePath contextLeft (singletonModalityPath sharedLegModality))
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode) contextRight))) := by
  have cupConv := StringSaturatedTwoCellConv.ofFull
    (stringMergedCupFrame_convFull_castCupLegRight sharedLegModality otherLegModality cupGen
      contextLeft contextRight)
  have capConv := stringSaturatedConv_castBoundary_congr
    (stringMergedFramesAlignRight sharedLegModality otherLegModality contextLeft contextRight)
    (stringMergedFramesEndpointRight sharedLegModality contextLeft contextRight)
    (StringSaturatedTwoCellConv.ofFull
      (stringMergedCapFrame_convFull_capLegRight sharedLegModality otherLegModality capGen
        contextLeft contextRight))
  refine StringSaturatedTwoCellConv.trans (StringSaturatedTwoCellConv.vcompCongrLeft _ cupConv)
    (StringSaturatedTwoCellConv.trans (StringSaturatedTwoCellConv.vcompCongrRight _ capConv) ?_)
  refine StringSaturatedTwoCellConv.trans (stringSaturatedConv_of_eq (vcompCastFuse _ _ _ _ _ _)) ?_
  exact StringSaturatedTwoCellConv.trans
    (stringSaturatedConv_castBoundary_congr _ _
      (stringGeneralContextFrameLegsCollapseRight sharedLegModality otherLegModality cupGen capGen triangle
        contextLeft contextRight))
    (stringSaturatedConv_of_eq (stringCastBoundaryIdSame _ _))

/-! ## Truth-probe — the RIGHT merged collapse fires on the concrete lower `G`-snake -/

/-- ★ **Truth-probe (RIGHT band collapse on a concrete RIGHT redex).**  The RIGHT merged frame collapse fires on the
bare lower `G`-snake `(G ◁ η) ⊟ (ε ▷ G)` (empty contexts, `L = G`, `M = F`, `triangleGlo`): the RIGHT cup/cap merged
frames collapse to `id (G)`.  Confirms the RIGHT geometry BEFORE the general band-collapse theorem — not a fabricated
flip. -/
theorem stringRightSnakeCollapseProbe :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (stringMergedCupFrameRight AdjointTripleModality.right AdjointTripleModality.left stringUnitLower
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
        (RawTwoCellExpr.castBoundary
          (stringMergedFramesAlignRight AdjointTripleModality.right AdjointTripleModality.left
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
          (stringMergedFramesEndpointRight AdjointTripleModality.right
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
          (stringMergedCapFrameRight AdjointTripleModality.right AdjointTripleModality.left stringCounitLower
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
            (singletonModalityPath AdjointTripleModality.right))
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)))) :=
  stringMergedSharedLegFramesCollapseRight AdjointTripleModality.right AdjointTripleModality.left
    stringUnitLower stringCounitLower StringSaturatedTwoCellConv.triangleGlo
    (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
    (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)

/-! ## THE RIGHT BAND COLLAPSE — the readback bands collapse, discharging the RIGHT STRAIGHTEN hypothesis -/

/-- ★★★ **THE RIGHT-HANDED BAND COLLAPSE, unconditional.**  For a located RIGHT-handed zigzag cup·cap pair
(`|lcCap| + 1 = |lcCup|`) with the shared window coherence and the endpoint reconnect, the readback bands collapse:
`stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id`.  This is EXACTLY the hypothesis
`stringStraightenCellDescentStep_ofCollapseRight` takes.  Casing the four cup×cap generator combos: the two
SAME-colour snakes (`η·ε` at `L = G` via `triangleGlo`, `η'·ε'` at `L = H` via `triangleH`) fire the RIGHT merged cast
bridge `stringMergedSharedLegFramesCollapseRight` after the RIGHT leg-factorization subst (`stringSharedLegLegShape`
cup·cap-swapped); the two MIXED combos are refuted at the 2-cell level by `sharedLegModeClash` (extending the shorter
cap side).  The role-swapped mirror of `stringZigZagBandCollapseLeft`. -/
theorem stringZigZagBandCollapseRight
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : cupAtom.isCupAtom = true) (isCap : capAtom.isCupAtom = false)
    (widthRel : capAtom.leftContext.length + 1 = cupAtom.leftContext.length)
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
          obtain ⟨lcCupEq, rcCapEq⟩ := stringSharedLegLegShape
            AdjointTripleModality.right AdjointTripleModality.left lcCap rcCap lcCup rcCup coh.symm widthRel
          subst rcCapEq
          subst lcCupEq
          exact stringMergedSharedLegFramesCollapseRight AdjointTripleModality.right AdjointTripleModality.left
            stringUnitLower stringCounitLower StringSaturatedTwoCellConv.triangleGlo lcCap rcCup
      | counitUpper =>
          refine (sharedLegModeClash lcCup (composePath stringFG rcCup)
            (composePath lcCap (singletonModalityPath AdjointTripleModality.coLeft))
            (ModalityPath.cons AdjointTripleModality.right rcCap) ?_ ?_
            (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCap (singletonModalityPath AdjointTripleModality.coLeft)
                (ModalityPath.cons AdjointTripleModality.right rcCap)]
            exact coh
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel.symm
  | unitUpper =>
      cases genCap with
      | unitLower => exact absurd isCap (by decide)
      | unitUpper => exact absurd isCap (by decide)
      | counitUpper =>
          dsimp only [stringGH, stringHG] at coh
          obtain ⟨lcCupEq, rcCapEq⟩ := stringSharedLegLegShape
            AdjointTripleModality.coLeft AdjointTripleModality.right lcCap rcCap lcCup rcCup coh.symm widthRel
          subst rcCapEq
          subst lcCupEq
          exact stringMergedSharedLegFramesCollapseRight AdjointTripleModality.coLeft AdjointTripleModality.right
            stringUnitUpper stringCounitUpper StringSaturatedTwoCellConv.triangleH lcCap rcCup
      | counitLower =>
          refine (sharedLegModeClash lcCup (composePath stringGH rcCup)
            (composePath lcCap (singletonModalityPath AdjointTripleModality.right))
            (ModalityPath.cons AdjointTripleModality.left rcCap) ?_ ?_
            (fun modeEqual => AdjointTripleMode.noConfusion modeEqual)).elim
          · rw [composePath_assoc lcCap (singletonModalityPath AdjointTripleModality.right)
                (ModalityPath.cons AdjointTripleModality.left rcCap)]
            exact coh
          · rw [ModalityPath.length_composePath, singletonModalityPath_length]
            exact widthRel.symm

/-! ## The UNCONDITIONAL RIGHT STRAIGHTEN producer -/

/-- ★ **The STRAIGHTEN producer for a located RIGHT `zigZagSharedLeg` redex, GIVEN the band collapse.**  The
role-swapped mirror of `stringStraightenCellDescentStep_ofCollapse`: reads the boundary coherence off `cell`'s own
realized chain, takes the reconnection from the RIGHT colour-aware `stringCupCapDeletionReconnectsRight`, realizes the
`stepConv`, builds the deleted `next`, packages.  The band collapse is the single remaining input. -/
def stringStraightenCellDescentStep_ofCollapseRight
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (widthRel : capAtom.leftContext.length + 1 = cupAtom.leftContext.length)
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
    stringCupCapDeletionReconnectsRight cupAtom capAtom isCupCup isCapCap coh widthRel
  let stepConv := stringStraightenStepConv cell prefixCells rest reconnect coh (collapse coh reconnect)
    sourceSplit
  let targetSplit := straightenNextCell_spine cell prefixCells rest reconnect sourceSplit
  stringCellDescentResult_ofStraightenStep stepConv prefixCells rest isCupCup isCapCap sourceSplit
    targetSplit

/-- ★★★ **THE RIGHT-HANDED STRAIGHTEN PRODUCER — UNCONDITIONAL.**  `StringRightStraightenProducer` inhabited: the
gated `stringStraightenCellDescentStep_ofCollapseRight` with its band-collapse hypothesis SUPPLIED by
`stringZigZagBandCollapseRight`.  This is the SOLE remaining input `stringDescentDispatch_ofLocatedPair` takes —
closing the descent oracle's RIGHT zigzag arm. -/
def stringStraightenCellDescentStep_right : StringRightStraightenProducer :=
  fun {_sourceMode _targetMode} {_sourcePath _targetPath} cell prefixCells rest {cupAtom capAtom}
      isCupCup isCapCap sourceSplit widthRel =>
    stringStraightenCellDescentStep_ofCollapseRight cell prefixCells rest isCupCup isCapCap sourceSplit widthRel
      (fun coh reconnect => stringZigZagBandCollapseRight cupAtom capAtom isCupCup isCapCap widthRel coh reconnect)

/-! ## Honesty marker -/

/-- **★★★ ESTABLISHED — the RIGHT-handed STRAIGHTEN producer is machine-checked (FC-3 r8, B2).**  The whole RIGHT
band-collapse stack is the role-swapped mirror of the LEFT: `stringSharedLegForcesSameColourRight` /
`stringCupCapDeletionReconnectsRight` (RIGHT reconnect, cup·cap-swapped `sharedLegSnakeReconnect`), the RIGHT engine
legs / merged frames / cast bridge (`stringMergedCupFrame_convFull_castCupLegRight` carries the casts,
`stringMergedCapFrame_convFull_capLegRight` cast-free — roles transposed from LEFT), the RIGHT merged collapse
`stringMergedSharedLegFramesCollapseRight` (the cup-bridge cast relocated across the vcomp and fused to identity), and
the unconditional `stringZigZagBandCollapseRight` (two SAME-colour snakes fire `triangleGlo`/`triangleH`, two MIXED
refuted by `sharedLegModeClash`).  Truth-probed on the concrete lower `G`-snake (`stringRightSnakeCollapseProbe`).
`stringStraightenCellDescentStep_right : StringRightStraightenProducer` is the resulting UNCONDITIONAL producer — the
SOLE remaining input to `stringDescentDispatch_ofLocatedPair`, closed.

  What this marker does NOT close (gates stay `false`): with the RIGHT producer AND the data-locate (B1) shipped, the
  per-step oracle can be inhabited (the oracle wire-up is the next brick); Piece II (`StringCellValleyTraceEquiv`) is
  separate and untouched, so `fxString_hasAdjointTripleCompleteness` stays `false`.  `= true`. -/
def fxString_hasStringRightStraightenProducer : Bool := true

end FX1Poly.Polygraph

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

  What this marker does NOT close (gates stay `false`): the FINAL band-collapse producer — rewriting the readback
  BANDS `stringReadbackBand` into the merged frames via the leg pins (a heterogeneous substitution on the atom's
  stored contexts, plus the generator PATH-level pinning) and reconciling the goal's `castBoundary coh.symm
  reconnect.symm` with the merged bridge's `castBoundary(align)`, together with the 2-cell MIXED-colour refutation.
  `fxString_hasStringValleyStraightenBandCollapse` stays `false`.  `= true`. -/
def fxString_hasStringSharedLegLegShape : Bool := true

end FX1Poly.Polygraph

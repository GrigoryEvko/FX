import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyStraightenReadback
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSaturatedConv

/-! # WalkingString — the STRAIGHTEN band collapse (FC-3 r7): the whiskered-triangle engine + the shared-leg
frame collapse

`StringValleyStraightenReadback` reduced the STRAIGHTEN arm to EXACTLY the band collapse
`stringReadbackBand cup ⊟ castBoundary (stringReadbackBand cap) ≈ id`, taken there as a HYPOTHESIS.  This file
builds the machinery that discharges it, ported from the adjunction's single-colour `SpineValleyFrameCollapse` to
the four-generator, two-colour string, GENERIC in the shared-leg modality `L`, its palindrome partner modality
`M`, and the cup / cap generators / triangle so ONE engine instantiates at both same-colour snakes (`F`-snake via
`triangleF` at `L = F`, `M = G`; upper-`G`-snake via `triangleGhi` at `L = G`, `M = H`).

Both legs are SINGLE modalities (`F`, `G`, `H` are all single generators), so every `composePath` reduces to a
concrete cons-list — associativity and right-identity are DEFINITIONAL, exactly as in the adjunction's concrete
`SpineValleyFrameCollapse`; nothing depends on a variable-path associativity cast.

## What this file ships (the cast-FREE core, B1's whiskered triangles)

  * ★ **`stringSnakeDoubleWhiskerCollapses`** — the WHISKERED-TRIANGLE firing point: ANY snake with a triangle
    `snake ≈ id L` collapses under a double-whisker context `contextLeft ◁ ((-) ▷ contextRight)`, cast-free.
    GENERIC in `(L, snake, triangle)`, so it serves all four string triangles by one derivation.
  * ★ **`stringSharedLegCupLeg` / `stringSharedLegCapLeg`** — the iterated-whisker readback legs of a shared-leg
    cup / cap partner, GENERIC in `L`, `M`, and the two generators.  Compose CAST-FREE.
  * ★ **`stringWhiskeredSnakeDistributesToLegs`** — the whiskered snake distributes into the vcomp of the two legs.
  * ★ **`stringGeneralContextFrameLegsCollapse`** — the cast-free GENERAL shared-leg frame collapse
    `cupLeg ⊟ capLeg ≈ id`, re-folding into the whiskered snake and firing `stringSnakeDoubleWhiskerCollapses`.

## What this file does NOT close (gates stay `false`)

The MERGED-`atomFrame` cast bridge, the leg-factorization extraction, the 2-cell MIXED-colour refutation, and the
final band-collapse producer are the remaining nodes.  No gate flag flips here:
`fxString_hasStringValleyStraightenBandCollapse` stays `false`.

Raw Lean 4 + Init; every proof is the shipped whisker functoriality + the two `whiskerVcomp` distributions + the
generic double-whisker collapse.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The whiskered-triangle firing point (generic in the snake + triangle) -/

/-- ★ **A snake collapses to the identity under a DOUBLE-whisker context** `contextLeft ◁ ((-) ▷ contextRight)`,
GIVEN its triangle `snake ≈ id sharedLeg`.  Collapse the inner right-whiskered snake first (`whiskerRightCongr`
of the triangle, then `whiskerRightId`), then strip the outer left whisker (`whiskerLeftCongr`, then
`whiskerLeftId`) — all cast-free.  The string twin of `leftSnakeDoubleWhiskerCollapses`, but GENERIC in
`(sharedLeg, snake, triangle)`: it serves `triangleF`, `triangleGlo`, `triangleGhi`, and `triangleH`. -/
theorem stringSnakeDoubleWhiskerCollapses
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    {contextLeftSourceMode contextRightTargetMode : AdjointTripleMode}
    (sharedLeg : ModalityPath adjointTripleGraph leftSourceMode leftTargetMode)
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode)
    (snake : RawTwoCellExpr adjointTripleModeSignature sharedLeg sharedLeg)
    (triangle : StringSaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) sharedLeg)) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft contextLeft
        (RawTwoCellExpr.whiskerRight contextRight snake))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath contextLeft (composePath sharedLeg contextRight))) := by
  have innerCollapse : StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight contextRight snake)
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath sharedLeg contextRight)) :=
    StringSaturatedTwoCellConv.trans
      (StringSaturatedTwoCellConv.whiskerRightCongr contextRight triangle)
      (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := adjointTripleModeSignature) sharedLeg contextRight)))
  exact StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.whiskerLeftCongr contextLeft innerCollapse)
    (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.whiskerLeftId (signature := adjointTripleModeSignature) contextLeft
        (composePath sharedLeg contextRight))))

/-! ## The snake's two generator legs (named so the shared middle reduces without metavars) -/

/-- The cup generator leg `cupGen ▷ L`.  The generic string twin of `seedSnakeCupGenLeg`. -/
def stringSnakeCupGenLeg
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (cupGen : RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
      (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
        (singletonModalityPath sharedLegModality))
      (composePath
        (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
        (singletonModalityPath sharedLegModality)) :=
  RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
    (singletonModalityPath sharedLegModality) cupGen

/-- The cap generator leg `L ◁ capGen`, its source restated in the `(L·M)·L` bracketing so it is SYNTACTICALLY the
cup leg's target (defeq — all single-modality legs, so `composePath` reduces).  The generic string twin of
`seedSnakeCapGenLeg`. -/
def stringSnakeCapGenLeg
    {leftSourceMode leftTargetMode : AdjointTripleMode}
    (sharedLegModality : AdjointTripleModality leftSourceMode leftTargetMode)
    (otherLegModality : AdjointTripleModality leftTargetMode leftSourceMode)
    (capGen : RawTwoCellExpr adjointTripleModeSignature
      (composePath (singletonModalityPath otherLegModality) (singletonModalityPath sharedLegModality))
      (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)) :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath
        (composePath (singletonModalityPath sharedLegModality) (singletonModalityPath otherLegModality))
        (singletonModalityPath sharedLegModality))
      (composePath (singletonModalityPath sharedLegModality)
        (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
    (singletonModalityPath sharedLegModality) capGen

/-! ## The iterated-whisker shared-leg legs (built on the gen-legs, boundaries in natural form) -/

/-- The iterated cup leg: the cup gen leg `cupGen ▷ L` right-whiskered by `contextRight`, then left-whiskered by
`contextLeft`.  Built on `stringSnakeCupGenLeg` so the distribution's `whiskerLeftVcomp` product is definitionally
this leg.  The generic string twin of `sharedLegCupLeg`. -/
def stringSharedLegCupLeg
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
        (composePath
          (composePath (ModalityPath.nil (graph := adjointTripleGraph) leftSourceMode)
            (singletonModalityPath sharedLegModality)) contextRight))
      (composePath contextLeft
        (composePath
          (composePath (composePath (singletonModalityPath sharedLegModality)
            (singletonModalityPath otherLegModality)) (singletonModalityPath sharedLegModality)) contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight contextRight
      (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen))

/-- The iterated cap leg: the cap gen leg `L ◁ capGen` right-whiskered by `contextRight`, then left-whiskered by
`contextLeft`.  Built on `stringSnakeCapGenLeg`.  The generic string twin of `sharedLegCapLeg`. -/
def stringSharedLegCapLeg
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
      (composePath contextLeft
        (composePath
          (composePath (composePath (singletonModalityPath sharedLegModality)
            (singletonModalityPath otherLegModality)) (singletonModalityPath sharedLegModality)) contextRight))
      (composePath contextLeft
        (composePath
          (composePath (singletonModalityPath sharedLegModality)
            (ModalityPath.nil (graph := adjointTripleGraph) leftTargetMode)) contextRight)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) contextLeft
    (RawTwoCellExpr.whiskerRight contextRight
      (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen))

/-! ## The distribution: the whiskered snake IS the two legs' vcomp -/

/-- The whiskered snake distributes (by the two `whiskerVcomp` laws) into the vcomp of the cup and cap legs.  The
generic string twin of `whiskeredSnakeDistributesToLegs`. -/
theorem stringWhiskeredSnakeDistributesToLegs
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
    (contextLeft : ModalityPath adjointTripleGraph contextLeftSourceMode leftSourceMode)
    (contextRight : ModalityPath adjointTripleGraph leftTargetMode contextRightTargetMode) :
    TwoCellConvFull adjointTripleModeSignature
      (RawTwoCellExpr.whiskerLeft contextLeft
        (RawTwoCellExpr.whiskerRight contextRight
          (RawTwoCellExpr.vcomp (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen)
            (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen))))
      (RawTwoCellExpr.vcomp
        (stringSharedLegCupLeg sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (stringSharedLegCapLeg sharedLegModality otherLegModality capGen contextLeft contextRight)) :=
  TwoCellConvFull.trans
    (TwoCellConvFull.whiskerLeftCongr contextLeft
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp contextRight
          (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen)
          (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen)))))
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftVcomp contextLeft
      (RawTwoCellExpr.whiskerRight contextRight (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen))
      (RawTwoCellExpr.whiskerRight contextRight (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen)))))

/-! ## The cast-free GENERAL shared-leg frame collapse -/

/-- ★★ **The GENERAL shared-leg frame collapse (cast-free).**  For ARBITRARY whisker contexts, the shared-leg cup
and cap legs compose to the identity on the shared boundary `contextLeft · L · contextRight`:
`cupLeg ⊟ capLeg ≈ id`.  The vcomp re-folds (by `stringWhiskeredSnakeDistributesToLegs`, reversed) into the
whiskered snake, which collapses by `stringSnakeDoubleWhiskerCollapses`.  Cast-free.  The generic string twin of
`generalContextFrameLegsCollapse`, serving both same-colour snakes via the supplied `triangle`. -/
theorem stringGeneralContextFrameLegsCollapse
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
      (RawTwoCellExpr.vcomp
        (stringSharedLegCupLeg sharedLegModality otherLegModality cupGen contextLeft contextRight)
        (stringSharedLegCapLeg sharedLegModality otherLegModality capGen contextLeft contextRight))
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature)
        (composePath contextLeft
          (composePath (singletonModalityPath sharedLegModality) contextRight))) :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.symm
        (stringWhiskeredSnakeDistributesToLegs sharedLegModality otherLegModality cupGen capGen
          contextLeft contextRight)))
    (stringSnakeDoubleWhiskerCollapses (singletonModalityPath sharedLegModality) contextLeft contextRight
      (RawTwoCellExpr.vcomp (stringSnakeCupGenLeg sharedLegModality otherLegModality cupGen)
        (stringSnakeCapGenLeg sharedLegModality otherLegModality capGen))
      triangle)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the cast-free whiskered-triangle engine (B1's whiskered triangles) is machine-checked at the
three-generator seed.**  `stringSnakeDoubleWhiskerCollapses` fires ANY string triangle (`snake ≈ id L`) under an
arbitrary double-whisker context, GENERIC in the snake and triangle — one derivation for all four triangles.  The
iterated shared-leg legs (`stringSharedLegCupLeg` / `stringSharedLegCapLeg`) compose cast-free, distribute out of
the whiskered snake (`stringWhiskeredSnakeDistributesToLegs`), and collapse to the identity
(`stringGeneralContextFrameLegsCollapse`) for any context, GENERIC in the shared-leg / cup / cap generators.  Both
legs being single modalities makes every `composePath` associativity / right-identity DEFINITIONAL, so the string
port is cast-free exactly as the adjunction's concrete `SpineValleyFrameCollapse`.

  What this marker does NOT close (gates stay `false`): the MERGED-`atomFrame` cast bridge relating the readback
  bands to these iterated legs, the leg-factorization extraction, the 2-cell MIXED-colour refutation, and the band
  collapse producer.  `fxString_hasStringValleyStraightenBandCollapse` stays `false`.  `= true`. -/
def fxString_hasStringSnakeWhiskeredTriangleEngine : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedCorr

/-! # ArcCupFusedBridge — the fused-component bridge across the cup legs (peel campaign H, cup rung 2d-v)

The fused rewiring's same-component chain: when one boundary read attaches to the cup's LEFT
leg and another to its RIGHT leg in the FRESH run, the cup join fuses them — and the head
correspondence transports the fused answer to the COMPOSITE run's sigma-image reads.  The
composite same-component fact produced here is exactly the candidate exhibition the composite
partner pin (`arcCupHeadFolded_partner_ofSameComponent`) dispatches on.

Two layers: the generic join algebra (`isSameComponent_unionFindJoin_bridgeLegs` — one leg
reaches each probe, so the join connects the probes) and the cup-head instances at both leg
orientations (`arcCupHeadFolded_compositeSameComponent_ofFreshLegs` and its flip).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic join algebra -/

/-- **The join fuses whatever the two legs reach**: if the left leg shares a component with
the left probe and the right leg with the right probe, then after joining the legs the two
probes share a component — the middle disjunct of the join characterization fires. -/
theorem isSameComponent_unionFindJoin_bridgeLegs (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (legLeft legRight probeLeft probeRight : Nat)
    (leftLegReaches : isSameComponent links legLeft probeLeft = true)
    (rightLegReaches : isSameComponent links legRight probeRight = true) :
    isSameComponent (unionFindJoin links legLeft legRight) probeLeft probeRight = true := by
  rw [isSameComponent_unionFindJoin links forest legLeft legRight probeLeft probeRight,
    leftLegReaches, rightLegReaches]
  cases baseQuery : isSameComponent links probeLeft probeRight with
  | true => rfl
  | false => rfl

/-! ## The cup-head instances -/

/-- ★ **The fused-component bridge at the cup head**: probes reached by the cup's left and
right legs respectively in the FRESH run have same-component sigma-images in the COMPOSITE
run — the head correspondence answers every sigma-image query as the fresh run with the
window pair joined first, and the join fuses the legs' components. -/
theorem arcCupHeadFolded_compositeSameComponent_ofFreshLegs
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (probeLeft probeRight : Nat)
    (leftLegReaches : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition probeLeft = true)
    (rightLegReaches : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1) probeRight = true) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight) = true :=
  (arcComponentShiftCorr_cupHeadFolded bottomCount windowPosition windowFits atoms chained
      probeLeft probeRight).trans
    (isSameComponent_unionFindJoin_bridgeLegs
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (isUnionFindForest_processArcSpine atoms
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        isUnionFindForest_nil)
      windowPosition (windowPosition + 1) probeLeft probeRight
      leftLegReaches rightLegReaches)

/-- ★ The fused-component bridge at the OPPOSITE leg orientation: the left probe reached by
the cup's RIGHT leg and the right probe by its LEFT leg.  One symmetry flip away from
`arcCupHeadFolded_compositeSameComponent_ofFreshLegs`. -/
theorem arcCupHeadFolded_compositeSameComponent_ofFreshLegsFlipped
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (probeLeft probeRight : Nat)
    (rightLegReaches : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1) probeLeft = true)
    (leftLegReaches : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition probeRight = true) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight) = true :=
  (isSameComponent_symm
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight)).trans
    (arcCupHeadFolded_compositeSameComponent_ofFreshLegs bottomCount windowPosition
      windowFits atoms chained probeRight probeLeft leftLegReaches rightLegReaches)

/-- **Honesty marker — the fused-component bridge across the cup legs is SHIPPED (peel
campaign H, cup rung 2d-v).**  The generic join algebra
(`isSameComponent_unionFindJoin_bridgeLegs`) and both leg orientations of the cup-head
instance (`arcCupHeadFolded_compositeSameComponent_ofFreshLegs` / `...Flipped`): fresh-run
reads attached to opposite cup legs have same-component sigma-images in the composite run,
ready for the composite partner pin.  What this marker does NOT claim: the boundary-read
instantiation (the sigma-image reads ARE the composite boundary reads), the leg-attachment
partner facts at the fresh run, and the cup-cancellation endgame.  `= true`. -/
def fxMode_hasArcCupFusedBridge : Bool := true

end FX1Poly.Polygraph

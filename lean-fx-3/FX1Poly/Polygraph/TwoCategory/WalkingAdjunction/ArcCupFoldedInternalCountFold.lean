import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedDiagramFold

/-! # ArcCupFoldedInternalCountFold — folding the per-index internal-count cancel into the whole count lists

`ArcCupFoldedDiagramFold` ships the diagram-partner leg of the cup-head `tailsCancel`: the per-index
fresh-partner agreement folds into the whole partner list through `natRangeMapCongr`, the propext-free
range-map congruence.  Its honesty marker names the next rung — "internal counts next" — and this brick
delivers it: the internal cup-count and cap-count folded lists are `(List.range …).map` of the
`freshShiftAbove`-shifted `internalEventCountAt` readoff, so exactly the same fold combinator carries a
per-index count agreement to the whole-list equality.

Both legs are a direct `natRangeMapCongr` instance at the cup/cap event-node readoff — mechanical, mirroring
`arcCupFoldedDiagramPartnerList_agrees`.  The orbit supplies the per-index count agreement pointwise (the
count analog of `arcCupFoldedPartner_agrees_ofSameClassification`, gated on the mixed-free second spine);
with all three legs now folding uniformly through `natRangeMapCongr`, the residual is exactly the three
pointwise agreements plus the folded↔clean transport down to the `bottomCount + 2` seed.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The folded internal CUP-count list agrees, given per-index agreement over the composite range.**
With the two chained runs' fresh internal cup-count readoffs coinciding at every composite index below the
running range bound, the two folded cup-count lists — each `List.range …` mapped through the
`freshShiftAbove`-shifted `internalEventCountAt` at the cup event nodes — are equal.  A direct instance of
`natRangeMapCongr`; the pointwise hypothesis is the count analog of the per-index partner agreement. -/
theorem arcCupFoldedInternalCupCountList_agrees
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pointwiseAgree : ∀ compositeIndex,
      compositeIndex < bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length →
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).cupEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).cupEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex)) :
    (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)).map
        (fun compositeIndex =>
          internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).cupEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).cupEventNodes
              (freshShiftAbove windowPosition 2 compositeIndex)) :=
  natRangeMapCongr _ _ _ pointwiseAgree

/-- ★ **The folded internal CAP-count list agrees, given per-index agreement over the composite range.**
The cap analog of `arcCupFoldedInternalCupCountList_agrees`: the two folded cap-count lists coincide once
the two chained runs' fresh cap-count readoffs agree at every shifted composite index.  Same
`natRangeMapCongr` fold, at the cap event nodes. -/
theorem arcCupFoldedInternalCapCountList_agrees
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pointwiseAgree : ∀ compositeIndex,
      compositeIndex < bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length →
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).capEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).capEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex)) :
    (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)).map
        (fun compositeIndex =>
          internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).capEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).capEventNodes
              (freshShiftAbove windowPosition 2 compositeIndex)) :=
  natRangeMapCongr _ _ _ pointwiseAgree

/-! ## Honesty marker -/

/-- **Honesty marker — the folded internal-count-list agreements are SHIPPED (peel campaign H).**
`arcCupFoldedInternalCupCountList_agrees` / `arcCupFoldedInternalCapCountList_agrees`: from the per-index
fresh internal-count agreement over the whole composite range, the two folded count lists coincide — the
internal-count legs of `tailsCancel` at the folded level, completing the fold trio (diagram partner +
internal cup + internal cap) uniformly through `natRangeMapCongr`.  What this marker does NOT claim: the
per-index count agreements themselves (the count analogs of `arcCupFoldedPartner_agrees_ofSameClassification`,
under the orbit's `sameClassification`), nor the folded↔clean transport down to the `bottomCount + 2` seed.
`= true`. -/
def fxMode_hasArcCupFoldedInternalCountFold : Bool := true

end FX1Poly.Polygraph

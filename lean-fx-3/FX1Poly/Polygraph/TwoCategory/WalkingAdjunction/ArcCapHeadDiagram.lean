import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapPartnerList
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadLoops

/-! # ArcCapHeadDiagram — the assembled cap-head `DiagramType` correspondence

The `DiagramType` leg of the cap-head extract correspondence, assembled (peel campaign H,
rung E-3, part 8).  The composite extract's whole boundary diagram is determined by the
fresh extract's: the bottom count carries the consumed pair, the top count agrees (the
composite top is the reindexed fresh top), the partner list is the fresh partner list
transported by the two-zone index shift with the consumed window pair spliced in at the
window position (part 6), and both loop counters read zero on the chained fragment
(part 7 and the fresh-side loop freedom).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The assembled cap-head `DiagramType` correspondence**: on the chained fragment, the
composite extract's boundary diagram (peeled cap at the window, then the tail atoms) is the
fresh extract's diagram transported — same bottom count (the consumed pair's two ports
included), the fresh top count, the fresh partner list mapped through the two-zone index
shift with the consumed window pair `[windowPosition + 1, windowPosition]` spliced in at
the window position, and the fresh loop count (both count zero). -/
theorem arcCapHeadFolded_extractDiagram
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    extractDiagram bottomCount
        ({ openWires := (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires,
           links := (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links,
           nextFresh := (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).nextFresh,
           loops := (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).loops } : WireState)
      = { bottomCount := bottomCount,
          topCount := (extractDiagram tailBoundary
            ({ openWires := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires,
               links := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).links,
               nextFresh := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).nextFresh,
               loops := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).loops } : WireState)).topCount,
          partner := natListInsertAt
            (((extractDiagram tailBoundary
              ({ openWires := (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires,
                 links := (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).links,
                 nextFresh := (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).nextFresh,
                 loops := (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).loops } : WireState)).partner).map
              (freshShiftAbove windowPosition 2))
            windowPosition
            [windowPosition + 1, windowPosition],
          loops := (extractDiagram tailBoundary
            ({ openWires := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires,
               links := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).links,
               nextFresh := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).nextFresh,
               loops := (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).loops } : WireState)).loops } := by
  have topLengthEq : (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    arcPositionalShiftSim_openWiresLength
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      3 tailBoundary [] [bottomCount]
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms)
      (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms)
  have partnerEq := arcCapHeadFolded_partnerListCorr bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained
  have compositeLoops : (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).loops = 0 :=
    arcCapHeadFolded_loops_zero bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained
  have freshLoops : (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).loops = 0 :=
    arcFoldLoops_zero_ofChainedSpineList tailBoundary atoms chained
  show DiagramType.mk bottomCount
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (partnerIndexOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)))
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).loops
    = DiagramType.mk bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length
        (natListInsertAt
          (((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length))).map
            (freshShiftAbove windowPosition 2))
          windowPosition
          [windowPosition + 1, windowPosition])
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).loops
  rw [partnerEq, topLengthEq, compositeLoops, freshLoops]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cap-head `DiagramType` correspondence (peel campaign H,
rung E-3, part 8).**  `arcCapHeadFolded_extractDiagram`: on the chained fragment the
composite cap-head extract's boundary diagram equals the fresh extract's transported —
same bottom count, the fresh top count (the positional shift simulation's open-wire map),
the fresh partner list through the two-zone shift with the consumed pair spliced at the
window (part 6), and the fresh loop count (parts 7 + the fresh loop freedom, both zero).
What this marker does NOT claim: the `FullArcStructure` legs (cup/cap totals, per-strand
internal counts) or the cup-head diagram leg — those are the remaining rungs before the
head-cancellation assembly.  `= true`. -/
def fxMode_hasArcCapHeadDiagramLeg : Bool := true

end FX1Poly.Polygraph

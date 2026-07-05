import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadDiagram
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapInternalCounts

/-! # ArcCapHeadStructure — the assembled cap-head `FullArcStructure` transport

The full arc-structure correspondence at the cap head, assembled (peel campaign H,
rung E-3, part 11 — the rung-E capstone).  The composite extract's WHOLE
`FullArcStructure` — boundary diagram, cup/cap event totals, per-port internal count
lists — is determined by the fresh extract's: the diagram transports through the two-zone
shift with the consumed pair spliced (part 8), the cap total carries the head's own event
(+1) while the cup total agrees (the simulation length legs), and the internal-count lists
splice the consumed strand's values `[1, 1]` / `[0, 0]` at the window (part 10).  One
five-field rewrite over the `FullArcStructure.mk` spine.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The assembled cap-head `FullArcStructure` transport**: on the chained fragment the
composite extract (peeled cap at the window, then the tail atoms) equals the fresh
extract transported — the diagram through the two-zone shift with the consumed pair
spliced, one extra cap event (the head's own), the same cup events, and the internal
count lists with the consumed strand's values spliced at the window. -/
theorem arcCapHeadFolded_extractArc
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    extractArc bottomCount
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms)
      = { diagram :=
            { bottomCount := bottomCount,
              topCount := (extractArc tailBoundary
                (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms)).diagram.topCount,
              partner := natListInsertAt
                (((extractArc tailBoundary
                  (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms)).diagram.partner).map (freshShiftAbove windowPosition 2))
                windowPosition [windowPosition + 1, windowPosition],
              loops := (extractArc tailBoundary
                (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms)).diagram.loops },
          cupCount := (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms)).cupCount,
          capCount := (extractArc tailBoundary
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms)).capCount + 1,
          internalCupCounts := natListInsertAt
            (extractArc tailBoundary
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms)).internalCupCounts
            windowPosition [0, 0],
          internalCapCounts := natListInsertAt
            (extractArc tailBoundary
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms)).internalCapCounts
            windowPosition [1, 1] } := by
  show FullArcStructure.mk
      (extractDiagram bottomCount
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
                windowPosition) atoms).loops } : WireState))
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes))
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes))
    = FullArcStructure.mk
        { bottomCount := bottomCount,
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
                  atoms).loops } : WireState)).loops }
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).cupEventNodes.length
        ((processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).capEventNodes.length + 1)
        (natListInsertAt
          ((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).cupEventNodes))
          windowPosition [0, 0])
        (natListInsertAt
          ((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).capEventNodes))
          windowPosition [1, 1])
  rw [arcCapHeadFolded_extractDiagram bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained,
    arcCapHeadFolded_cupEventsLength bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms,
    arcCapHeadFolded_capEventsLength bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms,
    arcCapHeadFolded_internalCupCountsCorr bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms chained,
    arcCapHeadFolded_internalCapCountsCorr bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms chained]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cap-head `FullArcStructure` transport (peel
campaign H, rung E-3, part 11 — the rung-E capstone).**  `arcCapHeadFolded_extractArc`:
on the chained fragment the composite cap-head extract's whole `FullArcStructure` equals
the fresh extract's transported — the diagram through the two-zone shift with the
consumed pair spliced (part 8), cap total +1 / cup total unchanged (the simulation length
legs), and the internal-count lists with `[1, 1]` / `[0, 0]` spliced at the window
(part 10).  One five-field rewrite over the `FullArcStructure.mk` spine; every leg is a
prior peel brick.  What this marker does NOT claim: injectivity of the transport, the
cup-head twin, or the head-cancellation assembly discharging
`SpineArcHeadExtractionChained` — the remaining rungs.  `= true`. -/
def fxMode_hasArcCapHeadStructure : Bool := true

end FX1Poly.Polygraph

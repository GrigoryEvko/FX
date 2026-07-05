import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadDiagram
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupInternalCounts

/-! # ArcCupHeadStructure — the assembled cup-head `FullArcStructure` transport

The full arc-structure correspondence at the cup head, assembled (peel campaign H, the
cup-rung capstone).  The composite extract's WHOLE `FullArcStructure` — boundary diagram,
cup/cap event totals, per-port internal count lists — is determined by the fresh
extract's run data: the diagram carries the transported partner list (rung 5), the cup
total carries the head's own event (+1) while the cap total agrees (the simulation length
legs), and the internal-count lists are the leg-joined fresh census through
`arcCupCountTransport` (rung 6).  One five-field rewrite over the `FullArcStructure.mk`
spine, on the legs-separate branch of the chained fragment.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The assembled cup-head `FullArcStructure` transport**: on the chained fragment
with the window legs fresh-separated, the composite extract (peeled cup at the window,
then the tail atoms) equals the fresh extract transported — the diagram with the
per-index partner transport, one extra cup event (the head's own), the same cap events,
and the internal count lists through the leg-joined count transport. -/
theorem arcCupHeadFolded_extractArc
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance overallSource windowPosition = AdjunctionMode.base)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false) :
    extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms)
      = { diagram :=
            { bottomCount := bottomCount,
              topCount := (extractArc (bottomCount + 2)
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms)).diagram.topCount,
              partner := (List.range
                  (bottomCount
                    + (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires.length)).map
                (arcCupPartnerTransport
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).links
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires)
                  (bottomCount + 2
                    + (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires.length)
                  windowPosition),
              loops := (extractArc (bottomCount + 2)
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms)).diagram.loops },
          cupCount := (extractArc (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms)).cupCount + 1,
          capCount := (extractArc (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms)).capCount,
          internalCupCounts := (List.range
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires.length)).map
            (arcCupCountTransport
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).cupEventNodes
              windowPosition 1),
          internalCapCounts := (List.range
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires.length)).map
            (arcCupCountTransport
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).capEventNodes
              windowPosition 0) } := by
  show FullArcStructure.mk
      (extractDiagram bottomCount
        ({ openWires := (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires,
           links := (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links,
           nextFresh := (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).nextFresh,
           loops := (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).loops } : WireState))
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes))
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes))
    = FullArcStructure.mk
        { bottomCount := bottomCount,
          topCount := (extractDiagram (bottomCount + 2)
            ({ openWires := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires,
               links := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links,
               nextFresh := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).nextFresh,
               loops := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).loops } : WireState)).topCount,
          partner := (List.range
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)).map
            (arcCupPartnerTransport
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)
              windowPosition),
          loops := (extractDiagram (bottomCount + 2)
            ({ openWires := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires,
               links := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links,
               nextFresh := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).nextFresh,
               loops := (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).loops } : WireState)).loops }
        ((processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).cupEventNodes.length + 1)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).capEventNodes.length
        ((List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)).map
          (arcCupCountTransport
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).cupEventNodes
            windowPosition 1))
        ((List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)).map
          (arcCupCountTransport
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).capEventNodes
            windowPosition 0))
  rw [arcCupHeadFolded_extractDiagram bottomCount windowPosition windowFits
      windowParityIsBase atoms chained legsSeparate,
    arcCupHeadFolded_cupEventsLength bottomCount windowPosition atoms,
    arcCupHeadFolded_capEventsLength bottomCount windowPosition atoms,
    arcCupHeadFolded_internalCupCountsCorr bottomCount windowPosition windowFits atoms
      chained,
    arcCupHeadFolded_internalCapCountsCorr bottomCount windowPosition windowFits atoms
      chained]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cup-head `FullArcStructure` transport (peel
campaign H, the cup-rung capstone).**  `arcCupHeadFolded_extractArc`: on the chained
fragment with the window legs fresh-separated, the composite cup-head extract's whole
`FullArcStructure` equals the fresh extract transported — the diagram with the per-index
partner transport (rung 5), cup total +1 / cap total unchanged (the simulation length
legs), and the internal-count lists through the leg-joined `arcCupCountTransport`
(rung 6).  One five-field rewrite over the `FullArcStructure.mk` spine; every leg is a
prior peel brick.  What this marker does NOT claim: the legs-CONNECTED (cup-cancel)
world's diagram leg, injectivity of the transport, or the head-location assembly
discharging `SpineArcHeadExtractionChained` — the remaining rungs.  `= true`. -/
def fxMode_hasArcCupHeadStructure : Bool := true

end FX1Poly.Polygraph

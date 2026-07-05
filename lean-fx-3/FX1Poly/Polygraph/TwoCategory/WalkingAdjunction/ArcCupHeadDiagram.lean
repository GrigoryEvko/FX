import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPartnerDispatch
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadLoops
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcLoopFreedom

/-! # ArcCupHeadDiagram — the assembled cup-head `DiagramType` correspondence

The `DiagramType` leg of the cup-head extract correspondence, assembled (peel campaign H,
cup rung 5).  The composite extract's whole boundary diagram is determined by the fresh
extract's: the bottom count carries the peeled cup's two consumed ports, the top count
agrees (the positional shift simulation's open-wire map), the partner list is the fresh
data transported pointwise through `arcCupPartnerTransport` (the per-index dispatch mapped
over the boundary range), and both loop counters read zero on the disciplined chained
fragment.  Requires the legs-separate hypothesis (the dispatch's precondition) and the
window parity discipline (the loops leg's precondition).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The composite cup partner list is the transported fresh partner list**: mapping the
per-index dispatch over the boundary range — the list-level closed form the diagram leg
consumes. -/
theorem arcCupHeadFolded_partnerListCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (partnerIndexOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      = (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)).map
        (arcCupPartnerTransport
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)
          windowPosition) := by
  have rangeEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length) := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
  rw [rangeEq]
  exact listMapCongr
    (partnerIndexOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length))
    (arcCupPartnerTransport
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
      windowPosition)
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length))
    (fun candidate candidateMem =>
      arcCupHeadFolded_partnerDispatch bottomCount windowPosition windowFits atoms
        chained legsSeparate candidate (mem_range_imp_lt candidateMem))

/-- ★ **The assembled cup-head `DiagramType` correspondence**: on the disciplined chained
fragment, the composite extract's boundary diagram (peeled cup at the window, then the
tail atoms) is the fresh extract's diagram transported — same bottom count (the peeled
cup's two ports consumed), the fresh top count, the fresh partner data mapped pointwise
through the per-index dispatch, and the fresh loop count (both count zero). -/
theorem arcCupHeadFolded_extractDiagram
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance overallSource windowPosition = AdjunctionMode.base)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false) :
    extractDiagram bottomCount
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
                windowPosition) atoms).loops } : WireState)
      = { bottomCount := bottomCount,
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
                    [] []) atoms).loops } : WireState)).loops } := by
  have topLengthEq : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms
  have partnerEq := arcCupHeadFolded_partnerListCorr bottomCount windowPosition windowFits
    atoms chained legsSeparate
  have compositeLoops : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).loops = 0 :=
    arcCupHeadFolded_loops_zero bottomCount windowPosition windowFits windowParityIsBase
      atoms chained
  have freshLoops : (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).loops = 0 :=
    arcFoldLoops_zero_ofChainedSpineList (bottomCount + 2) atoms chained
  show DiagramType.mk bottomCount
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      ((List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)).map
        (partnerIndexOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)))
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).loops
    = DiagramType.mk bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length
        ((List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)).map
          (arcCupPartnerTransport
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            windowPosition))
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).loops
  rw [partnerEq, topLengthEq, compositeLoops, freshLoops]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cup-head `DiagramType` correspondence (peel campaign
H, cup rung 5).**  `arcCupHeadFolded_partnerListCorr`: the composite partner list is the
per-index dispatch mapped over the boundary range.  `arcCupHeadFolded_extractDiagram`: on
the disciplined chained fragment the composite cup-head extract's boundary diagram equals
the fresh extract's transported — same bottom count, the fresh top count, the transported
partner list, and the fresh loop count (both zero).  Both require the legs-separate
hypothesis; the diagram leg additionally requires the window parity discipline (the loops
leg's precondition).  What this marker does NOT claim: the `FullArcStructure` legs
(cup/cap totals, per-strand internal counts), the legs-connected (cup-cancellation) world,
and the head-cancellation assembly — the remaining rungs.  `= true`. -/
def fxMode_hasArcCupHeadDiagramLeg : Bool := true

end FX1Poly.Polygraph

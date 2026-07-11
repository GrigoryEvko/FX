import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadLoops
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapPartnerList
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedSim

/-! # WalkingString/StringArcCapHeadDiagram — the assembled cap-head `DiagramType` correspondence,
ported (FC-3 r21, THE 110-PERCENT GRIND — Branch B)

Phantom-signature clone of the walking-adjunction `ArcCapHeadDiagram`, re-plumbed onto the
FOUR-generator adjoint-triple seed and NARROWED to the pure-cap regime (Route C): the composite
cap-head extract's boundary `DiagramType` equals the fresh extract's transported — same bottom count,
the fresh top count (the positional-shift simulation's open-wire map), the fresh partner list through
the two-zone shift with the consumed window pair spliced at the window
(`stringArcCapHeadFolded_partnerListCorr`), and the fresh loop count.

The two loop legs are the FC-3 r21 pure-cap deliverables: the composite side reads zero by
`stringArcCapHeadFolded_loops_zero` and the fresh side by `arcFoldLoops_zero_ofPureCapChained` — both
requiring the `AllCapArity` witness the sort call site provides.  With them the diagram correspondence
assembles on the pure-cap chained fragment exactly as the adjunction lane does on the general chained
fragment.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The assembled cap-head `DiagramType` correspondence** (adjoint-triple, pure-cap): on the
pure-cap chained fragment the composite extract's boundary diagram (peeled cap at the window, then the
tail atoms) equals the fresh extract's transported — same bottom count, the fresh top count, the fresh
partner list through the two-zone index shift with the consumed window pair
`[windowPosition + 1, windowPosition]` spliced at the window, and the fresh loop count (both zero). -/
theorem stringArcCapHeadFolded_extractDiagram
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (allCap : AllCapArity atoms)
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
      (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms)
  have partnerEq := stringArcCapHeadFolded_partnerListCorr bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained
  have compositeLoops : (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).loops = 0 :=
    stringArcCapHeadFolded_loops_zero bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms allCap chained
  have freshLoops : (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).loops = 0 :=
    arcFoldLoops_zero_ofPureCapChained tailBoundary atoms allCap chained
  dsimp only [extractDiagram]
  rw [partnerEq, topLengthEq, compositeLoops, freshLoops]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cap-head `DiagramType` correspondence, adjoint-triple pure-cap
(FC-3 r21).**  `stringArcCapHeadFolded_extractDiagram`: on the pure-cap chained fragment the composite
cap-head extract's boundary diagram equals the fresh extract's transported — same bottom count, the
fresh top count (the string positional-shift simulation's open-wire map), the fresh partner list
through the two-zone shift with the consumed pair spliced at the window
(`stringArcCapHeadFolded_partnerListCorr`), and the fresh loop count (both zero, via the r21 pure-cap
loops legs `stringArcCapHeadFolded_loops_zero` / `arcFoldLoops_zero_ofPureCapChained`).  What this
marker does NOT claim: the `FullArcStructure` legs (cup/cap totals, per-strand internal counts) — the
next rung (`StringArcCapHeadStructure`).  `= true`. -/
def fxString_hasArcCapHeadDiagramLeg : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadDiagram
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCounts

/-! # WalkingString/StringArcCapHeadStructure — the assembled cap-head `FullArcStructure` transport,
ported (FC-3 r21, THE 110-PERCENT GRIND — Branch B)

Phantom-signature clone of the walking-adjunction `ArcCapHeadStructure`, re-plumbed onto the
FOUR-generator adjoint-triple seed and NARROWED to the pure-cap regime (Route C): the composite
cap-head extract's WHOLE `FullArcStructure` — boundary diagram, cup/cap event totals, per-port
internal count lists — equals the fresh extract's transported.  The diagram leg is the r21
`stringArcCapHeadFolded_extractDiagram` (which threads the pure-cap `AllCapArity` loops legs); the
event totals are the shipped `stringArcCapHeadFolded_cupEventsLength` / `_capEventsLength` (cup
unchanged, cap `+1`); and the internal-count lists splice the consumed strand's `[0, 0]` / `[1, 1]` at
the window (`stringArcCapHeadFolded_internalCupCountsCorr` / `_internalCapCountsCorr`).  One five-field
rewrite over the `FullArcStructure.mk` spine.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The assembled cap-head `FullArcStructure` transport** (adjoint-triple, pure-cap): on the
pure-cap chained fragment the composite extract (peeled cap at the window, then the tail atoms) equals
the fresh extract transported — the diagram through the two-zone shift with the consumed pair spliced,
one extra cap event (the head's own), the same cup events, and the internal count lists with the
consumed strand's values spliced at the window. -/
theorem stringArcCapHeadFolded_extractArc
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (allCap : AllCapArity atoms)
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
  dsimp only [extractArc]
  rw [stringArcCapHeadFolded_extractDiagram bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms allCap chained,
    stringArcCapHeadFolded_cupEventsLength bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms,
    stringArcCapHeadFolded_capEventsLength bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms,
    stringArcCapHeadFolded_internalCupCountsCorr bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms chained,
    stringArcCapHeadFolded_internalCapCountsCorr bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms chained]

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cap-head `FullArcStructure` transport, adjoint-triple pure-cap
(FC-3 r21).**  `stringArcCapHeadFolded_extractArc`: on the pure-cap chained fragment the composite
cap-head extract's whole `FullArcStructure` equals the fresh extract's transported — the diagram
through the two-zone shift with the consumed pair spliced
(`stringArcCapHeadFolded_extractDiagram`, threading the r21 pure-cap loops legs), cap total `+1` / cup
total unchanged (the simulation length legs), and the internal-count lists with `[1, 1]` / `[0, 0]`
spliced at the window.  One five-field rewrite over the `FullArcStructure.mk` spine; every leg is a
shipped string brick.  What this marker does NOT claim: the head-cancellation extract equality (the
CANCEL theorem `stringArcCapHeadFolded_extractArc_cancel`, the next rung) or the sort-driver
inhabitation of the residual.  `= true`. -/
def fxString_hasArcCapHeadStructure : Bool := true

end FX1Poly.Polygraph

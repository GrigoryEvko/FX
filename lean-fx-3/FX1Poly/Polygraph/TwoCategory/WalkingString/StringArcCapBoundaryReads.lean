import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedSim

/-! # WalkingString/StringArcCapBoundaryReads — the composite boundary reads are reindexed fresh
reads, ported (FC-3 r20, THE CLONE CAMPAIGN — floor)

Phantom-signature two-token clone of the walking-adjunction `ArcCapBoundaryReads`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  The extract-correspondence DIAGRAM leg: at the cap head the
composite boundary (bottom `range bottomCount`, top the folded composite wires) reads the fresh
boundary (bottom `range tailBoundary`, top the fresh wires) through the cap-head reindexing, under the
two-zone boundary INDEX shift.  This brick ships the two folded-state zone corollaries (via the folded
positional sim's `openMap`, taken from the string clone `stringArcPositionalShiftSim_capHeadFolded`)
and the total-port count fact.  The generic zone correspondences (`arcCapBoundaryRead_belowWindow`/
`_atOrPastWindow`) are graph-neutral and REUSED by import; the signature is a pure phantom, so ONLY
the `SpineAtom`-quantified statements clone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The folded-state corollaries (the shapes the partner leg consumes) -/

/-- **Zone I at the folded states**: below the window, the composite end state's boundary
reads the reindexed fresh end state's boundary at the same index. -/
theorem stringArcCapHeadFolded_boundaryRead_belowWindow
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (probeIndex : Nat) (belowWindow : probeIndex < windowPosition) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        probeIndex
      = arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          probeIndex) := by
  rw [(stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms).openMap]
  exact arcCapBoundaryRead_belowWindow bottomCount windowPosition tailBoundary windowFits
    tailBoundaryFits
    (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).openWires
    probeIndex belowWindow

/-- **Zones II and III at the folded states**: at or past the window, the composite end
state's boundary reads the reindexed fresh end state's boundary two indices higher. -/
theorem stringArcCapHeadFolded_boundaryRead_atOrPastWindow
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (probeIndex : Nat) (atWindow : windowPosition ≤ probeIndex)
    (probeInRange : probeIndex
      < tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (probeIndex + 2)
      = arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          probeIndex) := by
  rw [(stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms).openMap]
  exact arcCapBoundaryRead_atOrPastWindow bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits
    (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).openWires
    probeIndex atWindow probeInRange

/-- **The composite has exactly two more boundary ports than the fresh run** — the consumed
window pair; the top counts agree since the composite top is the `sigma`-mapped fresh top. -/
theorem stringArcCapHeadFolded_totalPorts
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length
      = tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length
        + 2 := by
  rw [(stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms).openMap,
    mapLength (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
        3)
      (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires,
    ← tailBoundaryFits]
  exact Nat.add_right_comm tailBoundary 2
    (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).openWires.length

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head composite boundary reads, ported (FC-3 r20 clone campaign).**
The two folded-state zone corollaries via the string positional sim's `openMap`, and the
two-extra-ports count fact — phantom-signature two-token clones of `arcCapHeadFolded_boundaryRead_*`
and `_totalPorts`, riding the graph-neutral zone correspondences (reused by import).  What this marker
does NOT claim: the partner-scan congruence, the window pair partnering each other in the composite
extract, and the assembled diagram/partner leg.  `= true`. -/
def fxString_hasArcCapBoundaryReads : Bool := true

end FX1Poly.Polygraph

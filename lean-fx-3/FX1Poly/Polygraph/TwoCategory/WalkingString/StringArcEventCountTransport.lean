import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEventCountTransport
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedCorr
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcComponentPersistence

/-! # WalkingString/StringArcEventCountTransport — per-strand event counts through the head
correspondence, ported (FC-3 r20, THE CLONE CAMPAIGN — floor)

Phantom-signature two-token clone of the walking-adjunction `ArcEventCountTransport`, re-plumbed onto
the FOUR-generator adjoint-triple seed.  The four assembled composite-count decompositions at
reindexed probes: cup head cup/cap counts, cap head cup/cap counts.  The generic scan-transport kit
(`countEventsInRoot_singleton`/`_mapCorr`/`_append`) is graph-neutral and REUSED by import; the
folded positional sims (`stringArcPositionalShiftSim_*HeadFolded`), the folded component
correspondences (`stringArcComponentShiftCorr_*HeadFolded`), and the event-to-leg / event-to-wire
links (`stringArcCupHeadFolded_eventLegLinked` / `stringArcCapHeadFolded_eventWireLinked`) are the
string clones from the earlier bricks.  The signature is a pure phantom, so ONLY the
`SpineAtom`-quantified statements clone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The assembled counts at the cup head -/

/-- ★ **The composite cup-event count at a reindexed probe, under a cup head**: the fresh
run's leg-joined count plus the head's own cup event, which sits on the window leg's
strand. -/
theorem stringArcCupHeadFolded_cupEventCountAtImage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) (anchorProbe : Nat) :
    countEventsInRoot
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 anchorProbe))
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).cupEventNodes
      = countEventsInRoot
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          (unionFindRootOf
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).links
              windowPosition (windowPosition + 1))
            anchorProbe)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).cupEventNodes
        + (if isSameComponent
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).links
              windowPosition (windowPosition + 1))
            windowPosition anchorProbe
          then 1 else 0) := by
  have eventsShape := (stringArcPositionalShiftSim_cupHeadFolded bottomCount windowPosition
    atoms).cupEventsMap
  have foldedCorr := stringArcComponentShiftCorr_cupHeadFolded bottomCount windowPosition
    windowFits atoms chained
  have eventAtLeg : isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (bottomCount + 2)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 anchorProbe)
    = isSameComponent
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        bottomCount
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe) :=
    isSameComponent_congrOfLinked
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (bottomCount + 2) bottomCount
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 anchorProbe)
      (stringArcCupHeadFolded_eventLegLinked bottomCount windowPosition atoms)
  have legAsImage : isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 anchorProbe)
    = isSameComponent
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 windowPosition)
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe) :=
    congrArg
      (fun anchorNode => isSameComponent
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        anchorNode
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe))
      (arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits).symm
  have headTest : (unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (bottomCount + 2)
      == unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe))
      = isSameComponent
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          windowPosition anchorProbe :=
    (eventAtLeg.trans legAsImage).trans (foldedCorr windowPosition anchorProbe)
  rw [eventsShape,
    countEventsInRoot_append
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe))
      ((processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).cupEventNodes.map
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1))
      [bottomCount + 2],
    countEventsInRoot_mapCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      foldedCorr anchorProbe
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).cupEventNodes,
    countEventsInRoot_singleton
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe))
      (bottomCount + 2),
    headTest]

/-- **The composite cap-event count at a reindexed probe, under a cup head**: exactly the
fresh run's leg-joined count — the cup head contributes no cap event. -/
theorem stringArcCupHeadFolded_capEventCountAtImage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) (anchorProbe : Nat) :
    countEventsInRoot
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 anchorProbe))
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).capEventNodes
      = countEventsInRoot
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          (unionFindRootOf
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).links
              windowPosition (windowPosition + 1))
            anchorProbe)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).capEventNodes := by
  have eventsShape := (stringArcPositionalShiftSim_cupHeadFolded bottomCount windowPosition
    atoms).capEventsMap
  rw [eventsShape,
    countEventsInRoot_append
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 anchorProbe))
      ((processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).capEventNodes.map
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1))
      [],
    countEventsInRoot_mapCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (stringArcComponentShiftCorr_cupHeadFolded bottomCount windowPosition windowFits atoms
        chained)
      anchorProbe
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).capEventNodes]
  exact Nat.add_zero
    (countEventsInRoot
      (unionFindJoin
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        windowPosition (windowPosition + 1))
      (unionFindRootOf
        (unionFindJoin
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          windowPosition (windowPosition + 1))
        anchorProbe)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).capEventNodes)

/-! ## The assembled counts at the cap head -/

/-- **The composite cup-event count at a reindexed probe, under a cap head**: exactly the
fresh run's count — the cap head contributes no cup event, and the degenerate legs collapse
the join. -/
theorem stringArcCapHeadFolded_cupEventCountAtImage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) (anchorProbe : Nat) :
    countEventsInRoot
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            anchorProbe))
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).cupEventNodes
      = countEventsInRoot
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            anchorProbe)
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).cupEventNodes := by
  have eventsShape := (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms).cupEventsMap
  have joinCollapse : unionFindJoin
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0
    = (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links :=
    unionFindJoin_ofSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0
      (isSameComponent_self
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
        0)
  rw [eventsShape,
    countEventsInRoot_append
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          anchorProbe))
      ((processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).cupEventNodes.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      [],
    countEventsInRoot_mapCorr
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      0 0
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (stringArcComponentShiftCorr_capHeadFolded bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)
      anchorProbe
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).cupEventNodes,
    joinCollapse]
  exact Nat.add_zero
    (countEventsInRoot
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
        anchorProbe)
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).cupEventNodes)

/-- **The composite cap-event count at a reindexed probe, under a cap head**: the fresh run's
count plus the head's own cap event term — the head event rides the persistent event-to-wire
link onto the consumed left wire, whose query stays COMPOSITE-spelled here (the strand-closure
invariant will evaluate it to zero). -/
theorem stringArcCapHeadFolded_capEventCountAtImage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) (anchorProbe : Nat) :
    countEventsInRoot
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            anchorProbe))
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).capEventNodes
      = countEventsInRoot
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            anchorProbe)
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).capEventNodes
        + (if isSameComponent
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            windowPosition
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
              anchorProbe)
          then 1 else 0) := by
  have eventsShape := (stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms).capEventsMap
  have joinCollapse : unionFindJoin
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0
    = (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links :=
    unionFindJoin_ofSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0
      (isSameComponent_self
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
        0)
  have headTest : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        bottomCount
      == unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          anchorProbe))
      = isSameComponent
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            anchorProbe) :=
    isSameComponent_congrOfLinked
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount windowPosition
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        anchorProbe)
      (stringArcCapHeadFolded_eventWireLinked bottomCount windowPosition windowFits atoms)
  rw [eventsShape,
    countEventsInRoot_append
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          anchorProbe))
      ((processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).capEventNodes.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      [bottomCount],
    countEventsInRoot_mapCorr
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      0 0
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (stringArcComponentShiftCorr_capHeadFolded bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)
      anchorProbe
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).capEventNodes,
    joinCollapse,
    countEventsInRoot_singleton
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          anchorProbe))
      bottomCount,
    headTest]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-strand event-count transport through the head correspondence, ported
(FC-3 r20 clone campaign).**  The four assembled composite-count decompositions at reindexed probes:
cup head cup/cap counts (fully fresh-side — the head's cup event resolves onto the leg-joined window
query), cap head cup count (fully fresh-side, degenerate legs collapsed), cap head cap count (the
head's own event term stays composite-spelled at the consumed wire — evaluating it to zero NEEDS the
strand-closure invariant, NOT claimed here).  Riding the graph-neutral scan kit (reused) and the
string-clone folded sims/correspondences/links.  Also NOT claimed: the boundary-node read maps, the
diagram/partner leg, and the head-cancellation assembly.  `= true`. -/
def fxString_hasArcEventCountTransport : Bool := true

end FX1Poly.Polygraph

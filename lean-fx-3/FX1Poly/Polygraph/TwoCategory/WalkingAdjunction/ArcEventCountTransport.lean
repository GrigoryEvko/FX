import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentPersistence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues

/-! # ArcEventCountTransport — per-strand event counts through the head correspondence

The extract's internal cup/cap counts are `countEventsInRoot` scans: per event, one
same-component query against an anchor node.  This brick transports those scans through the
head-cancellation correspondence at the folded end states.  Generic kit: the scan distributes
over append, computes on a singleton, and maps a `sigma`-image event list at a `sigma`-image
anchor onto the leg-joined base scan (every per-event test is one `ArcComponentShiftCorr`
instance).  Assembled at the heads: the composite run's cup/cap event counts at a reindexed
probe decompose into the fresh run's count plus the head's own event term — fully fresh-side
for the cup head (the event rides the persistent event-to-leg link onto the left-leg query)
and for the cap head's cup leg (degenerate legs collapse the join); the cap head's own cap
event term stays composite-spelled at the consumed wire, awaiting the strand-closure
invariant that will evaluate it to zero.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic scan-transport kit

The append distribution `countEventsInRoot_append` already ships in `ArcSwapRenameable`;
this kit adds the singleton computation and the correspondence-map transport. -/

/-- The event scan on a singleton is its one membership test. -/
theorem countEventsInRoot_singleton (links : List (Nat × Nat)) (rootHere eventNode : Nat) :
    countEventsInRoot links rootHere [eventNode]
      = if unionFindRootOf links eventNode == rootHere then 1 else 0 := rfl

/-- ★ **The scan maps through a component correspondence**: scanning the `sigma`-image event
list against a `sigma`-image anchor over the shifted links equals scanning the base list
against the base anchor over the leg-joined base links — every per-event membership test is
one instance of the correspondence. -/
theorem countEventsInRoot_mapCorr (sigma : Nat → Nat) (legLeft legRight : Nat)
    (baseLinks shiftedLinks : List (Nat × Nat))
    (corr : ArcComponentShiftCorr sigma legLeft legRight baseLinks shiftedLinks)
    (anchorProbe : Nat) :
    (events : List Nat) →
    countEventsInRoot shiftedLinks (unionFindRootOf shiftedLinks (sigma anchorProbe))
        (events.map sigma)
      = countEventsInRoot (unionFindJoin baseLinks legLeft legRight)
          (unionFindRootOf (unionFindJoin baseLinks legLeft legRight) anchorProbe) events
  | [] => rfl
  | headEvent :: restEvents => by
      have testCorr : (unionFindRootOf shiftedLinks (sigma headEvent)
            == unionFindRootOf shiftedLinks (sigma anchorProbe))
          = (unionFindRootOf (unionFindJoin baseLinks legLeft legRight) headEvent
            == unionFindRootOf (unionFindJoin baseLinks legLeft legRight) anchorProbe) :=
        corr headEvent anchorProbe
      show (if unionFindRootOf shiftedLinks (sigma headEvent)
            == unionFindRootOf shiftedLinks (sigma anchorProbe) then 1 else 0)
          + countEventsInRoot shiftedLinks
              (unionFindRootOf shiftedLinks (sigma anchorProbe)) (restEvents.map sigma)
        = (if unionFindRootOf (unionFindJoin baseLinks legLeft legRight) headEvent
            == unionFindRootOf (unionFindJoin baseLinks legLeft legRight) anchorProbe
            then 1 else 0)
          + countEventsInRoot (unionFindJoin baseLinks legLeft legRight)
              (unionFindRootOf (unionFindJoin baseLinks legLeft legRight) anchorProbe)
              restEvents
      rw [testCorr, countEventsInRoot_mapCorr sigma legLeft legRight baseLinks shiftedLinks
        corr anchorProbe restEvents]

/-! ## The assembled counts at the cup head -/

/-- ★ **The composite cup-event count at a reindexed probe, under a cup head**: the fresh
run's leg-joined count plus the head's own cup event, which sits on the window leg's
strand. -/
theorem arcCupHeadFolded_cupEventCountAtImage
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have eventsShape := (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition
    atoms).cupEventsMap
  have foldedCorr := arcComponentShiftCorr_cupHeadFolded bottomCount windowPosition
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
      (arcCupHeadFolded_eventLegLinked bottomCount windowPosition atoms)
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
theorem arcCupHeadFolded_capEventCountAtImage
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have eventsShape := (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition
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
      (arcComponentShiftCorr_cupHeadFolded bottomCount windowPosition windowFits atoms
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
theorem arcCapHeadFolded_cupEventCountAtImage
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have eventsShape := (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition
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
      (arcComponentShiftCorr_capHeadFolded bottomCount windowPosition tailBoundary
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
theorem arcCapHeadFolded_capEventCountAtImage
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have eventsShape := (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition
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
      (arcCapHeadFolded_eventWireLinked bottomCount windowPosition windowFits atoms)
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
      (arcComponentShiftCorr_capHeadFolded bottomCount windowPosition tailBoundary
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

/-- **Honesty marker — the per-strand event-count transport through the head correspondence
(peel campaign H, extract-correspondence rung 2).**  Generic kit (`countEventsInRoot` over
append / singleton / `sigma`-mapped lists through any `ArcComponentShiftCorr`) plus the four
assembled composite-count decompositions at reindexed probes: cup head cup/cap counts (fully
fresh-side — the head's cup event resolves onto the leg-joined window query), cap head
cup count (fully fresh-side, degenerate legs collapsed), cap head cap count (the head's own
event term stays composite-spelled at the consumed wire — evaluating it to zero NEEDS the
strand-closure invariant, NOT claimed here).  Also NOT claimed: the boundary-node read maps
(composite ports as `sigma`-images of fresh ports), the diagram/partner leg, and the
head-cancellation assembly.  `= true`. -/
def fxMode_hasArcEventCountTransport : Bool := true

end FX1Poly.Polygraph

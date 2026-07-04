import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadReindex

/-! # ArcHeadFoldedSim — the positional correspondence at the folded end states

The positional half of the head-cancellation correspondence, END TO END: the cup-head and
cap-head seed pairs threaded through the unconditional positional-shift fold, plus the COUNT
LEGS the extract correspondence consumes.  At the folded end states the composite run's event
lists are the `sigma`-mapped fresh lists over the head's own suffix, so the extract totals
relate by the head's contribution alone: the composite run counts exactly ONE more cup event
than the fresh tail run under a cup head (exactly one more cap event under a cap head), the
other total agrees, and the open-wire boundary lengths agree.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private list plumbing (per-file copy, following the codebase pattern) -/

private theorem listLengthAppend : (leftList rightList : List Nat) →
    (leftList ++ rightList).length = leftList.length + rightList.length
  | [], rightList => (Nat.zero_add rightList.length).symm
  | _ :: restItems, rightList => by
      show (restItems ++ rightList).length + 1 = restItems.length + 1 + rightList.length
      rw [listLengthAppend restItems rightList]
      exact Nat.add_right_comm restItems.length rightList.length 1

/-! ## The event-count legs of any positional shift simulation -/

/-- The shifted run's cup-event total is the base total plus the head's own cup events. -/
theorem arcPositionalShiftSim_cupEventsLength (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    shiftedState.cupEventNodes.length
      = baseState.cupEventNodes.length + headCupEvents.length := by
  rw [sim.cupEventsMap,
    listLengthAppend (baseState.cupEventNodes.map sigma) headCupEvents,
    mapLength sigma baseState.cupEventNodes]

/-- The shifted run's cap-event total is the base total plus the head's own cap events. -/
theorem arcPositionalShiftSim_capEventsLength (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (baseState shiftedState : ArcWireState)
    (sim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState) :
    shiftedState.capEventNodes.length
      = baseState.capEventNodes.length + headCapEvents.length := by
  rw [sim.capEventsMap,
    listLengthAppend (baseState.capEventNodes.map sigma) headCapEvents,
    mapLength sigma baseState.capEventNodes]

/-! ## The folded simulations at the two head shapes -/

/-- ★ **The cup-head positional simulation at the folded end states**: running any tail spine
from the composite seed (peeled cup fired) and the fresh tail seed keeps the wires, allocator,
and event lists corresponding under the cup-head reindexing — unconditionally. -/
theorem arcPositionalShiftSim_cupHeadFolded
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      1 (bottomCount + 2) [bottomCount + 2] []
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms) :=
  arcPositionalShiftSim_processArcSpine
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (arcHeadReindex_cupSeedShifts bottomCount windowPosition)
    atoms
    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (arcPositionalShiftSim_cupHeadSeed bottomCount windowPosition)

/-- ★ **The cap-head positional simulation at the folded end states**: running any tail spine
from the composite seed (peeled cap fired) and the fresh tail seed keeps the wires, allocator,
and event lists corresponding under the cap-head reindexing. -/
theorem arcPositionalShiftSim_capHeadFolded
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      3 tailBoundary [] [bottomCount]
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms) :=
  arcPositionalShiftSim_processArcSpine
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)
    atoms
    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (arcPositionalShiftSim_capHeadSeed bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)

/-! ## The count legs at the two head shapes -/

/-- Under a cup head the composite run counts exactly ONE more cup event than the fresh run. -/
theorem arcCupHeadFolded_cupEventsLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).cupEventNodes.length + 1 :=
  arcPositionalShiftSim_cupEventsLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cup head the cap-event totals of the two runs agree. -/
theorem arcCupHeadFolded_capEventsLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).capEventNodes.length :=
  arcPositionalShiftSim_capEventsLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cup head the two runs keep equal boundary widths. -/
theorem arcCupHeadFolded_openWiresLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
  arcPositionalShiftSim_openWiresLength
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] []
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms)

/-- Under a cap head the composite run counts exactly ONE more cap event than the fresh run. -/
theorem arcCapHeadFolded_capEventsLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).capEventNodes.length + 1 :=
  arcPositionalShiftSim_capEventsLength
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-- Under a cap head the cup-event totals of the two runs agree. -/
theorem arcCapHeadFolded_cupEventsLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).cupEventNodes.length :=
  arcPositionalShiftSim_cupEventsLength
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount]
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-- Under a cap head the two runs keep equal boundary widths. -/
theorem arcCapHeadFolded_openWiresLength
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (processArcSpine
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
    (arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms)

/-! ## Honesty marker -/

/-- **Honesty marker — the POSITIONAL correspondence at the folded end states with its COUNT
legs (peel campaign H, extract-correspondence rung 1).**  The cup-head and cap-head seed
simulations threaded through the unconditional positional-shift fold, plus the count legs the
extract correspondence consumes: composite cup total = fresh total + 1 under a cup head
(mirror for the cap), the other total agrees, boundary widths agree.  What this marker does
NOT claim: the diagram/matching leg and the per-port internal-count legs of the extract
correspondence (they ride the component correspondence), the reindex injectivity on realized
structures, and the head-cancellation assembly.  `= true`. -/
def fxMode_hasArcHeadFoldedSim : Bool := true

end FX1Poly.Polygraph

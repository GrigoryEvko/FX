import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupScanTestCorr
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # ArcCupScanAssembly — the composite partner scan rides the joined-fresh scan

The cup-head partner-scan assembly (peel campaign H, cup rung 2b).  Two pieces:

  * the map-congruence assembly: the composite `partnerIndexOf`'s whole scan over the
    composite candidate range IS (through the two-zone shift) the JOINED-fresh scan over
    the shift-image candidates — `findPartnerScan_mapCongr` fed the per-candidate test
    correspondence (cup rung 2a), with the candidate range converted through the
    equal-top-lengths fact;
  * the puncture shape: the shift-image of a window-prefixed range splits as the
    below-window prefix plus the past-window tail two higher — making explicit that the
    two window legs `windowPosition`, `windowPosition + 1` are MISSING from the image.
    The punctured-scan-versus-full-scan analysis (the leg rewiring) is the next rung.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private pointwise map plumbing (structural recursion — no funext) -/

/-- A map that fixes every member is the identity on the list. -/
private theorem listMapIdentityOnMembers (mapped : Nat → Nat) :
    (wires : List Nat) → (∀ wire, wire ∈ wires → mapped wire = wire) →
    wires.map mapped = wires
  | [], _ => rfl
  | headWire :: rest, pointwise => by
      show mapped headWire :: rest.map mapped = headWire :: rest
      rw [pointwise headWire (List.Mem.head rest),
        listMapIdentityOnMembers mapped rest
          (fun laterWire laterMem => pointwise laterWire (List.Mem.tail headWire laterMem))]

/-- Two stacked maps whose composite agrees pointwise with a fused map ARE the fused
map on the list. -/
private theorem listMapComposePointwise (innerMap outerMap fusedMap : Nat → Nat) :
    (offsets : List Nat) →
    (∀ offset, offset ∈ offsets → outerMap (innerMap offset) = fusedMap offset) →
    (offsets.map innerMap).map outerMap = offsets.map fusedMap
  | [], _ => rfl
  | headOffset :: rest, pointwise => by
      show outerMap (innerMap headOffset) :: (rest.map innerMap).map outerMap
        = fusedMap headOffset :: rest.map fusedMap
      rw [pointwise headOffset (List.Mem.head rest),
        listMapComposePointwise innerMap outerMap fusedMap rest
          (fun laterOffset laterMem =>
            pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-! ## The puncture shape of the shift-image candidate range -/

/-- **The shift-image of a window-prefixed range splits at the window**: below-window
candidates are fixed, past-window candidates land two higher — and the two window legs
`windowPosition`, `windowPosition + 1` are MISSING from the image.  The explicit shape the
punctured-scan analysis consumes. -/
theorem rangeMapShift_splitsAtWindow (windowPosition tailCount : Nat) :
    (List.range (windowPosition + tailCount)).map (freshShiftAbove windowPosition 2)
      = List.range windowPosition
          ++ (List.range tailCount).map (fun offset => windowPosition + 2 + offset) := by
  rw [rangeSplit windowPosition tailCount,
    mapAppend (freshShiftAbove windowPosition 2) (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + offset)),
    listMapIdentityOnMembers (freshShiftAbove windowPosition 2) (List.range windowPosition)
      (fun wire wireMem =>
        freshShiftAbove_ofNotLe windowPosition 2 wire
          (fun windowLe => Nat.lt_irrefl windowPosition
            (Nat.lt_of_le_of_lt windowLe (mem_range_imp_lt wireMem)))),
    listMapComposePointwise (fun offset => windowPosition + offset)
      (freshShiftAbove windowPosition 2) (fun offset => windowPosition + 2 + offset)
      (List.range tailCount)
      (fun offset _ =>
        (freshShiftAbove_ofLe windowPosition 2 (windowPosition + offset)
          (Nat.le_add_right windowPosition offset)).trans
          (Nat.add_right_comm windowPosition offset 2))]

/-! ## The map-congruence assembly -/

/-- ★ **The composite partner index rides the joined-fresh scan over the shift-image
candidates**: the cup composite's `partnerIndexOf` — the whole exclude-and-root scan over
the composite candidate range — equals (through the two-zone shift) the JOINED-fresh scan
over the shift-image candidate list, by `findPartnerScan_mapCongr` fed the per-candidate
test correspondence, with the composite range converted through the equal-top-lengths
fact.  The shift-image list is the fresh range MINUS the two window legs
(`rangeMapShift_splitsAtWindow`) — relating this punctured scan to the PLAIN fresh partner
structure is the leg rewiring, the next rung. -/
theorem arcCupHeadFolded_partnerScanCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (compositeExclude : Nat)
    (excludeInRange : compositeExclude
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) :
    findPartnerScan
        (unionFindJoin
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          windowPosition (windowPosition + 1))
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (unionFindRootOf
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeExclude)))
        (freshShiftAbove windowPosition 2 compositeExclude)
        ((List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)).map (freshShiftAbove windowPosition 2))
      = freshShiftAbove windowPosition 2
          (partnerIndexOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            (bottomCount
              + (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires.length)
            compositeExclude) := by
  have mappedScan := findPartnerScan_mapCongr
    (unionFindJoin
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      windowPosition (windowPosition + 1))
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    (List.range (bottomCount + 2)
      ++ (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires)
    (List.range bottomCount
      ++ (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires)
    (unionFindRootOf
      (unionFindJoin
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        windowPosition (windowPosition + 1))
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude)))
    (unionFindRootOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeExclude))
    compositeExclude
    (freshShiftAbove windowPosition 2)
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length))
    (arcCupHeadFolded_scanTestCorr bottomCount windowPosition windowFits atoms chained
      compositeExclude excludeInRange)
  have lengthsEqual : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    (congrArg List.length
        (arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms).openMap).trans
      (mapLength
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
  have partnerAsScan : partnerIndexOf
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
            windowPosition) atoms).openWires.length)
      compositeExclude
    = findPartnerScan
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (unionFindRootOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            compositeExclude))
        compositeExclude
        (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)) := by
    show findPartnerScan
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (unionFindRootOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            compositeExclude))
        compositeExclude
        (List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                [] []) windowPosition) atoms).openWires.length))
      = findPartnerScan
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (unionFindRootOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                    [] []) windowPosition) atoms).openWires)
              compositeExclude))
          compositeExclude
          (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length))
    rw [lengthsEqual]
  exact mappedScan.trans
    (congrArg (freshShiftAbove windowPosition 2) partnerAsScan.symm)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head partner-scan assembly (peel campaign H, cup
rung 2b).**  `rangeMapShift_splitsAtWindow`: the shift-image of a window-prefixed range is
the below-window prefix plus the past-window tail two higher — the two window legs are
MISSING from the image.  `arcCupHeadFolded_partnerScanCorr`: the composite
`partnerIndexOf` equals (through the two-zone shift) the JOINED-fresh scan over exactly
that punctured candidate list, by `findPartnerScan_mapCongr` over the per-candidate test
correspondence.  What this marker does NOT claim: the punctured-versus-full scan analysis
over the joined links (the two missing leg candidates CAN test true inside the fused
component — the leg rewiring), the relation to the PLAIN fresh partner list, the window
entries, and the assembled cup partner list.  `= true`. -/
def fxMode_hasArcCupScanAssembly : Bool := true

end FX1Poly.Polygraph

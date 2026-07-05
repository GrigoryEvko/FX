import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCupBoundaryReads — the composite boundary reads at the cup head

The CUP twin of the boundary-read rung (peel campaign H, cup rung 1).  At the cup head the
FRESH tail run starts two ports WIDER (`range (bottomCount + 2)`, the inserted legs live at
the window), so the index shift runs the other way round from the cap: the composite
boundary (bottom `range bottomCount`, top the folded composite wires) reads the fresh
boundary through the cup-head reindexing with indices below the window read at the SAME
place and indices at or past the window read TWO HIGHER on the FRESH side — the fresh
run's two extra ports are exactly the cup's inserted legs.  This brick ships the two
generic zone correspondences (over any `sigma`-mapped top list), their folded-state
corollaries via the positional sim's `openMap`, and the total-port count fact (the fresh
run has exactly two more boundary ports).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## The generic zone correspondences (any `sigma`-mapped top list) -/

/-- **Zone I — below the window the composite boundary reads the reindexed fresh read at
the SAME index**: both sides read their untouched range prefixes, and the cup-head
reindexing is the identity there. -/
theorem arcCupBoundaryRead_belowWindow
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (freshTopWires : List Nat) (probeIndex : Nat)
    (belowWindow : probeIndex < windowPosition) :
    natListGetAt
        (List.range bottomCount ++ freshTopWires.map
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1))
        probeIndex
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1
        (natListGetAt (List.range (bottomCount + 2) ++ freshTopWires) probeIndex) := by
  have probeLtBoundary : probeIndex < bottomCount :=
    Nat.lt_of_lt_of_le belowWindow windowFits
  have probeLtTail : probeIndex < bottomCount + 2 :=
    Nat.lt_of_lt_of_le probeLtBoundary (Nat.le_add_right bottomCount 2)
  have leftRead : natListGetAt
      (List.range bottomCount ++ freshTopWires.map
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1))
      probeIndex
    = probeIndex := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (freshTopWires.map
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1))
      probeIndex (by rw [rangeLength]; exact probeLtBoundary)]
    exact rangeGetAt_below bottomCount probeIndex probeLtBoundary
  have rightRead : natListGetAt (List.range (bottomCount + 2) ++ freshTopWires) probeIndex
      = probeIndex := by
    rw [natListGetAt_append_inside (List.range (bottomCount + 2)) freshTopWires probeIndex
      (by rw [rangeLength]; exact probeLtTail)]
    exact rangeGetAt_below (bottomCount + 2) probeIndex probeLtTail
  rw [leftRead, rightRead]
  exact (arcCupHeadReindex_belowWindow bottomCount windowPosition probeIndex windowFits
    belowWindow).symm

/-- **Zones II and III — at or past the window the composite boundary reads the reindexed
fresh read TWO INDICES higher on the FRESH side**: the composite's bottom suffix reads the
fresh run's displaced range suffix through the down-shift, and top ports read the
`sigma`-mapped fresh wires at the same top offset. -/
theorem arcCupBoundaryRead_atOrPastWindow
    (bottomCount windowPosition : Nat)
    (freshTopWires : List Nat) (probeIndex : Nat)
    (atWindow : windowPosition ≤ probeIndex)
    (probeInRange : probeIndex < bottomCount + freshTopWires.length) :
    natListGetAt
        (List.range bottomCount ++ freshTopWires.map
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1))
        probeIndex
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1
        (natListGetAt (List.range (bottomCount + 2) ++ freshTopWires) (probeIndex + 2)) := by
  cases Nat.lt_or_ge probeIndex bottomCount with
  | inl belowBottom =>
      have leftRead : natListGetAt
          (List.range bottomCount ++ freshTopWires.map
            (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1))
          probeIndex
        = probeIndex := by
        rw [natListGetAt_append_inside (List.range bottomCount)
          (freshTopWires.map
            (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1))
          probeIndex (by rw [rangeLength]; exact belowBottom)]
        exact rangeGetAt_below bottomCount probeIndex belowBottom
      have shiftedLtTail : probeIndex + 2 < bottomCount + 2 :=
        Nat.succ_lt_succ (Nat.succ_lt_succ belowBottom)
      have rightRead : natListGetAt (List.range (bottomCount + 2) ++ freshTopWires)
          (probeIndex + 2)
        = probeIndex + 2 := by
        rw [natListGetAt_append_inside (List.range (bottomCount + 2)) freshTopWires
          (probeIndex + 2) (by rw [rangeLength]; exact shiftedLtTail)]
        exact rangeGetAt_below (bottomCount + 2) (probeIndex + 2) shiftedLtTail
      rw [leftRead, rightRead]
      obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atWindow
      have pastBound : windowPosition + pastOffset < bottomCount := by
        rw [offsetSpec]
        exact belowBottom
      rw [← offsetSpec]
      exact (arcCupHeadReindex_pastWindow bottomCount windowPosition pastOffset
        pastBound).symm
  | inr atBottom =>
      obtain ⟨topOffset, topOffsetSpec⟩ := Nat.le.dest atBottom
      have topOffsetInRange : topOffset < freshTopWires.length := by
        rw [← topOffsetSpec] at probeInRange
        exact Nat.lt_of_add_lt_add_left probeInRange
      have leftRead : natListGetAt
          (List.range bottomCount ++ freshTopWires.map
            (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1))
          (bottomCount + topOffset)
        = natListGetAt
            (freshTopWires.map
              (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
                [bottomCount, bottomCount + 1]) 1))
            topOffset := by
        have baseRead := natListGetAt_append_pastBlock (List.range bottomCount)
          (freshTopWires.map
            (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1))
          topOffset
        rw [rangeLength bottomCount, Nat.add_comm topOffset bottomCount] at baseRead
        exact baseRead
      have indexEq : topOffset + (bottomCount + 2) = bottomCount + topOffset + 2 := by
        rw [← Nat.add_assoc topOffset bottomCount 2, Nat.add_comm topOffset bottomCount]
      have rightRead : natListGetAt (List.range (bottomCount + 2) ++ freshTopWires)
          (bottomCount + topOffset + 2)
        = natListGetAt freshTopWires topOffset := by
        have baseRead := natListGetAt_append_pastBlock (List.range (bottomCount + 2))
          freshTopWires topOffset
        rw [rangeLength (bottomCount + 2), indexEq] at baseRead
        exact baseRead
      rw [← topOffsetSpec, leftRead, rightRead]
      exact natListGetAt_map_inRange
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1)
        freshTopWires topOffset topOffsetInRange

/-! ## The folded-state corollaries (the shapes the partner leg consumes) -/

/-- **Zone I at the folded states**: below the window, the composite end state's boundary
reads the reindexed fresh end state's boundary at the same index. -/
theorem arcCupHeadFolded_boundaryRead_belowWindow
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (probeIndex : Nat) (belowWindow : probeIndex < windowPosition) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        probeIndex
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          probeIndex) := by
  rw [(arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms).openMap]
  exact arcCupBoundaryRead_belowWindow bottomCount windowPosition windowFits
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      atoms).openWires
    probeIndex belowWindow

/-- **Zones II and III at the folded states**: at or past the window, the composite end
state's boundary reads the reindexed fresh end state's boundary two indices higher on the
fresh side. -/
theorem arcCupHeadFolded_boundaryRead_atOrPastWindow
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (probeIndex : Nat) (atWindow : windowPosition ≤ probeIndex)
    (probeInRange : probeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        probeIndex
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (probeIndex + 2)) := by
  rw [(arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms).openMap]
  exact arcCupBoundaryRead_atOrPastWindow bottomCount windowPosition
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      atoms).openWires
    probeIndex atWindow probeInRange

/-- **The fresh run has exactly two more boundary ports than the composite** — the cup's
inserted legs; the top counts agree since the composite top is the `sigma`-mapped fresh
top. -/
theorem arcCupHeadFolded_totalPorts
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length
      = bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length
        + 2 := by
  rw [(arcPositionalShiftSim_cupHeadFolded bottomCount windowPosition atoms).openMap,
    mapLength
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires]
  exact Nat.add_right_comm bottomCount 2
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      atoms).openWires.length

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head composite boundary reads (peel campaign H, cup
rung 1).**  The two generic zone correspondences (below the window: same index, identity
values; at or past: two indices higher on the FRESH side, through the down-shifted range
suffix and the `sigma`-mapped top), their folded-state corollaries via the positional
sim's `openMap`, and the fresh-side two-extra-ports count fact.  What this marker does NOT
claim: the cup partner-scan congruence, the window legs partnering each other in the fresh
extract, the cup loops/diagram/count assembly rungs, or the assembled cup `extractArc`
transport — the remaining cup rungs.  `= true`. -/
def fxMode_hasArcCupBoundaryReads : Bool := true

end FX1Poly.Polygraph

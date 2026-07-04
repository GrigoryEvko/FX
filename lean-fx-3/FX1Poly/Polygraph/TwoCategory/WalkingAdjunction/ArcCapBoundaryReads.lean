import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexValues
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCapBoundaryReads — the composite boundary reads are reindexed fresh reads

The extract-correspondence DIAGRAM leg opens (peel campaign H, rung E-3, part 1).  The
extracted `DiagramType`'s partner function scans BOUNDARY NODES — bottom ports are range
values, top ports are the end state's open wires.  At the cap head, the composite boundary
(bottom `range bottomCount`, top the folded composite wires) reads the fresh boundary
(bottom `range tailBoundary`, top the fresh wires) through the cap-head reindexing, under
the two-zone boundary INDEX shift: indices below the window are read as themselves, and
indices at or past the window are read two higher — the composite's two extra ports (the
window pair) are exactly the consumed cap legs.  This brick ships the two zone
correspondences generically over any `sigma`-mapped top list, their folded-state
corollaries (via the folded positional sim's `openMap`), and the total-port count fact.

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
the SAME index**: both sides read the untouched range prefix, and the reindexing is the
identity there. -/
theorem arcCapBoundaryRead_belowWindow
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (freshTopWires : List Nat) (probeIndex : Nat)
    (belowWindow : probeIndex < windowPosition) :
    natListGetAt
        (List.range bottomCount ++ freshTopWires.map
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
        probeIndex
      = arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt (List.range tailBoundary ++ freshTopWires) probeIndex) := by
  have windowLeTail : windowPosition ≤ tailBoundary :=
    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (Nat.le_trans windowFits (Nat.le_of_eq tailBoundaryFits.symm)))
  have probeLtBoundary : probeIndex < bottomCount :=
    Nat.lt_of_lt_of_le belowWindow
      (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits)
  have probeLtTail : probeIndex < tailBoundary :=
    Nat.lt_of_lt_of_le belowWindow windowLeTail
  have leftRead : natListGetAt
      (List.range bottomCount ++ freshTopWires.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      probeIndex
    = probeIndex := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (freshTopWires.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      probeIndex (by rw [rangeLength]; exact probeLtBoundary)]
    exact rangeGetAt_below bottomCount probeIndex probeLtBoundary
  have rightRead : natListGetAt (List.range tailBoundary ++ freshTopWires) probeIndex
      = probeIndex := by
    rw [natListGetAt_append_inside (List.range tailBoundary) freshTopWires probeIndex
      (by rw [rangeLength]; exact probeLtTail)]
    exact rangeGetAt_below tailBoundary probeIndex probeLtTail
  rw [leftRead, rightRead]
  exact (arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary probeIndex
    windowFits tailBoundaryFits belowWindow).symm

/-- **Zones II and III — at or past the window the composite boundary reads the reindexed
fresh read TWO INDICES higher**: displaced bottom ports read the shifted range suffix, and
top ports read the `sigma`-mapped fresh wires at the same top offset. -/
theorem arcCapBoundaryRead_atOrPastWindow
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (freshTopWires : List Nat) (probeIndex : Nat)
    (atWindow : windowPosition ≤ probeIndex)
    (probeInRange : probeIndex < tailBoundary + freshTopWires.length) :
    natListGetAt
        (List.range bottomCount ++ freshTopWires.map
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
        (probeIndex + 2)
      = arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt (List.range tailBoundary ++ freshTopWires) probeIndex) := by
  cases Nat.lt_or_ge probeIndex tailBoundary with
  | inl belowTail =>
      have shiftedLtBoundary : probeIndex + 2 < bottomCount :=
        Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ belowTail))
          (Nat.le_of_eq tailBoundaryFits)
      have leftRead : natListGetAt
          (List.range bottomCount ++ freshTopWires.map
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
              3))
          (probeIndex + 2)
        = probeIndex + 2 := by
        rw [natListGetAt_append_inside (List.range bottomCount)
          (freshTopWires.map
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
              3))
          (probeIndex + 2) (by rw [rangeLength]; exact shiftedLtBoundary)]
        exact rangeGetAt_below bottomCount (probeIndex + 2) shiftedLtBoundary
      have rightRead : natListGetAt (List.range tailBoundary ++ freshTopWires) probeIndex
          = probeIndex := by
        rw [natListGetAt_append_inside (List.range tailBoundary) freshTopWires probeIndex
          (by rw [rangeLength]; exact belowTail)]
        exact rangeGetAt_below tailBoundary probeIndex belowTail
      rw [leftRead, rightRead]
      obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atWindow
      have pastBound : windowPosition + pastOffset < tailBoundary := by
        rw [offsetSpec]
        exact belowTail
      rw [← offsetSpec]
      exact (arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary
        pastOffset windowFits tailBoundaryFits pastBound).symm
  | inr atTail =>
      obtain ⟨topOffset, topOffsetSpec⟩ := Nat.le.dest atTail
      have topOffsetInRange : topOffset < freshTopWires.length := by
        rw [← topOffsetSpec] at probeInRange
        exact Nat.lt_of_add_lt_add_left probeInRange
      have indexEq : topOffset + bottomCount = tailBoundary + topOffset + 2 := by
        rw [← tailBoundaryFits, ← Nat.add_assoc topOffset tailBoundary 2,
          Nat.add_comm topOffset tailBoundary]
      have leftRead : natListGetAt
          (List.range bottomCount ++ freshTopWires.map
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
              3))
          (tailBoundary + topOffset + 2)
        = natListGetAt
            (freshTopWires.map
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
                3))
            topOffset := by
        have baseRead := natListGetAt_append_pastBlock (List.range bottomCount)
          (freshTopWires.map
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition)
              3))
          topOffset
        rw [rangeLength bottomCount, indexEq] at baseRead
        exact baseRead
      have rightRead : natListGetAt (List.range tailBoundary ++ freshTopWires)
          (tailBoundary + topOffset)
        = natListGetAt freshTopWires topOffset := by
        have baseRead := natListGetAt_append_pastBlock (List.range tailBoundary)
          freshTopWires topOffset
        rw [rangeLength tailBoundary, Nat.add_comm topOffset tailBoundary] at baseRead
        exact baseRead
      rw [← topOffsetSpec, leftRead, rightRead]
      exact natListGetAt_map_inRange
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
        freshTopWires topOffset topOffsetInRange

/-! ## The folded-state corollaries (the shapes the partner leg consumes) -/

/-- **Zone I at the folded states**: below the window, the composite end state's boundary
reads the reindexed fresh end state's boundary at the same index. -/
theorem arcCapHeadFolded_boundaryRead_belowWindow
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  rw [(arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms).openMap]
  exact arcCapBoundaryRead_belowWindow bottomCount windowPosition tailBoundary windowFits
    tailBoundaryFits
    (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).openWires
    probeIndex belowWindow

/-- **Zones II and III at the folded states**: at or past the window, the composite end
state's boundary reads the reindexed fresh end state's boundary two indices higher. -/
theorem arcCapHeadFolded_boundaryRead_atOrPastWindow
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  rw [(arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms).openMap]
  exact arcCapBoundaryRead_atOrPastWindow bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits
    (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).openWires
    probeIndex atWindow probeInRange

/-- **The composite has exactly two more boundary ports than the fresh run** — the consumed
window pair; the top counts agree since the composite top is the `sigma`-mapped fresh top. -/
theorem arcCapHeadFolded_totalPorts
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length
      = tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length
        + 2 := by
  rw [(arcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
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

/-- **Honesty marker — the cap-head composite boundary reads (peel campaign H, rung E-3,
part 1).**  The two generic zone correspondences (below the window: same index, identity
values; at or past: two indices higher, through the displaced range suffix and the
`sigma`-mapped top), their folded-state corollaries via the positional sim's `openMap`, and
the two-extra-ports count fact.  What this marker does NOT claim: the partner-scan
congruence (the composite scan agreeing with the shifted fresh scan, with the closed
window-pair candidates failing every off-strand root test), the window pair partnering
EACH OTHER in the composite extract, and the assembled diagram/partner leg.  `= true`. -/
def fxMode_hasArcCapBoundaryReads : Bool := true

end FX1Poly.Polygraph

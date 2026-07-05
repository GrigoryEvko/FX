import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapScanAssembly

/-! # ArcCapWindowPartners — the consumed window pair partner each other

The cap-head partner correspondence (peel campaign H, rung E-3, part 5).  The composite
extract's partner list carries two entries the fresh extract never sees: the window
positions `windowPosition` and `windowPosition + 1`, whose boundary reads are the consumed
pair's own node ids.  This brick shows they partner EACH OTHER: the left window index's
partner scan returns the right window index and vice versa.  First-hit discipline drives
both: every below-window candidate reads a reindexed fresh node, and the strand-closure
anchor misses every reindexed probe (transferring across the persistent consumed-pair link
for the right exclude), so the below-window front fails through; the window's own index is
excluded by the bang-inequality; and the partner wire passes — the consumed pair is linked
at the seed and stays linked through the whole fold.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

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

private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

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

private theorem andFalse_eq_false : (value : Bool) → (value && false) = false
  | true => rfl
  | false => rfl

/-- A failing `Nat` equality test fails in the flipped order too (hand-rolled beq
symmetry at `false`; `==` on `Nat` is `decide (· = ·)`). -/
private theorem natBeqSymmFalse {leftValue rightValue : Nat}
    (missEq : (leftValue == rightValue) = false) : (rightValue == leftValue) = false :=
  decide_eq_false (fun valuesEqual => of_decide_eq_false missEq valuesEqual.symm)

/-- Hand-rolled append associativity (the core lemma leaks `propext`). -/
private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-! ## The left window index partners the right -/

/-- ★ **The left window candidate's partner is the right window candidate**: at the
cap-head folded end state, the partner scan at exclude `windowPosition` fails through every
below-window candidate (each reads a reindexed fresh node, and the strand-closure anchor
misses every reindexed probe), skips its own excluded index, and first-hits
`windowPosition + 1` — the consumed pair is linked at the seed and stays linked through the
whole fold. -/
theorem arcCapHeadFolded_windowLeftPartner
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)
        windowPosition
      = windowPosition + 1 := by
  have leftBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have boundaryReadWindow : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      windowPosition = windowPosition := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires windowPosition
      (by rw [rangeLength]; exact leftBelowBoundary)]
    exact rangeGetAt_below bottomCount windowPosition leftBelowBoundary
  have boundaryReadRight : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires (windowPosition + 1)
      (by rw [rangeLength]; exact windowFits)]
    exact rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have paddedLe : windowPosition + 2 ≤ tailBoundary + 2 := by
      rw [tailBoundaryFits]
      exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ paddedLe)
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((arcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have belowFails : ∀ candidate, candidate ∈ List.range windowPosition →
      (candidate != windowPosition
          && unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (natListGetAt
                (List.range bottomCount
                  ++ (processArcSpine
                    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      windowPosition) atoms).openWires)
                candidate)
            == unionFindRootOf
                (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).links
                windowPosition)
        = false := by
    intro candidate candidateMem
    have candidateBelow : candidate < windowPosition :=
      mem_range_imp_lt candidateMem
    have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
      freshShiftAbove_ofNotLe windowPosition 2 candidate
        (fun windowLe =>
          Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
    have candidateInFreshRange : candidate
        < tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length :=
      Nat.lt_of_lt_of_le candidateBelow windowLeTotal
    have readCandidate := arcCapHeadFolded_boundaryRead_shifted bottomCount windowPosition
      tailBoundary windowFits tailBoundaryFits atoms candidate candidateInFreshRange
    rw [shiftFixed] at readCandidate
    have rootsMissBeq : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links windowPosition
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                (natListGetAt
                  (List.range tailBoundary
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                      atoms).openWires)
                  candidate))) = false :=
      arcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          candidate)
    have rootsMissSym : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          (natListGetAt
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            candidate))
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              windowPosition) = false := natBeqSymmFalse rootsMissBeq
    rw [readCandidate, rootsMissSym]
    exact andFalse_eq_false (candidate != windowPosition)
  have belowScanExcludes : findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition (List.range windowPosition) = windowPosition :=
    findPartnerScan_eqExclude_ofAllFail
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition (List.range windowPosition) belowFails
  have selfTestFails : (windowPosition != windowPosition
      && unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            windowPosition)
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            windowPosition) = false := by
    have windowBeqSelf : (windowPosition == windowPosition) = true := decide_eq_true rfl
    show ((!(windowPosition == windowPosition))
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              windowPosition)
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              windowPosition) = false
    rw [windowBeqSelf]
    exact rfl
  have pairRootsBeq : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links windowPosition
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (windowPosition + 1)) = true :=
    arcCapHeadFolded_consumedPairLinked bottomCount windowPosition windowFits atoms
  have pairRootsSymBeq : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links (windowPosition + 1)
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            windowPosition) = true :=
    decide_eq_true (of_decide_eq_true pairRootsBeq).symm
  have rightTestPasses : (windowPosition + 1 != windowPosition
      && unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            (windowPosition + 1))
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            windowPosition) = true := by
    have rightBeqLeft : (windowPosition + 1 == windowPosition) = false :=
      decide_eq_false (fun succEqSelf =>
        Nat.lt_irrefl windowPosition
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
            (Nat.le_of_eq succEqSelf)))
    show ((!(windowPosition + 1 == windowPosition))
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (windowPosition + 1))
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              windowPosition) = true
    rw [rightBeqLeft, boundaryReadRight]
    exact pairRootsSymBeq
  show findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (natListGetAt
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          windowPosition))
      windowPosition
      (List.range
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
    = windowPosition + 1
  rw [boundaryReadWindow, compositeCandidatesEq,
    rangeInterleaveAtWindow windowPosition tailCount,
    appendAssoc (List.range windowPosition) [windowPosition, windowPosition + 1]
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    findPartnerScan_append_ofFrontFails
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition (List.range windowPosition)
      ([windowPosition, windowPosition + 1]
        ++ (List.range tailCount).map (fun offset => windowPosition + 2 + offset))
      belowScanExcludes]
  show findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition
      (windowPosition :: (windowPosition + 1)
        :: (List.range tailCount).map (fun offset => windowPosition + 2 + offset))
    = windowPosition + 1
  rw [findPartnerScan_cons_ofTestFails
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition windowPosition
      ((windowPosition + 1)
        :: (List.range tailCount).map (fun offset => windowPosition + 2 + offset))
      selfTestFails,
    findPartnerScan_cons
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      windowPosition (windowPosition + 1)
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    rightTestPasses]
  exact if_pos rfl

/-! ## The right window index partners the left -/

/-- ★ **The right window candidate's partner is the left window candidate** — the mirror:
at exclude `windowPosition + 1` the below-window front fails through (each candidate reads
a reindexed fresh node; the anchor's miss transfers across the persistent consumed-pair
link), and the very first window candidate `windowPosition` passes. -/
theorem arcCapHeadFolded_windowRightPartner
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)
        (windowPosition + 1)
      = windowPosition := by
  have leftBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have boundaryReadWindow : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      windowPosition = windowPosition := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires windowPosition
      (by rw [rangeLength]; exact leftBelowBoundary)]
    exact rangeGetAt_below bottomCount windowPosition leftBelowBoundary
  have boundaryReadRight : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 := by
    rw [natListGetAt_append_inside (List.range bottomCount)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires (windowPosition + 1)
      (by rw [rangeLength]; exact windowFits)]
    exact rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have paddedLe : windowPosition + 2 ≤ tailBoundary + 2 := by
      rw [tailBoundaryFits]
      exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ paddedLe)
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((arcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have pairRootsBeq : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links windowPosition
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (windowPosition + 1)) = true :=
    arcCapHeadFolded_consumedPairLinked bottomCount windowPosition windowFits atoms
  have belowFails : ∀ candidate, candidate ∈ List.range windowPosition →
      (candidate != windowPosition + 1
          && unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (natListGetAt
                (List.range bottomCount
                  ++ (processArcSpine
                    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      windowPosition) atoms).openWires)
                candidate)
            == unionFindRootOf
                (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).links
                (windowPosition + 1))
        = false := by
    intro candidate candidateMem
    have candidateBelow : candidate < windowPosition :=
      mem_range_imp_lt candidateMem
    have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
      freshShiftAbove_ofNotLe windowPosition 2 candidate
        (fun windowLe =>
          Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
    have candidateInFreshRange : candidate
        < tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length :=
      Nat.lt_of_lt_of_le candidateBelow windowLeTotal
    have readCandidate := arcCapHeadFolded_boundaryRead_shifted bottomCount windowPosition
      tailBoundary windowFits tailBoundaryFits atoms candidate candidateInFreshRange
    rw [shiftFixed] at readCandidate
    have rootsMissBeq : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links windowPosition
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                (natListGetAt
                  (List.range tailBoundary
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                      atoms).openWires)
                  candidate))) = false :=
      arcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          candidate)
    have queryTransferBeq : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links windowPosition
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                (natListGetAt
                  (List.range tailBoundary
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                      atoms).openWires)
                  candidate)))
        = (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links (windowPosition + 1)
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                (natListGetAt
                  (List.range tailBoundary
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                      atoms).openWires)
                  candidate))) :=
      isSameComponent_congrOfLinked
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition (windowPosition + 1)
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          (natListGetAt
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            candidate))
        pairRootsBeq
    have rootsMissRightSym : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          (natListGetAt
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            candidate))
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (windowPosition + 1)) = false :=
      natBeqSymmFalse (queryTransferBeq.symm.trans rootsMissBeq)
    rw [readCandidate, rootsMissRightSym]
    exact andFalse_eq_false (candidate != windowPosition + 1)
  have belowScanExcludes : findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1))
      (windowPosition + 1) (List.range windowPosition) = windowPosition + 1 :=
    findPartnerScan_eqExclude_ofAllFail
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1))
      (windowPosition + 1) (List.range windowPosition) belowFails
  have leftTestPasses : (windowPosition != windowPosition + 1
      && unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            windowPosition)
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (windowPosition + 1)) = true := by
    have leftBeqRight : (windowPosition == windowPosition + 1) = false :=
      decide_eq_false (fun selfEqSucc =>
        Nat.lt_irrefl windowPosition
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
            (Nat.le_of_eq selfEqSucc.symm)))
    show ((!(windowPosition == windowPosition + 1))
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              windowPosition)
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (windowPosition + 1)) = true
    rw [leftBeqRight, boundaryReadWindow]
    exact pairRootsBeq
  show findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (natListGetAt
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (windowPosition + 1)))
      (windowPosition + 1)
      (List.range
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
    = windowPosition
  rw [boundaryReadRight, compositeCandidatesEq,
    rangeInterleaveAtWindow windowPosition tailCount,
    appendAssoc (List.range windowPosition) [windowPosition, windowPosition + 1]
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    findPartnerScan_append_ofFrontFails
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1))
      (windowPosition + 1) (List.range windowPosition)
      ([windowPosition, windowPosition + 1]
        ++ (List.range tailCount).map (fun offset => windowPosition + 2 + offset))
      belowScanExcludes]
  show findPartnerScan
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1))
      (windowPosition + 1)
      (windowPosition :: (windowPosition + 1)
        :: (List.range tailCount).map (fun offset => windowPosition + 2 + offset))
    = windowPosition
  rw [findPartnerScan_cons
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1))
      (windowPosition + 1) windowPosition
      ((windowPosition + 1)
        :: (List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    leftTestPasses]
  exact if_pos rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the consumed window pair partner each other (peel campaign H,
rung E-3, part 5).**  At the cap-head folded end state, `partnerIndexOf` at the left window
index returns the right window index and vice versa: the below-window front fails through
(every candidate reads a reindexed fresh node and the strand-closure anchor misses every
reindexed probe, transferring across the persistent consumed-pair link for the right
exclude), the excluded index skips by the bang-inequality, and the partner wire first-hits
through the seed link's persistence.  What this marker does NOT claim: the mapped
partner-list equality (the composite partner list as the shift-transported fresh list with
the window pair spliced in) and the assembled `DiagramType` / `FullArcStructure` equality.
`= true`. -/
def fxMode_hasArcCapWindowPartners : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReselectionOrbit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCupSingleWindowReadoff — the single-cup forward-partner readoff (rung 1 of the cup window inversion)

The cup-side blocker (`windowPin`, the "cup window read-off") asks: recover a created cup's window from the
boundary arc.  This file lands the BASE CASE — a single cup folded onto the fresh seed — as the FORWARD
direction: at window `windowPosition ≤ bottomCount`, the cup's two legs land at boundary indices
`bottomCount + windowPosition` and `bottomCount + windowPosition + 1`, and `partnerIndexOf` reads the second
as the partner of the first.  This is the cup analog of the shipped cap lemma
`arcCapHeadFolded_windowLeftPartner`, but where the cap reads FIXED seed ports, the cup reads FRESH inserted
ports whose same-component is forced by the two nested `unionFindJoin`s that `stepCupArc` performs.

Proof shape: the two legs read off as the seed values `bottomCount`, `bottomCount + 1` (via
`natListGetAt_append_pastBlock` past the `List.range bottomCount` prefix, then
`natListGetAt_natListInsertAt_inside` into the inserted `[bottomCount, bottomCount + 1]` block); those two
nodes are same-component in the stepped links (`isSameComponent_unionFindJoin_joined` for the inner leg-join,
`isSameComponent_unionFindJoin_ofBase` monotonicity through the outer event-node join); the census carries
via `arcBoundaryCensus_stepCupArc` applied to `arcBoundaryCensus_initial`; and `partnerIndexOf_uniqueSameComponent`
finishes.  No concrete cup `SpineAtom` is constructed — the census steps directly off the seed census.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin.  Rung 1 is the base case and
does NOT by itself flip any gate flag — the general head-cup tail-tracking (rung 3) does. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

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

/-! ## The single-cup forward partner -/

/-- ★ **The single-cup forward-partner readoff (rung 1 of the cup window inversion).**  Fold a single cup at
window `windowPosition ≤ bottomCount` onto the fresh seed of `bottomCount` bottom ports.  The cup inserts its
two legs (the fresh ports `bottomCount`, `bottomCount + 1`) at `windowPosition` in the open-wire list, so in
the boundary index space `List.range bottomCount ++ openWires` they sit at indices `bottomCount + windowPosition`
and `bottomCount + windowPosition + 1`.  `stepCupArc` joins those two legs (and an event node) into one
component, so `partnerIndexOf` returns `bottomCount + windowPosition + 1` as the partner of
`bottomCount + windowPosition` — the FORWARD direction of the cup window read-off. -/
theorem singleCupForwardPartner (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    partnerIndexOf
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (bottomCount
          + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length)
        (bottomCount + windowPosition)
      = bottomCount + windowPosition + 1 := by
  -- structural reductions of the stepped state's fields (rfl through the stepCupArc def)
  have hOpenWires :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires
        = natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1] := rfl
  have hLinks :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        = unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount := rfl
  have hRangeLen : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  have hWindowLeRangeLen : windowPosition ≤ (List.range bottomCount).length := by
    rw [hRangeLen]; exact windowFits
  have hOpenLen :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length
        = bottomCount + 2 :=
    (natListInsertAt_length (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]).trans
      (congrArg (fun measured => measured + [bottomCount, bottomCount + 1].length) hRangeLen)
  -- boundary-index bridges (leg indices reshaped into `offset + prefixLength` form)
  have hIdxExclude : bottomCount + windowPosition = windowPosition + (List.range bottomCount).length := by
    rw [hRangeLen, Nat.add_comm windowPosition bottomCount]
  have hIdxCandidate :
      bottomCount + windowPosition + 1 = (windowPosition + 1) + (List.range bottomCount).length := by
    rw [hRangeLen, Nat.add_comm (windowPosition + 1) bottomCount, Nat.add_assoc bottomCount windowPosition 1]
  -- the two boundary reads resolve to the seed leg values
  have hExcludeRead :
      natListGetAt
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (bottomCount + windowPosition)
        = bottomCount := by
    rw [hOpenWires, hIdxExclude,
      natListGetAt_append_pastBlock (List.range bottomCount)
        (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) windowPosition]
    have hInner := natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1] 0 (Nat.succ_pos 1) hWindowLeRangeLen
    rw [Nat.add_zero] at hInner
    exact hInner
  have hCandidateRead :
      natListGetAt
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (bottomCount + windowPosition + 1)
        = bottomCount + 1 := by
    rw [hOpenWires, hIdxCandidate,
      natListGetAt_append_pastBlock (List.range bottomCount)
        (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) (windowPosition + 1)]
    exact natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1] 1 (Nat.lt_succ_self 1) hWindowLeRangeLen
  -- the two legs are same-component in the stepped links
  have hInnerSame :
      isSameComponent (unionFindJoin [] bottomCount (bottomCount + 1)) bottomCount (bottomCount + 1) = true :=
    isSameComponent_unionFindJoin_joined [] isUnionFindForest_nil bottomCount (bottomCount + 1)
  have hForestInner : isUnionFindForest (unionFindJoin [] bottomCount (bottomCount + 1)) :=
    isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil
  have hOuter :
      isSameComponent (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
          bottomCount (bottomCount + 1) = true :=
    isSameComponent_unionFindJoin_ofBase (unionFindJoin [] bottomCount (bottomCount + 1))
      hForestInner (bottomCount + 2) bottomCount bottomCount (bottomCount + 1) hInnerSame
  -- range bounds for the two boundary indices
  have hWinLt : windowPosition < bottomCount + 2 :=
    Nat.lt_of_le_of_lt windowFits
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_succ (bottomCount + 1)))
  have hWin1Lt : windowPosition + 1 < bottomCount + 2 :=
    Nat.lt_of_le_of_lt (Nat.succ_le_succ windowFits) (Nat.lt_succ_self (bottomCount + 1))
  -- assemble via the uniqueness finisher
  refine partnerIndexOf_uniqueSameComponent bottomCount
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
    ?census (bottomCount + windowPosition) (bottomCount + windowPosition + 1)
    ?excludeInRange ?candidateInRange ?candidateNeExclude ?sameReads
  case census =>
    exact arcBoundaryCensus_stepCupArc bottomCount
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount) (isUnionFindForest_initialLinks bottomCount)
      (Nat.le_refl bottomCount) hWindowLeRangeLen (arcBoundaryCensus_initial bottomCount)
  case excludeInRange =>
    rw [hOpenLen]; exact Nat.add_lt_add_left hWinLt bottomCount
  case candidateInRange =>
    rw [hOpenLen, Nat.add_assoc bottomCount windowPosition 1]
    exact Nat.add_lt_add_left hWin1Lt bottomCount
  case candidateNeExclude =>
    intro hEq
    have hLt : bottomCount + windowPosition < bottomCount + windowPosition + 1 :=
      Nat.lt_succ_self (bottomCount + windowPosition)
    rw [hEq] at hLt
    exact Nat.lt_irrefl (bottomCount + windowPosition) hLt
  case sameReads =>
    rw [hExcludeRead, hCandidateRead, hLinks]; exact hOuter

/-! ## The single-cup reverse partner (the fresh-seed window pair, both legs) -/

/-- The single-cup stepped state's open-wire count is `bottomCount + 2` (the two fresh legs inserted). -/
private theorem singleCupOpenLen (bottomCount windowPosition : Nat) :
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length
      = bottomCount + 2 :=
  (natListInsertAt_length (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]).trans
    (congrArg (fun measured => measured + [bottomCount, bottomCount + 1].length) (rangeLength bottomCount))

/-- The boundary census survives folding one cup onto the fresh seed (steps off `arcBoundaryCensus_initial`). -/
private theorem singleCupStateCensus (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount) :
    ArcBoundaryCensus bottomCount
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition) := by
  have hWindowLeRangeLen : windowPosition ≤ (List.range bottomCount).length := by
    rw [rangeLength bottomCount]; exact windowFits
  exact arcBoundaryCensus_stepCupArc bottomCount
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
    (arcStateFresh_initial bottomCount) (isUnionFindForest_initialLinks bottomCount)
    (Nat.le_refl bottomCount) hWindowLeRangeLen (arcBoundaryCensus_initial bottomCount)

/-- ★ **The single-cup reverse-partner readoff (the other leg of the fresh-seed window pair).**  Mirror of
`singleCupForwardPartner`: `partnerIndexOf` of the RIGHT leg (`bottomCount + windowPosition + 1`) is the LEFT
leg (`bottomCount + windowPosition`).  Proved with NO fresh union-find work — the matching is an involution
(`partnerIndexOf_isInvolution`, discharged by the seed census), so the reverse leg is forced by the forward
one.  This is the cup analog of the shipped cap `arcCapHeadFolded_windowRightPartner`; together with the
forward lemma it gives the full fresh-seed window pair (both legs matched to each other). -/
theorem singleCupReversePartner (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    partnerIndexOf
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (bottomCount
          + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length)
        (bottomCount + windowPosition + 1)
      = bottomCount + windowPosition := by
  have forward := singleCupForwardPartner bottomCount windowPosition windowFits
  have indexInRange :
      bottomCount + windowPosition
        < bottomCount
          + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length := by
    rw [singleCupOpenLen bottomCount windowPosition]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt windowFits
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_succ (bottomCount + 1)))) bottomCount
  have notFixed :
      partnerIndexOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (bottomCount
            + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length)
          (bottomCount + windowPosition)
        ≠ bottomCount + windowPosition := by
    rw [forward]
    intro hEq
    have hLt : bottomCount + windowPosition < bottomCount + windowPosition + 1 :=
      Nat.lt_succ_self (bottomCount + windowPosition)
    rw [hEq] at hLt
    exact Nat.lt_irrefl (bottomCount + windowPosition) hLt
  have involuted := partnerIndexOf_isInvolution bottomCount
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
    (singleCupStateCensus bottomCount windowPosition windowFits)
    (bottomCount + windowPosition) indexInRange notFixed
  rw [forward] at involuted
  exact involuted

/-! ## Honesty marker -/

/-- **Honesty marker — the fresh-seed single-cup window pair is proved (both legs).**  `singleCupForwardPartner`
+ `singleCupReversePartner`: for a lone cup folded onto the fresh seed at window `windowPosition ≤ bottomCount`,
`partnerIndexOf` matches the left leg (`bottomCount + windowPosition`) and the right leg
(`bottomCount + windowPosition + 1`) to each other, in BOTH directions (the reverse follows from the forward by
`partnerIndexOf_isInvolution`).  What these do NOT claim: lifting off the fresh seed onto an arbitrary processed
TAIL (the tail-carrying `arcCupHeadFolded_windowLeftPartner`, the cup analog of the shipped cap lemma — the
driver's actual need), the leftContext-length recovery `windowPin`, nor the leg-aligned reselection
`AtomicTraceEquiv` (`arcCupReselection_exists`, the genuine planar residual).  This is the base case of the cup
window read-off; no gate flag flips here.  `= true`. -/
def fxMode_hasSingleCupWindowPair : Bool := true

end FX1Poly.Polygraph

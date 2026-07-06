import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryCensus
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan

/-! # ArcPerfectMatching — every boundary port is genuinely matched (short-chord no-fixed-point prereq)

The short-chord planar lemma's third hypothesis is NO FIXED POINT: `partnerIndexOf index ≠ index`, i.e.
every boundary port has a DISTINCT partner.  That is the `≥ 2`-boundary-ends direction of the census
(dual to `ArcBoundaryCensus`'s `≤ 2`): at the walking adjunction no oriented loop ever closes and every
event node is internal, so each strand carries exactly two boundary ends.

This brick ships the STATEMENT layer of that invariant (`ArcPerfectMatching` — every in-range boundary
index has a distinct in-range same-component index), the BRIDGE that consumes it
(`partnerIndexOf_neSelf_ofPerfectMatching`: a genuine partner exists ⟹ the scan does not return the
index itself), and its truth at the FRESH SEED (each seed strand `{bottom port v, open slot v}` reads the
same node `v`, so the two are mutual partners).  The cup/cap step preservation and the fold are the next
rungs (mirroring `ArcNonCrossing`'s D2a-iii/iv).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

private theorem natListGetAt_append_below :
    (block wires : List Nat) → (index : Nat) → index < block.length →
    natListGetAt (block ++ wires) index = natListGetAt block index
  | [], _, index, below => absurd below (Nat.not_lt_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, wires, index + 1, below =>
      natListGetAt_append_below rest wires index (Nat.lt_of_succ_lt_succ below)

private theorem natListGetAt_appendPast :
    (block wires : List Nat) → (offset : Nat) →
    natListGetAt (block ++ wires) (offset + block.length) = natListGetAt wires offset
  | [], _, _ => rfl
  | _ :: blockRest, wires, offset => natListGetAt_appendPast blockRest wires offset

private theorem rangeMem_ofLt : (count target : Nat) → target < count → target ∈ List.range count
  | count, target, targetBelow => by
      have loopMem : ∀ (loopCount : Nat) (accumulated : List Nat),
          target < loopCount → target ∈ List.range.loop loopCount accumulated := by
        intro loopCount
        induction loopCount with
        | zero => intro _ targetBelowZero; exact absurd targetBelowZero (Nat.not_lt_zero target)
        | succ loopPred inductiveHypothesis =>
            intro accumulated targetBelowSucc
            cases Nat.lt_or_ge target loopPred with
            | inl below => exact inductiveHypothesis (loopPred :: accumulated) below
            | inr atLeast =>
                have targetEq : target = loopPred :=
                  Nat.le_antisymm (Nat.le_of_succ_le_succ targetBelowSucc) atLeast
                have headMem : loopPred ∈ List.range.loop loopPred (loopPred :: accumulated) := by
                  have accMem : ∀ (innerCount : Nat) (innerAcc : List Nat),
                      loopPred ∈ innerAcc → loopPred ∈ List.range.loop innerCount innerAcc := by
                    intro innerCount
                    induction innerCount with
                    | zero => intro _ mem; exact mem
                    | succ innerPred innerHypothesis =>
                        intro innerAcc mem
                        exact innerHypothesis (innerPred :: innerAcc) (List.Mem.tail innerPred mem)
                  exact accMem loopPred (loopPred :: accumulated) (List.Mem.head accumulated)
                rw [targetEq]; exact headMem
      exact loopMem count [] targetBelow

/-! ## The perfect-matching invariant -/

/-- ★ **The perfect-matching invariant (index form).**  Every in-range boundary index has a DISTINCT
in-range boundary index reading into its union-find component — the `≥ 2`-boundary-ends dual of the
census.  At the walking adjunction it holds because loops never close and event nodes are internal, so
every strand carries exactly two boundary ends. -/
def ArcPerfectMatching (bottomCount : Nat) (state : ArcWireState) : Prop :=
  ∀ index, index < bottomCount + state.openWires.length →
    ∃ partnerIdx, partnerIdx < bottomCount + state.openWires.length ∧ partnerIdx ≠ index ∧
      isSameComponent state.links
        (natListGetAt (List.range bottomCount ++ state.openWires) index)
        (natListGetAt (List.range bottomCount ++ state.openWires) partnerIdx) = true

/-! ## The bridge: perfect matching ⟹ no fixed point -/

/-- ★ **A perfectly-matched boundary index has a genuine partner.**  If a distinct in-range
same-component index exists, the canonical partner scan does not return the index itself — that
candidate makes the completeness lemma fire. -/
theorem partnerIndexOf_neSelf_ofPerfectMatching (bottomCount : Nat) (state : ArcWireState)
    (perfect : ArcPerfectMatching bottomCount state)
    (index : Nat) (indexInRange : index < bottomCount + state.openWires.length) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
      (bottomCount + state.openWires.length) index ≠ index := by
  obtain ⟨partnerIdx, partnerBelow, partnerNe, sameReads⟩ := perfect index indexInRange
  exact findPartnerScan_neExclude_ofTarget state.links (List.range bottomCount ++ state.openWires)
    (unionFindRootOf state.links (natListGetAt (List.range bottomCount ++ state.openWires) index))
    index (List.range (bottomCount + state.openWires.length))
    partnerIdx
    (rangeMem_ofLt (bottomCount + state.openWires.length) partnerIdx partnerBelow)
    partnerNe
    (of_decide_eq_true sameReads).symm

/-! ## The invariant at the fresh seed -/

/-- ★ **The fresh seed is perfectly matched.**  At the seed `openWires = List.range bottomCount`, so
boundary index `v < bottomCount` and boundary index `bottomCount + v` both read node `v` (the two ends of
the straight seed strand); with the empty link list same-component is node equality, so each is the
other's distinct partner. -/
theorem arcPerfectMatching_initial (bottomCount : Nat) :
    ArcPerfectMatching bottomCount
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) := by
  intro index indexInRange
  have openLength : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  have totalEq : bottomCount + (List.range bottomCount).length = bottomCount + bottomCount := by
    rw [openLength]
  rw [openLength] at indexInRange
  cases Nat.lt_or_ge index bottomCount with
  | inl indexBelowBottom =>
      -- bottom port `index`: its partner is the open slot at the same value, boundary index bottomCount + index
      refine ⟨bottomCount + index, ?_, ?_, ?_⟩
      · rw [openLength]; exact Nat.add_lt_add_left indexBelowBottom bottomCount
      · have posBottom : 0 < bottomCount := Nat.lt_of_le_of_lt (Nat.zero_le index) indexBelowBottom
        intro eq
        have lt : index < bottomCount + index := by
          have step := Nat.add_lt_add_right posBottom index
          rw [Nat.zero_add] at step
          exact step
        rw [eq] at lt
        exact Nat.lt_irrefl index lt
      · have nodeIndex : natListGetAt (List.range bottomCount ++ List.range bottomCount) index = index := by
          have inBlock : index < (List.range bottomCount).length := by rw [openLength]; exact indexBelowBottom
          rw [natListGetAt_append_below (List.range bottomCount) (List.range bottomCount) index inBlock,
            rangeGetAt_below bottomCount index indexBelowBottom]
        have nodePartner : natListGetAt (List.range bottomCount ++ List.range bottomCount)
            (bottomCount + index) = index := by
          have reshape : bottomCount + index = index + (List.range bottomCount).length := by
            rw [openLength, Nat.add_comm bottomCount index]
          rw [reshape, natListGetAt_appendPast (List.range bottomCount) (List.range bottomCount) index,
            rangeGetAt_below bottomCount index indexBelowBottom]
        show isSameComponent [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) index)
          (natListGetAt (List.range bottomCount ++ List.range bottomCount) (bottomCount + index)) = true
        rw [nodeIndex, nodePartner]
        exact decide_eq_true (rfl : unionFindRootOf [] index = unionFindRootOf [] index)
  | inr indexAtLeastBottom =>
      -- open slot: partner is the bottom port at the reversed value `index - bottomCount`
      obtain ⟨slot, slotEq⟩ := Nat.le.dest indexAtLeastBottom
      have slotBelow : slot < bottomCount := by
        have raw : bottomCount + slot < bottomCount + bottomCount := by rw [slotEq]; exact indexInRange
        exact Nat.lt_of_add_lt_add_left raw
      refine ⟨slot, ?_, ?_, ?_⟩
      · rw [openLength]; exact Nat.lt_of_lt_of_le slotBelow (Nat.le_add_right bottomCount bottomCount)
      · have posBottom : 0 < bottomCount := Nat.lt_of_le_of_lt (Nat.zero_le slot) slotBelow
        intro eq
        have lt : slot < bottomCount + slot := by
          have step := Nat.add_lt_add_right posBottom slot
          rw [Nat.zero_add] at step
          exact step
        rw [slotEq, eq] at lt
        exact Nat.lt_irrefl index lt
      · have nodeSlot : natListGetAt (List.range bottomCount ++ List.range bottomCount) slot = slot := by
          have inBlock : slot < (List.range bottomCount).length := by rw [openLength]; exact slotBelow
          rw [natListGetAt_append_below (List.range bottomCount) (List.range bottomCount) slot inBlock,
            rangeGetAt_below bottomCount slot slotBelow]
        have nodeIndex : natListGetAt (List.range bottomCount ++ List.range bottomCount) index = slot := by
          have reshape : index = slot + (List.range bottomCount).length := by
            rw [openLength, ← slotEq, Nat.add_comm bottomCount slot]
          rw [reshape, natListGetAt_appendPast (List.range bottomCount) (List.range bottomCount) slot,
            rangeGetAt_below bottomCount slot slotBelow]
        show isSameComponent [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) index)
          (natListGetAt (List.range bottomCount ++ List.range bottomCount) slot) = true
        rw [nodeIndex, nodeSlot]
        exact decide_eq_true (rfl : unionFindRootOf [] slot = unionFindRootOf [] slot)

/-! ## The token-frame perfect matching (fold-composable form) -/

/-- ★ **The perfect-matching invariant, token frame.**  Every valid boundary end token has a DISTINCT
valid boundary end token on its union-find component — the fold-composable dual of `ArcBoundaryCensus`
(stable tokens, shifting node reads).  This is the frame the cup/cap preservation and whole-spine fold
run in, because a token survives the `natListInsertAt`/`natListRemoveTwoAt` reshaping while a raw range
index would shift.  The range-frame `ArcPerfectMatching` is recovered from it at the extracted state for
the `partnerIndexOf` bridge. -/
def ArcPerfectMatchingTokens (seedBoundary : Nat) (state : ArcWireState) : Prop :=
  ∀ token, isValidArcEndToken seedBoundary state token →
    ∃ partner, isValidArcEndToken seedBoundary state partner ∧ partner ≠ token ∧
      isSameComponent state.links (arcEndTokenNode state token)
        (arcEndTokenNode state partner) = true

/-- ★ **The token-frame perfect matching holds at the fresh seed.**  A bottom port `v` and the open slot
`v` are distinct tokens both reading node `v` (the two ends of the straight seed strand), so each is the
other's genuine partner. -/
theorem arcPerfectMatchingTokens_initial (seedBoundary : Nat) :
    ArcPerfectMatchingTokens seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) := by
  intro token valid
  cases token with
  | bottomPort portValue =>
      have portBelow : portValue < seedBoundary := valid
      refine ⟨ArcEndToken.openSlot portValue, ?_, ?_, ?_⟩
      · show portValue < (List.range seedBoundary).length
        rw [rangeLength]; exact portBelow
      · exact fun eq => ArcEndToken.noConfusion eq
      · show isSameComponent [] portValue (natListGetAt (List.range seedBoundary) portValue) = true
        rw [rangeGetAt_below seedBoundary portValue portBelow]
        exact decide_eq_true (rfl : unionFindRootOf [] portValue = unionFindRootOf [] portValue)
  | openSlot slotPosition =>
      have slotBelow : slotPosition < seedBoundary := by
        have raw : slotPosition < (List.range seedBoundary).length := valid
        rw [rangeLength] at raw; exact raw
      refine ⟨ArcEndToken.bottomPort slotPosition, ?_, ?_, ?_⟩
      · show slotPosition < seedBoundary
        exact slotBelow
      · exact fun eq => ArcEndToken.noConfusion eq
      · show isSameComponent [] (natListGetAt (List.range seedBoundary) slotPosition) slotPosition
          = true
        rw [rangeGetAt_below seedBoundary slotPosition slotBelow]
        exact decide_eq_true (rfl : unionFindRootOf [] slotPosition = unionFindRootOf [] slotPosition)

/-! ## Honesty marker -/

/-- **Honesty marker — the perfect-matching invariant is DEFINED (range + token frames), BRIDGED to
no-fixed-point, and TRUE AT THE FRESH SEED in both frames (short-chord no-fixed-point prereq).**
`ArcPerfectMatching` (range frame: every in-range boundary index has a distinct same-component in-range
index), `partnerIndexOf_neSelf_ofPerfectMatching` (the bridge discharging the short-chord's `noFixedPoint`
hypothesis), `arcPerfectMatching_initial` (range-frame seed), plus `ArcPerfectMatchingTokens` (the
fold-composable token frame, dual to `ArcBoundaryCensus`) and `arcPerfectMatchingTokens_initial` (its
seed — each seed strand is a `{bottom port v, open slot v}` mutual pair).  What this marker does NOT claim:
the stepCupArc / stepCapArc preservation of `ArcPerfectMatchingTokens`, its whole-spine fold, or the
extracted-state token→range bridge — the next rungs, mirroring `ArcNonCrossing`'s preservation chain.
`= true`. -/
def fxMode_hasArcPerfectMatching : Bool := true

end FX1Poly.Polygraph

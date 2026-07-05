import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcPairSeparation — an untouched pair defeats the partner pin

The head-location scan's END-STATE kill: if the two tracked bottom ports are still untouched
(open + unlinked) at a state, the partner read-off at one of them cannot name the other —
each unlinked node is its own union-find root, so the scan-soundness root equation collapses
to equality of the two distinct indices.  Contrapositively: a final arc structure that PINS
`partner(leftIndex) = rightIndex` (the cap-head read-off) forces some fold step to touch the
pair — the scan's termination guarantee.

* `ArcPairUntouched.swap` — the invariant is symmetric in its two nodes;
* `isSameComponent_eq_false_ofBothUnlinked` — two distinct unlinked nodes never share a
  component (both roots are the nodes themselves);
* ★ `arcPairUntouched_partnerIndexOf_ne` — the kill: at any state where the pair (whose
  node ids are its own bottom-port indices) is untouched, `partnerIndexOf` at the left index
  differs from the right index.  Scan soundness (`findPartnerScan_root_ofFound`) turns a hit
  into a root equation; the boundary reads below the seed width are the indices themselves;
  the unlinked roots are self (`unionFindRootOf_eq_self_ofUntouched`).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range read plumbing (private copies — the seed files' kits are file-private) -/

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

/-! ## Symmetry and component separation of an untouched pair -/

/-- The untouched-pair invariant is symmetric in its two nodes. -/
theorem ArcPairUntouched.swap {leftNode rightNode : Nat} {state : ArcWireState}
    (untouched : ArcPairUntouched leftNode rightNode state) :
    ArcPairUntouched rightNode leftNode state :=
  ⟨untouched.isRightOpen, untouched.isLeftOpen,
    untouched.isRightUnlinked, untouched.isLeftUnlinked⟩

/-- An unlinked node is its own root — the membership-form root lemma fed by the stronger
edge-avoidance invariant. -/
theorem unionFindRootOf_eq_self_ofUnlinked (links : List (Nat × Nat)) {node : Nat}
    (unlinked : ArcNodeUnlinked links node) :
    unionFindRootOf links node = node :=
  unionFindRootOf_eq_self_ofUntouched links node
    (fun edge edgeListed => (unlinked edge edgeListed).1)

/-- Two DISTINCT unlinked nodes never share a component — both roots are the nodes
themselves. -/
theorem isSameComponent_eq_false_ofBothUnlinked (links : List (Nat × Nat))
    {firstNode secondNode : Nat}
    (firstUnlinked : ArcNodeUnlinked links firstNode)
    (secondUnlinked : ArcNodeUnlinked links secondNode)
    (nodesNe : firstNode ≠ secondNode) :
    isSameComponent links firstNode secondNode = false := by
  show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = false
  rw [unionFindRootOf_eq_self_ofUnlinked links firstUnlinked,
    unionFindRootOf_eq_self_ofUnlinked links secondUnlinked]
  cases beqTest : (firstNode == secondNode) with
  | true => exact absurd (of_decide_eq_true beqTest) nodesNe
  | false => rfl

/-! ## The end-state kill -/

/-- ★ **An untouched pair defeats the partner pin.**  At any state where the pair of bottom
ports (node ids = indices, both below the seed width) is untouched, the partner read-off at
the left index cannot name the right index: a hit would make the scan-soundness root
equation identify the two distinct self-rooted indices. -/
theorem arcPairUntouched_partnerIndexOf_ne (bottomCount : Nat) (state : ArcWireState)
    {leftIndex rightIndex : Nat}
    (leftBelow : leftIndex < bottomCount) (rightBelow : rightIndex < bottomCount)
    (indexesNe : leftIndex ≠ rightIndex)
    (untouched : ArcPairUntouched leftIndex rightIndex state) :
    partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) leftIndex
      ≠ rightIndex := by
  intro partnerHit
  have leftRead : natListGetAt (List.range bottomCount ++ state.openWires) leftIndex
      = leftIndex := by
    rw [natListGetAt_append_inside (List.range bottomCount) state.openWires leftIndex
      (by rw [rangeLength]; exact leftBelow)]
    exact rangeGetAt_below bottomCount leftIndex leftBelow
  have rightRead : natListGetAt (List.range bottomCount ++ state.openWires) rightIndex
      = rightIndex := by
    rw [natListGetAt_append_inside (List.range bottomCount) state.openWires rightIndex
      (by rw [rangeLength]; exact rightBelow)]
    exact rangeGetAt_below bottomCount rightIndex rightBelow
  have scanHit : findPartnerScan state.links (List.range bottomCount ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ state.openWires) leftIndex))
      leftIndex (List.range (bottomCount + state.openWires.length)) = rightIndex :=
    partnerHit
  have scanFound : findPartnerScan state.links (List.range bottomCount ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ state.openWires) leftIndex))
      leftIndex (List.range (bottomCount + state.openWires.length)) ≠ leftIndex := by
    rw [scanHit]
    exact Ne.symm indexesNe
  have rootEquation := findPartnerScan_root_ofFound state.links
    (List.range bottomCount ++ state.openWires)
    (unionFindRootOf state.links
      (natListGetAt (List.range bottomCount ++ state.openWires) leftIndex))
    leftIndex (List.range (bottomCount + state.openWires.length)) scanFound
  rw [scanHit, rightRead, leftRead,
    unionFindRootOf_eq_self_ofUnlinked state.links untouched.isRightUnlinked,
    unionFindRootOf_eq_self_ofUnlinked state.links untouched.isLeftUnlinked]
    at rootEquation
  exact indexesNe rootEquation.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the untouched-pair partner separation is SHIPPED.**  An unlinked node
is its own root, two distinct unlinked nodes never share a component, and at any state where
the tracked pair of bottom ports is untouched the partner read-off at one cannot name the
other — so a final structure pinning them as partners forces some fold step to touch the
pair.  NOT yet shipped: the touching-step dichotomy (one-node caps contradict the count
pins) and the scan induction consuming this as its termination guarantee.  `= true`. -/
def fxMode_hasArcPairPartnerSeparation : Bool := true

end FX1Poly.Polygraph

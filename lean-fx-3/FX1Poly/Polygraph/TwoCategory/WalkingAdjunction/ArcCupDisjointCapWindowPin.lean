import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSingleInternalWindowReadoff
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCupDisjointCapWindowPin — the R1 census read-off lifted past one WINDOW-DISJOINT cap

`ArcCupSingleInternalWindowReadoff` shipped the R1 head-cup window read-off for the EMPTY tail
(`singleCupHeadWindowPinned`): for a lone cup, `internalCupCounts` reads `1` at the cup's left leg and `0`
below, so the window is a total function of that field.  This brick takes the census inversion its FIRST
non-empty-tail step (FM Prop 4.2.4 / 4.3.1 window-disjoint peel): the head cup is still pinned when the
tail's leading event is a WINDOW-DISJOINT cap.

The decisive structural fact — a cap adds a CAP event, never a cup event — means the two-atom spine
`[cupHead, capTail]` still carries a SINGLE cup event node (`bc + 2`).  So its `internalCupCounts` census is
one boolean per port exactly as in the base case, only its links carry two extra `unionFindJoin`s from the
cap.  Both zone reads therefore flow through ONE identity: the cup event's same-component view is UNCHANGED
by the disjoint cap's joins, because neither cap wire nor the cap event sits in the cup's leg component.

  * ★ `isSameComponent_unionFindJoin_offProbe` — a reusable join-invariance lemma: joining two nodes that
    both avoid `probe`'s component leaves `probe`'s same-component view pointwise unchanged.  The
    flat-disjunction characterization with the two off-probe factors killing the mixed disjuncts.
  * ★ `cupEventComponent_reduce_pastDisjointCap` — the cup event `bc + 2`'s same-component view survives the
    cap's two joins: `isSameComponent finalLinks (bc + 2) probe = isSameComponent (cupLinks bc) (bc + 2)
    probe`, via `offProbe` applied twice (the cap wires are `< bc`, the cap event is `bc + 3`, all off the
    leg strand's `bc ≤ · < bc + 3` closures).
  * ★ `twoAtomCupInternalCupCount_atLeftLeg` / `_belowWindow` — the census reads `1` at the cup's left leg
    (`bc + cupWindow`) and `0` at every port below it, GIVEN the cap sits a gap above the cup's two legs
    (`cupWindow + 2 + gap = capWindow ≤ bc`).  The two-cap-join links reduce to the single-cup links, and
    the boundary reads reduce past the disjoint removal (`natListGetAt_natListRemoveTwoAt_below`).
  * ★ `singleCupHeadWindowPinned_pastDisjointCap` — the R1 pin lifted: two cup-then-window-disjoint-cap
    spines with equal arc structure have equal head windows.

Raw Lean 4 + Init; the same union-find + range-read kit as the base brick, no `omega` / `simp`-AC /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range-read plumbing (the established per-file private idiom) -/

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

private theorem natRangeMapGetAt (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLength total]; exact indexInRange),
    rangeGetAt_below total index indexInRange]

/-! ## The single-cup link partition and its two node-set closures -/

/-- The union-find partition after a lone cup folds onto the fresh seed at `bottomCount` bottom ports: the
two legs `bottomCount`, `bottomCount + 1` joined, plus the cup event `bottomCount + 2` joined onto the left
leg.  This is exactly `(stepCupArc (fresh seed) windowPosition).links` — window-independent (a cup always
allocates the same three fresh ids). -/
private def cupLinks (bottomCount : Nat) : List (Nat × Nat) :=
  unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount

/-- The cup partition is a union-find forest (two joins from the empty forest). -/
private theorem cupLinks_isForest (bottomCount : Nat) : isUnionFindForest (cupLinks bottomCount) :=
  isUnionFindForest_unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
    (bottomCount + 2) bottomCount
    (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil)

/-- Every edge of the cup partition has both endpoints `≥ bottomCount` — the leg strand lives at or above the
bottom boundary (the same node closure the base brick's below-window read uses). -/
private theorem cupLinks_closedLower (bottomCount : Nat) :
    ∀ edge ∈ cupLinks bottomCount, bottomCount ≤ edge.1 ∧ bottomCount ≤ edge.2 :=
  unionFindJoin_preservesNodeClosure (fun value => bottomCount ≤ value)
    (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
    (unionFindJoin_preservesNodeClosure (fun value => bottomCount ≤ value) [] bottomCount
      (bottomCount + 1) (fun _ edgeInNil => nomatch edgeInNil)
      (Nat.le_refl bottomCount) (Nat.le_succ bottomCount))
    (Nat.le_add_right bottomCount 2) (Nat.le_refl bottomCount)

/-- Every edge of the cup partition has both endpoints `< bottomCount + 3` — the leg strand is exactly the
three fresh ids `bottomCount, bottomCount + 1, bottomCount + 2`, all strictly below the next fresh id. -/
private theorem cupLinks_closedUpper (bottomCount : Nat) :
    ∀ edge ∈ cupLinks bottomCount, edge.1 < bottomCount + 3 ∧ edge.2 < bottomCount + 3 :=
  unionFindJoin_preservesNodeClosure (fun value => value < bottomCount + 3)
    (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
    (unionFindJoin_preservesNodeClosure (fun value => value < bottomCount + 3) [] bottomCount
      (bottomCount + 1) (fun _ edgeInNil => nomatch edgeInNil)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_add_right (bottomCount + 1) 2))
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (bottomCount + 1)) (Nat.le_succ (bottomCount + 2))))
    (Nat.lt_succ_self (bottomCount + 2)) (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount)
      (Nat.le_add_right (bottomCount + 1) 2))

/-- The cup event `bottomCount + 2` is NOT same-component with any node strictly below the bottom boundary:
that node is an untouched singleton disjoint from the leg strand (`bottomCount ≤ ·` closure). -/
private theorem cupEvent_notSame_belowBottom (bottomCount lowerNode : Nat)
    (lowerBelow : lowerNode < bottomCount) :
    isSameComponent (cupLinks bottomCount) (bottomCount + 2) lowerNode = false := by
  cases hsame : isSameComponent (cupLinks bottomCount) (bottomCount + 2) lowerNode with
  | true =>
      have nodesEq := nodesEqual_ofConnectedToUntouched (fun value => bottomCount ≤ value)
        (cupLinks bottomCount) (cupLinks_closedLower bottomCount) (bottomCount + 2) lowerNode
        (fun bottomLe => Nat.lt_irrefl bottomCount (Nat.lt_of_le_of_lt bottomLe lowerBelow)) hsame
      exact absurd (nodesEq ▸ Nat.le_add_right bottomCount 2)
        (fun bottomLe => Nat.lt_irrefl bottomCount (Nat.lt_of_le_of_lt bottomLe lowerBelow))
  | false => rfl

/-- The cup event `bottomCount + 2` is NOT same-component with any node at or above `bottomCount + 3`: the
cap event `bottomCount + 3` is an untouched singleton disjoint from the leg strand (`· < bottomCount + 3`
closure). -/
private theorem cupEvent_notSame_aboveStrand (bottomCount upperNode : Nat)
    (upperAtLeast : bottomCount + 3 ≤ upperNode) :
    isSameComponent (cupLinks bottomCount) (bottomCount + 2) upperNode = false := by
  cases hsame : isSameComponent (cupLinks bottomCount) (bottomCount + 2) upperNode with
  | true =>
      have nodesEq := nodesEqual_ofConnectedToUntouched (fun value => value < bottomCount + 3)
        (cupLinks bottomCount) (cupLinks_closedUpper bottomCount) (bottomCount + 2) upperNode
        (fun upperLt => Nat.lt_irrefl upperNode (Nat.lt_of_lt_of_le upperLt upperAtLeast)) hsame
      exact absurd (nodesEq ▸ Nat.lt_succ_self (bottomCount + 2))
        (fun upperLt => Nat.lt_irrefl upperNode (Nat.lt_of_lt_of_le upperLt upperAtLeast))
  | false => rfl

/-! ## The reusable join-off-probe invariance lemma -/

/-- ★ **A join of two nodes both off `probe`'s component leaves `probe`'s same-component view unchanged.**
If neither `joinFirst` nor `joinSecond` is same-component with `probe`, then after `unionFindJoin joinFirst
joinSecond` the probe shares a component with any `other` node iff it already did — the two mixed disjuncts
of the flat-disjunction characterization both carry an off-probe factor and vanish.  Forest-conditioned on
the base. -/
theorem isSameComponent_unionFindJoin_offProbe (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinFirst joinSecond probe other : Nat)
    (firstOff : isSameComponent links joinFirst probe = false)
    (secondOff : isSameComponent links joinSecond probe = false) :
    isSameComponent (unionFindJoin links joinFirst joinSecond) probe other
      = isSameComponent links probe other := by
  rw [isSameComponent_unionFindJoin links forest joinFirst joinSecond probe other, firstOff,
    isSameComponent_symm links probe joinSecond, secondOff]
  cases isSameComponent links probe other <;>
    cases isSameComponent links joinFirst other <;> rfl

/-! ## The cup event's component survives the disjoint cap's two joins -/

/-- ★ **The disjoint cap does not move the cup's leg strand.**  With the two cap wires `capWireLeft`,
`capWireRight` strictly below the bottom boundary and the cap event `bottomCount + 3` above the strand, the
cup event `bottomCount + 2`'s same-component view is UNCHANGED by the cap's two joins.  Applying
`isSameComponent_unionFindJoin_offProbe` twice: the inner cap-wire join is off the cup event (both wires
`< bottomCount`), and the outer cap-event join is off it too (the moved cap wire is off, and the cap event
`bottomCount + 3` is off the strand). -/
private theorem cupEventComponent_reduce_pastDisjointCap (bottomCount capWireLeft capWireRight probe : Nat)
    (leftBelow : capWireLeft < bottomCount) (rightBelow : capWireRight < bottomCount) :
    isSameComponent
        (unionFindJoin (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight)
          (bottomCount + 3) capWireLeft)
        (bottomCount + 2) probe
      = isSameComponent (cupLinks bottomCount) (bottomCount + 2) probe := by
  have forestBase := cupLinks_isForest bottomCount
  have forestMerged : isUnionFindForest
      (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight) :=
    isUnionFindForest_unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight forestBase
  -- inner: the cap-wire join is off the cup event (both wires below the strand)
  have leftOff : isSameComponent (cupLinks bottomCount) capWireLeft (bottomCount + 2) = false := by
    rw [isSameComponent_symm]; exact cupEvent_notSame_belowBottom bottomCount capWireLeft leftBelow
  have rightOff : isSameComponent (cupLinks bottomCount) capWireRight (bottomCount + 2) = false := by
    rw [isSameComponent_symm]; exact cupEvent_notSame_belowBottom bottomCount capWireRight rightBelow
  have innerReduce : ∀ probeInner : Nat,
      isSameComponent (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight)
          (bottomCount + 2) probeInner
        = isSameComponent (cupLinks bottomCount) (bottomCount + 2) probeInner := fun probeInner =>
    isSameComponent_unionFindJoin_offProbe (cupLinks bottomCount) forestBase
      capWireLeft capWireRight (bottomCount + 2) probeInner leftOff rightOff
  -- outer: the cap-event join is off the cup event (moved wire off, cap event above the strand)
  have capEventOffMerged :
      isSameComponent (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight)
        (bottomCount + 3) (bottomCount + 2) = false := by
    rw [isSameComponent_symm, innerReduce (bottomCount + 3)]
    exact cupEvent_notSame_aboveStrand bottomCount (bottomCount + 3) (Nat.le_refl (bottomCount + 3))
  have leftWireOffMerged :
      isSameComponent (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight)
        capWireLeft (bottomCount + 2) = false := by
    rw [isSameComponent_symm, innerReduce capWireLeft]
    exact cupEvent_notSame_belowBottom bottomCount capWireLeft leftBelow
  rw [isSameComponent_unionFindJoin_offProbe
      (unionFindJoin (cupLinks bottomCount) capWireLeft capWireRight) forestMerged
      (bottomCount + 3) capWireLeft (bottomCount + 2) probe capEventOffMerged leftWireOffMerged]
  exact innerReduce probe

/-! ## The two-atom state and its census -/

/-- The wire state after folding `[cupHead, capTail]` directly: a cup at `cupWindow` then a cap at
`capWindow`, both onto the fresh `bottomCount`-port seed.  Its `cupEventNodes` is the SINGLETON
`[bottomCount + 2]` — the cap contributes only a cap event. -/
private def twoAtomState (bottomCount cupWindow capWindow : Nat) : ArcWireState :=
  stepCapArc (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) cupWindow)
    capWindow

/-- The inserted open-wire list after the cup step — the seed range with the two legs spliced at the cup
window. -/
private def cupOpenWires (bottomCount cupWindow : Nat) : List Nat :=
  natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1]

/-- The two-atom state's fields, definitionally.  `links` is two cap joins on top of `cupLinks`, its
`openWires` the disjoint removal of the cup-inserted wires, its `cupEventNodes` the singleton cup event. -/
private theorem twoAtomState_fields (bottomCount cupWindow capWindow : Nat) :
    (twoAtomState bottomCount cupWindow capWindow).links
        = unionFindJoin (unionFindJoin (cupLinks bottomCount)
            (natListGetAt (cupOpenWires bottomCount cupWindow) capWindow)
            (natListGetAt (cupOpenWires bottomCount cupWindow) (capWindow + 1)))
          (bottomCount + 3) (natListGetAt (cupOpenWires bottomCount cupWindow) capWindow)
      ∧ (twoAtomState bottomCount cupWindow capWindow).openWires
          = natListRemoveTwoAt (cupOpenWires bottomCount cupWindow) capWindow
      ∧ (twoAtomState bottomCount cupWindow capWindow).cupEventNodes = [bottomCount + 2] :=
  ⟨rfl, rfl, rfl⟩

/-- The census read at any boundary index collapses to the single cup event's same-component test. -/
private theorem twoAtomCensus_asIf (bottomCount cupWindow capWindow index : Nat) :
    internalEventCountAt (twoAtomState bottomCount cupWindow capWindow).links
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires)
        (twoAtomState bottomCount cupWindow capWindow).cupEventNodes index
      = (if isSameComponent (twoAtomState bottomCount cupWindow capWindow).links (bottomCount + 2)
            (natListGetAt
              (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires) index)
          then 1 else 0) := by
  obtain ⟨_, _, cupEventsForm⟩ := twoAtomState_fields bottomCount cupWindow capWindow
  rw [cupEventsForm]
  show (if isSameComponent (twoAtomState bottomCount cupWindow capWindow).links (bottomCount + 2)
          (natListGetAt
            (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires) index)
        then 1 else 0) + 0 = _
  rw [Nat.add_zero]

/-- The census read reduces to the single-cup partition's same-component test at the same probe: the two-atom
links' two cap joins do not touch the cup event `bottomCount + 2`, provided the two cap wires are below the
bottom boundary. -/
private theorem twoAtomCensus_reduce (bottomCount cupWindow capWindow index : Nat)
    (leftBelow : natListGetAt (cupOpenWires bottomCount cupWindow) capWindow < bottomCount)
    (rightBelow : natListGetAt (cupOpenWires bottomCount cupWindow) (capWindow + 1) < bottomCount) :
    internalEventCountAt (twoAtomState bottomCount cupWindow capWindow).links
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires)
        (twoAtomState bottomCount cupWindow capWindow).cupEventNodes index
      = (if isSameComponent (cupLinks bottomCount) (bottomCount + 2)
            (natListGetAt
              (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires) index)
          then 1 else 0) := by
  rw [twoAtomCensus_asIf bottomCount cupWindow capWindow index]
  obtain ⟨linksForm, _, _⟩ := twoAtomState_fields bottomCount cupWindow capWindow
  rw [linksForm,
    cupEventComponent_reduce_pastDisjointCap bottomCount
      (natListGetAt (cupOpenWires bottomCount cupWindow) capWindow)
      (natListGetAt (cupOpenWires bottomCount cupWindow) (capWindow + 1)) _ leftBelow rightBelow]

/-! ## The cap-wire reads: both cap wires sit below the bottom boundary -/

/-- The cup-inserted open-wire list has length `bottomCount + 2` (the seed range plus two legs). -/
private theorem cupOpenWires_length (bottomCount cupWindow : Nat) :
    (cupOpenWires bottomCount cupWindow).length = bottomCount + 2 := by
  show (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1]).length
    = bottomCount + 2
  rw [natListInsertAt_length]
  show (List.range bottomCount).length + 2 = bottomCount + 2
  rw [rangeLength]

/-- The cap's left wire, a gap ABOVE the cup's two legs, reads a bottom-boundary value strictly below
`bottomCount` — it is the range value `cupWindow + gap` spliced past the two-leg block. -/
private theorem capLeftWire_belowBottom (bottomCount cupWindow gap : Nat)
    (cupFits : cupWindow ≤ bottomCount) (capReaches : cupWindow + 2 + gap ≤ bottomCount) :
    natListGetAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap) < bottomCount := by
  have h2 : cupWindow + gap + 2 ≤ bottomCount := by
    rw [Nat.add_right_comm cupWindow 2 gap] at capReaches; exact capReaches
  have valueBelow : cupWindow + gap < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (cupWindow + gap))
      (Nat.le_trans (Nat.le_succ (cupWindow + gap + 1)) h2)
  have readValue : natListGetAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)
      = cupWindow + gap := by
    show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
        (cupWindow + 2 + gap) = cupWindow + gap
    rw [Nat.add_right_comm cupWindow 2 gap]
    show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
        (cupWindow + gap + [bottomCount, bottomCount + 1].length) = cupWindow + gap
    rw [natListGetAt_natListInsertAt_pastBlock (List.range bottomCount) cupWindow
        [bottomCount, bottomCount + 1] gap (by rw [rangeLength]; exact cupFits)]
    exact rangeGetAt_below bottomCount (cupWindow + gap) valueBelow
  rw [readValue]; exact valueBelow

/-- The cap's right wire reads a bottom-boundary value strictly below `bottomCount` — the range value
`cupWindow + gap + 1`. -/
private theorem capRightWire_belowBottom (bottomCount cupWindow gap : Nat)
    (cupFits : cupWindow ≤ bottomCount) (capReaches : cupWindow + 2 + gap ≤ bottomCount) :
    natListGetAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap + 1) < bottomCount := by
  have h2 : cupWindow + gap + 2 ≤ bottomCount := by
    rw [Nat.add_right_comm cupWindow 2 gap] at capReaches; exact capReaches
  have valueBelow : cupWindow + gap + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (cupWindow + gap + 1)) h2
  have idxEq : cupWindow + 2 + gap + 1 = cupWindow + (gap + 1) + 2 :=
    (congrArg (· + 1) (Nat.add_right_comm cupWindow 2 gap)).trans rfl
  have readValue : natListGetAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap + 1)
      = cupWindow + gap + 1 := by
    show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
        (cupWindow + 2 + gap + 1) = cupWindow + gap + 1
    rw [idxEq]
    show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
        (cupWindow + (gap + 1) + [bottomCount, bottomCount + 1].length) = cupWindow + gap + 1
    rw [natListGetAt_natListInsertAt_pastBlock (List.range bottomCount) cupWindow
        [bottomCount, bottomCount + 1] (gap + 1) (by rw [rangeLength]; exact cupFits)]
    exact rangeGetAt_below bottomCount (cupWindow + (gap + 1)) valueBelow
  rw [readValue]; exact valueBelow

/-! ## The boundary reads at and below the cup window -/

/-- The boundary read at the cup's left leg index `bottomCount + cupWindow` is the left leg `bottomCount`:
the disjoint cap removal (at `capWindow > cupWindow`) leaves the read below it untouched, and the cup insert
places the left leg there. -/
private theorem twoAtomBoundaryRead_atLeftLeg (bottomCount cupWindow gap : Nat)
    (cupFits : cupWindow ≤ bottomCount) :
    natListGetAt
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires)
        (bottomCount + cupWindow) = bottomCount := by
  obtain ⟨_, openForm, _⟩ := twoAtomState_fields bottomCount cupWindow (cupWindow + 2 + gap)
  rw [openForm]
  have hIdx : bottomCount + cupWindow = cupWindow + (List.range bottomCount).length := by
    rw [rangeLength, Nat.add_comm cupWindow bottomCount]
  rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
      (natListRemoveTwoAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)) cupWindow]
  rw [natListGetAt_natListRemoveTwoAt_below (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)
      cupWindow (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos 1))
        (Nat.le_add_right (cupWindow + 2) gap))]
  show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
      cupWindow = bottomCount
  have hInner := natListGetAt_natListInsertAt_inside (List.range bottomCount) cupWindow
    [bottomCount, bottomCount + 1] 0 (Nat.succ_pos 1) (by rw [rangeLength]; exact cupFits)
  rw [Nat.add_zero] at hInner
  exact hInner

/-- The boundary read strictly below the cup window is strictly below `bottomCount` — a bottom port or a
below-window seed wire, in either case untouched by the disjoint cap removal. -/
private theorem twoAtomBoundaryRead_belowWindow (bottomCount cupWindow gap index : Nat)
    (cupFits : cupWindow ≤ bottomCount) (indexBelow : index < bottomCount + cupWindow) :
    natListGetAt
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires)
        index < bottomCount := by
  obtain ⟨_, openForm, _⟩ := twoAtomState_fields bottomCount cupWindow (cupWindow + 2 + gap)
  rw [openForm]
  cases Nat.lt_or_ge index bottomCount with
  | inl indexInPrefix =>
      rw [natListGetAt_append_inside (List.range bottomCount)
          (natListRemoveTwoAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)) index
          (by rw [rangeLength]; exact indexInPrefix),
        rangeGetAt_below bottomCount index indexInPrefix]
      exact indexInPrefix
  | inr indexAtLeast =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest indexAtLeast
      have offsetLtWindow : offset < cupWindow :=
        Nat.lt_of_add_lt_add_left
          (show bottomCount + offset < bottomCount + cupWindow by rw [offsetEq]; exact indexBelow)
      have hIdx : bottomCount + offset = offset + (List.range bottomCount).length := by
        rw [rangeLength, Nat.add_comm]
      have readVal : natListGetAt
          (List.range bottomCount
            ++ natListRemoveTwoAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap))
          (bottomCount + offset) < bottomCount := by
        rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
            (natListRemoveTwoAt (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)) offset]
        rw [natListGetAt_natListRemoveTwoAt_below (cupOpenWires bottomCount cupWindow)
            (cupWindow + 2 + gap) offset
            (Nat.lt_of_lt_of_le offsetLtWindow
              (Nat.le_trans (Nat.le_add_right cupWindow 2) (Nat.le_add_right (cupWindow + 2) gap)))]
        show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
            offset < bottomCount
        rw [natListGetAt_natListInsertAt_below (List.range bottomCount) cupWindow
            [bottomCount, bottomCount + 1] offset offsetLtWindow
            (by rw [rangeLength]; exact Nat.lt_of_lt_of_le offsetLtWindow cupFits),
          rangeGetAt_below bottomCount offset (Nat.lt_of_lt_of_le offsetLtWindow cupFits)]
        exact Nat.lt_of_lt_of_le offsetLtWindow cupFits
      rw [← offsetEq]; exact readVal

/-! ## The two census reads: `1` at the leg, `0` below -/

/-- ★ **The disjoint-cap census reads `1` at the cup's left leg.**  For `[cupHead, capTail]` with the cap a
gap above the cup legs (`cupWindow + 2 + gap = capWindow ≤ bottomCount`), the single cup event
`bottomCount + 2` is same-component with its left leg (surviving the cap's joins), which sits at boundary
index `bottomCount + cupWindow`. -/
private theorem twoAtomCupInternalCupCount_atLeftLeg (bottomCount cupWindow gap : Nat)
    (cupFits : cupWindow ≤ bottomCount) (capReaches : cupWindow + 2 + gap ≤ bottomCount) :
    internalEventCountAt (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).links
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires)
        (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).cupEventNodes
        (bottomCount + cupWindow)
      = 1 := by
  rw [twoAtomCensus_reduce bottomCount cupWindow (cupWindow + 2 + gap) (bottomCount + cupWindow)
      (capLeftWire_belowBottom bottomCount cupWindow gap cupFits capReaches)
      (capRightWire_belowBottom bottomCount cupWindow gap cupFits capReaches),
    twoAtomBoundaryRead_atLeftLeg bottomCount cupWindow gap cupFits]
  have joined : isSameComponent (cupLinks bottomCount) (bottomCount + 2) bottomCount = true :=
    isSameComponent_unionFindJoin_joined (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil)
      (bottomCount + 2) bottomCount
  exact if_pos joined

/-- ★ **The disjoint-cap census reads `0` below the cup window.**  Below the cup's left leg the boundary node
is a bottom port or below-window seed wire — strictly below `bottomCount`, disjoint from the cup event's leg
strand (and the cap's joins do not connect them). -/
private theorem twoAtomCupInternalCupCount_belowWindow (bottomCount cupWindow gap index : Nat)
    (cupFits : cupWindow ≤ bottomCount) (capReaches : cupWindow + 2 + gap ≤ bottomCount)
    (indexBelow : index < bottomCount + cupWindow) :
    internalEventCountAt (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).links
        (List.range bottomCount ++ (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires)
        (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).cupEventNodes
        index
      = 0 := by
  rw [twoAtomCensus_reduce bottomCount cupWindow (cupWindow + 2 + gap) index
      (capLeftWire_belowBottom bottomCount cupWindow gap cupFits capReaches)
      (capRightWire_belowBottom bottomCount cupWindow gap cupFits capReaches)]
  refine if_neg ?_
  rw [cupEvent_notSame_belowBottom bottomCount _
      (twoAtomBoundaryRead_belowWindow bottomCount cupWindow gap index cupFits indexBelow)]
  exact fun heq => Bool.noConfusion heq

/-! ## The state-level window pin -/

/-- The `internalCupCounts` field entry at an in-range boundary index is the per-port census count. -/
private theorem twoAtomInternalCupCountsGetAt (bottomCount cupWindow capWindow index : Nat)
    (indexInRange :
      index < bottomCount + (twoAtomState bottomCount cupWindow capWindow).openWires.length) :
    natListGetAt (extractArc bottomCount (twoAtomState bottomCount cupWindow capWindow)).internalCupCounts
        index
      = internalEventCountAt (twoAtomState bottomCount cupWindow capWindow).links
          (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires)
          (twoAtomState bottomCount cupWindow capWindow).cupEventNodes index := by
  have fieldUnfold :
      (extractArc bottomCount (twoAtomState bottomCount cupWindow capWindow)).internalCupCounts
        = (List.range (bottomCount + (twoAtomState bottomCount cupWindow capWindow).openWires.length)).map
            (internalEventCountAt (twoAtomState bottomCount cupWindow capWindow).links
              (List.range bottomCount ++ (twoAtomState bottomCount cupWindow capWindow).openWires)
              (twoAtomState bottomCount cupWindow capWindow).cupEventNodes) := rfl
  rw [fieldUnfold]
  exact natRangeMapGetAt _ _ index indexInRange

/-- The two-atom state's open-wire count is `bottomCount` — the cup adds two wires, the disjoint cap removes
two.  This bounds the probe index below the internal-count list length. -/
private theorem twoAtomOpenWires_length (bottomCount cupWindow gap : Nat)
    (capReaches : cupWindow + 2 + gap ≤ bottomCount) :
    (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires.length = bottomCount := by
  obtain ⟨_, openForm, _⟩ := twoAtomState_fields bottomCount cupWindow (cupWindow + 2 + gap)
  rw [openForm]
  have capInRange : (cupWindow + 2 + gap) + 2 ≤ (cupOpenWires bottomCount cupWindow).length := by
    rw [cupOpenWires_length]
    exact Nat.add_le_add_right capReaches 2
  have dropped := natListRemoveTwoAt_length (cupOpenWires bottomCount cupWindow) (cupWindow + 2 + gap)
    capInRange
  rw [cupOpenWires_length] at dropped
  exact Nat.succ.inj (Nat.succ.inj dropped)

/-- The probe index `bottomCount + windowProbe` is in range of the two-atom internal-count list whenever the
probe window is strictly below `bottomCount`. -/
private theorem twoAtomProbeInRange (bottomCount cupWindow gap windowProbe : Nat)
    (capReaches : cupWindow + 2 + gap ≤ bottomCount) (probeBelow : windowProbe < bottomCount) :
    bottomCount + windowProbe
      < bottomCount + (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap)).openWires.length := by
  rw [twoAtomOpenWires_length bottomCount cupWindow gap capReaches]
  exact Nat.add_lt_add_left probeBelow bottomCount

/-- The cup window is strictly below `bottomCount` once a disjoint cap fits above it. -/
private theorem cupWindow_lt_bottom (bottomCount cupWindow gap : Nat)
    (capReaches : cupWindow + 2 + gap ≤ bottomCount) : cupWindow < bottomCount :=
  Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos 1))
    (Nat.le_add_right (cupWindow + 2) gap)) capReaches

/-- The internal cup-count list of a cup-then-disjoint-cap spine, as a named abbreviation (keeps the field
projection attached to its subject — a leading-dot projection on a fresh line reparses as dot-notation). -/
private def twoAtomCupCounts (bottomCount cupWindow gap : Nat) : List Nat :=
  (extractArc bottomCount (twoAtomState bottomCount cupWindow (cupWindow + 2 + gap))).internalCupCounts

/-- One direction of the disjoint-cap window pin: a strictly smaller cup window cannot share the larger
window's `internalCupCounts` — its left leg reads `1` on one side but `0` (below the larger window) on the
other. -/
private theorem twoAtomWindowPin_notLt (bottomCount cupWindowSmall gapSmall cupWindowLarge gapLarge : Nat)
    (smallFits : cupWindowSmall ≤ bottomCount) (smallReaches : cupWindowSmall + 2 + gapSmall ≤ bottomCount)
    (largeFits : cupWindowLarge ≤ bottomCount) (largeReaches : cupWindowLarge + 2 + gapLarge ≤ bottomCount)
    (countsEqual : twoAtomCupCounts bottomCount cupWindowSmall gapSmall
        = twoAtomCupCounts bottomCount cupWindowLarge gapLarge)
    (strict : cupWindowSmall < cupWindowLarge) : False := by
  have smallRead :
      natListGetAt (twoAtomCupCounts bottomCount cupWindowSmall gapSmall) (bottomCount + cupWindowSmall)
        = 1 := by
    dsimp only [twoAtomCupCounts]
    rw [twoAtomInternalCupCountsGetAt bottomCount cupWindowSmall (cupWindowSmall + 2 + gapSmall)
        (bottomCount + cupWindowSmall)
        (twoAtomProbeInRange bottomCount cupWindowSmall gapSmall cupWindowSmall smallReaches
          (cupWindow_lt_bottom bottomCount cupWindowSmall gapSmall smallReaches))]
    exact twoAtomCupInternalCupCount_atLeftLeg bottomCount cupWindowSmall gapSmall smallFits smallReaches
  have largeRead :
      natListGetAt (twoAtomCupCounts bottomCount cupWindowLarge gapLarge) (bottomCount + cupWindowSmall)
        = 0 := by
    dsimp only [twoAtomCupCounts]
    rw [twoAtomInternalCupCountsGetAt bottomCount cupWindowLarge (cupWindowLarge + 2 + gapLarge)
        (bottomCount + cupWindowSmall)
        (twoAtomProbeInRange bottomCount cupWindowLarge gapLarge cupWindowSmall largeReaches
          (Nat.lt_of_lt_of_le strict largeFits))]
    exact twoAtomCupInternalCupCount_belowWindow bottomCount cupWindowLarge gapLarge
      (bottomCount + cupWindowSmall) largeFits largeReaches (Nat.add_lt_add_left strict bottomCount)
  have clash : (1 : Nat) = 0 := by rw [← smallRead, countsEqual, largeRead]
  exact Nat.noConfusion clash

/-- ★ **`internalCupCounts` pins the head cup's window past a disjoint cap (state level).**  Two spines,
each a cup then a window-disjoint cap onto the fresh `bottomCount`-port seed, with EQUAL `internalCupCounts`
have equal head windows.  The census read-off survives the disjoint cap's joins — the first non-empty-tail
step of the census inversion. -/
private theorem twoAtomWindowPinnedByInternalCupCounts
    (bottomCount cupWindowLeft gapLeft cupWindowRight gapRight : Nat)
    (leftFits : cupWindowLeft ≤ bottomCount) (leftReaches : cupWindowLeft + 2 + gapLeft ≤ bottomCount)
    (rightFits : cupWindowRight ≤ bottomCount) (rightReaches : cupWindowRight + 2 + gapRight ≤ bottomCount)
    (countsEqual : twoAtomCupCounts bottomCount cupWindowLeft gapLeft
        = twoAtomCupCounts bottomCount cupWindowRight gapRight) :
    cupWindowLeft = cupWindowRight := by
  cases Nat.lt_trichotomy cupWindowLeft cupWindowRight with
  | inl leftLt =>
      exact (twoAtomWindowPin_notLt bottomCount cupWindowLeft gapLeft cupWindowRight gapRight
        leftFits leftReaches rightFits rightReaches countsEqual leftLt).elim
  | inr rest =>
      cases rest with
      | inl windowsEq => exact windowsEq
      | inr rightLt =>
          exact (twoAtomWindowPin_notLt bottomCount cupWindowRight gapRight cupWindowLeft gapLeft
            rightFits rightReaches leftFits leftReaches countsEqual.symm rightLt).elim

/-! ## The R1 pin on the spine list, lifted past one window-disjoint cap -/

/-- A cap-arity atom's arc step is the cap step at its window. -/
private theorem stepArcAtom_capBranch {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hasCapDom : atom.generatorDom.length = 2) (hasCapCod : atom.generatorCod.length = 0) :
    stepArcAtom state atom = stepCapArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCapDom, hasCapCod]

/-- A cup-arity atom's arc step is the cup step at its window. -/
private theorem stepArcAtom_cupBranch {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hasCupDom : atom.generatorDom.length = 0) (hasCupCod : atom.generatorCod.length = 2) :
    stepArcAtom state atom = stepCupArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCupDom, hasCupCod]

/-- The arc structure of a cup-then-cap spine is the two-atom state's extract, with the cap window pinned to
`cupWindow + 2 + gap` by the disjoint hypothesis. -/
private theorem cupCapSpine_arcStructure {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat) (cupHead capTail : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (cupDom : cupHead.generatorDom.length = 0) (cupCod : cupHead.generatorCod.length = 2)
    (capDom : capTail.generatorDom.length = 2) (capCod : capTail.generatorCod.length = 0)
    (gap : Nat) (disjoint : cupHead.leftContext.length + 2 + gap = capTail.leftContext.length) :
    arcStructureOfSpineList bottomCount [cupHead, capTail]
      = extractArc bottomCount
          (twoAtomState bottomCount cupHead.leftContext.length
            (cupHead.leftContext.length + 2 + gap)) := by
  show extractArc bottomCount
      (stepArcAtom (stepArcAtom (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) cupHead)
        capTail)
    = extractArc bottomCount
        (twoAtomState bottomCount cupHead.leftContext.length (cupHead.leftContext.length + 2 + gap))
  dsimp only [twoAtomState]
  rw [stepArcAtom_cupBranch _ cupHead cupDom cupCod,
    stepArcAtom_capBranch _ capTail capDom capCod, disjoint]

/-- ★ **The R1 head-cup window read-off, lifted past one WINDOW-DISJOINT cap.**  Two spines, each a cup head
followed by a cap whose window sits a gap ABOVE the cup's two legs (`cupWindow + 2 + gap = capWindow`), with
equal arc structure have equal head windows.  The head cup stays pinned because the disjoint cap does not
merge its legs: the single cup event's `internalCupCounts` census still reads `1` at the left leg and `0`
below, exactly as in the empty-tail base case.  This is the first non-empty-tail rung of the census
inversion (the FM Prop 4.2.4 window-disjoint peel, `|f_{i0-1}| ≤ |f_{i0}| - 2` case). -/
theorem singleCupHeadWindowPinned_pastDisjointCap
    {overallSourceLeft overallTargetLeft overallSourceRight overallTargetRight : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (cupHeadLeft : SpineAtom adjunctionModeSignature overallSourceLeft overallTargetLeft)
    (capTailLeft : SpineAtom adjunctionModeSignature overallSourceLeft overallTargetLeft)
    (cupHeadRight : SpineAtom adjunctionModeSignature overallSourceRight overallTargetRight)
    (capTailRight : SpineAtom adjunctionModeSignature overallSourceRight overallTargetRight)
    (leftCupDom : cupHeadLeft.generatorDom.length = 0) (leftCupCod : cupHeadLeft.generatorCod.length = 2)
    (leftCapDom : capTailLeft.generatorDom.length = 2) (leftCapCod : capTailLeft.generatorCod.length = 0)
    (rightCupDom : cupHeadRight.generatorDom.length = 0) (rightCupCod : cupHeadRight.generatorCod.length = 2)
    (rightCapDom : capTailRight.generatorDom.length = 2) (rightCapCod : capTailRight.generatorCod.length = 0)
    (leftGap : Nat)
    (leftDisjoint :
      cupHeadLeft.leftContext.length + 2 + leftGap = capTailLeft.leftContext.length)
    (leftCapFits : capTailLeft.leftContext.length ≤ bottomCount)
    (rightGap : Nat)
    (rightDisjoint :
      cupHeadRight.leftContext.length + 2 + rightGap = capTailRight.leftContext.length)
    (rightCapFits : capTailRight.leftContext.length ≤ bottomCount)
    (arcEqual : arcStructureOfSpineList bottomCount [cupHeadLeft, capTailLeft]
        = arcStructureOfSpineList bottomCount [cupHeadRight, capTailRight]) :
    cupHeadLeft.leftContext.length = cupHeadRight.leftContext.length := by
  have leftReaches : cupHeadLeft.leftContext.length + 2 + leftGap ≤ bottomCount := by
    rw [leftDisjoint]; exact leftCapFits
  have rightReaches : cupHeadRight.leftContext.length + 2 + rightGap ≤ bottomCount := by
    rw [rightDisjoint]; exact rightCapFits
  have leftFits : cupHeadLeft.leftContext.length ≤ bottomCount :=
    Nat.le_of_lt (cupWindow_lt_bottom bottomCount cupHeadLeft.leftContext.length leftGap leftReaches)
  have rightFits : cupHeadRight.leftContext.length ≤ bottomCount :=
    Nat.le_of_lt (cupWindow_lt_bottom bottomCount cupHeadRight.leftContext.length rightGap rightReaches)
  refine twoAtomWindowPinnedByInternalCupCounts bottomCount
    cupHeadLeft.leftContext.length leftGap cupHeadRight.leftContext.length rightGap
    leftFits leftReaches rightFits rightReaches ?_
  have countsEqual := congrArg FullArcStructure.internalCupCounts arcEqual
  rw [cupCapSpine_arcStructure bottomCount cupHeadLeft capTailLeft leftCupDom leftCupCod
      leftCapDom leftCapCod leftGap leftDisjoint,
    cupCapSpine_arcStructure bottomCount cupHeadRight capTailRight rightCupDom rightCupCod
      rightCapDom rightCapCod rightGap rightDisjoint] at countsEqual
  exact countsEqual

/-! ## Honesty marker -/

/-- **Honesty marker — the R1 head-cup window read-off is PROVED past one WINDOW-DISJOINT cap.**
`singleCupHeadWindowPinned_pastDisjointCap`: for `[cupHead, capTail]` with the cap a gap above the cup's two
legs, the head cup's window is still a total function of `internalCupCounts`.  The decisive structural fact —
a cap adds a cap event, never a cup event — keeps the census a single boolean per port; the two extra cap
`unionFindJoin`s leave the cup event's leg strand untouched (`cupEventComponent_reduce_pastDisjointCap`, via
the reusable `isSameComponent_unionFindJoin_offProbe`), so `1` at the left leg
(`twoAtomCupInternalCupCount_atLeftLeg`) and `0` below (`twoAtomCupInternalCupCount_belowWindow`) survive,
pinning the window (`twoAtomWindowPinnedByInternalCupCounts`).  This is the FM Prop 4.2.4 / 4.3.1
window-disjoint peel's `|f_{i0-1}| ≤ |f_{i0}| - 2` rung — the FIRST non-empty-tail step of the census
inversion, generalizing the shipped empty-tail base `singleCupHeadWindowPinned`.

What this marker does NOT claim: (1) the INTERACTING (adjacent, gap = 0/1) cap — where the cup and cap ARE a
zigzag and cancel via the snake, not a census read-off; (2) more than one tail event (a cap-then-cap or
mixed longer tail — the leg strand may then move, needing the general-state census through a moved leg); (3)
the peel-and-recurse `MixedTailArcCompleteness` itself.  The width measure `N = (N1, N2^eta, N2^eps)` is not
yet decreased structurally — round 1 lands the single window-disjoint locator rung, not the recursion.  No
gate flip; `fxMode_hasArcStructureReconstruction` stays as is.  `= true`. -/
def fxMode_hasArcCupDisjointCapWindowPin : Bool := true

end FX1Poly.Polygraph

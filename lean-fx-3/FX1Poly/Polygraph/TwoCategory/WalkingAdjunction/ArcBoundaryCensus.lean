import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # ArcBoundaryCensus — the two-endpoint boundary census of the arc fold (peel campaign H, cup rung 2d-i)

Every union-find component of an arc-fold state is a path of wires, and a path has exactly two
ends — so at most two BOUNDARY endpoints (original bottom ports and currently-open wire ends)
can ever share a component.  This census is the load-bearing fact for the cup rewiring rung:
the peeled cup fuses the two leg components, and reading the composite partner structure off
the joined-fresh scan needs to know that NO boundary index beyond the window legs and their two
attachments tests into the fused component.

A boundary END TOKEN is either a bottom port (an original seed node, one per value below the
seed boundary width) or an open slot (a position into the current `openWires`).  Both ends of a
straight-through seed wire are two DISTINCT tokens on the SAME node — the census counts wire
ENDS, not nodes.  Event nodes carry no token: they decorate components without adding ends.

This brick ships the STATEMENT layer: the token type, its node map and validity, the pairwise
three-token census (no three distinct valid tokens pairwise share a component — the zero-dep
rendering of "at most two"), and its truth at the fresh seed state, where every component is a
single wire holding exactly its bottom-port token and its open-slot token.  The cup/cap step
PRESERVATION and the fold transport are the campaign's next rungs.

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

/-! ## The boundary end tokens -/

/-- A boundary END of an arc-fold state: an original bottom port (one per seed node value) or a
currently-open wire end (one per `openWires` position).  A straight-through seed wire owns two
distinct tokens on the same node — the census counts wire ends, not nodes. -/
inductive ArcEndToken where
  /-- The bottom-boundary end of the original seed wire with this node value. -/
  | bottomPort (portValue : Nat)
  /-- The open (top-candidate) end currently sitting at this `openWires` position. -/
  | openSlot (slotPosition : Nat)

/-- The union-find node a boundary end token reads: a bottom port IS its node value, an open
slot reads the wire node at its position. -/
def arcEndTokenNode (state : ArcWireState) : ArcEndToken → Nat
  | ArcEndToken.bottomPort portValue => portValue
  | ArcEndToken.openSlot slotPosition => natListGetAt state.openWires slotPosition

/-- Is this token a genuine boundary end of the state?  Bottom ports must sit below the seed
boundary width; open slots must index into the current `openWires`. -/
def isValidArcEndToken (seedBoundary : Nat) (state : ArcWireState) : ArcEndToken → Prop
  | ArcEndToken.bottomPort portValue => portValue < seedBoundary
  | ArcEndToken.openSlot slotPosition => slotPosition < state.openWires.length

/-! ## The census -/

/-- ★ **The two-endpoint boundary census.**  No three distinct valid boundary end tokens share
a union-find component (hub form: the first token reaches the other two).  Every component is a
path of wires with exactly two ends, so at most two boundary endpoints — this is the zero-dep
pigeonhole rendering of that bound, and it is exactly what the cup rewiring rung consumes: away
from the fused legs' two attachments, no boundary index tests into the fused component. -/
def ArcBoundaryCensus (seedBoundary : Nat) (state : ArcWireState) : Prop :=
  ∀ tokenOne tokenTwo tokenThree : ArcEndToken,
    isValidArcEndToken seedBoundary state tokenOne →
    isValidArcEndToken seedBoundary state tokenTwo →
    isValidArcEndToken seedBoundary state tokenThree →
    tokenOne ≠ tokenTwo →
    tokenOne ≠ tokenThree →
    tokenTwo ≠ tokenThree →
    isSameComponent state.links (arcEndTokenNode state tokenOne)
        (arcEndTokenNode state tokenTwo) = true →
    isSameComponent state.links (arcEndTokenNode state tokenOne)
        (arcEndTokenNode state tokenThree) = true →
    False

/-! ## The census at the fresh seed -/

/-- With no links, every node is its own root. -/
private theorem unionFindRootOf_nil (node : Nat) : unionFindRootOf [] node = node := rfl

/-- Over the empty link list, same-component is node equality. -/
private theorem arcSeedNodesEqual_ofSameComponent (leftNode rightNode : Nat)
    (sameComponentHolds : isSameComponent [] leftNode rightNode = true) :
    leftNode = rightNode := by
  have rootsEqualTrue : (unionFindRootOf [] leftNode == unionFindRootOf [] rightNode) = true :=
    sameComponentHolds
  rw [unionFindRootOf_nil leftNode, unionFindRootOf_nil rightNode] at rootsEqualTrue
  have nodesDecideTrue : decide (leftNode = rightNode) = true := rootsEqualTrue
  exact of_decide_eq_true nodesDecideTrue

/-- At the seed, an in-range open slot reads its own position: the seed `openWires` is the
range list. -/
private theorem arcSeedSlotRead (seedBoundary slotPosition : Nat)
    (slotBelowLength : slotPosition < (List.range seedBoundary).length) :
    natListGetAt (List.range seedBoundary) slotPosition = slotPosition := by
  rw [rangeLength seedBoundary] at slotBelowLength
  exact rangeGetAt_below seedBoundary slotPosition slotBelowLength

/-- ★ The fresh seed state satisfies the census: every component is a single straight wire,
whose only boundary ends are its bottom port and its open slot — any three distinct tokens
pairwise on one component would force two tokens of the same kind with the same payload. -/
theorem arcBoundaryCensus_initial (seedBoundary : Nat) :
    ArcBoundaryCensus seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  cases tokenOne with
  | bottomPort valueOne =>
      cases tokenTwo with
      | bottomPort valueTwo =>
          exact oneNeTwo (congrArg ArcEndToken.bottomPort
            (arcSeedNodesEqual_ofSameComponent valueOne valueTwo sameOneTwo))
      | openSlot slotTwo =>
          cases tokenThree with
          | bottomPort valueThree =>
              exact oneNeThree (congrArg ArcEndToken.bottomPort
                (arcSeedNodesEqual_ofSameComponent valueOne valueThree sameOneThree))
          | openSlot slotThree =>
              have readSlotTwo : natListGetAt (List.range seedBoundary) slotTwo = slotTwo :=
                arcSeedSlotRead seedBoundary slotTwo validTwo
              have readSlotThree : natListGetAt (List.range seedBoundary) slotThree = slotThree :=
                arcSeedSlotRead seedBoundary slotThree validThree
              have anchorReachesTwo :
                  valueOne = natListGetAt (List.range seedBoundary) slotTwo :=
                arcSeedNodesEqual_ofSameComponent valueOne
                  (natListGetAt (List.range seedBoundary) slotTwo) sameOneTwo
              have anchorReachesThree :
                  valueOne = natListGetAt (List.range seedBoundary) slotThree :=
                arcSeedNodesEqual_ofSameComponent valueOne
                  (natListGetAt (List.range seedBoundary) slotThree) sameOneThree
              have slotsEqual : slotTwo = slotThree :=
                readSlotTwo.symm.trans
                  ((anchorReachesTwo.symm.trans anchorReachesThree).trans readSlotThree)
              exact twoNeThree (congrArg ArcEndToken.openSlot slotsEqual)
  | openSlot slotOne =>
      have readSlotOne : natListGetAt (List.range seedBoundary) slotOne = slotOne :=
        arcSeedSlotRead seedBoundary slotOne validOne
      cases tokenTwo with
      | bottomPort valueTwo =>
          cases tokenThree with
          | bottomPort valueThree =>
              have anchorReachesTwo :
                  natListGetAt (List.range seedBoundary) slotOne = valueTwo :=
                arcSeedNodesEqual_ofSameComponent
                  (natListGetAt (List.range seedBoundary) slotOne) valueTwo sameOneTwo
              have anchorReachesThree :
                  natListGetAt (List.range seedBoundary) slotOne = valueThree :=
                arcSeedNodesEqual_ofSameComponent
                  (natListGetAt (List.range seedBoundary) slotOne) valueThree sameOneThree
              exact twoNeThree (congrArg ArcEndToken.bottomPort
                (anchorReachesTwo.symm.trans anchorReachesThree))
          | openSlot slotThree =>
              have readSlotThree : natListGetAt (List.range seedBoundary) slotThree = slotThree :=
                arcSeedSlotRead seedBoundary slotThree validThree
              have anchorReachesThree :
                  natListGetAt (List.range seedBoundary) slotOne
                    = natListGetAt (List.range seedBoundary) slotThree :=
                arcSeedNodesEqual_ofSameComponent
                  (natListGetAt (List.range seedBoundary) slotOne)
                  (natListGetAt (List.range seedBoundary) slotThree) sameOneThree
              have slotsEqual : slotOne = slotThree :=
                readSlotOne.symm.trans (anchorReachesThree.trans readSlotThree)
              exact oneNeThree (congrArg ArcEndToken.openSlot slotsEqual)
      | openSlot slotTwo =>
          have readSlotTwo : natListGetAt (List.range seedBoundary) slotTwo = slotTwo :=
            arcSeedSlotRead seedBoundary slotTwo validTwo
          have anchorReachesTwo :
              natListGetAt (List.range seedBoundary) slotOne
                = natListGetAt (List.range seedBoundary) slotTwo :=
            arcSeedNodesEqual_ofSameComponent
              (natListGetAt (List.range seedBoundary) slotOne)
              (natListGetAt (List.range seedBoundary) slotTwo) sameOneTwo
          have slotsEqual : slotOne = slotTwo :=
            readSlotOne.symm.trans (anchorReachesTwo.trans readSlotTwo)
          exact oneNeTwo (congrArg ArcEndToken.openSlot slotsEqual)

/-- **Honesty marker — the boundary-census STATEMENT layer is SHIPPED (peel campaign H, cup
rung 2d-i).**  The boundary end-token type (bottom ports and open slots), its node map and
validity, the three-token pigeonhole census, and its truth at the fresh seed state.  What this
marker does NOT claim: preservation of the census through `stepCupArc` / `stepCapArc` (rungs
2d-ii/iii — the token-surgery accounting across a join) and the fold transport to the folded
cup states (rung 2d-iv) — the rewiring consequence stays pending on those.  `= true`. -/
def fxMode_hasArcBoundaryCensusSeed : Bool := true

end FX1Poly.Polygraph

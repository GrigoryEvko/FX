import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingCountRestricted — count congruence at a node set (MODE3-D)

The LOOP leg counts the mid edges over the two renamed traces' folds, and those folds agree
only BELOW the fresh base (their interior fresh nodes differ) — full-view count congruence
(`countJoinEventLoops_congr`) is out of reach.  But the count of an event list only ever
probes and joins at the list's own nodes, so agreement AT THE LIST'S NODE SET suffices:

* ★ `countJoinEventLoops_congrOnNodeSet` — two bases whose views agree at pairs from a node
  set closed over the events give equal loop counts.  The join preserves the restricted
  correspondence through the flat-disjunction characterization, whose five atoms are pairs
  of the (in-set) join and probe nodes.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- One join at an in-set pair preserves the in-set view correspondence: every atom of the
flat-disjunction characterization is a pair of in-set nodes. -/
private theorem restrictedViewCorrespondence_unionFindJoin (nodeSet : Nat → Prop)
    (linksOne linksTwo : List (Nat × Nat))
    (forestOne : isUnionFindForest linksOne) (forestTwo : isUnionFindForest linksTwo)
    (viewsAgree : ∀ probeOne probeTwo : Nat, nodeSet probeOne → nodeSet probeTwo →
      isSameComponent linksOne probeOne probeTwo = isSameComponent linksTwo probeOne probeTwo)
    (joinLeft joinRight : Nat)
    (joinLeftInSet : nodeSet joinLeft) (joinRightInSet : nodeSet joinRight)
    (probeOne probeTwo : Nat) (oneInSet : nodeSet probeOne) (twoInSet : nodeSet probeTwo) :
    isSameComponent (unionFindJoin linksOne joinLeft joinRight) probeOne probeTwo
      = isSameComponent (unionFindJoin linksTwo joinLeft joinRight) probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin linksOne forestOne joinLeft joinRight probeOne probeTwo,
    isSameComponent_unionFindJoin linksTwo forestTwo joinLeft joinRight probeOne probeTwo,
    viewsAgree probeOne probeTwo oneInSet twoInSet,
    viewsAgree joinLeft probeOne joinLeftInSet oneInSet,
    viewsAgree joinRight probeTwo joinRightInSet twoInSet,
    viewsAgree joinLeft probeTwo joinLeftInSet twoInSet,
    viewsAgree probeOne joinRight oneInSet joinRightInSet]

/-- ★ **Count congruence at a node set**: two bases whose views agree at pairs from a node
set closed over the event list produce equal loop counts — every test and every join stays
inside the set. -/
theorem countJoinEventLoops_congrOnNodeSet (nodeSet : Nat → Prop) :
    (events : List (Nat × Nat)) → (linksOne linksTwo : List (Nat × Nat)) →
    isUnionFindForest linksOne → isUnionFindForest linksTwo →
    (∀ pair ∈ events, nodeSet pair.1 ∧ nodeSet pair.2) →
    (∀ probeOne probeTwo : Nat, nodeSet probeOne → nodeSet probeTwo →
      isSameComponent linksOne probeOne probeTwo
        = isSameComponent linksTwo probeOne probeTwo) →
    countJoinEventLoops events linksOne = countJoinEventLoops events linksTwo
  | [], _, _, _, _, _, _ => rfl
  | (firstNode, secondNode) :: restEvents, linksOne, linksTwo, forestOne, forestTwo,
      eventsClosed, viewsAgree => by
      have headClosed : nodeSet firstNode ∧ nodeSet secondNode :=
        eventsClosed (firstNode, secondNode) (List.Mem.head restEvents)
      show (isSameComponent linksOne firstNode secondNode).toNat
            + countJoinEventLoops restEvents (unionFindJoin linksOne firstNode secondNode)
          = (isSameComponent linksTwo firstNode secondNode).toNat
              + countJoinEventLoops restEvents (unionFindJoin linksTwo firstNode secondNode)
      rw [viewsAgree firstNode secondNode headClosed.1 headClosed.2,
        countJoinEventLoops_congrOnNodeSet nodeSet restEvents
          (unionFindJoin linksOne firstNode secondNode)
          (unionFindJoin linksTwo firstNode secondNode)
          (isUnionFindForest_unionFindJoin linksOne firstNode secondNode forestOne)
          (isUnionFindForest_unionFindJoin linksTwo firstNode secondNode forestTwo)
          (fun pair restMembership =>
            eventsClosed pair (List.Mem.tail (firstNode, secondNode) restMembership))
          (fun probeOne probeTwo oneInSet twoInSet =>
            restrictedViewCorrespondence_unionFindJoin nodeSet linksOne linksTwo forestOne
              forestTwo viewsAgree firstNode secondNode headClosed.1 headClosed.2
              probeOne probeTwo oneInSet twoInSet)]

/-- **Honesty marker — the node-set-restricted count congruence is PROVED.**  NOT yet shipped:
the below-base view agreement between the two renamed folds that discharges its hypothesis,
and the final loop-increment glue. -/
def fxMode_hasRestrictedCountCongruence : Bool := true

end FX1Poly.Polygraph

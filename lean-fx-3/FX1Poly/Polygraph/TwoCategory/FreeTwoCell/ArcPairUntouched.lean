import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldSupport

/-! # ArcPairUntouched — the untouched-pair invariant through the arc fold

The head-location scan tracks two bottom-boundary nodes through a second spine's arc fold
until the step that realizes the head consumes them.  Before that step the pair is
**untouched**: both nodes are still open wires and neither appears in any union-find edge
(unlinked — a strictly syntactic form of "singleton component" that needs no forest
threading).  This file ships the invariant and its preservation under the two non-touching
step shapes:

* `ArcNodeUnlinked` — the node appears in no recorded edge; equivalently, the links list is
  closed under `(· ≠ node)`, so preservation under a join whose ARGUMENTS differ from the
  node is a direct instantiation of the shipped `unionFindJoin_preservesNodeClosure`
  (a root is the start node or a recorded parent value, hence never the unlinked node);
* `arcPairUntouched_stepCupArc` — a cup step NEVER touches the pair: it splices fresh legs
  (membership is stable under a splice) and joins only fresh nodes (all at or above
  `nextFresh`, while the pair's nodes sit below it by `ArcStateFresh`);
* `arcPairUntouched_stepCapArc_ofDisjointReads` — a cap step whose two consumed reads both
  differ from both pair nodes keeps the pair untouched: the removal keeps every other value
  (no distinctness needed — the survival argument is purely structural), and the joins touch
  only the consumed reads and the fresh event node;
* `arcPairUntouched_initial` — any two bottom ports below the boundary width are untouched
  at the canonical initial arc state.

Adjacency is deliberately NOT part of the invariant: a bubble (cup then cap between the pair)
temporarily separates the pair's positions without ever touching its nodes.  The touching
step recovers adjacency for free — a cap consumes two ADJACENT positions, so a cap consuming
both pair nodes finds them adjacent.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Membership plumbing (splice, removal, range) -/

private theorem mem_append_of_mem_right (target : Nat) :
    (block : List Nat) → {rest : List Nat} → target ∈ rest → target ∈ block ++ rest
  | [], _, inRest => inRest
  | blockHead :: blockTail, _, inRest =>
      List.Mem.tail blockHead (mem_append_of_mem_right target blockTail inRest)

/-- An existing wire survives a splice at any position — the converse of
`mem_natListInsertAt_imp`'s left disjunct. -/
theorem mem_natListInsertAt_of_mem {target : Nat} :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    target ∈ wires → target ∈ natListInsertAt wires position block
  | [], 0, _, inWires => nomatch inWires
  | head :: rest, 0, block, inWires => by
      show target ∈ block ++ (head :: rest)
      exact mem_append_of_mem_right target block inWires
  | [], _ + 1, _, inWires => nomatch inWires
  | head :: rest, position + 1, block, inWires => by
      show target ∈ head :: natListInsertAt rest position block
      cases inWires with
      | head => exact List.Mem.head _
      | tail _ inRest =>
          exact List.Mem.tail head (mem_natListInsertAt_of_mem rest position block inRest)

/-- A wire whose value differs from BOTH reads at the removal window survives a pair
removal — purely structural, no positional distinctness needed. -/
theorem mem_natListRemoveTwoAt_of_ne_reads {target : Nat} :
    (wires : List Nat) → (position : Nat) → target ∈ wires →
    natListGetAt wires position ≠ target → natListGetAt wires (position + 1) ≠ target →
    target ∈ natListRemoveTwoAt wires position
  | [], _, inWires, _, _ => nomatch inWires
  | [_], 0, inWires, _, _ => inWires
  | [_], _ + 1, inWires, _, _ => inWires
  | _ :: _ :: _, 0, inWires, firstReadMisses, secondReadMisses => by
      cases inWires with
      | head => exact absurd rfl firstReadMisses
      | tail _ inTail =>
          cases inTail with
          | head => exact absurd rfl secondReadMisses
          | tail _ inRest => exact inRest
  | first :: second :: rest, position + 1, inWires, firstReadMisses, secondReadMisses => by
      show target ∈ first :: natListRemoveTwoAt (second :: rest) position
      cases inWires with
      | head => exact List.Mem.head _
      | tail _ inRest =>
          exact List.Mem.tail first
            (mem_natListRemoveTwoAt_of_ne_reads (second :: rest) position inRest
              firstReadMisses secondReadMisses)

private theorem mem_rangeLoop_of_below : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated ∨ target < count →
    target ∈ List.range.loop count accumulated
  | 0, _, _, hyp => by
      cases hyp with
      | inl inAccumulated => exact inAccumulated
      | inr belowZero => exact absurd belowZero (Nat.not_lt_zero _)
  | count + 1, accumulated, target, hyp => by
      show target ∈ List.range.loop count (count :: accumulated)
      refine mem_rangeLoop_of_below count (count :: accumulated) target ?_
      cases hyp with
      | inl inAccumulated => exact Or.inl (List.Mem.tail count inAccumulated)
      | inr belowSucc =>
          cases Nat.lt_or_ge target count with
          | inl below => exact Or.inr below
          | inr atLeast =>
              have targetEq : target = count :=
                Nat.le_antisymm (Nat.le_of_succ_le_succ belowSucc) atLeast
              rw [targetEq]
              exact Or.inl (List.Mem.head accumulated)

/-- Every value below the count is a member of the range — the converse of
`mem_range_imp_lt`. -/
theorem mem_range_of_lt {target count : Nat} (below : target < count) :
    target ∈ List.range count :=
  mem_rangeLoop_of_below count [] target (Or.inr below)

/-! ## Nat helper (hand-rolled; the core cancellation lemmas leak `propext`) -/

private theorem natNeOfLt {smaller larger : Nat} (strict : smaller < larger) :
    smaller ≠ larger :=
  fun wereEqual => absurd (wereEqual ▸ strict) (Nat.lt_irrefl larger)

/-! ## The unlinked-node predicate and its join preservation -/

/-- A node is **unlinked** when it appears in no recorded union-find edge.  Syntactically
this says the links list is closed under `(· ≠ node)` — the strongest form of "the node's
component is the singleton `{node}`", and the one whose preservation needs no forest
hypothesis. -/
def ArcNodeUnlinked (links : List (Nat × Nat)) (node : Nat) : Prop :=
  ∀ edge ∈ links, edge.1 ≠ node ∧ edge.2 ≠ node

/-- **A join whose arguments differ from an unlinked node keeps it unlinked** — the recorded
edge (if any) connects the arguments' ROOTS, and a root is the start node or a recorded
parent value, neither of which can be the unlinked node.  Direct instantiation of the
node-set closure kit at `(· ≠ node)`. -/
theorem arcNodeUnlinked_unionFindJoin (links : List (Nat × Nat)) {node : Nat}
    (firstNode secondNode : Nat)
    (unlinked : ArcNodeUnlinked links node)
    (firstMisses : firstNode ≠ node) (secondMisses : secondNode ≠ node) :
    ArcNodeUnlinked (unionFindJoin links firstNode secondNode) node :=
  unionFindJoin_preservesNodeClosure (· ≠ node) links firstNode secondNode
    unlinked firstMisses secondMisses

/-! ## The untouched-pair invariant -/

/-- **The untouched-pair invariant**: both tracked nodes are still open wires and neither
appears in any union-find edge.  Adjacency is deliberately absent — a bubble between the
pair separates its positions without touching its nodes. -/
structure ArcPairUntouched (leftNode rightNode : Nat) (state : ArcWireState) : Prop where
  /-- The left tracked node is still an open wire. -/
  isLeftOpen : leftNode ∈ state.openWires
  /-- The right tracked node is still an open wire. -/
  isRightOpen : rightNode ∈ state.openWires
  /-- The left tracked node appears in no union-find edge. -/
  isLeftUnlinked : ArcNodeUnlinked state.links leftNode
  /-- The right tracked node appears in no union-find edge. -/
  isRightUnlinked : ArcNodeUnlinked state.links rightNode

/-! ## Per-step preservation -/

/-- A cup step keeps one open node unlinked: both joins touch only the fresh legs and the
fresh event node, all at or above `nextFresh`, while the node sits below it. -/
private theorem arcNodeUnlinked_stepCupArc (state : ArcWireState) (position : Nat)
    {node : Nat} (nodeBelowFresh : node < state.nextFresh)
    (unlinked : ArcNodeUnlinked state.links node) :
    ArcNodeUnlinked (stepCupArc state position).links node := by
  show ArcNodeUnlinked
    (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh) node
  have missesLeg : state.nextFresh ≠ node := (natNeOfLt nodeBelowFresh).symm
  have missesUpperLeg : state.nextFresh + 1 ≠ node :=
    (natNeOfLt (Nat.lt_of_lt_of_le nodeBelowFresh (Nat.le_add_right state.nextFresh 1))).symm
  have missesEvent : state.nextFresh + 2 ≠ node :=
    (natNeOfLt (Nat.lt_of_lt_of_le nodeBelowFresh (Nat.le_add_right state.nextFresh 2))).symm
  exact arcNodeUnlinked_unionFindJoin _ (state.nextFresh + 2) state.nextFresh
    (arcNodeUnlinked_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      unlinked missesLeg missesUpperLeg)
    missesEvent missesLeg

/-- ★ **A cup step never touches the pair**: membership survives the splice, and both joins
touch only fresh nodes. -/
theorem arcPairUntouched_stepCupArc (state : ArcWireState) (position : Nat)
    {leftNode rightNode : Nat} (fresh : ArcStateFresh state)
    (untouched : ArcPairUntouched leftNode rightNode state) :
    ArcPairUntouched leftNode rightNode (stepCupArc state position) := by
  obtain ⟨leftOpen, rightOpen, leftUnlinked, rightUnlinked⟩ := untouched
  refine ⟨?_, ?_, ?_, ?_⟩
  · show leftNode ∈ natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]
    exact mem_natListInsertAt_of_mem state.openWires position _ leftOpen
  · show rightNode ∈ natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]
    exact mem_natListInsertAt_of_mem state.openWires position _ rightOpen
  · exact arcNodeUnlinked_stepCupArc state position (fresh.1 leftNode leftOpen) leftUnlinked
  · exact arcNodeUnlinked_stepCupArc state position (fresh.1 rightNode rightOpen) rightUnlinked

/-- A disjoint cap step keeps one open node unlinked: the joins touch only the two consumed
reads (which differ from the node by hypothesis) and the fresh event node. -/
private theorem arcNodeUnlinked_stepCapArc (state : ArcWireState) (position : Nat)
    {node : Nat} (nodeBelowFresh : node < state.nextFresh)
    (firstReadMisses : natListGetAt state.openWires position ≠ node)
    (secondReadMisses : natListGetAt state.openWires (position + 1) ≠ node)
    (unlinked : ArcNodeUnlinked state.links node) :
    ArcNodeUnlinked (stepCapArc state position).links node := by
  show ArcNodeUnlinked
    (unionFindJoin
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      state.nextFresh (natListGetAt state.openWires position)) node
  exact arcNodeUnlinked_unionFindJoin _ state.nextFresh
    (natListGetAt state.openWires position)
    (arcNodeUnlinked_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) unlinked firstReadMisses secondReadMisses)
    (natNeOfLt nodeBelowFresh).symm firstReadMisses

/-- ★ **A cap step whose consumed reads miss both pair nodes never touches the pair**: the
removal keeps every other value, and the joins touch only the consumed reads and the fresh
event node. -/
theorem arcPairUntouched_stepCapArc_ofDisjointReads (state : ArcWireState) (position : Nat)
    {leftNode rightNode : Nat} (fresh : ArcStateFresh state)
    (firstReadMissesLeft : natListGetAt state.openWires position ≠ leftNode)
    (secondReadMissesLeft : natListGetAt state.openWires (position + 1) ≠ leftNode)
    (firstReadMissesRight : natListGetAt state.openWires position ≠ rightNode)
    (secondReadMissesRight : natListGetAt state.openWires (position + 1) ≠ rightNode)
    (untouched : ArcPairUntouched leftNode rightNode state) :
    ArcPairUntouched leftNode rightNode (stepCapArc state position) := by
  obtain ⟨leftOpen, rightOpen, leftUnlinked, rightUnlinked⟩ := untouched
  refine ⟨?_, ?_, ?_, ?_⟩
  · show leftNode ∈ natListRemoveTwoAt state.openWires position
    exact mem_natListRemoveTwoAt_of_ne_reads state.openWires position leftOpen
      firstReadMissesLeft secondReadMissesLeft
  · show rightNode ∈ natListRemoveTwoAt state.openWires position
    exact mem_natListRemoveTwoAt_of_ne_reads state.openWires position rightOpen
      firstReadMissesRight secondReadMissesRight
  · exact arcNodeUnlinked_stepCapArc state position (fresh.1 leftNode leftOpen)
      firstReadMissesLeft secondReadMissesLeft leftUnlinked
  · exact arcNodeUnlinked_stepCapArc state position (fresh.1 rightNode rightOpen)
      firstReadMissesRight secondReadMissesRight rightUnlinked

/-! ## The initial-state instance -/

/-- Any two bottom ports below the boundary width are untouched at the canonical initial
arc state: its open wires are exactly the range, and its links are empty. -/
theorem arcPairUntouched_initial (bottomCount leftNode rightNode : Nat)
    (leftBelow : leftNode < bottomCount) (rightBelow : rightNode < bottomCount) :
    ArcPairUntouched leftNode rightNode
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) :=
  ⟨mem_range_of_lt leftBelow, mem_range_of_lt rightBelow,
    (fun _ edgeInNil => nomatch edgeInNil), (fun _ edgeInNil => nomatch edgeInNil)⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the untouched-pair invariant substrate is SHIPPED.**  The invariant
(both tracked nodes open + unlinked, adjacency deliberately excluded) is preserved by every
cup step and by every cap step whose consumed reads miss both nodes, and holds for any two
bottom ports at the canonical initial arc state.  NOT yet shipped: the touching-step
dichotomy (a cap consuming exactly one pair node contradicts the final count pins) and the
head-location scan itself.  `= true`. -/
def fxMode_hasArcPairUntouchedInvariant : Bool := true

end FX1Poly.Polygraph

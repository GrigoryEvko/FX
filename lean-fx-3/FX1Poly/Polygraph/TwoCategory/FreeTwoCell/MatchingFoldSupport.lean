import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingFoldSupport — the event fold's support closure + untouched-probe rigidity (MODE3-D)

The D5 segment-transfer hypothesis quantifies over ALL corresponding probe pairs, including
below-base identifiers never touched by the second-half traces (gamma-interior wires).  For
those the transfer must be VACUOUS — and this file makes it so:

* `unionFindRootOf_eq_self_or_parentValue` — a root is the node itself or some recorded
  edge's parent value (the chase only ever lands on parent entries);
* `applyJoinEvents_preservesNodeClosure` — folding a trace whose event nodes all satisfy a
  node predicate over links whose entries satisfy it keeps every entry inside the predicate
  (each join prepends a pair of ROOTS, and roots stay inside by the previous point);
* `unionFindRootOf_eq_self_ofUntouched` — a node that is no recorded child is its own root
  (membership form of the fresh-root lemma);
* ★ `nodesEqual_ofFoldConnectedToUntouched` — RIGIDITY: an empty-base fold can connect a
  probe to a node OUTSIDE the trace's node set only if they are equal.  The untouched node is
  its own root; the probe's root is itself (forcing equality) or a fold-entry value (which
  would put the untouched node inside the set).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The root lands on the node itself or a parent value -/

/-- A recorded parent lookup returns some edge's parent value. -/
private theorem parentIsEdgeValue :
    (links : List (Nat × Nat)) → (node parent : Nat) →
    unionFindParent links node = some parent →
    ∃ edge, edge ∈ links ∧ edge.2 = parent
  | [], _, _, parentEq => nomatch parentEq
  | (child, recordedParent) :: rest, node, parent, parentEq => by
      dsimp only [unionFindParent] at parentEq
      cases hchild : child == node with
      | true =>
          rw [hchild] at parentEq
          exact ⟨(child, recordedParent), List.Mem.head rest, Option.some.inj parentEq⟩
      | false =>
          rw [hchild] at parentEq
          obtain ⟨edge, edgeListed, valueEq⟩ := parentIsEdgeValue rest node parent parentEq
          exact ⟨edge, List.Mem.tail (child, recordedParent) edgeListed, valueEq⟩

private theorem unionFindRoot_eq_self_or_parentValue :
    (fuel : Nat) → (links : List (Nat × Nat)) → (node : Nat) →
    unionFindRoot fuel links node = node
      ∨ ∃ edge, edge ∈ links ∧ unionFindRoot fuel links node = edge.2
  | 0, _, _ => Or.inl rfl
  | fuel + 1, links, node => by
      have oneStep : unionFindRoot (fuel + 1) links node
          = match unionFindParent links node with
            | none => node
            | some parent => unionFindRoot fuel links parent := rfl
      cases hparent : unionFindParent links node with
      | none =>
          rw [oneStep, hparent]
          exact Or.inl rfl
      | some parent =>
          rw [oneStep, hparent]
          cases unionFindRoot_eq_self_or_parentValue fuel links parent with
          | inl rootSelf =>
              obtain ⟨edge, edgeListed, valueEq⟩ := parentIsEdgeValue links node parent hparent
              exact Or.inr ⟨edge, edgeListed, rootSelf.trans valueEq.symm⟩
          | inr parentValue =>
              obtain ⟨edge, edgeListed, rootEq⟩ := parentValue
              exact Or.inr ⟨edge, edgeListed, rootEq⟩

/-- **A root is the node itself or some recorded edge's parent value** — the parent chase can
only stop on the node or land inside the recorded entries. -/
theorem unionFindRootOf_eq_self_or_parentValue (links : List (Nat × Nat)) (node : Nat) :
    unionFindRootOf links node = node
      ∨ ∃ edge, edge ∈ links ∧ unionFindRootOf links node = edge.2 :=
  unionFindRoot_eq_self_or_parentValue (links.length + 1) links node

/-! ## Node-set closure through the fold -/

/-- The root of an in-set node is in-set (self, or a recorded parent value covered by the
links closure). -/
theorem nodeSetHoldsAtRoot (nodeSet : Nat → Prop) (links : List (Nat × Nat))
    (linksClosed : ∀ edge ∈ links, nodeSet edge.1 ∧ nodeSet edge.2)
    (node : Nat) (nodeInSet : nodeSet node) :
    nodeSet (unionFindRootOf links node) := by
  cases unionFindRootOf_eq_self_or_parentValue links node with
  | inl rootSelf =>
      rw [rootSelf]
      exact nodeInSet
  | inr parentValue =>
      obtain ⟨edge, edgeListed, rootEq⟩ := parentValue
      rw [rootEq]
      exact (linksClosed edge edgeListed).2

/-- One join of two in-set nodes keeps every entry in-set: the no-op branch keeps the links,
the joining branch prepends the pair of their roots. -/
theorem unionFindJoin_preservesNodeClosure (nodeSet : Nat → Prop)
    (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (linksClosed : ∀ edge ∈ links, nodeSet edge.1 ∧ nodeSet edge.2)
    (firstInSet : nodeSet firstNode) (secondInSet : nodeSet secondNode) :
    ∀ edge ∈ unionFindJoin links firstNode secondNode, nodeSet edge.1 ∧ nodeSet edge.2 := by
  cases htest : unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true =>
      have joinEq : unionFindJoin links firstNode secondNode = links := by
        dsimp only [unionFindJoin]
        rw [htest]
        rfl
      rw [joinEq]
      exact linksClosed
  | false =>
      have joinEq : unionFindJoin links firstNode secondNode
          = (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links := by
        dsimp only [unionFindJoin]
        rw [htest]
        rfl
      rw [joinEq]
      intro edge edgeListed
      cases edgeListed with
      | head =>
          exact ⟨nodeSetHoldsAtRoot nodeSet links linksClosed firstNode firstInSet,
            nodeSetHoldsAtRoot nodeSet links linksClosed secondNode secondInSet⟩
      | tail _ tailListed => exact linksClosed edge tailListed

/-- **The whole event fold preserves node-set closure**: with every event node and every base
entry in-set, every fold entry is in-set. -/
theorem applyJoinEvents_preservesNodeClosure (nodeSet : Nat → Prop) :
    (events links : List (Nat × Nat)) →
    (∀ pair ∈ events, nodeSet pair.1 ∧ nodeSet pair.2) →
    (∀ edge ∈ links, nodeSet edge.1 ∧ nodeSet edge.2) →
    ∀ edge ∈ applyJoinEvents events links, nodeSet edge.1 ∧ nodeSet edge.2
  | [], _, _, linksClosed => linksClosed
  | (firstNode, secondNode) :: restEvents, links, eventsClosed, linksClosed =>
      applyJoinEvents_preservesNodeClosure nodeSet restEvents
        (unionFindJoin links firstNode secondNode)
        (fun pair pairListed =>
          eventsClosed pair (List.Mem.tail (firstNode, secondNode) pairListed))
        (unionFindJoin_preservesNodeClosure nodeSet links firstNode secondNode linksClosed
          (eventsClosed (firstNode, secondNode) (List.Mem.head restEvents)).1
          (eventsClosed (firstNode, secondNode) (List.Mem.head restEvents)).2)

/-! ## Untouched-probe rigidity -/

/-- A node recorded as no edge's child has no parent entry (membership form of the fresh
lookup). -/
private theorem unionFindParent_eq_none_ofNotChild :
    (links : List (Nat × Nat)) → (node : Nat) →
    (∀ edge ∈ links, edge.1 ≠ node) →
    unionFindParent links node = none
  | [], _, _ => rfl
  | (child, parent) :: rest, node, notChild => by
      show (if child == node then some parent else unionFindParent rest node) = none
      rw [show (child == node) = false from decide_eq_false
        (notChild (child, parent) (List.Mem.head rest))]
      exact unionFindParent_eq_none_ofNotChild rest node
        (fun edge edgeListed => notChild edge (List.Mem.tail (child, parent) edgeListed))

private theorem unionFindRoot_eq_self_ofParentNone :
    (fuel : Nat) → (links : List (Nat × Nat)) → (node : Nat) →
    unionFindParent links node = none →
    unionFindRoot fuel links node = node
  | 0, _, _, _ => rfl
  | fuel + 1, links, node, parentNone => by
      have oneStep : unionFindRoot (fuel + 1) links node
          = match unionFindParent links node with
            | none => node
            | some parent => unionFindRoot fuel links parent := rfl
      rw [oneStep, parentNone]

/-- **A node that is no recorded child is its own root** — the membership form of the
bound-based fresh-root lemma. -/
theorem unionFindRootOf_eq_self_ofUntouched (links : List (Nat × Nat)) (node : Nat)
    (notChild : ∀ edge ∈ links, edge.1 ≠ node) :
    unionFindRootOf links node = node :=
  unionFindRoot_eq_self_ofParentNone (links.length + 1) links node
    (unionFindParent_eq_none_ofNotChild links node notChild)

/-- **Rigidity over closed links**: a connection from any probe to a node OUTSIDE the node
set forces equality — the outside node is its own root, and the probe's root is either the
probe itself or an in-set parent value (which the outside node is not). -/
theorem nodesEqual_ofConnectedToUntouched (nodeSet : Nat → Prop)
    (links : List (Nat × Nat))
    (linksClosed : ∀ edge ∈ links, nodeSet edge.1 ∧ nodeSet edge.2)
    (probeNode untouchedNode : Nat)
    (untouched : ¬ nodeSet untouchedNode)
    (connected : isSameComponent links probeNode untouchedNode = true) :
    probeNode = untouchedNode := by
  have rootsEqual : unionFindRootOf links probeNode = unionFindRootOf links untouchedNode :=
    of_decide_eq_true connected
  rw [unionFindRootOf_eq_self_ofUntouched links untouchedNode
    (fun edge edgeListed childEq =>
      untouched (childEq ▸ (linksClosed edge edgeListed).1))] at rootsEqual
  cases unionFindRootOf_eq_self_or_parentValue links probeNode with
  | inl rootSelf =>
      rw [rootSelf] at rootsEqual
      exact rootsEqual
  | inr parentValue =>
      obtain ⟨edge, edgeListed, rootEq⟩ := parentValue
      rw [rootEq] at rootsEqual
      exact absurd (rootsEqual ▸ (linksClosed edge edgeListed).2) untouched

/-- ★ **Untouched-probe rigidity for the empty-base fold**: a trace whose event nodes all lie
in a node set can connect a probe to a node outside the set only if they are equal — the
vacuous-case discharger for the interface transfer's segment hypothesis. -/
theorem nodesEqual_ofFoldConnectedToUntouched (nodeSet : Nat → Prop)
    (events : List (Nat × Nat))
    (eventsClosed : ∀ pair ∈ events, nodeSet pair.1 ∧ nodeSet pair.2)
    (probeNode untouchedNode : Nat)
    (untouched : ¬ nodeSet untouchedNode)
    (connected : isSameComponent (applyJoinEvents events []) probeNode untouchedNode = true) :
    probeNode = untouchedNode :=
  nodesEqual_ofConnectedToUntouched nodeSet (applyJoinEvents events [])
    (applyJoinEvents_preservesNodeClosure nodeSet events [] eventsClosed
      (fun edge edgeListed => by cases edgeListed))
    probeNode untouchedNode untouched connected

/-- The flipped reading (untouched node on the left). -/
theorem nodesEqual_ofUntouchedFoldConnected (nodeSet : Nat → Prop)
    (events : List (Nat × Nat))
    (eventsClosed : ∀ pair ∈ events, nodeSet pair.1 ∧ nodeSet pair.2)
    (untouchedNode probeNode : Nat)
    (untouched : ¬ nodeSet untouchedNode)
    (connected : isSameComponent (applyJoinEvents events []) untouchedNode probeNode = true) :
    untouchedNode = probeNode :=
  (nodesEqual_ofFoldConnectedToUntouched nodeSet events eventsClosed probeNode untouchedNode
    untouched
    (isSameComponent_flip (applyJoinEvents events []) untouchedNode probeNode connected)).symm

/-! ## Honesty marker -/

/-- **Honesty marker — the fold support closure and untouched-probe rigidity are SHIPPED.**
Fold entries stay inside any node set closed over the trace and base, so probes outside the
trace's node set are rigid: empty-base fold connectivity to them forces equality.  This
discharges the vacuous below-base cases of the interface transfer's segment hypothesis (gamma-
interior wires untouched by the second-half traces).  NOT yet shipped: the D5 instantiation
assembling `Corresponds` and the boundary-image transfer.  `= true`. -/
def fxMode_hasFoldSupportRigidity : Bool := true

end FX1Poly.Polygraph

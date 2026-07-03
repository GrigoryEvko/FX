import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence

/-! # mode-3 keystone — the same-component algebra of the union-find join

The block-swap witness's `componentComm` field is the join-order INDEPENDENCE of the partition — comparing the
same-component view after two DIFFERENT join sequences.  The root-after-join characterization
(`unionFindRootOf_unionFindJoin`) speaks in nested root-ifs, which compose badly across reordered joins; this
file ships the SEMANTIC form the reorder bashes consume:

  ★ `isSameComponent_unionFindJoin` — the flat-disjunction characterization: after joining
    `firstNode`/`secondNode`, two probes share a component iff they already did, or one sat with `firstNode`
    and the other with `secondNode`.  Forest-conditioned; a nine-leaf boolean case tree whose inconsistent
    leaves are refuted by root-equality transitivity.
  ★ `unionFindJoin_ofSameComponent` + `stepCap_links_eq_unionFindJoin` — the join's built-in no-op test makes
    the cap's OUTER same-component test redundant for `links`: every fold step's link update is a UNIFORM
    `unionFindJoin` (cup on the fresh legs, cap on the read wires) — the event fold is join-homogeneous.
  ★ `isSameComponent_self` / `_symm` / `_trans` — the equivalence-relation kit the reorder bashes discharge
    their inconsistent branches with.

Raw Lean 4 + Init; `decide`-level boolean reasoning (`of_decide_eq_true` / `decide_eq_true`), no `omega` /
`simp`-AC.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## The equivalence-relation kit -/

/-- Same-component is reflexive. -/
theorem isSameComponent_self (links : List (Nat × Nat)) (node : Nat) :
    isSameComponent links node node = true :=
  decide_eq_true rfl

/-- Same-component is symmetric. -/
theorem isSameComponent_symm (links : List (Nat × Nat)) (firstNode secondNode : Nat) :
    isSameComponent links firstNode secondNode = isSameComponent links secondNode firstNode := by
  cases hforward : isSameComponent links firstNode secondNode with
  | true => exact (decide_eq_true (of_decide_eq_true hforward).symm).symm
  | false =>
      exact (decide_eq_false
        (fun rootsEq => of_decide_eq_false hforward rootsEq.symm)).symm

/-- Same-component is transitive. -/
theorem isSameComponent_trans (links : List (Nat × Nat)) (firstNode middleNode lastNode : Nat)
    (firstMiddle : isSameComponent links firstNode middleNode = true)
    (middleLast : isSameComponent links middleNode lastNode = true) :
    isSameComponent links firstNode lastNode = true :=
  decide_eq_true ((of_decide_eq_true firstMiddle).trans (of_decide_eq_true middleLast))

/-! ## The join fold is join-homogeneous -/

/-- Joining two already-connected nodes is a no-op (the join's internal test). -/
theorem unionFindJoin_ofSameComponent (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (sameComponent : isSameComponent links firstNode secondNode = true) :
    unionFindJoin links firstNode secondNode = links := by
  have rootsEqTrue : (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true :=
    sameComponent
  dsimp only [unionFindJoin]
  rw [rootsEqTrue]
  rfl

/-- ★ **The cap's link update is an UNCONDITIONAL join** — the outer same-component test (which drives the
loop count) is redundant for `links`, because `unionFindJoin` performs the same test internally.  So every
fold step's link update is a uniform `unionFindJoin`: the cup on its two fresh legs, the cap on its two read
wires — the partition evolution is a homogeneous join fold over the read pairs. -/
theorem stepCap_links_eq_unionFindJoin (state : WireState) (position : Nat) :
    (stepCap state position).links
      = unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) := by
  rw [stepCap_links]
  cases htest : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) with
  | true =>
      exact (unionFindJoin_ofSameComponent state.links _ _ htest).symm
  | false => rfl

/-! ## The flat-disjunction characterization of the join -/

/-- ★ **The same-component view after a join, as a flat disjunction.**  After joining
`firstNode`/`secondNode` (forest-conditioned), two probes share a component iff they ALREADY did, or
`probeOne` sat with `firstNode` and `probeTwo` with `secondNode`, or vice versa.  The semantic replacement
for composing nested `unionFindRootOf_unionFindJoin` root-ifs — everything the join-reorder bashes
(`componentComm` of the block swap) read off the partition goes through this one equation.  The mixed
argument orientations match the root-if conditions exactly, so every leaf of the nine-leaf case tree reduces
definitionally; the two inconsistent leaves are refuted by root-equality transitivity. -/
theorem isSameComponent_unionFindJoin (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstNode secondNode probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) probeOne probeTwo
      = (isSameComponent links probeOne probeTwo
          || (isSameComponent links firstNode probeOne && isSameComponent links secondNode probeTwo)
          || (isSameComponent links firstNode probeTwo && isSameComponent links probeOne secondNode)) := by
  show (unionFindRootOf (unionFindJoin links firstNode secondNode) probeOne
        == unionFindRootOf (unionFindJoin links firstNode secondNode) probeTwo)
      = ((unionFindRootOf links probeOne == unionFindRootOf links probeTwo)
          || ((unionFindRootOf links firstNode == unionFindRootOf links probeOne)
              && (unionFindRootOf links secondNode == unionFindRootOf links probeTwo))
          || ((unionFindRootOf links firstNode == unionFindRootOf links probeTwo)
              && (unionFindRootOf links probeOne == unionFindRootOf links secondNode)))
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode probeOne forest,
    unionFindRootOf_unionFindJoin links firstNode secondNode probeTwo forest]
  cases hfirstOne : unionFindRootOf links firstNode == unionFindRootOf links probeOne with
  | true =>
      cases hfirstTwo : unionFindRootOf links firstNode == unionFindRootOf links probeTwo with
      | true =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true => exact decide_eq_true rfl
          | false =>
              exact absurd ((of_decide_eq_true hfirstOne).symm.trans (of_decide_eq_true hfirstTwo))
                (of_decide_eq_false hprobes)
      | false =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true =>
              exact absurd ((of_decide_eq_true hfirstOne).trans (of_decide_eq_true hprobes))
                (of_decide_eq_false hfirstTwo)
          | false =>
              cases hsecondTwo : unionFindRootOf links secondNode == unionFindRootOf links probeTwo with
              | true => exact hsecondTwo
              | false => exact hsecondTwo
  | false =>
      cases hfirstTwo : unionFindRootOf links firstNode == unionFindRootOf links probeTwo with
      | true =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true =>
              exact absurd ((of_decide_eq_true hfirstTwo).trans (of_decide_eq_true hprobes).symm)
                (of_decide_eq_false hfirstOne)
          | false => rfl
      | false =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true => exact hprobes
          | false => exact hprobes

/-! ## Honesty marker -/

/-- **Honesty marker — the same-component join algebra is PROVED.**  The flat-disjunction characterization
(`isSameComponent_unionFindJoin`, forest-conditioned), the join-homogeneity of the fold's link updates
(`stepCap_links_eq_unionFindJoin` — the cap's outer test is redundant for `links`), and the
equivalence-relation kit (`_self` / `_symm` / `_trans`).  This is the algebra the block-swap witness's
`componentComm` reorder bash reads the partition through: expanding both run orders' joins by the
characterization reduces join-order independence to a boolean-lattice identity over base-partition atoms,
with inconsistent branches refuted by the kit.  That reorder bash — and the `loopsEq` exchange it powers —
is the next brick; see `fxMode_hasMatchingComponentCoreSwapWitness`.  `= true`. -/
def fxMode_hasSameComponentJoinAlgebra : Bool := true

end FX1Poly.Tier0

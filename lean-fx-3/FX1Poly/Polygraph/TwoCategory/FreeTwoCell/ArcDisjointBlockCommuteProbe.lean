import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # mode-3 floor — the path-factoring atom + the disjoint-block commutation, with the negative control

`FreeTwoCellMatchingComponentAlgebra` ships `isSameComponent_unionFindJoin_swap`: swapping two adjacent
`unionFindJoin`s leaves the same-component (PARTITION) view pointwise EQUAL, forest-conditioned on the base.  That
is the path-factoring atom the block-swap commutation rides.  The recon flagged that this atom is UNCONDITIONAL on
disjointness (partition = transitive closure) and demanded the negative control be probed: does the
partition-level commutation actually FAIL for non-disjoint blocks?

This file adjudicates that, honestly, by machine:

  ★ **positive control (disjoint blocks).**  Transposing the disjoint joins `(0, 1)` and `(2, 3)` commutes at the
    partition level (`isSameComponent_unionFindJoin_swap`, fired on the empty forest).

  ★ **the negative control, RE-ADJUDICATED (non-disjoint blocks STILL commute at the partition level).**  The
    recon's provisional statement "non-disjoint blocks must NOT commute at partition level" is FALSE: transposing
    the SHARING joins `(0, 1)` and `(0, 2)` — which both touch node `0` — STILL commutes at the partition level,
    because the partition is the transitive closure and both orders close the same component `{0, 1, 2}`.  The
    swap atom holds for them by the very same unconditional lemma.

  ★ **where disjointness (really: join order) IS load-bearing — the ROOT level.**  The union-find ROOTS of the
    merged component DIFFER between the two orders (`unionFindJoin` points the first argument's root at the
    second): the `(0,1)`-then-`(0,2)` order roots the component at `2`, the `(0,2)`-then-`(0,1)` order at `1`.
    So a ROOT-level formulation of the block swap is false even when the PARTITION-level one is true — the
    machine-witness of why the whole route must read the partition (`isSameComponent`), never the root.

Raw Lean 4 + Init; the partition-level commutations are direct applications of the shipped swap atom, the
root-flip is `decide` on the two SMALL concrete link lists.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Positive control — disjoint blocks commute at the partition level -/

/-- ★ **Disjoint block swap commutes at the partition level.**  Transposing the disjoint joins `(0, 1)` and
`(2, 3)` leaves the same-component view of any two probes unchanged — the path-factoring atom
`isSameComponent_unionFindJoin_swap` on the empty forest. -/
theorem arcDisjointBlockPartitionCommutes (probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin [] 0 1) 2 3) probeOne probeTwo
      = isSameComponent (unionFindJoin (unionFindJoin [] 2 3) 0 1) probeOne probeTwo :=
  isSameComponent_unionFindJoin_swap [] isUnionFindForest_nil 0 1 2 3 probeOne probeTwo

/-! ## The negative control, re-adjudicated — non-disjoint blocks STILL commute at the partition level -/

/-- ★ **Non-disjoint block swap STILL commutes at the partition level.**  Transposing the SHARING joins `(0, 1)`
and `(0, 2)` — both touch node `0` — leaves the same-component view of any two probes unchanged, by the SAME
unconditional swap atom.  This refutes the recon's provisional "non-disjoint blocks must NOT commute at the
partition level": the partition is the transitive closure, so join order (disjoint or not) is invisible to it. -/
theorem arcNonDisjointBlockPartitionCommutes (probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin [] 0 1) 0 2) probeOne probeTwo
      = isSameComponent (unionFindJoin (unionFindJoin [] 0 2) 0 1) probeOne probeTwo :=
  isSameComponent_unionFindJoin_swap [] isUnionFindForest_nil 0 1 0 2 probeOne probeTwo

/-! ## Where join order IS load-bearing — the root level (the root-flip) -/

/-- ★ **Root-level block swap FAILS for the non-disjoint blocks (the root-flip).**  While the partition view is
order-invariant, the union-find ROOT of the merged component `{0, 1, 2}` is `2` in the `(0,1)`-then-`(0,2)` order
but `1` in the `(0,2)`-then-`(0,1)` order — `unionFindJoin` points the first argument's root at the second's.  So
a root-level formulation of the block swap is refuted where the partition-level one holds; kernel-decided on the
two small concrete link lists. -/
theorem arcNonDisjointRootLevelDiffers :
    unionFindRootOf (unionFindJoin (unionFindJoin [] 0 1) 0 2) 0
      ≠ unionFindRootOf (unionFindJoin (unionFindJoin [] 0 2) 0 1) 0 := by
  decide

/-- The two merged roots, made explicit: `2` vs `1` — the flip that root-level commutation would (falsely)
require to be equal. -/
theorem arcNonDisjointRoots :
    unionFindRootOf (unionFindJoin (unionFindJoin [] 0 1) 0 2) 0 = 2
      ∧ unionFindRootOf (unionFindJoin (unionFindJoin [] 0 2) 0 1) 0 = 1 := by
  decide

/-! ## Honesty marker -/

/-- **Honesty marker — the disjoint-block commutation is probed, the negative control RE-ADJUDICATED.**  The
path-factoring atom `isSameComponent_unionFindJoin_swap` commutes the partition view for BOTH disjoint blocks
(`arcDisjointBlockPartitionCommutes`) and — refuting the recon's provisional negative-control statement —
non-disjoint blocks (`arcNonDisjointBlockPartitionCommutes`), because the partition is the transitive closure and
is unconditionally invisible to join order.  Disjointness (really: join order) IS load-bearing only at the ROOT
level: `arcNonDisjointRootLevelDiffers` / `arcNonDisjointRoots` decide the root-flip `2 ≠ 1`, the machine-witness
that the block-swap route must read the partition (`isSameComponent`), never the root.  `= true`. -/
def fxMode_hasArcDisjointBlockCommuteProbe : Bool := true

end FX1Poly.Polygraph

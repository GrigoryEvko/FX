import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # UnionFindFloorAbove — a root stays AT OR ABOVE the floor when no edge crosses it

`ArcSwapRenameable` ships the BELOW-floor locality of the union-find root: when every edge's parent lies
strictly below a bound, a below-bound node's root stays below the bound (`unionFindRoot_lt_of_below` /
`unionFindRootOf_lt_of_fresh`) — the fact that an old node's component root is an old node.  The valley
classification also needs the DUAL, for the cup-leg direction: a cup leg (a fresh node `≥ bc`) keeps its
root `≥ bc`.

The clean hypothesis is FLOOR-HOMOGENEITY of the edges: no valley edge crosses the floor — a cap edge
joins two old nodes (both `< bc`), a cup edge joins two fresh legs (both `≥ bc`).  Equivalently, every
edge whose CHILD sits at or above the floor has its PARENT at or above the floor too.  Under that single
condition, root-following from an at-or-above-floor node never descends below the floor: each parent step
lands on an edge whose child is the current (≥ floor) node, so its parent is `≥ floor`.

  * `unionFindParent_ge` — one parent step from an `≥ floor` node lands `≥ floor` (the edge dual of
    `unionFindParent_below`).
  * `unionFindRoot_ge_of_edgesPreserveFloor` — fuel-bounded root-following stays `≥ floor` (the dual of
    `unionFindRoot_lt_of_below`).
  * `unionFindRootOf_ge_of_edgesPreserveFloor` — the packaged root form (the dual of
    `unionFindRootOf_lt_of_fresh`).

Raw Lean 4 + Init; structural on the edge list then fuel recursion, no `omega` / `simp`-AC /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **One parent step from an at-or-above-floor node lands at or above the floor.**  When every edge
whose child is `≥ bound` has its parent `≥ bound` (floor-homogeneity), and `node ≥ bound` has a recorded
parent, that parent is `≥ bound`: the matching edge's child IS `node`, itself `≥ bound`, so the edge's
parent is `≥ bound`.  Structural on the edge list; the edge dual of `unionFindParent_below`. -/
theorem unionFindParent_ge (bound : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, bound ≤ edge.1 → bound ≤ edge.2) →
    (node parent : Nat) → bound ≤ node → unionFindParent links node = some parent → bound ≤ parent
  | [], _, node, parent, _, h => by
      rw [show unionFindParent ([] : List (Nat × Nat)) node = none from rfl] at h
      nomatch h
  | (child, par) :: rest, edgesPreserve, node, parent, boundLeNode, h => by
      have hh : (if child == node then some par else unionFindParent rest node) = some parent := h
      cases hcn : child == node with
      | true =>
          rw [hcn] at hh
          have childEqNode : child = node := of_decide_eq_true hcn
          have boundLeChild : bound ≤ child := Nat.le_trans boundLeNode (Nat.le_of_eq childEqNode.symm)
          rw [← Option.some.inj hh]
          exact edgesPreserve (child, par) (List.Mem.head _) boundLeChild
      | false =>
          rw [hcn] at hh
          exact unionFindParent_ge bound rest
            (fun edge edgeInRest => edgesPreserve edge (List.Mem.tail _ edgeInRest)) node parent
            boundLeNode hh

/-- ★ **Root-following stays at or above the floor.**  Under floor-homogeneity of the edges (every edge
whose child is `≥ bound` has parent `≥ bound`), a node `≥ bound` has `unionFindRoot fuel links node ≥
bound`: each descent step lands on the recorded parent, itself `≥ bound` by `unionFindParent_ge`.  Fuel
induction; the dual of `unionFindRoot_lt_of_below`. -/
theorem unionFindRoot_ge_of_edgesPreserveFloor (links : List (Nat × Nat)) (bound : Nat)
    (edgesPreserve : ∀ edge ∈ links, bound ≤ edge.1 → bound ≤ edge.2) :
    (fuel node : Nat) → bound ≤ node → bound ≤ unionFindRoot fuel links node
  | 0, _, h => h
  | fuel + 1, node, h => by
      show bound ≤ (match unionFindParent links node with
            | none => node | some parent => unionFindRoot fuel links parent)
      cases hp : unionFindParent links node with
      | none => exact h
      | some parent =>
          exact unionFindRoot_ge_of_edgesPreserveFloor links bound edgesPreserve fuel parent
            (unionFindParent_ge bound links edgesPreserve node parent h hp)

/-- ★ **A node's root stays at or above the floor** (packaged form).  Under floor-homogeneity of the
edges, every `node ≥ bound` has `unionFindRootOf links node ≥ bound` — a fresh cup leg (`≥ bc`) keeps its
component root `≥ bc`, disjoint from every old (below-`bc`) root.  The dual of `unionFindRootOf_lt_of_fresh`
and the cup-leg root-separation the valley classification's cup direction needs. -/
theorem unionFindRootOf_ge_of_edgesPreserveFloor (links : List (Nat × Nat)) (bound : Nat)
    (edgesPreserve : ∀ edge ∈ links, bound ≤ edge.1 → bound ≤ edge.2) (node : Nat) (h : bound ≤ node) :
    bound ≤ unionFindRootOf links node :=
  unionFindRoot_ge_of_edgesPreserveFloor links bound edgesPreserve (links.length + 1) node h

/-! ## Honesty marker -/

/-- **Honesty marker — the AT-OR-ABOVE-floor root locality is SHIPPED (the cup-leg root-separation
kernel).**  Landed here, all zero-axiom, the exact dual of the shipped below-floor locality
(`unionFindRoot_lt_of_below` / `unionFindRootOf_lt_of_fresh`):

  * `unionFindParent_ge`, `unionFindRoot_ge_of_edgesPreserveFloor`,
    `unionFindRootOf_ge_of_edgesPreserveFloor` — under floor-homogeneity of the edges (no edge crosses the
    floor: every edge whose child is `≥ bound` has parent `≥ bound`), an at-or-above-floor node keeps its
    root at or above the floor.

This is the reusable union-find kernel of the classification's CUP-LEG direction (N2): a cup leg's root
stays `≥ bc`, disjoint from every below-`bc` bottom root, so a cup-leg top port's whole bottom-front
misses and its partner is another TOP.  What this marker does NOT itself close: the floor-homogeneity
INVARIANT for the whole valley's links (`∀ edge ∈ (processSpine capState cupBlock).links, bc ≤ edge.1 → bc
≤ edge.2`) — that cap-block edges join old nodes both `< bc` and cup-block edges join fresh legs both `≥
bc` — which requires threading `WireStateFresh` + forest through the cup fold (the invariant-threading port
the classification assembly consumes).  No gate flag is flipped.  `= true`. -/
def fxMode_hasUnionFindFloorAbove : Bool := true

end FX1Poly.Polygraph

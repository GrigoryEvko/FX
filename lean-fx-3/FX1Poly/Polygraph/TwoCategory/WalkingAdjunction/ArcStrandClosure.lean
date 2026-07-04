import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcStrandClosure — a closed strand's component never grows

When a cap consumes its two wires, the merged strand (the two wires plus the cap's event
node) leaves the open boundary: no later step can reach it, because every later join's
endpoints are current open wires or freshly allocated nodes.  This file ships the substrate
for that argument: the AVOIDED-JOIN workhorse (a join whose endpoints both miss an anchor's
component leaves every query against that anchor unchanged — the two spurious disjuncts of
the Boolean join characterization die on the avoidance facts), the `ArcStrandClosure`
invariant (the anchor's component misses every open wire and every future-fresh node), and
the per-step QUERY STABILITY computations: a cup or cap step fired at a state satisfying the
avoidance premises changes no query against the anchor.  The field preservations, the
whole-spine fold, the cap-head seed instantiation, and the zero evaluation of the cap head's
event term all consume these in the next rungs.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The avoided-join workhorse -/

/-- ★ **An avoided join changes no query against the anchor**: when both join endpoints miss
the anchor's component, every same-component query against the anchor answers as before —
the join characterization's two mixed disjuncts die on the avoidance facts. -/
theorem isSameComponent_unionFindJoin_ofAvoided (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight anchorNode probeNode : Nat)
    (missesLeft : isSameComponent links anchorNode joinLeft = false)
    (missesRight : isSameComponent links anchorNode joinRight = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) anchorNode probeNode
      = isSameComponent links anchorNode probeNode := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight anchorNode probeNode,
    isSameComponent_symm links joinLeft anchorNode, missesLeft, missesRight]
  cases baseQuery : isSameComponent links anchorNode probeNode with
  | true =>
      cases leftLegQuery : isSameComponent links joinLeft probeNode with
      | true => rfl
      | false => rfl
  | false =>
      cases leftLegQuery : isSameComponent links joinLeft probeNode with
      | true => rfl
      | false => rfl

/-! ## The closed-strand invariant -/

/-- **The closed-strand invariant**: the anchor's component misses every open wire and every
node at or above the allocation frontier.  Since each fold step joins only open-wire reads
and fresh allocations, such an anchor's component can never grow — its queries stay stable
through the whole run (the fold rung concludes exactly that). -/
structure ArcStrandClosure (anchorNode : Nat) (state : ArcWireState) : Prop where
  /-- The anchor's component misses every current open wire. -/
  missesOpenWires : ∀ position, position < state.openWires.length →
    isSameComponent state.links anchorNode
      (natListGetAt state.openWires position) = false
  /-- The anchor's component misses every node at or above the allocation frontier. -/
  missesFreshNodes : ∀ freshNode, state.nextFresh ≤ freshNode →
    isSameComponent state.links anchorNode freshNode = false

/-! ## Per-step query stability -/

/-- **A cup step changes no query against a closed anchor**: both its joins touch only fresh
nodes (the two legs and the event), which the anchor misses. -/
theorem isSameComponent_stepCupArc_queriesStable (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (missesFreshNodes : ∀ freshNode, state.nextFresh ≤ freshNode →
      isSameComponent state.links anchorNode freshNode = false)
    (probeNode : Nat) :
    isSameComponent (stepCupArc state position).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode := by
  have innerAvoided : ∀ innerProbe : Nat,
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          anchorNode innerProbe
        = isSameComponent state.links anchorNode innerProbe :=
    fun innerProbe =>
      isSameComponent_unionFindJoin_ofAvoided state.links forest
        state.nextFresh (state.nextFresh + 1) anchorNode innerProbe
        (missesFreshNodes state.nextFresh (Nat.le_refl state.nextFresh))
        (missesFreshNodes (state.nextFresh + 1) (Nat.le_add_right state.nextFresh 1))
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) anchorNode probeNode
    = isSameComponent state.links anchorNode probeNode
  exact (isSameComponent_unionFindJoin_ofAvoided
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
        forest)
      (state.nextFresh + 2) state.nextFresh anchorNode probeNode
      ((innerAvoided (state.nextFresh + 2)).trans
        (missesFreshNodes (state.nextFresh + 2) (Nat.le_add_right state.nextFresh 2)))
      ((innerAvoided state.nextFresh).trans
        (missesFreshNodes state.nextFresh (Nat.le_refl state.nextFresh)))).trans
    (innerAvoided probeNode)

/-- **A cap step changes no query against a closed anchor**: its joins touch only the two
read wires (which the anchor misses by the read premises) and the fresh event node. -/
theorem isSameComponent_stepCapArc_queriesStable (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (missesLeftRead : isSameComponent state.links anchorNode
      (natListGetAt state.openWires position) = false)
    (missesRightRead : isSameComponent state.links anchorNode
      (natListGetAt state.openWires (position + 1)) = false)
    (missesFreshNodes : ∀ freshNode, state.nextFresh ≤ freshNode →
      isSameComponent state.links anchorNode freshNode = false)
    (probeNode : Nat) :
    isSameComponent (stepCapArc state position).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode := by
  have innerAvoided : ∀ innerProbe : Nat,
      isSameComponent
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          anchorNode innerProbe
        = isSameComponent state.links anchorNode innerProbe :=
    fun innerProbe =>
      isSameComponent_unionFindJoin_ofAvoided state.links forest
        (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) anchorNode innerProbe
        missesLeftRead missesRightRead
  show isSameComponent
      (unionFindJoin
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position)) anchorNode probeNode
    = isSameComponent state.links anchorNode probeNode
  exact (isSameComponent_unionFindJoin_ofAvoided
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      (isUnionFindForest_unionFindJoin state.links
        (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) forest)
      state.nextFresh (natListGetAt state.openWires position) anchorNode probeNode
      ((innerAvoided state.nextFresh).trans
        (missesFreshNodes state.nextFresh (Nat.le_refl state.nextFresh)))
      ((innerAvoided (natListGetAt state.openWires position)).trans missesLeftRead)).trans
    (innerAvoided probeNode)

/-! ## Honesty marker -/

/-- **Honesty marker — the closed-strand substrate (peel campaign H, strand-closure rung 1).**
The avoided-join workhorse (a join both of whose endpoints miss an anchor's component changes
no query against it), the `ArcStrandClosure` invariant (the anchor misses every open wire and
every future-fresh node), and the per-step query-stability computations at cup and cap steps
(the cap's read premises stated directly — the invariant's field discharges them once the
window bound is threaded).  What this marker does NOT claim: the field preservations and the
whole-spine fold, the cap-head seed instantiation, and the resulting ZERO evaluation of the
cap head's event term in the count decomposition.  `= true`. -/
def fxMode_hasArcStrandClosureSubstrate : Bool := true

end FX1Poly.Polygraph

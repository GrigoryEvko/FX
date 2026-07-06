import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # The cup event node sits with its legs — the boundary-index → cup-atom inversion foundation

`stepCupArc` allocates two fresh connected leg wires (`nextFresh`, `nextFresh + 1`) plus one fresh
**event node** (`nextFresh + 2`) and unions the event node into the cup's component.  Its `links` field is
the two nested joins

  `unionFindJoin (unionFindJoin state.links leftLeg rightLeg) eventNode leftLeg`

— the INNER join relates the two legs, the OUTER join relates the event node to the left leg.  This file
reads that connectivity back off the partition: the event node lands in the SAME connected component as both
legs.  That is the identifying fact the cup-atom inversion needs — the event node in `cupEventNodes`
identifies WHICH cup a boundary port's strand turns back on, and the legs carry the window.

Both statements are conditioned on `isUnionFindForest state.links` — the acyclicity the whole spine fold
maintains (`isUnionFindForest_stepCupArc`, and from the empty initial `links` up).  The condition is
essential, not cosmetic: on a cyclic `links` the fuel-bounded root walk can stop mid-cycle, so the
join's "joined pair share a component" fact (`isSameComponent_unionFindJoin_joined`) is itself
forest-conditioned.  Every state reachable in the fold discharges it.

Raw Lean 4 + Init; the outer join is read off by `isSameComponent_unionFindJoin_joined`, the inner-then-outer
survival by `isSameComponent_unionFindJoin_ofBase`, both from the shipped same-component join algebra.
`propext`-free. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup event node shares its LEFT leg's component after `stepCupArc`.**  The step's `links` is
`unionFindJoin (unionFindJoin state.links leftLeg rightLeg) eventNode leftLeg`; the OUTER join relates
`eventNode` (`nextFresh + 2`) to `leftLeg` (`nextFresh`) directly, read off by the join's built-in
"joined pair share a component" fact on a forest — the inner join is again a forest
(`isUnionFindForest_unionFindJoin`), so the outer join's `isSameComponent_unionFindJoin_joined` fires.  This
is the primitive: the fresh event node lands on the cup's left leg, identifying the cup atom the leg
belongs to. -/
theorem arcCupEventNode_sameComponent_leftLeg (state : ArcWireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCupArc state windowPosition).links
      (state.nextFresh + 2) state.nextFresh = true := by
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh)
      (state.nextFresh + 2) state.nextFresh = true
  exact isSameComponent_unionFindJoin_joined
    (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
    (isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest)
    (state.nextFresh + 2) state.nextFresh

/-- ★ **The cup event node shares its RIGHT leg's component after `stepCupArc`.**  The event node sits with
the left leg (the outer join, `arcCupEventNode_sameComponent_leftLeg`), and the two legs sit together in the
inner join (`isSameComponent_unionFindJoin_joined` on `state.links`), which SURVIVES the outer join
(`isSameComponent_unionFindJoin_ofBase`, the inner join being a forest).  Transitivity closes
`eventNode ~ leftLeg ~ rightLeg`, so the event node lands on the WHOLE cup strand — either leg identifies it.
-/
theorem arcCupEventNode_sameComponent_rightLeg (state : ArcWireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCupArc state windowPosition).links
      (state.nextFresh + 2) (state.nextFresh + 1) = true := by
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh)
      (state.nextFresh + 2) (state.nextFresh + 1) = true
  have innerForest :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have eventLeftLeg :
      isSameComponent
        (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh)
        (state.nextFresh + 2) state.nextFresh = true :=
    isSameComponent_unionFindJoin_joined
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) innerForest
      (state.nextFresh + 2) state.nextFresh
  have legsInner :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh (state.nextFresh + 1) = true :=
    isSameComponent_unionFindJoin_joined state.links forest state.nextFresh (state.nextFresh + 1)
  have legsOuter :
      isSameComponent
        (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh)
        state.nextFresh (state.nextFresh + 1) = true :=
    isSameComponent_unionFindJoin_ofBase
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) innerForest
      (state.nextFresh + 2) state.nextFresh state.nextFresh (state.nextFresh + 1) legsInner
  exact isSameComponent_trans
    (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh)
    (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) eventLeftLeg legsOuter

/-- **Honesty marker — the cup event node's component is READ OFF, both legs, forest-conditioned.**  After
`stepCupArc`, the fresh event node (`nextFresh + 2`) shares a connected component with BOTH the left leg
(`nextFresh`, the outer join) and the right leg (`nextFresh + 1`, transitively through the inner join),
under the spine fold's maintained acyclicity `isUnionFindForest state.links`.  This is the identifying fact
of the boundary-index → cup-atom inversion: the event node in `cupEventNodes` pins the cup whose strand a
boundary port turns back on.  `= true`. -/
def fxMode_hasArcCupEventNodeLegComponent : Bool := true

end FX1Poly.Polygraph

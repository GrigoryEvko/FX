import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility

/-! # ArcCupLegSeparation — the cup's fresh strand contains no old nodes (peel campaign H, cup rung 2d-iii prep)

The cup census preservation classifies each boundary end of the stepped state by its node:
either an OLD node (below `nextFresh` — a surviving wire or a bottom port) or a node of the
freshly-created leg strand.  The classification dispatch needs the separation fact: after a cup
step, no fresh-allocation node shares a component with any old node — the cup's two leg joins
touch only its own three fresh nodes.  This brick ships that separation:

  * a join of two at-or-above-bound nodes never relates an at-or-above-bound probe to a
    below-bound probe (`isSameComponent_unionFindJoin_offFreshPair`);
  * hence after a CUP step every fresh-allocation probe (`nextFresh`, `nextFresh + 1`, or the
    event node `nextFresh + 2`) is off every old probe's component, in both argument orders
    (`isSameComponent_stepCupArc_freshOldProbes` / `_oldFreshProbes`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ A join of two at-or-above-bound nodes never relates an at-or-above-bound probe to a
below-bound probe: the base view separates them (`isSameComponent_offFreshNode`), and both
cross disjuncts of the join characterization die on the join nodes' freshness. -/
theorem isSameComponent_unionFindJoin_offFreshPair (links : List (Nat × Nat)) (bound : Nat)
    (childrenBelow : ∀ edge ∈ links, edge.1 < bound)
    (parentsBelow : ∀ edge ∈ links, edge.2 < bound)
    (forest : isUnionFindForest links) (joinLeft joinRight freshProbe oldProbe : Nat)
    (joinLeftAtLeast : bound ≤ joinLeft) (joinRightAtLeast : bound ≤ joinRight)
    (freshAtLeast : bound ≤ freshProbe) (oldBelow : oldProbe < bound) :
    isSameComponent (unionFindJoin links joinLeft joinRight) freshProbe oldProbe = false := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight freshProbe oldProbe,
    isSameComponent_offFreshNode links bound childrenBelow parentsBelow freshProbe oldProbe
      freshAtLeast oldBelow,
    isSameComponent_offFreshNode links bound childrenBelow parentsBelow joinRight oldProbe
      joinRightAtLeast oldBelow,
    isSameComponent_offFreshNode links bound childrenBelow parentsBelow joinLeft oldProbe
      joinLeftAtLeast oldBelow]
  cases leftFreshTest : isSameComponent links joinLeft freshProbe with
  | true => rfl
  | false => rfl

/-- ★ **After a CUP step, fresh-allocation probes are off every old component.**  The two legs
and the event node (`nextFresh`, `nextFresh + 1`, `nextFresh + 2`) form their own strand: both
the leg join and the event join relate only fresh nodes, so no old node ever tests into the new
strand — the separation the census classification dispatches on. -/
theorem isSameComponent_stepCupArc_freshOldProbes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (freshProbe oldProbe : Nat) (freshAtLeast : state.nextFresh ≤ freshProbe)
    (oldBelow : oldProbe < state.nextFresh) :
    isSameComponent (stepCupArc state position).links freshProbe oldProbe = false := by
  obtain ⟨_openBelow, linksBelow, _cupBelow, _capBelow⟩ := fresh
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeInLinks => (linksBelow edge edgeInLinks).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (linksBelow edge edgeInLinks).2
  have innerFreshOld :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        freshProbe oldProbe = false :=
    isSameComponent_unionFindJoin_offFreshPair state.links state.nextFresh childrenBelow
      parentsBelow forest state.nextFresh (state.nextFresh + 1) freshProbe oldProbe
      (Nat.le_refl state.nextFresh) (Nat.le_succ state.nextFresh) freshAtLeast oldBelow
  have innerLeftLegOld :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh oldProbe = false :=
    isSameComponent_unionFindJoin_offFreshPair state.links state.nextFresh childrenBelow
      parentsBelow forest state.nextFresh (state.nextFresh + 1) state.nextFresh oldProbe
      (Nat.le_refl state.nextFresh) (Nat.le_succ state.nextFresh)
      (Nat.le_refl state.nextFresh) oldBelow
  have innerEventOld :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) oldProbe = false :=
    isSameComponent_unionFindJoin_offFreshPair state.links state.nextFresh childrenBelow
      parentsBelow forest state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2) oldProbe
      (Nat.le_refl state.nextFresh) (Nat.le_succ state.nextFresh)
      (Nat.le_add_right state.nextFresh 2) oldBelow
  have innerForest :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh)
      freshProbe oldProbe = false
  rw [isSameComponent_unionFindJoin
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) innerForest
      (state.nextFresh + 2) state.nextFresh freshProbe oldProbe,
    innerFreshOld, innerLeftLegOld, innerEventOld]
  cases eventFreshTest : isSameComponent
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) freshProbe with
  | true => rfl
  | false => rfl

/-- The separation in the other argument order: after a CUP step, old probes are off every
fresh-allocation probe's component. -/
theorem isSameComponent_stepCupArc_oldFreshProbes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (oldProbe freshProbe : Nat) (oldBelow : oldProbe < state.nextFresh)
    (freshAtLeast : state.nextFresh ≤ freshProbe) :
    isSameComponent (stepCupArc state position).links oldProbe freshProbe = false :=
  (isSameComponent_symm (stepCupArc state position).links oldProbe freshProbe).trans
    (isSameComponent_stepCupArc_freshOldProbes state position fresh forest freshProbe oldProbe
      freshAtLeast oldBelow)

/-- **Honesty marker — the cup leg separation is SHIPPED (peel campaign H, cup rung 2d-iii
prep).**  A join of two fresh nodes keeps fresh probes off old probes, and after a cup step no
fresh-allocation node shares a component with any old node, in both argument orders.  What this
marker does NOT claim: the cup census preservation itself (rung 2d-iii proper — the three-zone
token classification over the spliced open wires) and the fold transport (rung 2d-iv).
`= true`. -/
def fxMode_hasArcCupLegSeparation : Bool := true

end FX1Poly.Polygraph

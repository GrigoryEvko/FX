import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcComponentShiftCorr — the component leg of the head-cancellation simulation

The head-cancellation pair (peel campaign H) relates the composite run's links to the fresh
tail run's links: the composite state is the base state with ONE extra leg-join applied first,
transported through the fold under the positional reindexing `sigma`.  This file ships the
links-level invariant and its per-join preservation:

  * `ArcComponentShiftCorr sigma legLeft legRight baseLinks shiftedLinks` — every
    `sigma`-image same-component query on the shifted links reads as the base query over the
    base links WITH the leg-join applied;
  * `isSameComponent_unionFindJoin_mapTransport` — a corresponding join (`sigma`-image
    arguments on the shifted side) preserves any such pointwise correspondence, by pure
    rewriting through the Boolean join characterization `isSameComponent_unionFindJoin`;
  * `arcComponentShiftCorr_correspondingJoin` — the invariant survives one corresponding
    join: transport lands the new join INSIDE the leg-join, and the component-level join
    commutation `isSameComponent_unionFindJoin_swap` (MatchingComponentAlgebra) re-fronts the
    leg-join.  Join order is invisible at the partition level even though the raw link lists
    diverge — exactly the satisfiable component-level formulation the machine-checked
    list-level refutations force.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The component-leg invariant of the head cancellation.**  Every `sigma`-image
same-component query on the shifted links agrees with the base query over the base links with
the head's leg-join applied first. -/
def ArcComponentShiftCorr (sigma : Nat → Nat) (legLeft legRight : Nat)
    (baseLinks shiftedLinks : List (Nat × Nat)) : Prop :=
  ∀ probeLeft probeRight : Nat,
    isSameComponent shiftedLinks (sigma probeLeft) (sigma probeRight)
      = isSameComponent (unionFindJoin baseLinks legLeft legRight) probeLeft probeRight

/-- **A corresponding join preserves a pointwise `sigma` component correspondence.**  Both
sides expand through the Boolean join characterization into three disjuncts whose atoms are
plain same-component queries at `sigma`-image pairs; the correspondence rewrites each atom. -/
theorem isSameComponent_unionFindJoin_mapTransport (sigma : Nat → Nat)
    (baseLinks shiftedLinks : List (Nat × Nat))
    (baseForest : isUnionFindForest baseLinks)
    (shiftedForest : isUnionFindForest shiftedLinks)
    (componentCorr : ∀ probeLeft probeRight : Nat,
      isSameComponent shiftedLinks (sigma probeLeft) (sigma probeRight)
        = isSameComponent baseLinks probeLeft probeRight)
    (joinLeft joinRight probeLeft probeRight : Nat) :
    isSameComponent (unionFindJoin shiftedLinks (sigma joinLeft) (sigma joinRight))
        (sigma probeLeft) (sigma probeRight)
      = isSameComponent (unionFindJoin baseLinks joinLeft joinRight)
        probeLeft probeRight := by
  rw [isSameComponent_unionFindJoin shiftedLinks shiftedForest (sigma joinLeft)
      (sigma joinRight) (sigma probeLeft) (sigma probeRight),
    isSameComponent_unionFindJoin baseLinks baseForest joinLeft joinRight
      probeLeft probeRight,
    componentCorr probeLeft probeRight, componentCorr joinLeft probeLeft,
    componentCorr joinRight probeRight, componentCorr joinLeft probeRight,
    componentCorr probeLeft joinRight]

/-- ★ **The invariant survives one corresponding join.**  Transporting the new join through
the correspondence lands it INSIDE the leg-join (`join(join(base, legs), new)`); the
component-level join commutation re-fronts the leg-join to match the invariant's shape at the
new base links (`join(join(base, new), legs)`). -/
theorem arcComponentShiftCorr_correspondingJoin (sigma : Nat → Nat)
    (legLeft legRight : Nat) (baseLinks shiftedLinks : List (Nat × Nat))
    (baseForest : isUnionFindForest baseLinks)
    (shiftedForest : isUnionFindForest shiftedLinks)
    (corr : ArcComponentShiftCorr sigma legLeft legRight baseLinks shiftedLinks)
    (joinLeft joinRight : Nat) :
    ArcComponentShiftCorr sigma legLeft legRight
      (unionFindJoin baseLinks joinLeft joinRight)
      (unionFindJoin shiftedLinks (sigma joinLeft) (sigma joinRight)) := by
  intro probeLeft probeRight
  have legForest : isUnionFindForest (unionFindJoin baseLinks legLeft legRight) :=
    isUnionFindForest_unionFindJoin baseLinks legLeft legRight baseForest
  have transported := isSameComponent_unionFindJoin_mapTransport sigma
    (unionFindJoin baseLinks legLeft legRight) shiftedLinks legForest shiftedForest
    corr joinLeft joinRight probeLeft probeRight
  rw [transported]
  exact isSameComponent_unionFindJoin_swap baseLinks baseForest legLeft legRight
    joinLeft joinRight probeLeft probeRight

/-! ## Honesty marker -/

/-- **Honesty marker — the component-leg invariant's PER-JOIN preservation is SHIPPED (peel
campaign H, rung 2 core).**  `ArcComponentShiftCorr` (shifted components = base components
with the head's leg-join re-fronted, under `sigma`), the pure-rewrite join transport, and the
corresponding-join preservation riding `isSameComponent_unionFindJoin_swap` — the EXISTING
component-level join commutation from `MatchingComponentAlgebra` (near-duplicated this rung
and caught: scout multi-line signatures by NAME, not by statement shape).  What this marker
does NOT claim: the cup/cap step lemmas over `ArcWireState` (the join arguments read as
`sigma`-images through `openMap` need the in-range wire-read plumbing), the fold, the seed
instantiation, and the extract correspondence.  `= true`. -/
def fxMode_hasArcComponentShiftCorr : Bool := true

end FX1Poly.Polygraph

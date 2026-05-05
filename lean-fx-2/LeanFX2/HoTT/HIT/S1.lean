import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/S1

Setoid-level presentation of the circle HIT.

This module records the circle's point/path labels and exposes the
0-truncated setoid presentation with one representative and one loop
relation witness.

This is not the full circle HIT: it does not model nontrivial loop
transport or the fundamental group.  Those require a richer path
algebra than the current `HITSetoid` foundation.  The purpose here is
to make the base/loop wiring load-bearing without importing axioms.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe resultLevel

/-- Point labels for the circle HIT. -/
inductive S1PointLabel : Type where
  | base : S1PointLabel

/-- Path labels for the circle HIT. -/
inductive S1PathLabel : Type where
  | loop : S1PathLabel

/-- First-order HIT specification for the circle: one point and one
loop path from that point to itself. -/
def S1Spec : HITSpec where
  pointLabel := S1PointLabel
  pathLabel := S1PathLabel
  pathSource := fun
    | S1PathLabel.loop => S1PointLabel.base
  pathTarget := fun
    | S1PathLabel.loop => S1PointLabel.base

namespace S1

/-- The loop label witnesses a path from base to base in the HIT
specification. -/
theorem loopSpec :
    S1Spec.hasPathBetween S1PointLabel.base S1PointLabel.base :=
  ⟨S1PathLabel.loop, rfl, rfl⟩

/-- 0-truncated setoid presentation of S1.

The single carrier representative is the base point.  The relation is
indiscrete so the loop can be represented as a relation witness. -/
def setoid : HITSetoid :=
  HITSetoid.indiscrete Unit

/-- Base representative of the setoid-level circle. -/
def base : setoid.carrier :=
  ()

/-- Loop relation witness at the base representative. -/
theorem loop : setoid.relation base base :=
  True.intro

/-- Non-dependent recursion out of the setoid-level circle.

At this 0-truncated level, a recursor is just the constant recursor
chosen by the base case. -/
def rec (resultType : Sort resultLevel)
    (baseCase : resultType) :
    HITRecursor setoid resultType :=
  HITRecursor.constant resultType baseCase

/-- Circle recursion computes at the base representative by reflexive
reduction. -/
theorem rec_base (resultType : Sort resultLevel)
    (baseCase : resultType) :
    (S1.rec resultType baseCase).run S1.base = baseCase :=
  rfl

/-- The circle recursor respects the loop relation. -/
theorem rec_loop (resultType : Sort resultLevel)
    (baseCase : resultType) :
    (S1.rec resultType baseCase).run S1.base =
      (S1.rec resultType baseCase).run S1.base :=
  HITRecursor.run_respects (S1.rec resultType baseCase) S1.loop

/-- Dependent induction out of the current setoid-level circle.

Because this presentation is 0-truncated with a single carrier
representative, the dependent motive is discharged by the base case.
The relation-respect proof is reflexive after case analysis on the
single `Unit` representative. -/
def dependentInductor (motive : setoid.carrier → Sort resultLevel)
    (baseCase : motive S1.base) :
    HITInductor setoid motive where
  apply := fun
    | () => baseCase
  respectsRelation := by
    intro leftValue rightValue _relationWitness
    cases leftValue
    cases rightValue
    exact HEq.rfl

/-- Circle dependent induction computes at the base representative by
reflexive reduction. -/
theorem dependentInductor_base (motive : setoid.carrier → Sort resultLevel)
    (baseCase : motive S1.base) :
    (S1.dependentInductor motive baseCase).run S1.base = baseCase :=
  rfl

/-- The circle dependent inductor respects the loop relation. -/
theorem dependentInductor_loop (motive : setoid.carrier → Sort resultLevel)
    (baseCase : motive S1.base) :
    HEq ((S1.dependentInductor motive baseCase).run S1.base)
      ((S1.dependentInductor motive baseCase).run S1.base) :=
  HITInductor.run_respects (S1.dependentInductor motive baseCase) S1.loop

end S1

end HIT
end HoTT
end LeanFX2

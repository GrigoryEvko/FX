import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/S1

Setoid-level presentation of the circle HIT.

This module records the circle's point/path labels and exposes a
0-truncated setoid presentation with explicit winding representatives.
The relation is connected, so every winding is path-related to every
other winding.  Eliminators over non-constant motives must therefore
carry real heterogeneous relation-coherence data.

This is still not the full circle HIT: it does not model the
fundamental group or higher loop composition.  Those require a richer
path algebra than the current `HITSetoid` foundation.  The purpose here
is to make the base/loop/coherence wiring non-vacuous without importing
axioms.
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

/-- Circle point representatives at the setoid layer.

`base` is the canonical point.  `loopFwd n` and `loopBwd n` are explicit
positive and negative winding representatives; the setoid relation
connects all of them. -/
inductive S1Loop : Type where
  | base : S1Loop
  | loopFwd (innerWinding : Nat) : S1Loop
  | loopBwd (innerWinding : Nat) : S1Loop

namespace S1Loop

/-- Setoid-level circle connectivity: every winding representative is
related to every other representative. -/
def relation (_leftValue _rightValue : S1Loop) : Prop :=
  True

/-- Reflexivity for the connected winding relation. -/
theorem relation_refl (someValue : S1Loop) :
    S1Loop.relation someValue someValue :=
  True.intro

/-- Symmetry for the connected winding relation. -/
theorem relation_symm {leftValue rightValue : S1Loop}
    (_relationWitness : S1Loop.relation leftValue rightValue) :
    S1Loop.relation rightValue leftValue :=
  True.intro

/-- Transitivity for the connected winding relation. -/
theorem relation_trans {leftValue middleValue rightValue : S1Loop}
    (_firstWitness : S1Loop.relation leftValue middleValue)
    (_secondWitness : S1Loop.relation middleValue rightValue) :
    S1Loop.relation leftValue rightValue :=
  True.intro

end S1Loop

/-- The loop label witnesses a path from base to base in the HIT
specification. -/
theorem loopSpec :
    S1Spec.hasPathBetween S1PointLabel.base S1PointLabel.base :=
  ⟨S1PathLabel.loop, rfl, rfl⟩

/-- 0-truncated setoid presentation of S1 over explicit winding
representatives. -/
def setoid : HITSetoid :=
  HITSetoid.fromEquivalence
    S1Loop
    S1Loop.relation
    S1Loop.relation_refl
    S1Loop.relation_symm
    S1Loop.relation_trans

/-- Base representative of the setoid-level circle. -/
def base : setoid.carrier :=
  S1Loop.base

/-- Positive winding representative. -/
def forwardLoop (innerWinding : Nat) : setoid.carrier :=
  S1Loop.loopFwd innerWinding

/-- Negative winding representative. -/
def backwardLoop (innerWinding : Nat) : setoid.carrier :=
  S1Loop.loopBwd innerWinding

/-- Loop relation witness at the base representative. -/
theorem loop : setoid.relation base base :=
  True.intro

/-- Positive windings are connected to the base representative. -/
theorem loopForward (innerWinding : Nat) :
    setoid.relation base (forwardLoop innerWinding) :=
  True.intro

/-- Negative windings are connected to the base representative. -/
theorem loopBackward (innerWinding : Nat) :
    setoid.relation base (backwardLoop innerWinding) :=
  True.intro

/-- Any two winding representatives are connected in the setoid-level
circle. -/
theorem loopBetween (leftValue rightValue : setoid.carrier) :
    setoid.relation leftValue rightValue :=
  True.intro

/-- Non-dependent recursion out of the setoid-level circle.

At this 0-truncated level, the ordinary circle recursor is the constant
recursor chosen by the base case.  Use `recFromWinding` when an
implementation wants to inspect explicit winding representatives; it
then must prove relation preservation for all connected windings. -/
def rec (resultType : Sort resultLevel)
    (baseCase : resultType) :
    HITRecursor setoid resultType :=
  HITRecursor.constant resultType baseCase

/-- Recursion from explicit winding representatives.

The relation on S1 is connected, so a non-constant implementation must
prove that every pair of winding outputs is equal. -/
def recFromWinding (resultType : Sort resultLevel)
    (windingCase : setoid.carrier → resultType)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        windingCase leftValue = windingCase rightValue) :
    HITRecursor setoid resultType where
  apply := windingCase
  respectsRelation := fun {leftValue} {rightValue} _relationWitness =>
    loopRespects leftValue rightValue

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

/-- Winding recursion computes at the base representative. -/
theorem recFromWinding_base (resultType : Sort resultLevel)
    (windingCase : setoid.carrier → resultType)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        windingCase leftValue = windingCase rightValue) :
    (S1.recFromWinding resultType windingCase loopRespects).run S1.base =
      windingCase S1.base :=
  rfl

/-- Winding recursion respects every connected pair of representatives. -/
theorem recFromWinding_loopBetween (resultType : Sort resultLevel)
    (windingCase : setoid.carrier → resultType)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        windingCase leftValue = windingCase rightValue)
    (leftValue rightValue : setoid.carrier) :
    (S1.recFromWinding resultType windingCase loopRespects).run leftValue =
      (S1.recFromWinding resultType windingCase loopRespects).run rightValue :=
  HITRecursor.run_respects
    (S1.recFromWinding resultType windingCase loopRespects)
    (S1.loopBetween leftValue rightValue)

/-- Dependent induction out of the setoid-level circle.

The carrier has multiple winding representatives, so the caller must
provide a motive witness for every representative and prove that those
witnesses are heterogeneously equal across the connected relation. -/
def dependentInductor (motive : setoid.carrier → Sort resultLevel)
    (windingCase : ∀ windingValue : setoid.carrier, motive windingValue)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        HEq (windingCase leftValue) (windingCase rightValue)) :
    HITInductor setoid motive where
  apply := windingCase
  respectsRelation := fun {leftValue} {rightValue} _relationWitness =>
    loopRespects leftValue rightValue

/-- Circle dependent induction computes at the base representative by
reflexive reduction. -/
theorem dependentInductor_base (motive : setoid.carrier → Sort resultLevel)
    (windingCase : ∀ windingValue : setoid.carrier, motive windingValue)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        HEq (windingCase leftValue) (windingCase rightValue)) :
    (S1.dependentInductor motive windingCase loopRespects).run S1.base =
      windingCase S1.base :=
  rfl

/-- The circle dependent inductor respects the loop relation. -/
theorem dependentInductor_loop (motive : setoid.carrier → Sort resultLevel)
    (windingCase : ∀ windingValue : setoid.carrier, motive windingValue)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        HEq (windingCase leftValue) (windingCase rightValue)) :
    HEq
      ((S1.dependentInductor motive windingCase loopRespects).run S1.base)
      ((S1.dependentInductor motive windingCase loopRespects).run S1.base) :=
  HITInductor.run_respects
    (S1.dependentInductor motive windingCase loopRespects)
    S1.loop

/-- The circle dependent inductor respects every connected pair of
winding representatives. -/
theorem dependentInductor_loopBetween
    (motive : setoid.carrier → Sort resultLevel)
    (windingCase : ∀ windingValue : setoid.carrier, motive windingValue)
    (loopRespects :
      ∀ leftValue rightValue : setoid.carrier,
        HEq (windingCase leftValue) (windingCase rightValue))
    (leftValue rightValue : setoid.carrier) :
    HEq
      ((S1.dependentInductor motive windingCase loopRespects).run leftValue)
      ((S1.dependentInductor motive windingCase loopRespects).run rightValue) :=
  HITInductor.run_respects
    (S1.dependentInductor motive windingCase loopRespects)
    (S1.loopBetween leftValue rightValue)

end S1

end HIT
end HoTT
end LeanFX2

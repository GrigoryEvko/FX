import LeanFX2.HoTT.HIT.Setoid

/-! # HoTT/HIT/Eliminator — HIT induction principles

For each HIT, an induction principle: to prove a property of all
values, prove it for each point constructor AND prove it respects
each path constructor.

```lean
def HITSpec.elim (spec : HITSpec) (motive : spec.Type → Type) ... : ...
```

Generic elimination principle parameterized by the HIT spec.

## Computation rules

Each ι rule says: applying the eliminator on a point constructor
applied to data reduces to the case for that constructor.

For S¹:
* `S¹.elim Pmotive baseCase loopCase base = baseCase`
* (no separate computation for `loop` because path constructors
  don't have unique reducts; instead, the eliminator's *transport*
  along `loop` reduces to `loopCase`)

## Dependencies

* `HoTT/HIT/Setoid.lean`

## Downstream consumers

* `HoTT/HIT/Examples.lean` — concrete HIT eliminators
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe carrierLevel resultLevel

/-- Non-dependent recursor out of an explicit HIT setoid presentation.

This is the safe first eliminator: a map out of the carrier plus a proof
that it respects the generated path relation.  It does not quotient by
Lean's `Quot`, and therefore does not rely on `Quot.sound`. -/
structure HITRecursor
    (encodedHit : HITSetoid.{carrierLevel})
    (resultType : Sort resultLevel) where
  /-- Underlying function on point representatives. -/
  apply : encodedHit.carrier → resultType
  /-- The function respects the HIT path relation. -/
  respectsRelation :
    HITSetoid.preservesRelation encodedHit apply

namespace HITRecursor

/-- Apply a HIT recursor to a representative. -/
def run {encodedHit : HITSetoid.{carrierLevel}}
    {resultType : Sort resultLevel}
    (recursor : HITRecursor encodedHit resultType)
    (someValue : encodedHit.carrier) : resultType :=
  recursor.apply someValue

/-- A recursor maps related representatives to equal outputs. -/
theorem run_respects {encodedHit : HITSetoid.{carrierLevel}}
    {resultType : Sort resultLevel}
    (recursor : HITRecursor encodedHit resultType)
    {leftValue rightValue : encodedHit.carrier}
    (relationWitness : encodedHit.relation leftValue rightValue) :
    recursor.run leftValue = recursor.run rightValue :=
  recursor.respectsRelation relationWitness

/-- Build a recursor from a constant function. -/
def constant {encodedHit : HITSetoid.{carrierLevel}}
    (resultType : Sort resultLevel)
    (resultValue : resultType) :
    HITRecursor encodedHit resultType where
  apply := fun _ => resultValue
  respectsRelation := fun _ => rfl

/-- The constant recursor computes by reflexive reduction. -/
theorem constant_run {encodedHit : HITSetoid.{carrierLevel}}
    (resultType : Sort resultLevel)
    (resultValue : resultType)
    (someValue : encodedHit.carrier) :
    (HITRecursor.constant resultType resultValue).run someValue =
      resultValue :=
  rfl

end HITRecursor

end HIT
end HoTT
end LeanFX2

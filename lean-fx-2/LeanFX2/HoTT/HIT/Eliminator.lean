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

end LeanFX2

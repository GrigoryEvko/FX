import LeanFX2.HoTT.HIT.PropTrunc
import LeanFX2.HoTT.HIT.SetTrunc
import LeanFX2.HoTT.HIT.Quot
import LeanFX2.HoTT.HIT.S1
import LeanFX2.HoTT.HIT.Suspension
import LeanFX2.HoTT.HIT.Pushout
import LeanFX2.HoTT.HIT.Coequalizer

/-! # HoTT/HIT/Examples — concrete HITs

Reference concrete HIT presentations that downstream HoTT proofs use.

## Circle (S¹)

```lean
inductive S1 : Type
  | base : S1
  -- loop : Id S1 base base   (encoded as setoid quotient)
```

* Point: `base : S¹`
* Path: `loop : Id S¹ base base`

Use cases: foundational HoTT examples (computing fundamental group,
non-set-ness).

## Suspension

```lean
inductive Susp (A : Type) : Type
  | north : Susp A
  | south : Susp A
  -- merid : A → Id (Susp A) north south   (setoid-encoded)
```

Use cases: define spheres recursively (`S^n = Susp (S^{n-1})`).

## Quotient

```lean
def Quotient (A : Type) (R : A → A → Prop) : Type :=
  -- A modulo R, with respect proofs
```

Use cases: real numbers as Cauchy sequences, equivalence-class
constructions.

## Propositional truncation

```lean
inductive Trunc (A : Type) : Type
  | mk : A → Trunc A
  -- ∀ x y, Id (Trunc A) x y   (squash: any two Trunc values equal)
```

Use cases: turning data into a proposition (existence).

## Dependencies

* `HoTT/HIT/{PropTrunc,SetTrunc,Quot,S1,Suspension,Pushout,Coequalizer}.lean`

## Downstream consumers

* HoTT smoke tests (`Smoke/HoTT.lean`)
* End-user HoTT proofs

## Implementation plan (Phase 6)

1. Encode each HIT via the setoid encoding from `HIT/Setoid.lean`
2. Provide eliminators per `HIT/Eliminator.lean`
3. Smoke: compute on `S¹.base`, transport along `loop`, etc.

This file is intentionally modest: it checks that all seven concrete
presentations are importable together and gives small representative
values over `Unit`.  The mathematical content lives in the per-HIT
modules; this module is the load-bearing examples surface named by the
sprint plan.
-/

namespace LeanFX2
namespace HoTT
namespace HIT
namespace Examples

/-- Unit equality quotient example. -/
def quotientUnit : (QuotientHIT.equality Unit).carrier :=
  QuotientHIT.intro ()

/-- Unit propositional-truncation example. -/
def propTruncUnit : (PropTrunc Unit).carrier :=
  PropTrunc.intro ()

/-- Unit set-truncation example. -/
def setTruncUnit : (SetTrunc Unit).carrier :=
  SetTrunc.intro ()

/-- Circle base-point example. -/
def s1BaseUnit : S1.setoid.carrier :=
  S1.base

/-- Unit suspension north-point example. -/
def suspensionNorthUnit : (Suspension.setoid Unit).carrier :=
  Suspension.north (sourceType := Unit)

/-- Unit pushout presentation used by the examples surface. -/
def pushoutUnit : HITSetoid :=
  PushoutHIT
    Unit Unit Unit
    (fun sourceValue => sourceValue)
    (fun sourceValue => sourceValue)
    (fun _ _ => True)
    (fun _ => True.intro)
    (fun _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ => True.intro)

/-- Unit pushout left-point example. -/
def pushoutLeftUnit : pushoutUnit.carrier :=
  PushoutHIT.left ()

/-- Unit coequalizer presentation used by the examples surface. -/
def coequalizerUnit : HITSetoid :=
  CoequalizerHIT
    Unit Unit
    (fun sourceValue => sourceValue)
    (fun sourceValue => sourceValue)
    (fun _ _ => True)
    (fun _ => True.intro)
    (fun _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ => True.intro)

/-- Unit coequalizer point example. -/
def coequalizerPointUnit : coequalizerUnit.carrier :=
  CoequalizerHIT.point ()

end Examples
end HIT
end HoTT
end LeanFX2

import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Examples — concrete HITs

Reference HITs that downstream HoTT proofs use.

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

* `HoTT/HIT/Eliminator.lean`

## Downstream consumers

* HoTT smoke tests (`Smoke/HoTT.lean`)
* End-user HoTT proofs

## Implementation plan (Phase 6)

1. Encode each HIT via the setoid encoding from `HIT/Setoid.lean`
2. Provide eliminators per `HIT/Eliminator.lean`
3. Smoke: compute on `S¹.base`, transport along `loop`, etc.
-/

namespace LeanFX2

end LeanFX2

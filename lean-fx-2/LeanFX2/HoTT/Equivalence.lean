import LeanFX2.HoTT.Transport

/-! # HoTT/Equivalence — type equivalence ≃

```lean
structure Equiv (A B : Type) where
  toFun     : A → B
  invFun    : B → A
  leftInv   : ∀ x, invFun (toFun x) = x   -- via Id, not =
  rightInv  : ∀ y, toFun (invFun y) = y
  -- coherence: leftInv and rightInv agree under toFun-action
```

The "coherent bi-inverse" formulation.  `coherence` ensures the
two inverse proofs aren't independent.

## ≃ refl

```lean
def Equiv.refl : Equiv A A := { toFun := id, invFun := id, ... }
```

## ≃ trans, ≃ sym

Compose / invert.  Both via J.

## Connection to univalence

Univalence (Layer 5 `Univalence.lean`) postulates:

```lean
axiom Univalence : Equiv A B → Id Type A B  -- @[univalence_postulate]
```

(or derives this via cubical machinery).

## Dependencies

* `HoTT/Transport.lean`

## Downstream consumers

* `HoTT/Univalence.lean` — univalence inverts type Id and equivalence
* `HoTT/HIT/Eliminator.lean` — HIT eliminators preserve equivalence
-/

namespace LeanFX2

end LeanFX2

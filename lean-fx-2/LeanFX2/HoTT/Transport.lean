import LeanFX2.HoTT.J

/-! # HoTT/Transport — transport along paths

```lean
def transport (P : A → Type) (p : Id A a b) : P a → P b
```

Substitution along an identity proof.  Defined by J with motive
`λ b _. P a → P b`; on refl, result is identity.

## Computation

```lean
theorem transport_refl : transport P (refl a) = id
```

By J — actually `rfl` because of the ι rule on `idJ`.

## Composition

```lean
theorem transport_trans (p : Id A a b) (q : Id A b c) :
    transport P (p · q) = transport P q ∘ transport P p
```

By J on `p`.

## Dependencies

* `HoTT/J.lean`

## Downstream consumers

* `HoTT/Equivalence.lean` — equivalence's transport-fibers
* `HoTT/HIT/Examples.lean` — concrete transport on HITs
-/

namespace LeanFX2

end LeanFX2

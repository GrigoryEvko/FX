import LeanFX2.HoTT.J

/-! # HoTT/Path/Inverse — Id.sym

Path inverse: given `p : Id A a b`, build `p⁻¹ : Id A b a`.

## Statement

```lean
def Id.sym : Id A a b → Id A b a
```

Defined by J on the path: when it's `refl a`, the result is `refl a`.

## Groupoid law: inverse-then-self

```lean
theorem Id.trans_sym : p · p⁻¹ = refl
theorem Id.sym_trans : p⁻¹ · p = refl
```

Provable by J.  These are the *intensional* inverse laws.

## Inversion is involutive

```lean
theorem Id.sym_sym : (p⁻¹)⁻¹ = p
```

By J.

## Dependencies

* `HoTT/J.lean`

## Downstream consumers

* `HoTT/Path/Groupoid.lean` — combined with Composition gives groupoid
-/

namespace LeanFX2

end LeanFX2

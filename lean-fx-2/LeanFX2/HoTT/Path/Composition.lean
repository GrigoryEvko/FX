import LeanFX2.HoTT.J

/-! # HoTT/Path/Composition — Id.trans

Path concatenation: given `p : Id A a b` and `q : Id A b c`, build
`p · q : Id A a c`.

## Statement

```lean
def Id.trans : Id A a b → Id A b c → Id A a c
```

Defined by J on the first path: when it's `refl`, the result is `q`.

## Groupoid law: associativity

```lean
theorem Id.trans_assoc : (p · q) · r = p · (q · r)
```

Provable by J on each path.

## Identity laws

```lean
theorem Id.trans_refl_left : refl · p = p
theorem Id.trans_refl_right : p · refl = p
```

The "trans_refl_left" is `rfl` (computation rule); "trans_refl_right"
requires J.

## Dependencies

* `HoTT/J.lean`

## Downstream consumers

* `HoTT/Path/Inverse.lean` — inverse paths
* `HoTT/Path/Groupoid.lean` — full groupoid laws
-/

namespace LeanFX2

end LeanFX2

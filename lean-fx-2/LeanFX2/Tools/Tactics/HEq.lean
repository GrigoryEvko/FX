/-! # Tools/Tactics/HEq — HEq → Eq via Term-typing

When proving Term-level equalities, HEq frequently appears via
substitution / renaming of dependent index types.  Helpers in this
file convert HEq to Eq when the types align.

## Key helpers

```lean
theorem Term.eq_of_heq_typeEq
    {t1 : Term ctx ty1 raw1} {t2 : Term ctx ty2 raw2}
    (typeEq : ty1 = ty2) (rawEq : raw1 = raw2)
    (heq : HEq t1 t2) :
    typeEq ▸ rawEq ▸ t1 = t2
```

```lean
theorem Term.heq_iff_eq_after_cast
    {t1 : Term ctx ty1 raw1} {t2 : Term ctx ty2 raw2}
    (typeEq : ty1 = ty2) (rawEq : raw1 = raw2) :
    HEq t1 t2 ↔ typeEq ▸ rawEq ▸ t1 = t2
```

## Why

HEq is frequently introduced when matching on Step.par cases where
the target type depends on substituted indices.  Converting HEq to
plain Eq makes downstream proof manipulation cleaner.

## refuteViaToRaw

The breakthrough helper from `feedback_typed_inversion_breakthrough`:

```lean
theorem refuteViaToRaw
    (sourceTerm : Term ctx_a sourceType src) (targetTerm : Term ctx_a targetType tgt)
    (typeEq : sourceType = targetType)
    (rawNeq : src ≠ tgt)
    (heq : HEq sourceTerm targetTerm) : False
```

Uses Term's raw index to refute incompatible source/target Terms via
RawTerm ctor injectivity.  Avoids dep-elim wall.

## Dependencies

* `Term.lean`

## Downstream

* `Reduction/Compat.lean`
* `Confluence/*.lean`
* `Bridge.lean`

## Implementation plan (Layer 12)

1. Define `eq_of_heq_typeEq`, `heq_iff_eq_after_cast`
2. Define `refuteViaToRaw` as the load-bearing inversion helper
3. Smoke: round-trip HEq ↔ Eq

Target: ~150 lines.
-/

namespace LeanFX2.Tools.Tactics

-- TODO Layer 12: HEq ↔ Eq helpers
-- TODO Layer 12: refuteViaToRaw

end LeanFX2.Tools.Tactics

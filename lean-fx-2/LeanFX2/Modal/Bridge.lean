/-! # Modal/Bridge — Bridge modality (parametricity)

The Bridge modality `Bridge` encodes parametricity at the software
mode.  A `Bridge A` is a "value definable parametrically over `A`".

## Operations

* `bridge_intro : (∀ R : A → A → Prop, ParametricRespects R x y) → Bridge ?`
* `bridge_extract : Bridge A → ParametricResult`

## Why Bridge

Parametricity is the principle that "a polymorphic function's
behavior is determined by its type".  Encoded internally via
type-indexed relations, it gives free theorems:

```lean
theorem id_polymorphic : ∀ (f : ∀ A, A → A), ∀ A x, f A x = x
```

This kind of theorem can be derived internally with the Bridge
modality.  See lean-fx tasks v3.29–v3.33.

## Internal parametricity (axiom-free)

lean-fx-2 implements internal parametricity via type-indexed
relations + Bridge modality interface.  No `funext` or univalence
needed for the basic version.

## Free theorem extractor

```lean
theorem extractFree (h : Bridge A) : FreeTheorem A
```

Auto-derive free theorems from Bridge inhabitants.

## Smoke

* Noninterference: `secret int → int` cannot leak
* Linearity preservation: linear functions stay linear after subst

## Dependencies

* `Modal/Foundation.lean`

## Downstream consumers

* User-level free-theorem extraction
-/

namespace LeanFX2

end LeanFX2

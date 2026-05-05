/-! # Modal/Ghost — Ghost (erased) modality

The Ghost modality marks data as **compile-time only** — present in
typing but erased at runtime.  Used for proofs, complexity bounds,
and other phantom information.

## Modality

```lean
def Modality.ghost : Modality
```

## Adjunction: ghost ⊣ erase

The ghost modality has a left adjoint `erase` that turns every
runtime value into ghost form.  This pair forms a 2LTT layering:
* Static (ghost) layer: types containing ghost values
* Dynamic layer: runtime values, accessible via `erase`

```lean
theorem Modality.ghost_erase_adjunction :
    Equiv (Hom (ghost A) B) (Hom A (erase B))
```

(2-cell adjunction in the Mode 2-category.)

## Erasure semantics

In compiled code, `Ty.modal Modality.ghost ty` values are *not
emitted* — they exist only at typing time.  This corresponds to
fx_design.md's "ghost" effect.

## Dependencies

* `Modal/Foundation.lean`

## Downstream consumers

* `Modal/2LTT.lean` — 2LTT layer separation uses ghost
* User-level erased proofs / compile-time annotations
-/

namespace LeanFX2

end LeanFX2

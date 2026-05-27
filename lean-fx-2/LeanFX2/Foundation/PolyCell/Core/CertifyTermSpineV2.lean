import LeanFX2.Foundation.PolyCell.Core.CertifyChildSpineV2
import LeanFX2.Foundation.PolyCell.Core.ReconcileChildV2

/-! # Foundation/PolyCell/Core/CertifyTermSpineV2 — wired spine certifier

This file ships `certifyTermSpineV2?`: the top-level child-spine
certifier produced by wiring the parametric `certifyChildSpineV2?`
(#156) with the per-child reconciler `reconcileChildV2` (#157).

## The wiring

`certifyChildSpineV2?` takes a `perChildCertifier` callback.
`reconcileChildV2` IS that callback, parameterized by a general
recursive certifier.  Partial application:

```
certifyChildSpineV2? (reconcileChildV2 recursiveCertifier)
```

gives a spine certifier that walks (childSpecs, children) in
parallel, calling `reconcileChildV2 recursiveCertifier` on each
child to handle the sort/dim/raw reconciliation.

This is the FIRST stage of the certifier that handles BOTH the
structural recursion AND the per-position reconciliation.

## Why a separate file

`certifyTermSpineV2?` is essentially a one-line definition.  It
ships in its own file (rather than appending to ReconcileChildV2)
because:

1. Future expansion: this file is the natural home for spine-related
   helpers + lemmas (e.g., spine arity preservation, the spine
   certifier's soundness theorem) as the certifier work matures.
2. Dependency clarity: separating the wiring from its components
   makes the architectural layering visible — `CertifyChildSpineV2`
   (the abstract walk) + `ReconcileChildV2` (the abstract reconciler)
   combine here into the concrete spine certifier.

## Zero-axiom verification

Pure function composition: the body is a single application of
`certifyChildSpineV2?` to `reconcileChildV2 recursiveCertifier`.
No new tactics, no transports, no Decidable dispatch beyond what
the components already do.  Inherits axiom-cleanliness from its
two components.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Top-level certified-term-spine certifier.  Given:

* `recursiveCertifier` — the general v2 certifier (forward-declared
  as a callback; closed mutually by `certifyRawCellExactV2?` #162)
* `childSpecs` — a generator's metadata
* `children` — the raw children spine at the parent's scope

Produces a `CertifiedTermSpineV2` if all children pass reconciliation,
else a `CellCheckRejection`.

Body: `certifyChildSpineV2?` walks the spine in parallel with the
specs, calling `reconcileChildV2 recursiveCertifier` on each child
to perform sort/dim/raw reconciliation via Decidable + subst.

This is the certifier-side input for `PolyCellV2.gen`'s
`CertifiedTermSpineV2` parameter (Stage L1c.4 task #159
`certifyTermExactV2?` consumes this to build the gen-ctor cell). -/
def certifyTermSpineV2? {profile : PolyProfile}
    (recursiveCertifier :
      (scope : Nat) → (raw : RawCellV2 scope) →
      Except CellCheckRejection (CertifiedCellV2 profile scope))
    {parentScope : Nat}
    (childSpecs : List ChildSpecV2)
    (children :
      RawTermChildrenV2 (childSpecs.map (·.scopeShift)) parentScope) :
    Except CellCheckRejection
      (CertifiedTermSpineV2 profile childSpecs parentScope
        (childSpecs.map (·.scopeShift)) children) :=
  certifyChildSpineV2? (reconcileChildV2 recursiveCertifier)
    childSpecs children

end LeanFX2.Foundation.PolyCell.Core

import LeanFX2.Foundation.PolyCell.Core.CertifyChildSpineV2
import LeanFX2.Foundation.PolyCell.Core.ReconcileChildV2

/-! # Foundation/PolyCell/Core/CertifyTermSpineV2 — wired spine certifier

This file ships `certifyTermSpineV2?`: the top-level child-spine
certifier produced by wiring the parametric `certifyChildSpineV2?`
(#156) with the per-child reconciler `reconcileChildV2` (#157).

## The signature: binderShifts + coherence

To enable downstream callers (`certifyTermExactV2?` in #159) to pass
`children : RawTermChildrenV2 generator.binderShifts scope` directly
— without a `▸` transport — this function takes `binderShifts` as
an explicit type-level parameter along with a coherence proof:

```
def certifyTermSpineV2? ...
    (childSpecs : List ChildSpecV2)
    {binderShifts : List Nat}
    (coherence : binderShifts = childSpecs.map (·.scopeShift))
    (children : RawTermChildrenV2 binderShifts parentScope) :
    Except CellCheckRejection
      (CertifiedTermSpineV2 profile childSpecs parentScope
        binderShifts children)
```

The caller supplies `binderShifts` (e.g., `generator.binderShifts`)
and `coherence` (e.g.,
`Generator.childSpecs_scopeShifts_eq_binderShifts generator |>.symm`).
The output spine is at the CALLER's `binderShifts`, ready for
direct use in `PolyCellV2.gen`'s signature without any cast.

Internally, the body uses tactic-mode `subst coherence` to globally
rewrite `binderShifts := childSpecs.map (·.scopeShift)`.  After
`subst`, the goal and children types match what
`certifyChildSpineV2?` expects, and the wired call goes through.

## The wiring (post-subst)

After `subst coherence`, the body reduces to:

```
certifyChildSpineV2? (reconcileChildV2 recursiveCertifier)
  childSpecs children
```

— the same one-line composition that previously was the entire
body.  The coherence threading happens entirely at the boundary.

## Why coherence as a parameter rather than .map directly

Forcing callers to pre-transport children to `.map`-indexed form
would require a `▸` chain at every call site — and the spine
output would still be `.map`-indexed, not `binderShifts`-indexed,
requiring ANOTHER `▸` chain at the consumer side.

Taking `binderShifts + coherence` lifts the transport into ONE
tactic-mode `subst` step inside this function, eliminating ALL
caller-side `▸` chains.  This is the standard "thread the equation
as data" pattern from intrinsic-typing literature.

## Zero-axiom verification

`subst` uses `Eq.ndrec`, propext-free.  The rest is composition
with already-clean functions (`certifyChildSpineV2?`,
`reconcileChildV2`).  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Top-level certified-term-spine certifier.  Given:

* `recursiveCertifier` — the general v2 certifier (forward-declared
  as a callback; closed mutually by `certifyRawCellExactV2?` #162)
* `childSpecs` — a generator's metadata
* `binderShifts` — the type-level binderShifts (typically
  `generator.binderShifts` from the caller)
* `coherence` — a proof that `binderShifts = childSpecs.map (·.scopeShift)`
* `children` — the raw children spine at parentScope, indexed by
  `binderShifts`

Produces a `CertifiedTermSpineV2` indexed by the CALLER's
`binderShifts` (NOT the `.map` form) if all children pass
reconciliation, else a `CellCheckRejection`.

Body: tactic-mode `subst coherence` to normalize `binderShifts`
into the `.map` form, then wire `certifyChildSpineV2?` with
`reconcileChildV2` as the per-child callback.

This is the certifier-side input for `PolyCellV2.gen`'s
`CertifiedTermSpineV2` parameter (Stage L1c.4 task #159
`certifyTermExactV2?` consumes this to build the gen-ctor cell). -/
def certifyTermSpineV2? {profile : PolyProfile}
    (recursiveCertifier :
      (scope : Nat) → (raw : RawCellV2 scope) →
      Except CellCheckRejection (CertifiedCellV2 profile scope))
    {parentScope : Nat}
    (childSpecs : List ChildSpecV2)
    {binderShifts : List Nat}
    (coherence : binderShifts = childSpecs.map (·.scopeShift))
    (children : RawTermChildrenV2 binderShifts parentScope) :
    Except CellCheckRejection
      (CertifiedTermSpineV2 profile childSpecs parentScope
        binderShifts children) := by
  subst coherence
  exact certifyChildSpineV2? (reconcileChildV2 recursiveCertifier)
    childSpecs children

end LeanFX2.Foundation.PolyCell.Core

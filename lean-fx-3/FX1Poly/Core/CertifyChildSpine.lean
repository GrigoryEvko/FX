import FX1Poly.Core.PolyCell
import FX1Poly.Core.CheckResult

/-! # Foundation/PolyCell/Core/CertifyChildSpine — generic child-spine recursion

This file ships the parametric child-spine certifier: ONE function
that walks a generator's child specs in parallel with a raw children
spine, producing a certified `CertifiedTermSpine` or a rejection.
ONE recursive function handles every generator's child spine.

## The architectural trick

The per-child reconciliation (sort/dim/scope checks, `▸` transports)
is DELEGATED to a callback `perChildCertifier`.  This file ships
the parallel-walk recursion; `reconcileChild` supplies the callback
that closes the loop with the recursive certifier.

This decoupling lets the spine recursion be straightforward (no
casts, no Decidable dispatch inside the walk) while the
reconciliation logic lives in its own dedicated function (where
it can use the `▸ + Decidable + cast` pattern).

## The CertifiedChildAtSpec struct

The callback's return type bundles `headBoundary` (existentialized)
with the certified head cell:

```
structure CertifiedChildAtSpec ... where
  headBoundary : CellBoundary ...
  headCell : PolyCell ... headBoundary (.termBase headRaw)
```

Both fields share the same `(profile, spec, parentScope, headRaw)`
parameters.  Only the boundary varies — and even that is fixed for
dim 0 children (where boundary is `Unit`), so under fxProfile this
is effectively a one-field wrapper around the cell.

## The walk

`certifyChildSpine?` walks two indexed lists in lockstep:

* `childSpecs : List ChildSpec` — the generator's metadata
* `children : RawTermChildren (childSpecs.map (·.scopeShift)) parentScope`
  — the raw children

The `.map (·.scopeShift)` reduces definitionally on `::`, so the
pattern matching on `childSpecs` automatically refines the
children's type:

* `[]` case: `children : RawTermChildren [] parentScope` — only
  `.childNil` matches.
* `headSpec :: restSpecs` case: `children : RawTermChildren
  (headSpec.scopeShift :: restSpecs.map (·.scopeShift)) parentScope`
  — only `.childCons` matches.

Each step calls `perChildCertifier` on the head + recurses on the
tail.  Both must succeed for the spine to succeed; either failure
propagates the rejection.

## Termination

Structural recursion on `childSpecs`: the recursive call passes
`restSpecs`, a strictly-smaller list.  Lean's well-founded
recursion accepts this without an explicit `termination_by`.

## Zero-axiom verification

The recursion uses:

* Pattern matching on closed inductives (`List`, `RawTermChildren`,
  `Except`) with full enumeration — propext-clean per
  `feedback_lean_zero_axiom_match` memory.
* Direct constructor applications (no wildcards, no `_` patterns
  hiding case analysis).
* No HEq, no `▸` (the only `▸` would be inside reconcileChild,
  not here).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Per-child certifier output: a packaged certified cell matching
a specific `ChildSpec` and `headRaw`.

The `headBoundary` field is existentialized (the perChildCertifier
chooses what boundary to assert).  The `headCell` field is the
certified cell at the spec's `cellSort`, `cellDimension`, parent
scope shifted by `spec.scopeShift`, the chosen boundary, and raw
erasure `.termBase headRaw`.

Under fxProfile, all current ChildSpec's have `cellDimension = 0`,
so `headBoundary` is always `Unit` (i.e., `()`) and the struct
effectively wraps just the cell. -/
structure CertifiedChildAtSpec (profile : PolyProfile)
    (spec : ChildSpec) (parentScope : Nat)
    (headRaw : RawTerm (parentScope + spec.scopeShift)) where
  /-- The chosen boundary for the head cell.  For dim-0 specs this
  is `()` (Unit); for higher-dim specs it's a (source, target)
  pair. -/
  headBoundary : CellBoundary profile spec.cellSort
    spec.cellDimension (parentScope + spec.scopeShift)
  /-- The certified cell at the spec's sort/dim/scope, with the
  chosen boundary and raw erasure `.termBase headRaw`. -/
  headCell : PolyCell profile spec.cellSort spec.cellDimension
    (parentScope + spec.scopeShift) headBoundary
    (.termBase headRaw)

/-- Generic child-spine certifier.

Parametric over a per-child certifier callback.  Walks `childSpecs`
and `children` in parallel:

* On `([], .childNil)` returns an empty `CertifiedTermSpine.nil`.
* On `(headSpec :: restSpecs, .childCons headRaw restRaws)`, calls
  `perChildCertifier headSpec headRaw` for the head, recurses on
  the tail, and combines both successes with
  `CertifiedTermSpine.cons`.  Either failure propagates.

Output type indexed by both `childSpecs` and `children.map
(·.scopeShift)` — these are kept in lockstep by the recursive
structure (the `cons` constructor of `CertifiedTermSpine`
maintains the lockstep at each step).

`certifyTermSpine?` and the recursive certifier consume this;
`reconcileChild` supplies the per-child callback that closes the
loop with the recursive certifier. -/
def certifyChildSpine? {profile : PolyProfile} {parentScope : Nat}
    (perChildCertifier :
      (spec : ChildSpec) →
      (childRaw : RawTerm (parentScope + spec.scopeShift)) →
      Except CellCheckRejection
        (CertifiedChildAtSpec profile spec parentScope childRaw)) :
    (childSpecs : List ChildSpec) →
    (children :
      RawTermChildren (childSpecs.map (·.scopeShift)) parentScope) →
    Except CellCheckRejection
      (CertifiedTermSpine profile childSpecs parentScope
        (childSpecs.map (·.scopeShift)) children)
  | [], .childNil => .ok .nil
  | headSpec :: restSpecs, .childCons headRaw restRaws =>
      match perChildCertifier headSpec headRaw,
            certifyChildSpine? perChildCertifier restSpecs
              restRaws with
      | .ok headPackage, .ok restSpine =>
          .ok (.cons headPackage.headCell restSpine)
      | .error rejection, _ => .error rejection
      | _, .error rejection => .error rejection

end FX1Poly.Core

import LeanFX2.Foundation.PolyCell.Core.PolyCellV2
import LeanFX2.Foundation.PolyCell.Core.CheckResult

/-! # Foundation/PolyCell/Core/CertifyChildSpineV2 — generic child-spine recursion

This file ships the parametric child-spine certifier: ONE function
that walks a generator's child specs in parallel with a raw children
spine, producing a certified `CertifiedTermSpineV2` or a rejection.

## The v1 spike

Per `polycell.md` §3 ("Stages overview"):

> The generic children-spine recursion is already settled —
> `certifyChildSpine?` spiked axiom-free.

This file ports that proven shape to v2 vocabulary.  v1's
`screenRawChildDescriptorsWith?` (`Core/Check.lean:796`) was the
parametric screener: it walked `RawChildDescriptors` against
`List ChildSpec` returning yes/no.  v1's per-fixture certifiers
(`certifyLambdaUnitTypeBodyVarZeroChildren?` etc.) were the
constructive versions — one per generator, ~30 LoC each.

v2's `certifyChildSpineV2?` is the FIRST generic constructive
spine certifier: ONE recursive function handles every generator's
child spine.  Per-fixture builders are obsolete.

## The architectural trick

The per-child reconciliation (sort/dim/scope checks, `▸` transports)
is DELEGATED to a callback `perChildCertifier`.  This file ships
the parallel-walk recursion; task #157 (`reconcileChildV2`) ships
the callback that closes the loop with the recursive certifier.

This decoupling lets the spine recursion be straightforward (no
casts, no Decidable dispatch inside the walk) while the
reconciliation logic lives in its own dedicated function (where
it can use the proven `▸ + Decidable + cast` pattern from v1's
`buildTermStepCellExact?` etc.).

## The CertifiedChildAtSpecV2 struct

The callback's return type bundles `headBoundary` (existentialized)
with the certified head cell:

```
structure CertifiedChildAtSpecV2 ... where
  headBoundary : CellBoundaryV2 ...
  headCell : PolyCellV2 ... headBoundary (.termBase headRaw)
```

Both fields share the same `(profile, spec, parentScope, headRaw)`
parameters.  Only the boundary varies — and even that is fixed for
dim 0 children (where boundary is `Unit`), so under fxProfile this
is effectively a one-field wrapper around the cell.

Future profiles with dim-1+ child positions get richer boundary
variation, but the struct shape doesn't change.

## The walk

`certifyChildSpineV2?` walks two indexed lists in lockstep:

* `childSpecs : List ChildSpecV2` — the generator's metadata
* `children : RawTermChildrenV2 (childSpecs.map (·.scopeShift)) parentScope`
  — the raw children

The `.map (·.scopeShift)` reduces definitionally on `::`, so the
pattern matching on `childSpecs` automatically refines the
children's type:

* `[]` case: `children : RawTermChildrenV2 [] parentScope` — only
  `.childNil` matches.
* `headSpec :: restSpecs` case: `children : RawTermChildrenV2
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

* Pattern matching on closed inductives (`List`, `RawTermChildrenV2`,
  `Except`) with full enumeration — propext-clean per
  `feedback_lean_zero_axiom_match` memory.
* Direct constructor applications (no wildcards, no `_` patterns
  hiding case analysis).
* No HEq, no `▸` (the only `▸` would be inside reconcileChildV2,
  not here).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Per-child certifier output: a packaged certified cell matching
a specific `ChildSpecV2` and `headRaw`.

The `headBoundary` field is existentialized (the perChildCertifier
chooses what boundary to assert).  The `headCell` field is the
certified cell at the spec's `cellSort`, `cellDimension`, parent
scope shifted by `spec.scopeShift`, the chosen boundary, and raw
erasure `.termBase headRaw`.

Under fxProfile, all current ChildSpecV2's have `cellDimension = 0`,
so `headBoundary` is always `Unit` (i.e., `()`) and the struct
effectively wraps just the cell.  Forward-compat for future
non-zero-dim children. -/
structure CertifiedChildAtSpecV2 (profile : PolyProfile)
    (spec : ChildSpecV2) (parentScope : Nat)
    (headRaw : RawTermV2 (parentScope + spec.scopeShift)) where
  /-- The chosen boundary for the head cell.  For dim-0 specs this
  is `()` (Unit); for higher-dim specs it's a (source, target)
  pair. -/
  headBoundary : CellBoundaryV2 profile spec.cellSort
    spec.cellDimension (parentScope + spec.scopeShift)
  /-- The certified cell at the spec's sort/dim/scope, with the
  chosen boundary and raw erasure `.termBase headRaw`. -/
  headCell : PolyCellV2 profile spec.cellSort spec.cellDimension
    (parentScope + spec.scopeShift) headBoundary
    (.termBase headRaw)

/-- Generic child-spine certifier.

Parametric over a per-child certifier callback.  Walks `childSpecs`
and `children` in parallel:

* On `([], .childNil)` returns an empty `CertifiedTermSpineV2.nil`.
* On `(headSpec :: restSpecs, .childCons headRaw restRaws)`, calls
  `perChildCertifier headSpec headRaw` for the head, recurses on
  the tail, and combines both successes with
  `CertifiedTermSpineV2.cons`.  Either failure propagates.

Output type indexed by both `childSpecs` and `children.map
(·.scopeShift)` — these are kept in lockstep by the recursive
structure (the `cons` constructor of `CertifiedTermSpineV2`
maintains the lockstep at each step).

Used by task #158 (`certifyTermSpineV2?`) and downstream by the
recursive certifier (#162).  `reconcileChildV2` (#157) supplies
the per-child callback that closes the loop with the recursive
certifier. -/
def certifyChildSpineV2? {profile : PolyProfile} {parentScope : Nat}
    (perChildCertifier :
      (spec : ChildSpecV2) →
      (childRaw : RawTermV2 (parentScope + spec.scopeShift)) →
      Except CellCheckRejection
        (CertifiedChildAtSpecV2 profile spec parentScope childRaw)) :
    (childSpecs : List ChildSpecV2) →
    (children :
      RawTermChildrenV2 (childSpecs.map (·.scopeShift)) parentScope) →
    Except CellCheckRejection
      (CertifiedTermSpineV2 profile childSpecs parentScope
        (childSpecs.map (·.scopeShift)) children)
  | [], .childNil => .ok .nil
  | headSpec :: restSpecs, .childCons headRaw restRaws =>
      match perChildCertifier headSpec headRaw,
            certifyChildSpineV2? perChildCertifier restSpecs
              restRaws with
      | .ok headPackage, .ok restSpine =>
          .ok (.cons headPackage.headCell restSpine)
      | .error rejection, _ => .error rejection
      | _, .error rejection => .error rejection

end LeanFX2.Foundation.PolyCell.Core

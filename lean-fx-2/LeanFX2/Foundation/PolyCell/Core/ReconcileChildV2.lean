import LeanFX2.Foundation.PolyCell.Core.CertifyChildSpineV2
import LeanFX2.Foundation.PolyCell.Core.PolyCellV2Helpers
import LeanFX2.Foundation.PolyCell.Core.RawCellV2DecEq

/-! # Foundation/PolyCell/Core/ReconcileChildV2 — per-child reconciler

This file ships `reconcileChildV2`: the bridge that turns the
general recursive certifier (returning `CertifiedCellV2 profile
scope` with EXISTENTIAL sort/dim/boundary/rawCell) into the
SPEC-MATCHED `CertifiedChildAtSpecV2 profile spec parentScope
headRaw` that `certifyChildSpineV2?` (#156) demands as its per-child
callback.

## What reconciliation does

The recursive certifier accepts ANY raw cell and produces a
`CertifiedCellV2` with whatever sort/dim/rawCell it found.  When
used inside a child-spine walk, each child position has a SPEC
demanding specific values:

* `spec.cellSort` — the required cellSort
* `spec.cellDimension` — the required dim
* `.termBase headRaw` — the required rawCell (a termBase wrapper
  around the position's headRaw)

`reconcileChildV2` checks these three demands and rejects with
`.wrongChildShape` if any fails.  On success, it transports the
certified cell from its existential type to the spec-matched type.

## The transport pattern — `cases` + `by_cases` + `subst`

v1's `buildTermStepCellExact?` (`Core/Check.lean:1796`) established
the propext-clean recipe:

1. `cases cell with | mk resultSort resultDim ... => ...` — destructure
   the struct, freeing its fields as separate variables.
2. `by_cases hSort : resultSort = spec.cellSort` — Decidable test;
   under `pos`, `hSort` is in scope as an equation.
3. `subst hSort` — substitutes `resultSort` with `spec.cellSort`
   globally (in all hypotheses and the goal).  Uses `Eq.ndrec`,
   which is propext-free.
4. Repeat for `hDim` and `hRaw`.
5. After all three substs, the cell's fields have the required types
   DEFINITIONALLY.  No `▸` chains, no HEq, no equation-compiler
   gymnastics — just rebuild the target struct from the now-typed
   fields.

This avoids the `▸`-chain propext risk of explicit transports and
matches the v1 spike's proven shape.

## Decidability requirements

Three Decidable instances are needed:

* `DecidableEq CellSort` — shipped at L0 in `CellSort.lean`
* `DecidableEq Nat` — Lean core stdlib
* `DecidableEq (RawCellV2 _)` — shipped at L0 in `RawCellV2DecEq.lean`

All zero-axiom by prior audit gates.

## Rejection reasons

`.wrongChildShape` for any sort/dim/raw mismatch.  Per
`polycell.md` §4's CellCheckRejection enum, this is the canonical
rejection class for child-position spec violations.  The recursive
certifier's own rejections (badPayload, unsupportedCompH, etc.)
propagate unchanged through `reconcileChildV2`.

## Zero-axiom verification

The tactic-mode body uses only:
* `cases` on a single-ctor structure (no wildcards)
* `by_cases h : P` with Decidable instances
* `subst h` (Eq.ndrec, propext-free)
* `exact` with direct constructor applications

All propext-free per the empirical recipe in
`feedback_lean_zero_axiom_match` memory.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Reconcile a general certifier result against a specific
`ChildSpecV2`, producing a spec-matched `CertifiedChildAtSpecV2` or
a `.wrongChildShape` rejection.

The `recursiveCertifier` is the v2 recursive certifier from #162
(or any function with the right type) — supplied as a callback to
avoid an explicit mutual recursion at this stage.  The Stage L1c.4
work (#162) ties the recursion by passing its own
`certifyRawCellExactV2?` as the callback.

Implementation: standard tactic-mode `cases` + `by_cases` + `subst`
pattern.  Three Decidable tests:

1. Cell's `sort` matches `spec.cellSort`
2. Cell's `dim` matches `spec.cellDimension`
3. Cell's `rawCell` matches `.termBase headRaw`

After all three pass + are `subst`'d, the cell's `boundary` and
`certifiedCell` fields have the spec-matched types definitionally.
The `CertifiedChildAtSpecV2` is then built directly from these
fields without any `▸` transports. -/
def reconcileChildV2 {profile : PolyProfile}
    (recursiveCertifier :
      (scope : Nat) → (raw : RawCellV2 scope) →
      Except CellCheckRejection (CertifiedCellV2 profile scope))
    {parentScope : Nat} (spec : ChildSpecV2)
    (headRaw : RawTermV2 (parentScope + spec.scopeShift)) :
    Except CellCheckRejection
      (CertifiedChildAtSpecV2 profile spec parentScope headRaw) := by
  match recursiveCertifier (parentScope + spec.scopeShift)
        (.termBase headRaw) with
  | .error rejection => exact .error rejection
  | .ok cell =>
    cases cell with
    | mk resultSort resultDim resultRaw resultBoundary resultCertCell =>
      by_cases hSort : resultSort = spec.cellSort
      · subst hSort
        by_cases hDim : resultDim = spec.cellDimension
        · subst hDim
          by_cases hRaw : resultRaw =
            (RawCellV2.termBase headRaw :
              RawCellV2 (parentScope + spec.scopeShift))
          · subst hRaw
            exact .ok
              { headBoundary := resultBoundary
                headCell := resultCertCell }
          · exact .error .wrongChildShape
        · exact .error .wrongChildShape
      · exact .error .wrongChildShape

end LeanFX2.Foundation.PolyCell.Core

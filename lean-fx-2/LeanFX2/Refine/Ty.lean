import LeanFX2.Foundation.Ty

/-! # Refine/Ty — refinement type machinery

`Ty.refine base predicate` decorates `base : Ty level scope` with a
predicate carving out the inhabitants satisfying it.

The Ty.refine constructor itself lives in `Foundation/Ty.lean` (per
the `Modal/Refine ctors as foundational` decision).  This file
provides the supporting machinery: predicate representation,
decidability, etc.

## RefinePredicate

```lean
structure RefinePredicate (base : Ty level scope) where
  pred       : Term ctx base raw → Prop
  decidable  : Decidable (pred t)  -- for Lean-internal fragment
  smtCertify : Bool                -- true if SMT-cert recheck path used
```

## Examples

* `nat { x > 0 } = Ty.refine nat (fun n => 0 < n)`
* `string { length > 0 }`
* `list(a) { sorted }` (sorted-list type)
* `array(u8, 256)` (array of fixed length 256 — refinement on `nat`
  position width)

## Boundaries: where predicates are checked

Per fx_design.md §10.8 (trust boundaries):

* **Lean-internal fragment**: predicate is `Decidable` in Lean —
  checks happen at typecheck time
* **SMT-cert fragment**: predicate is decidable by SMT solver —
  validator generated at trust boundary, runtime check emits
  certificate
* **Axiom fragment**: predicate is undecidable — only `axiom`
  marker (rare)

Most common refinements (linear arithmetic, bit-vector ops) fall
into the Lean-internal fragment via `Decidable` instances.

## Subtype semantics

`Ty.refine T p` is a subtype of `T`.  Inhabitants are pairs `(t, h)`
where `t : T` and `h : pred t`.  Coercion to base is the first
projection; weakening from `T` requires a proof of `p`.

## Dependencies

* `Foundation/Ty.lean` — `Ty.refine` constructor

## Downstream

* `Refine/Term.lean` — intro/elim
* `Refine/Decidable.lean` — Lean-internal decision
* `Refine/SMTCert.lean` — SMT-cert format
* `Refine/SMTRecheck.lean` — Lean-side rechecker

## Implementation plan (Phase 9)

1. Define `RefinePredicate` structure
2. Define attached metadata (decidable, smt_certify, ...)
3. Smoke: simple `nat { x > 0 }` example with `Decidable`
   discharge

Target: ~150 lines.
-/

namespace LeanFX2.Refine

-- TODO Phase 9: RefinePredicate structure
-- TODO Phase 9: example refinement types

end LeanFX2.Refine

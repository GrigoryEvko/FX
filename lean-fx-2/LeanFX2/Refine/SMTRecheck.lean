/-! # Refine/SMTRecheck — Lean-side certificate validator

Given an `SMTCert`, validate it inside Lean (no SMT solver in the
trust base).  Produces a `Decidable` result that the elaborator can
use to discharge refinement obligations.

## Validator structure

```lean
def SMTCert.validate
    (cert : SMTCert)
    (target : RefinePredicate base)
    (term : Term ctx base raw) :
    Decidable (target.pred term)
```

For each `SMTCert` constructor, validate by reconstructing the proof
from first principles:
* `linarith` cert: combine inequality coefficients and check the
  linear combination zeroes the goal
* `bvtable` cert: check the bit-vector truth table satisfies the goal
* `quantified` cert: instantiate witness, recurse on sub-cert

## Why a Lean rechecker

Trusting an SMT solver requires `axiom Z3Sound` (or analog).  The
rechecker pattern lifts the trust base from "the solver is correct"
to "Lean's logic is correct" — which we already trust (Layer 1 in
AXIOMS.md).

## Performance

Validation is much cheaper than solving (linear in cert size vs
exponential in problem size).  For typical refinements (linear
arithmetic, bv ops), validation is sub-millisecond.

## Dependencies

* `Refine/SMTCert.lean`

## Downstream

* `Refine/Decidable.lean` — falls back to SMT path when Lean-internal
  decidable instance not found
* fx_design.md §10.7 — boundary semantics

## Implementation plan (Phase 9 — actually Layer 8)

1. Define validator per SMTCert ctor
2. Each ctor case: recompute the proof from witnesses
3. Smoke: round-trip generate-from-Lean-decidable / validate

Target: ~300 lines.
-/

namespace LeanFX2.Refine

-- TODO Layer 8: SMTCert.validate per ctor
-- TODO Layer 8: integration with Decidable typeclass

end LeanFX2.Refine

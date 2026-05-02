import LeanFX2.Refine.Ty

/-! # Refine/Decidable — Lean-internal decidable refinements

For refinements whose predicate has a `Decidable` instance in Lean,
the typechecker discharges proof obligations directly without SMT.

## Decidable predicate fragment

Includes:
* Linear arithmetic over `Nat` / `Int` (`x > 0`, `x ≤ 10`, etc.)
* Bit-vector operations (`bits(n).aligned`, etc.)
* Boolean combinations of decidable predicates
* Pattern matches with finite case analysis (constructor-shape preds)

## Decision interface

```lean
class DecidableRefine (R : RefinePredicate base) where
  decide : (t : Term ctx base raw) → Decidable (R.pred t)
```

Instances are typically synthesized via Lean's `Decidable` typeclass
machinery.

## Auto-discharge in elaboration

When elaborating `Term.refineIntro term`, the elaborator looks for
a `DecidableRefine` instance.  If found and the decision returns
`isTrue`, the refinement is discharged with the proof; if `isFalse`,
elaboration error with the counterexample.

## Failure path

If no `DecidableRefine` instance exists, elaboration looks for
SMT-certifiable preds (`Refine/SMTCert.lean`).  Failing both, the
refinement is rejected as undecidable (or marked with `axiom`).

## Dependencies

* `Refine/Ty.lean`

## Downstream

* Elaboration in `Surface/Elab.lean`
* Type checking in `Algo/Check.lean`

## Implementation plan (Phase 9)

1. Define `DecidableRefine` typeclass
2. Provide instances for common refinement shapes
3. Smoke: `nat { x > 0 }` with constant `5` gets discharged
4. Smoke: `nat { x > 0 }` with constant `0` gets rejected

Target: ~150 lines.
-/

namespace LeanFX2.Refine

-- TODO Phase 9: DecidableRefine typeclass
-- TODO Phase 9: instances for common preds (>, <, =, mod, alignment)
-- TODO Phase 9: integration with elaboration

end LeanFX2.Refine

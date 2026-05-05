/-! # Refine/SMTCert — SMT certificate format

For predicates beyond Lean's `Decidable` fragment but within
SMT's reach (linear arithmetic over reals, bit vectors, arrays,
quantified theories), we use **certificates** — proof artifacts
produced by an external solver and rechecked inside Lean without
trusting the solver.

## Certificate format

```lean
inductive SMTCert
  | constant (term : Term ctx ty raw) (predValue : Bool)
  | linarith (terms : List ...) (combination : List ...)
  | bvtable (vars : List ...) (rows : List ...)
  | quantified (witnessTerm : ...) (subCert : SMTCert)
  -- ... extensible per SMT theory
```

A certificate is **proof data** — once constructed, the Lean-side
rechecker (`Refine/SMTRecheck.lean`) validates the certificate's
soundness from first principles.  No `axiom` of the SMT solver's
correctness is needed.

## Why certificates over axioms

Trusting Z3/CVC5 directly requires `axiom Z3_correct : ...`.  With
certificates we get:
* Solver bugs do not corrupt our trust base
* Different solvers produce certificates we recheck identically
* Audit trail (the certificate is the proof, inspectable)

## Certificate generation

Build process: Lean elaboration encounters refinement obligation
that's not Lean-decidable.  Compiler emits SMT problem.  Solver
returns proof.  Proof is parsed into `SMTCert`.  Rechecker validates.
Decidable instance built from validation.

## Dependencies

* `Refine/Ty.lean`

## Downstream

* `Refine/SMTRecheck.lean` — rechecks certs
* `Algo/Check.lean` — uses cert path when Decidable not available
* fx_design.md §10.7 — full SMT semantics

## Implementation plan (Phase 9)

1. Define `SMTCert` inductive (extensible per theory)
2. Each theory case carries proof witnesses (not raw solver output)
3. Smoke: linarith cert for `a + b > 0 ∧ a > 0 → b ≠ 0`

Target: ~250 lines.
-/

namespace LeanFX2.Refine

-- TODO Phase 9: SMTCert inductive (linarith, bvtable, quantified, ...)
-- TODO Phase 9: certificate construction interface
-- TODO Phase 9: integration with elaboration

end LeanFX2.Refine

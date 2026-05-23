import LeanFX2.Foundation.Polygraph.Generator
import LeanFX2.Tools.DependencyAudit

/-! # AuditGenerator — zero-axiom audit for the polygraph Generator spike.

Smoke gates for accelerate-P2.0 (#2121) — the GO/NO-GO spike on whether
the polygraph re-foundation's `Generator`-coded dependent output types
can be extracted cast-free.

## Coverage

* `Generator` enum (10 ctors covering atomic / closed-type / dependent
  shape-classes).
* `Generator.arity` total lookup function.
* `Generator.binderShifts` per-child binder-shift table (non-dependent
  `List Nat` to dodge the Fin-indexed propext leak — see file header).
* `Generator.binderShifts_length_eq_arity` discipline lemma.
* **`Generator.outputTypeAppPi`** — the load-bearing spike artifact:
  extracts the dependent `appPi` output type from typed children
  cast-free.
* `Generator.outputTypeAppPi_matches_Term_appPi` — the spike's
  headline rfl-verified equality showing the Generator output type
  matches `Term.appPi`'s output type definitionally.

All clean = SPIKE-PASS (preliminary, dependent-typed-children case).
The opaque-children case (P2.2) is documented in
`Foundation/Polygraph/Generator.lean` trailing comment block.
-/

namespace LeanFX2.SmokeGenerator

#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.arity
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.binderShifts
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.binderShifts_length_eq_arity
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeAppPi
#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeAppPi_matches_Term_appPi

#print axioms LeanFX2.Foundation.Polygraph.Generator
#print axioms LeanFX2.Foundation.Polygraph.Generator.arity
#print axioms LeanFX2.Foundation.Polygraph.Generator.binderShifts
#print axioms LeanFX2.Foundation.Polygraph.Generator.binderShifts_length_eq_arity
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeAppPi
#print axioms LeanFX2.Foundation.Polygraph.Generator.outputTypeAppPi_matches_Term_appPi

end LeanFX2.SmokeGenerator

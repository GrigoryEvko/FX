import LeanFX2.Foundation.Polygraph.Generator
import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.StrictHarness.TrustEscape

/-! # AuditGenerator — zero-axiom audit for the polygraph Generator.

Smoke gates for **two consecutive ships** along the polygraph re-foundation:

* accelerate-P2.0 (#2121) — the GO/NO-GO spike on whether dependent
  output types extract cast-free from typed children.
* accelerate-P2.1 (#2122) — the full 74-summand `Generator` enum +
  `arity` + `binderShifts` (one summand per `RawTerm` ctor).

## Coverage

* `Generator` enum — 74 ctors mirroring `LeanFX2.RawTerm`.  The
  ctor-count ratchet below pins the bijection.
* `Generator.arity` — total `Generator → Nat` lookup.
* `Generator.binderShifts` — per-child binder-shift table as a
  non-dependent `List Nat` (Fin-indexed dependent matches leak
  propext — see `feedback_lean_zero_axiom_match.md`).
* `Generator.binderShifts_length_eq_arity` — discipline lemma
  recovering the total-function invariant `binderShifts.length =
  arity`, closed by `cases <;> rfl` across all 74 arms.
* `Generator.outputTypeAppPi` — the load-bearing P2.0 spike
  artifact: extracts the dependent `appPi` output type from typed
  children cast-free.
* `Generator.outputTypeAppPi_matches_Term_appPi` — the spike's
  headline rfl-verified equality.

All `#assert_no_axioms` clean = SPIKE-PASS + enum bijection lock-in.
The opaque-children outputType case (P2.2) is documented in the
Generator file's trailing comment block.

## Bijection invariant

The `#assert_inductive_ctor_count_ratchet` below holds the
`Generator` ctor count at 74 — equal to `LeanFX2.RawTerm`'s ctor
count (pinned at 74 by `Tools/AuditAll/GatesIndCount.lean:20`).
If a new `RawTerm` ctor lands, both ratchets must be bumped
together; the polygraph relies on the bijection.
-/

namespace LeanFX2.SmokeGenerator

-- Ctor-count ratchet: locks Generator at 74 ctors, matching RawTerm.
#assert_inductive_ctor_count_ratchet
  LeanFX2.Foundation.Polygraph.Generator 74

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

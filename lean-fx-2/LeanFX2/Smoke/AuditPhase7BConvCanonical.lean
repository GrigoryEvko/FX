import LeanFX2.Reduction.ConvCanonical

/-! Phase 7.B — Conv canonical theorems zero-axiom audit.

For each nullary canonical-head Term ctor, two terms with that
raw projection are convertible (regardless of the *stated* type
since the raw form forces the type via Phase 7.A inversion).

These give the BASE CASES of typed conversion checking:
when both sides reduce to canonical heads with matching ctors,
typed Conv follows immediately.
-/

namespace LeanFX2.SmokePhase7BConvCanonical

#print axioms LeanFX2.Conv.canonical_unit
#print axioms LeanFX2.Conv.canonical_boolTrue
#print axioms LeanFX2.Conv.canonical_boolFalse
#print axioms LeanFX2.Conv.canonical_natZero

end LeanFX2.SmokePhase7BConvCanonical

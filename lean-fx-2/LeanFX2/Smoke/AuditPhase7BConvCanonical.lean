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
#print axioms LeanFX2.Conv.canonical_listNil
#print axioms LeanFX2.Conv.canonical_optionNone
#print axioms LeanFX2.Conv.canonical_refl
#print axioms LeanFX2.Conv.natSucc_cong
#print axioms LeanFX2.Conv.boolElimScrutinee_cong
#print axioms LeanFX2.Conv.natElimScrutinee_cong
#print axioms LeanFX2.Conv.natRecScrutinee_cong
#print axioms LeanFX2.Conv.boolElimThen_cong_unit
#print axioms LeanFX2.Conv.boolElimThen_cong_bool
#print axioms LeanFX2.Conv.boolElimThen_cong_nat
#print axioms LeanFX2.Conv.boolElimElse_cong_unit
#print axioms LeanFX2.Conv.boolElimElse_cong_bool
#print axioms LeanFX2.Conv.boolElimElse_cong_nat

end LeanFX2.SmokePhase7BConvCanonical

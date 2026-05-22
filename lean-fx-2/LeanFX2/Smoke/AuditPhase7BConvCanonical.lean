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
#print axioms LeanFX2.Conv.natElimZero_cong_unit
#print axioms LeanFX2.Conv.natElimZero_cong_bool
#print axioms LeanFX2.Conv.natElimZero_cong_nat
#print axioms LeanFX2.Conv.natRecZero_cong_unit
#print axioms LeanFX2.Conv.intervalOpp_cong
#print axioms LeanFX2.Conv.cong2_at_isClosedTy
#print axioms LeanFX2.Conv.intervalMeet_cong
#print axioms LeanFX2.Conv.intervalJoin_cong
#print axioms LeanFX2.Conv.unit_cong
#print axioms LeanFX2.Conv.boolTrue_cong
#print axioms LeanFX2.Conv.boolFalse_cong
#print axioms LeanFX2.Conv.natZero_cong
#print axioms LeanFX2.Conv.listNil_cong
#print axioms LeanFX2.Conv.optionNone_cong
#print axioms LeanFX2.Conv.interval0_cong
#print axioms LeanFX2.Conv.interval1_cong
#print axioms LeanFX2.Conv.var_cong
#print axioms LeanFX2.Conv.refl_cong
#print axioms LeanFX2.Conv.universeCode_cong
#print axioms LeanFX2.Conv.equivReflId_cong
#print axioms LeanFX2.Conv.funextRefl_cong
#print axioms LeanFX2.Conv.equivReflIdAtId_cong
#print axioms LeanFX2.Conv.funextReflAtId_cong
#print axioms LeanFX2.Conv.oeqRefl_cong
#print axioms LeanFX2.Conv.idStrictRefl_cong
#print axioms LeanFX2.Conv.arrowCode_cong
#print axioms LeanFX2.Conv.piTyCode_cong
#print axioms LeanFX2.Conv.sigmaTyCode_cong
#print axioms LeanFX2.Conv.productCode_cong
#print axioms LeanFX2.Conv.sumCode_cong
#print axioms LeanFX2.Conv.listCode_cong
#print axioms LeanFX2.Conv.optionCode_cong
#print axioms LeanFX2.Conv.eitherCode_cong
#print axioms LeanFX2.Conv.idCode_cong
#print axioms LeanFX2.Conv.equivCode_cong

end LeanFX2.SmokePhase7BConvCanonical

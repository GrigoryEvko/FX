import LeanFX2.Algo.RawWHNFCorrect

/-! Phase 9.A.1 ?-projection inversion lemmas zero-axiom audit.

The inversions recover the constructor form of a RawTerm from a
witness that one of the WHNF helper projections returns `some`.
Foundation for the upcoming `RawTerm.whnf_reaches` correctness
theorem (Phase 9.A.2).
-/

namespace LeanFX2.SmokePhase9AInversions

#print axioms LeanFX2.RawTerm.eq_lam_of_lamBody?_eq_some
#print axioms LeanFX2.RawTerm.eq_pair_of_pairComponents?_eq_some
#print axioms LeanFX2.RawTerm.eq_natSucc_of_natSuccPred?_eq_some
#print axioms LeanFX2.RawTerm.eq_listCons_of_listConsParts?_eq_some
#print axioms LeanFX2.RawTerm.eq_optionSome_of_optionSomeValue?_eq_some
#print axioms LeanFX2.RawTerm.eq_eitherInl_of_eitherInlValue?_eq_some
#print axioms LeanFX2.RawTerm.eq_eitherInr_of_eitherInrValue?_eq_some

end LeanFX2.SmokePhase9AInversions

import LeanFX2.Algo.RawWHNFCorrect

/-! Phase 9.A.1 + 9.A.2 zero-axiom audit.

7 ?-projection inversion lemmas (Phase 9.A.1) recover the
constructor form of a RawTerm from a witness that a WHNF
projection helper returns `some`.

Headline `RawTerm.whnf_reaches` (Phase 9.A.2): every output of
the WHNF reducer is reachable from the input via the reflexive-
transitive closure of parallel reduction.  Soundness of WHNF
with respect to the kernel reduction relation.
-/

namespace LeanFX2.SmokePhase9AInversions

#print axioms LeanFX2.RawTerm.eq_lam_of_lamBody?_eq_some
#print axioms LeanFX2.RawTerm.eq_pair_of_pairComponents?_eq_some
#print axioms LeanFX2.RawTerm.eq_natSucc_of_natSuccPred?_eq_some
#print axioms LeanFX2.RawTerm.eq_listCons_of_listConsParts?_eq_some
#print axioms LeanFX2.RawTerm.eq_optionSome_of_optionSomeValue?_eq_some
#print axioms LeanFX2.RawTerm.eq_eitherInl_of_eitherInlValue?_eq_some
#print axioms LeanFX2.RawTerm.eq_eitherInr_of_eitherInrValue?_eq_some

#print axioms LeanFX2.RawTerm.whnf_reaches
#print axioms LeanFX2.RawTerm.whnf_agreement_join

end LeanFX2.SmokePhase9AInversions

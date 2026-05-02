import LeanFX2.Term.HEqCongr

/-! Phase 2 zero-axiom audit — Term HEq congruence lemmas.

These 18 ctor congruence lemmas are the foundational scaffolding for
all HEq cascades in downstream Compat / Confluence / Bridge layers.
Each must be zero-axiom to maintain kernel discipline. -/

#print axioms LeanFX2.Term.app_HEq_congr
#print axioms LeanFX2.Term.lam_HEq_congr
#print axioms LeanFX2.Term.appPi_HEq_congr
#print axioms LeanFX2.Term.lamPi_HEq_congr
#print axioms LeanFX2.Term.pair_HEq_congr
#print axioms LeanFX2.Term.fst_HEq_congr
#print axioms LeanFX2.Term.snd_HEq_congr
#print axioms LeanFX2.Term.boolElim_HEq_congr
#print axioms LeanFX2.Term.natSucc_HEq_congr
#print axioms LeanFX2.Term.natElim_HEq_congr
#print axioms LeanFX2.Term.natRec_HEq_congr
#print axioms LeanFX2.Term.listCons_HEq_congr
#print axioms LeanFX2.Term.listElim_HEq_congr
#print axioms LeanFX2.Term.optionSome_HEq_congr
#print axioms LeanFX2.Term.optionMatch_HEq_congr
#print axioms LeanFX2.Term.eitherInl_HEq_congr
#print axioms LeanFX2.Term.eitherInr_HEq_congr
#print axioms LeanFX2.Term.eitherMatch_HEq_congr
#print axioms LeanFX2.Term.refl_HEq_congr
#print axioms LeanFX2.Term.idJ_HEq_congr
#print axioms LeanFX2.Term.modIntro_HEq_congr
#print axioms LeanFX2.Term.modElim_HEq_congr
#print axioms LeanFX2.Term.subsume_HEq_congr

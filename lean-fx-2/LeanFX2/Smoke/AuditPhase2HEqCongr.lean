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
#print axioms LeanFX2.Term.cumulUp_HEq_congr
#print axioms LeanFX2.Term.equivReflId_HEq_congr
#print axioms LeanFX2.Term.funextRefl_HEq_congr
#print axioms LeanFX2.Term.equivReflIdAtId_HEq_congr
#print axioms LeanFX2.Term.funextReflAtId_HEq_congr
#print axioms LeanFX2.Term.uaToEquiv_HEq_congr
#print axioms LeanFX2.Term.equivApply_HEq_congr
#print axioms LeanFX2.Term.var_HEq_congr
#print axioms LeanFX2.Term.unit_HEq_congr
#print axioms LeanFX2.Term.boolTrue_HEq_congr
#print axioms LeanFX2.Term.boolFalse_HEq_congr
#print axioms LeanFX2.Term.natZero_HEq_congr
#print axioms LeanFX2.Term.listNil_HEq_congr
#print axioms LeanFX2.Term.optionNone_HEq_congr
#print axioms LeanFX2.Term.interval0_HEq_congr
#print axioms LeanFX2.Term.interval1_HEq_congr
#print axioms LeanFX2.Term.intervalOpp_HEq_congr
#print axioms LeanFX2.Term.intervalMeet_HEq_congr
#print axioms LeanFX2.Term.intervalJoin_HEq_congr
#print axioms LeanFX2.Term.pathLam_HEq_congr
#print axioms LeanFX2.Term.pathApp_HEq_congr
#print axioms LeanFX2.Term.glueIntro_HEq_congr
#print axioms LeanFX2.Term.glueElim_HEq_congr
#print axioms LeanFX2.Term.hcomp_HEq_congr
#print axioms LeanFX2.Term.recordIntro_HEq_congr
#print axioms LeanFX2.Term.recordProj_HEq_congr
#print axioms LeanFX2.Term.refineElim_HEq_congr
#print axioms LeanFX2.Term.codataDest_HEq_congr
#print axioms LeanFX2.Term.sessionRecv_HEq_congr
#print axioms LeanFX2.Term.equivApp_HEq_congr
#print axioms LeanFX2.Term.oeqRefl_HEq_congr
#print axioms LeanFX2.Term.oeqJ_HEq_congr
#print axioms LeanFX2.Term.oeqFunext_HEq_congr
#print axioms LeanFX2.Term.idStrictRefl_HEq_congr
#print axioms LeanFX2.Term.idStrictRec_HEq_congr
#print axioms LeanFX2.Term.universeCode_HEq_congr
#print axioms LeanFX2.Term.arrowCode_HEq_congr
#print axioms LeanFX2.Term.piTyCode_HEq_congr
#print axioms LeanFX2.Term.sigmaTyCode_HEq_congr
#print axioms LeanFX2.Term.productCode_HEq_congr
#print axioms LeanFX2.Term.sumCode_HEq_congr
#print axioms LeanFX2.Term.listCode_HEq_congr
#print axioms LeanFX2.Term.optionCode_HEq_congr
#print axioms LeanFX2.Term.eitherCode_HEq_congr
#print axioms LeanFX2.Term.idCode_HEq_congr
#print axioms LeanFX2.Term.equivCode_HEq_congr

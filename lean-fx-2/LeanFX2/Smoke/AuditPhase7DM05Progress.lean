import LeanFX2.Algo.Progress

/-! Phase 7.D — M05 Progress lemma zero-axiom audit.

Each `#print axioms` below MUST report
"does not depend on any axioms" for the build to count as Progress
shipping under the strict-zero-axiom policy of `lean-fx-2/CLAUDE.md`. -/

#print axioms LeanFX2.Term.headCtor_lam_raw
#print axioms LeanFX2.Term.headCtor_pair_raw
#print axioms LeanFX2.Term.headCtor_refl_raw
#print axioms LeanFX2.Term.headCtor_lamPi_raw
#print axioms LeanFX2.Term.headCtor_modIntro_raw
#print axioms LeanFX2.Term.headCtor_recordIntro_raw
#print axioms LeanFX2.Term.headCtor_pathLam_raw
#print axioms LeanFX2.Term.headCtor_glueIntro_raw
#print axioms LeanFX2.Term.headCtor_refineIntro_raw
#print axioms LeanFX2.Term.headCtor_codataUnfold_raw
#print axioms LeanFX2.Term.headCtor_universeCode_raw
#print axioms LeanFX2.Term.headCtor_arrowCode_raw
#print axioms LeanFX2.Term.headCtor_piTyCode_raw
#print axioms LeanFX2.Term.headCtor_sigmaTyCode_raw
#print axioms LeanFX2.Term.headCtor_productCode_raw
#print axioms LeanFX2.Term.headCtor_sumCode_raw
#print axioms LeanFX2.Term.headCtor_listCode_raw
#print axioms LeanFX2.Term.headCtor_optionCode_raw
#print axioms LeanFX2.Term.headCtor_eitherCode_raw
#print axioms LeanFX2.Term.headCtor_idCode_raw
#print axioms LeanFX2.Term.headCtor_equivCode_raw
#print axioms LeanFX2.Term.headCtor_interval0_raw
#print axioms LeanFX2.Term.headCtor_interval1_raw
#print axioms LeanFX2.Term.headCtor_intervalOpp_raw
#print axioms LeanFX2.Term.headCtor_intervalMeet_raw
#print axioms LeanFX2.Term.headCtor_intervalJoin_raw
#print axioms LeanFX2.Term.headCtor_equivReflId_raw
#print axioms LeanFX2.Term.headCtor_funextRefl_raw
#print axioms LeanFX2.Term.headCtor_equivReflIdAtId_raw
#print axioms LeanFX2.Term.headCtor_funextReflAtId_raw
#print axioms LeanFX2.Term.headCtor_equivIntroHet_raw
#print axioms LeanFX2.Term.headCtor_uaIntroHet_raw
#print axioms LeanFX2.Term.headCtor_funextIntroHet_raw
#print axioms LeanFX2.Term.headCtor_oeqRefl_raw
#print axioms LeanFX2.Term.headCtor_idStrictRefl_raw
#print axioms LeanFX2.Term.app_lam_steps
#print axioms LeanFX2.Term.appPi_lamPi_steps
#print axioms LeanFX2.Term.fst_pair_steps
#print axioms LeanFX2.Term.snd_pair_steps
#print axioms LeanFX2.Term.boolElim_boolTrue_steps
#print axioms LeanFX2.Term.boolElim_boolFalse_steps
#print axioms LeanFX2.Term.natElim_natZero_steps
#print axioms LeanFX2.Term.natElim_natSucc_steps
#print axioms LeanFX2.Term.natRec_natZero_steps
#print axioms LeanFX2.Term.natRec_natSucc_steps
#print axioms LeanFX2.Term.listElim_listNil_steps
#print axioms LeanFX2.Term.listElim_listCons_steps
#print axioms LeanFX2.Term.optionMatch_optionNone_steps
#print axioms LeanFX2.Term.optionMatch_optionSome_steps
#print axioms LeanFX2.Term.eitherMatch_eitherInl_steps
#print axioms LeanFX2.Term.eitherMatch_eitherInr_steps
#print axioms LeanFX2.Term.idJ_refl_steps
#print axioms LeanFX2.Term.idStrictRec_idStrictRefl_steps
#print axioms LeanFX2.Term.modElim_modIntro_steps
#print axioms LeanFX2.Term.pathApp_pathLam_steps
#print axioms LeanFX2.Term.glueElim_glueIntro_steps
#print axioms LeanFX2.Term.transp_pathRefl_steps
#print axioms LeanFX2.Term.recordProj_recordIntro_steps
#print axioms LeanFX2.Term.refineElim_refineIntro_steps
#print axioms LeanFX2.Term.codataDest_codataUnfold_steps
#print axioms LeanFX2.Term.cumulUp_inner_steps

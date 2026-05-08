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

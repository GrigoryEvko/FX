import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.SubstHEq

Tait reducibility — `Term.weaken_subst_singleton_*_heq`
family for every term constructor, plus the supporting cast/HEq
glue (`of_neutral_progress_closure`, `of_type_eq_*_cast`,
`of_heq`, `Term.type_eq_cast_heq`, `Term.raw_eq_cast_heq`,
`Term.type_raw_eq_cast_heq`, `Term.subst_type_eq_cast_heq`,
`Term.rename_type_eq_cast_heq`, `Term.weaken_head_type_eq_heq`,
`Ty.weaken_subst_lift_singleton`, `RawTerm.subst_lift_singleton_eq_subst0`,
`RawTerm.weaken_lift_subst_singleton_lift`),
`Reducible.of_varShape`, `TermSubst.identity` / `renameOutput`
/ `precomposeRenaming`
/ `consSingleton`, and `TermSubst.lift_zero_subst_singleton_heq`.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms Reducible.of_raw_eq_cast
#print axioms Reducible.of_heq
#print axioms Term.type_eq_cast_heq
#print axioms Term.raw_eq_cast_heq
#print axioms Term.type_raw_eq_cast_heq
#print axioms Term.subst_type_eq_cast_heq
#print axioms Term.rename_type_eq_cast_heq
#print axioms Term.weaken_head_type_eq_heq
#print axioms Ty.weaken_subst_lift_singleton
#print axioms RawTerm.subst_lift_singleton_eq_subst0
#print axioms RawTerm.weaken_lift_subst_singleton_lift
#print axioms Reducible.of_varShape
#print axioms TermSubst.identity
#print axioms TermSubst.renameOutput
#print axioms TermSubst.precomposeRenaming
#print axioms TermSubst.consSingleton
#print axioms TermSubst.lift_zero_subst_singleton_heq
#print axioms Term.weaken_subst_singleton_var_heq
#print axioms Term.weaken_subst_singleton_unit_heq
#print axioms Term.weaken_subst_singleton_boolTrue_heq
#print axioms Term.weaken_subst_singleton_boolFalse_heq
#print axioms Term.weaken_subst_singleton_natZero_heq
#print axioms Term.weaken_subst_singleton_lam_heq
#print axioms Term.weaken_subst_singleton_lamPi_heq
#print axioms Term.weaken_subst_singleton_listNil_heq
#print axioms Term.weaken_subst_singleton_optionNone_heq
#print axioms Term.weaken_subst_singleton_interval0_heq
#print axioms Term.weaken_subst_singleton_interval1_heq
#print axioms Term.weaken_subst_singleton_natSucc_heq
#print axioms Term.weaken_subst_singleton_listCons_heq
#print axioms Term.weaken_subst_singleton_optionSome_heq
#print axioms Term.weaken_subst_singleton_eitherInl_heq
#print axioms Term.weaken_subst_singleton_eitherInr_heq
#print axioms Term.weaken_subst_singleton_intervalOpp_heq
#print axioms Term.weaken_subst_singleton_intervalMeet_heq
#print axioms Term.weaken_subst_singleton_intervalJoin_heq
#print axioms Term.weaken_subst_singleton_pathLam_heq
#print axioms Term.weaken_subst_singleton_modIntro_heq
#print axioms Term.weaken_subst_singleton_modElim_heq
#print axioms Term.weaken_subst_singleton_subsume_heq
#print axioms Term.weaken_subst_singleton_app_heq
#print axioms Term.weaken_subst_singleton_natElim_heq
#print axioms Term.weaken_subst_singleton_natRec_heq
#print axioms Term.weaken_subst_singleton_listElim_heq
#print axioms Term.weaken_subst_singleton_optionMatch_heq
#print axioms Term.weaken_subst_singleton_eitherMatch_heq
#print axioms Term.weaken_subst_singleton_refl_heq
#print axioms Term.weaken_subst_singleton_idJ_heq
#print axioms Term.weaken_subst_singleton_oeqRefl_heq
#print axioms Term.weaken_subst_singleton_oeqJ_heq
#print axioms Term.weaken_subst_singleton_oeqFunext_heq
#print axioms Term.weaken_subst_singleton_idStrictRefl_heq
#print axioms Term.weaken_subst_singleton_idStrictRec_heq
#print axioms Term.weaken_subst_singleton_universeCode_heq
#print axioms Term.weaken_subst_singleton_arrowCode_heq
#print axioms Term.weaken_subst_singleton_piTyCode_heq
#print axioms Term.weaken_subst_singleton_sigmaTyCode_heq
#print axioms Term.weaken_subst_singleton_productCode_heq
#print axioms Term.weaken_subst_singleton_sumCode_heq
#print axioms Term.weaken_subst_singleton_listCode_heq
#print axioms Term.weaken_subst_singleton_optionCode_heq
#print axioms Term.weaken_subst_singleton_eitherCode_heq
#print axioms Term.weaken_subst_singleton_idCode_heq
#print axioms Term.weaken_subst_singleton_equivCode_heq
#print axioms Term.weaken_subst_singleton_equivReflId_heq
#print axioms Term.weaken_subst_singleton_equivReflIdAtId_heq
#print axioms Term.weaken_subst_singleton_funextRefl_heq
#print axioms Term.weaken_subst_singleton_funextReflAtId_heq
#print axioms Term.weaken_subst_singleton_glueIntro_heq
#print axioms Term.weaken_subst_singleton_transp_heq
#print axioms Term.weaken_subst_singleton_hcomp_heq
#print axioms Term.weaken_subst_singleton_recordIntro_heq
#print axioms Term.weaken_subst_singleton_refineIntro_heq
#print axioms Term.weaken_subst_singleton_refineElim_heq
#print axioms Term.weaken_subst_singleton_codataUnfold_heq
#print axioms Term.weaken_subst_singleton_sessionSend_heq
#print axioms Term.weaken_subst_singleton_sessionRecv_heq
#print axioms Term.weaken_subst_singleton_uaToEquiv_heq
#print axioms Term.weaken_subst_singleton_pathApp_heq
#print axioms Term.weaken_subst_singleton_glueElim_heq
#print axioms Term.weaken_subst_singleton_recordProj_heq
#print axioms Term.weaken_subst_singleton_codataDest_heq
#print axioms Term.weaken_subst_singleton_equivIntroHet_heq
#print axioms Term.weaken_subst_singleton_equivApp_heq
#print axioms Term.weaken_subst_singleton_equivApply_heq
#print axioms Term.weaken_subst_singleton_uaIntroHet_heq
#print axioms Term.weaken_subst_singleton_funextIntroHet_heq
#print axioms Term.weaken_subst_singleton_cumulUp_heq
#print axioms ReducibleSubst.singleton
#print axioms ReducibleSubst.identity
#print axioms IsRenamingStableReducibleSubst.identity
#print axioms ReducibleSubst.lift_isStronglyNormalizing
#print axioms ReducibleSubst.lift_of_renamingStable
#print axioms Term.strong_normalization_of_identity_subst
#print axioms Reducible.strong_normalization_of_identity_reducible
#print axioms RawTerm.subst_identity_lift
#print axioms RawTerm.subst_identity_isStronglyNormalizing
#print axioms RawTerm.subst_identity_lift_isStronglyNormalizing
#print axioms Reducible.identity_lift_body_sn_of_identity_reducible
#print axioms Reducible.identity_lift_body_sn_of_identity_reducible_at
#print axioms Reducible.fundamental_identity_lam_at_arrow_sn
#print axioms Reducible.fundamental_identity_lamPi_at_piTy_sn
#print axioms Reducible.fundamental_identity_pathLam_at_path_sn
#print axioms Ty.weaken_lift_subst_singleton_lift
#print axioms Term.weaken_subst_singleton_pair_heq
#print axioms Term.weaken_subst_singleton_fst_heq
#print axioms Term.weaken_subst_singleton_snd_heq
#print axioms Term.weaken_subst_singleton_appPi_heq
#print axioms Term.weaken_subst_singleton_boolElim_heq
#print axioms Term.weaken_subst_singleton_effectPerform_heq
#print axioms ReducibleSubst.consSingleton
#print axioms TermSubst.consSingleton_zero_HEq
#print axioms TermSubst.consSingleton_succ_HEq
#print axioms TermSubst.compose_position_HEq
#print axioms Term.type_eq_symm_cast_heq
#print axioms Term.var_zero_cons_type_eq_heq
#print axioms TermSubst.lift_compose_zero_HEq
#print axioms TermSubst.compose_lift_singleton_consSingleton_zero_HEq
#print axioms TermSubst.compose_lift_singleton_consSingleton_succ_of_entry_HEq
#print axioms TermSubst.compose_lift_singleton_consSingleton_pointwise_of_entry
#print axioms Term.subst_compose_lift_singleton_eq_consSingleton_of_entry
#print axioms ReducibleSubst.renameOutput_of_renamingStable
#print axioms TermSubst.renameOutput_position_HEq
#print axioms Term.rename_type_eq_symm_cast_heq
#print axioms TermSubst.precomposeRenaming_position_HEq
#print axioms Term.rename_var_HEq
#print axioms TermSubst.precompose_lift_weaken_singleton_lift_position_HEq

end LeanFX2.Smoke

import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.StableAndVarShape

Tait reducibility — `ReducibleSubst` lifting infrastructure
(`singleton`, `identity`, `consSingleton`, `lift_*` variants),
`Term.strong_normalization_of_identity_subst`, the
identity-subst lift family, the per-Ty `Reducible.X_of_varShape`
headlines (arrow/piTy/sigmaTy/path/glue/refine/equiv/record/
codata/listType/optionType/eitherType/id/oeq/idStrict), their
`X_of_neutral_progress_closure` and `X_of_progress_closure`
siblings, every `step_preserves_X` arm, and the `_stable`
variant of every fundamental case (natSucc/interval*/session*/
effectPerform/universeCode/cumulUp + every modal/subsume/
parametric/eliminator variant).

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms IsRenamingStableReducibleSubst.singleton
#print axioms IsRenamingStableReducibleSubst.consSingleton
#print axioms Reducible.unit_of_varShape
#print axioms Reducible.bool_of_varShape
#print axioms Reducible.nat_of_varShape
#print axioms Reducible.empty_of_varShape
#print axioms Reducible.interval_of_varShape
#print axioms Reducible.universe_of_varShape
#print axioms Reducible.tyVar_of_varShape
#print axioms Reducible.session_of_varShape
#print axioms Reducible.effect_of_varShape
#print axioms Reducible.modal_of_varShape
#print axioms Reducible.arrow_of_varShape
#print axioms Reducible.arrow_of_neutral_progress_closure
#print axioms Reducible.piTy_of_neutral_progress_closure
#print axioms Reducible.sigmaTy_of_neutral_progress_closure
#print axioms Reducible.sigmaTy_of_varShape
#print axioms Reducible.path_of_neutral_progress_closure
#print axioms Reducible.path_of_varShape
#print axioms Reducible.glue_of_neutral_progress_closure
#print axioms Reducible.glue_of_varShape
#print axioms Reducible.refine_of_neutral_progress_closure
#print axioms Reducible.equiv_of_neutral_progress_closure
#print axioms Reducible.equiv_of_varShape
#print axioms Reducible.refine_of_varShape
#print axioms Reducible.record_of_neutral_progress_closure
#print axioms Reducible.record_of_varShape
#print axioms Reducible.codata_of_neutral_progress_closure
#print axioms Reducible.codata_of_varShape
#print axioms Reducible.listType_of_neutral_progress_closure
#print axioms Reducible.listType_of_varShape
#print axioms Reducible.optionType_of_neutral_progress_closure
#print axioms Reducible.optionType_of_varShape
#print axioms Reducible.eitherType_of_neutral_progress_closure
#print axioms Reducible.eitherType_of_varShape
#print axioms Reducible.id_of_neutral_progress_closure
#print axioms Reducible.oeq_of_neutral_progress_closure
#print axioms Reducible.idStrict_of_neutral_progress_closure
#print axioms Reducible.unit_of_progress_closure
#print axioms Reducible.bool_of_progress_closure
#print axioms Reducible.nat_of_progress_closure
#print axioms Reducible.empty_of_progress_closure
#print axioms Reducible.interval_of_progress_closure
#print axioms Reducible.universe_of_progress_closure
#print axioms Reducible.tyVar_of_progress_closure
#print axioms Reducible.session_of_progress_closure
#print axioms Reducible.effect_of_progress_closure
#print axioms Reducible.modal_of_progress_closure
#print axioms Reducible.step_preserves_arrow
#print axioms Reducible.step_preserves_piTy
#print axioms Reducible.step_preserves_sigmaTy
#print axioms Reducible.step_preserves_id
#print axioms Reducible.step_preserves_listType
#print axioms Reducible.step_preserves_optionType
#print axioms Reducible.step_preserves_eitherType
#print axioms Reducible.step_preserves_path
#print axioms Reducible.step_preserves_glue
#print axioms Reducible.step_preserves_oeq
#print axioms Reducible.step_preserves_idStrict
#print axioms Reducible.step_preserves_equiv
#print axioms Reducible.step_preserves_refine
#print axioms Reducible.step_preserves_record
#print axioms Reducible.step_preserves_codata
#print axioms Reducible.step_preserves
#print axioms Reducible.fundamental_natSucc
#print axioms Reducible.fundamental_natSucc_stable
#print axioms Reducible.fundamental_interval0_stable
#print axioms Reducible.fundamental_interval1_stable
#print axioms Reducible.fundamental_intervalOpp_stable
#print axioms Reducible.fundamental_intervalMeet_stable
#print axioms Reducible.fundamental_intervalJoin_stable
#print axioms Reducible.fundamental_sessionRecv_stable
#print axioms Reducible.fundamental_sessionSend_stable
#print axioms Reducible.fundamental_effectPerform_stable
#print axioms Reducible.fundamental_universeCode_stable
#print axioms Reducible.fundamental_cumulUp_stable
#print axioms Reducible.IsSNDirect.rename
#print axioms Reducible.of_isStronglyNormalizing_when_SNDirect
#print axioms IsRenamingStableReducible.of_stableSN_when_SNDirect
#print axioms Reducible.fundamental_subsume_SNDirect
#print axioms Reducible.fundamental_modIntro_SNDirect
#print axioms Reducible.fundamental_modElim_SNDirect
#print axioms Reducible.fundamental_subsume_stable
#print axioms Reducible.fundamental_modIntro_stable
#print axioms Reducible.fundamental_modElim_stable
#print axioms Reducible.fundamental_listNil_at_listType_stable
#print axioms Reducible.fundamental_listCons_at_listType_stable
#print axioms Reducible.fundamental_optionNone_at_optionType_stable
#print axioms Reducible.fundamental_optionSome_at_optionType_stable
#print axioms Reducible.fundamental_eitherInl_at_eitherType_stable
#print axioms Reducible.fundamental_eitherInr_at_eitherType_stable
#print axioms Reducible.fundamental_app_at_arrow_stable
#print axioms Reducible.fundamental_fst_at_sigmaTy_stable
#print axioms Reducible.fundamental_recordProj_at_record_stable
#print axioms Reducible.fundamental_refineElim_at_refine_stable
#print axioms Reducible.fundamental_pathApp_at_path_stable
#print axioms Reducible.fundamental_glueElim_at_glue_stable
#print axioms Reducible.fundamental_equivApp_at_equiv_stable
#print axioms Reducible.fundamental_codataDest_at_codata_stable

end LeanFX2.Smoke

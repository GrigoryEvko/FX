import LeanFX2.Reducibility.Kripke.Predicate
import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.Kripke.Weaken
import LeanFX2.Reducibility.Kripke.Monotone
import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.SNClosure
import LeanFX2.Reducibility.Kripke.Fundamental
import LeanFX2.Reducibility.Kripke.Headline
import LeanFX2.Reducibility.Kripke.Arrow

/-! Kripke Tait reducibility zero-axiom audit log. -/

#print axioms LeanFX2.ReducibleK
#print axioms LeanFX2.ReducibleKBody
#print axioms LeanFX2.ReducibleK.zero_eq_true
#print axioms LeanFX2.ReducibleK.succ_unit_iff_sn
#print axioms LeanFX2.ReducibleK.succ_bool_iff_sn
#print axioms LeanFX2.ReducibleK.succ_nat_iff_sn
#print axioms LeanFX2.ReducibleK.succ_empty_iff_sn
#print axioms LeanFX2.ReducibleK.succ_interval_iff_sn
#print axioms LeanFX2.ReducibleK.weaken_unit
#print axioms LeanFX2.ReducibleK.weaken_bool
#print axioms LeanFX2.ReducibleK.weaken_nat
#print axioms LeanFX2.ReducibleK.weaken_empty
#print axioms LeanFX2.ReducibleK.weaken_interval
#print axioms LeanFX2.ReducibleK.mono_unit
#print axioms LeanFX2.ReducibleK.mono_bool
#print axioms LeanFX2.ReducibleK.mono_nat
#print axioms LeanFX2.ReducibleK.mono_empty
#print axioms LeanFX2.ReducibleK.mono_interval
#print axioms LeanFX2.ReducibleK.sn_of_unit
#print axioms LeanFX2.ReducibleK.sn_of_bool
#print axioms LeanFX2.ReducibleK.sn_of_nat
#print axioms LeanFX2.ReducibleK.sn_of_empty
#print axioms LeanFX2.ReducibleK.sn_of_interval
#print axioms LeanFX2.RawTerm.isStronglyNormalizing.step_closure
#print axioms LeanFX2.Term.isStronglyNormalizing.step_closure
#print axioms LeanFX2.ReducibleK.cr2_unit
#print axioms LeanFX2.ReducibleK.cr2_bool
#print axioms LeanFX2.ReducibleK.cr2_nat
#print axioms LeanFX2.ReducibleK.cr2_empty
#print axioms LeanFX2.ReducibleK.cr2_interval
#print axioms LeanFX2.ReducibleK.fundamental_unit
#print axioms LeanFX2.ReducibleK.fundamental_boolTrue
#print axioms LeanFX2.ReducibleK.fundamental_boolFalse
#print axioms LeanFX2.ReducibleK.fundamental_natZero
#print axioms LeanFX2.Term.unit_strong_normalization_via_kripke
#print axioms LeanFX2.Term.boolTrue_strong_normalization_via_kripke
#print axioms LeanFX2.Term.boolFalse_strong_normalization_via_kripke
#print axioms LeanFX2.Term.natZero_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_var_unit
#print axioms LeanFX2.ReducibleK.fundamental_var_bool
#print axioms LeanFX2.ReducibleK.fundamental_var_nat
#print axioms LeanFX2.ReducibleK.fundamental_var_empty
#print axioms LeanFX2.ReducibleK.fundamental_var_interval
#print axioms LeanFX2.ReducibleK.fundamental_natSucc
#print axioms LeanFX2.ReducibleK.fundamental_listNil
#print axioms LeanFX2.ReducibleK.fundamental_optionNone
#print axioms LeanFX2.ReducibleK.fundamental_listCons_sn
#print axioms LeanFX2.ReducibleK.fundamental_optionSome_sn
#print axioms LeanFX2.ReducibleK.fundamental_eitherInl_sn
#print axioms LeanFX2.ReducibleK.fundamental_eitherInr_sn
#print axioms LeanFX2.ReducibleK.arrow_sn
#print axioms LeanFX2.ReducibleK.arrow_apply
#print axioms LeanFX2.Term.natSucc_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_intervalOpp
#print axioms LeanFX2.ReducibleK.fundamental_intervalMeet
#print axioms LeanFX2.ReducibleK.fundamental_intervalJoin
#print axioms LeanFX2.ReducibleK.fundamental_modIntro_sn
#print axioms LeanFX2.ReducibleK.fundamental_subsume_sn
#print axioms LeanFX2.ReducibleK.fundamental_pair_sn
#print axioms LeanFX2.ReducibleK.fundamental_fst_sn
#print axioms LeanFX2.ReducibleK.fundamental_snd_sn
#print axioms LeanFX2.ReducibleK.fundamental_refl_sn
#print axioms LeanFX2.ReducibleK.fundamental_oeqRefl_sn
#print axioms LeanFX2.ReducibleK.fundamental_idStrictRefl_sn
#print axioms LeanFX2.ReducibleK.fundamental_sessionRecv_sn
#print axioms LeanFX2.ReducibleK.fundamental_sessionSend_sn
#print axioms LeanFX2.ReducibleK.fundamental_cumulUp_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivReflId_sn
#print axioms LeanFX2.ReducibleK.fundamental_uaToEquiv_sn
#print axioms LeanFX2.ReducibleK.fundamental_arrowCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_eitherCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_listCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_optionCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_idCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_recordIntro_sn
#print axioms LeanFX2.ReducibleK.fundamental_recordProj_sn
#print axioms LeanFX2.ReducibleK.fundamental_refineIntro_sn
#print axioms LeanFX2.ReducibleK.fundamental_refineElim_sn
#print axioms LeanFX2.ReducibleK.fundamental_codataUnfold_sn
#print axioms LeanFX2.ReducibleK.fundamental_lam_sn
#print axioms LeanFX2.ReducibleK.fundamental_lamPi_sn
#print axioms LeanFX2.ReducibleK.fundamental_pathLam_sn
#print axioms LeanFX2.ReducibleK.fundamental_glueIntro_sn
#print axioms LeanFX2.ReducibleK.fundamental_glueElim_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivIntroHet_sn
#print axioms LeanFX2.ReducibleK.fundamental_funextRefl_sn
#print axioms LeanFX2.ReducibleK.fundamental_funextReflAtId_sn
#print axioms LeanFX2.ReducibleK.fundamental_oeqFunext_sn
#print axioms LeanFX2.ReducibleK.fundamental_effectPerform_sn
#print axioms LeanFX2.ReducibleK.fundamental_uaIntroHet_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivReflIdAtId_sn
#print axioms LeanFX2.Term.var_strong_normalization_via_kripke
#print axioms LeanFX2.Term.pair_strong_normalization_via_kripke
#print axioms LeanFX2.Term.fst_strong_normalization_via_kripke
#print axioms LeanFX2.Term.snd_strong_normalization_via_kripke
#print axioms LeanFX2.Term.lam_strong_normalization_via_kripke
#print axioms LeanFX2.Term.lamPi_strong_normalization_via_kripke
#print axioms LeanFX2.Term.modIntro_strong_normalization_via_kripke
#print axioms LeanFX2.Term.subsume_strong_normalization_via_kripke
#print axioms LeanFX2.Term.recordIntro_strong_normalization_via_kripke
#print axioms LeanFX2.Term.recordProj_strong_normalization_via_kripke
#print axioms LeanFX2.Term.refineIntro_strong_normalization_via_kripke
#print axioms LeanFX2.Term.refineElim_strong_normalization_via_kripke
#print axioms LeanFX2.Term.codataUnfold_strong_normalization_via_kripke
#print axioms LeanFX2.Term.sessionRecv_strong_normalization_via_kripke
#print axioms LeanFX2.Term.sessionSend_strong_normalization_via_kripke
#print axioms LeanFX2.Term.intervalOpp_strong_normalization_via_kripke
#print axioms LeanFX2.Term.intervalMeet_strong_normalization_via_kripke
#print axioms LeanFX2.Term.intervalJoin_strong_normalization_via_kripke
#print axioms LeanFX2.Term.listNil_strong_normalization_via_kripke
#print axioms LeanFX2.Term.optionNone_strong_normalization_via_kripke
#print axioms LeanFX2.Term.listCons_strong_normalization_via_kripke
#print axioms LeanFX2.Term.optionSome_strong_normalization_via_kripke
#print axioms LeanFX2.Term.eitherInl_strong_normalization_via_kripke
#print axioms LeanFX2.Term.eitherInr_strong_normalization_via_kripke
#print axioms LeanFX2.Term.refl_strong_normalization_via_kripke
#print axioms LeanFX2.Term.oeqRefl_strong_normalization_via_kripke
#print axioms LeanFX2.Term.idStrictRefl_strong_normalization_via_kripke
#print axioms LeanFX2.Term.cumulUp_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivReflId_strong_normalization_via_kripke
#print axioms LeanFX2.Term.uaToEquiv_strong_normalization_via_kripke
#print axioms LeanFX2.Term.arrowCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.eitherCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.listCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.optionCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.idCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.pathLam_strong_normalization_via_kripke
#print axioms LeanFX2.Term.glueIntro_strong_normalization_via_kripke
#print axioms LeanFX2.Term.glueElim_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivIntroHet_strong_normalization_via_kripke
#print axioms LeanFX2.Term.funextRefl_strong_normalization_via_kripke
#print axioms LeanFX2.Term.funextReflAtId_strong_normalization_via_kripke
#print axioms LeanFX2.Term.oeqFunext_strong_normalization_via_kripke
#print axioms LeanFX2.Term.effectPerform_strong_normalization_via_kripke
#print axioms LeanFX2.Term.uaIntroHet_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivReflIdAtId_strong_normalization_via_kripke

-- SN-only eliminator headlines via Kripke (7 wrappers)
#print axioms LeanFX2.Term.boolElim_strong_normalization_via_kripke
#print axioms LeanFX2.Term.idJ_strong_normalization_via_kripke
#print axioms LeanFX2.Term.oeqJ_strong_normalization_via_kripke
#print axioms LeanFX2.Term.idStrictRec_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivApp_strong_normalization_via_kripke
#print axioms LeanFX2.Term.equivApply_strong_normalization_via_kripke
#print axioms LeanFX2.Term.modElim_strong_normalization_via_kripke
#print axioms LeanFX2.Term.natElim_strong_normalization_via_kripke
#print axioms LeanFX2.Term.natRec_strong_normalization_via_kripke

-- K12.26 closed-leaf Kripke headlines (7 new aliases for interval0,
-- interval1, universeCode, piTyCode, sigmaTyCode, productCode, sumCode)
#print axioms LeanFX2.Term.interval0_strong_normalization_via_kripke
#print axioms LeanFX2.Term.interval1_strong_normalization_via_kripke
#print axioms LeanFX2.Term.universeCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.piTyCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.sigmaTyCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.productCode_strong_normalization_via_kripke
#print axioms LeanFX2.Term.sumCode_strong_normalization_via_kripke

-- K12.26 closed-leaf ReducibleK fundamentals delegating to existing
-- Term-level SN helpers (7 new wrappers)
#print axioms LeanFX2.ReducibleK.fundamental_interval0
#print axioms LeanFX2.ReducibleK.fundamental_interval1
#print axioms LeanFX2.ReducibleK.fundamental_universeCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_piTyCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_sigmaTyCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_productCode_sn
#print axioms LeanFX2.ReducibleK.fundamental_sumCode_sn

-- K12.24 funextIntroHet (heterogeneous funext intro, schematic-payload)
#print axioms LeanFX2.Term.funextIntroHet_isStronglyNormalizing
#print axioms LeanFX2.Term.funextIntroHet_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_funextIntroHet_sn

-- K12.25 codataDest (codata destructor with β-fire on codataUnfold)
#print axioms LeanFX2.RawTerm.codataUnfold_state_isStronglyNormalizing
#print axioms LeanFX2.RawTerm.codataUnfold_transition_isStronglyNormalizing
#print axioms LeanFX2.RawTerm.codataDest_isStronglyNormalizing
#print axioms LeanFX2.Term.codataDest_isStronglyNormalizing
#print axioms LeanFX2.Term.codataDest_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_codataDest_sn

-- K12.22 listElim (generic ι recursor with nil-fire + cons-fire contractum closure)
#print axioms LeanFX2.RawTerm.listElim_isStronglyNormalizing
#print axioms LeanFX2.Term.listElim_isStronglyNormalizing
#print axioms LeanFX2.Term.listElim_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_listElim_sn

-- K12.22 optionMatch (generic ι recursor with none-fire + some-fire contractum closure)
#print axioms LeanFX2.RawTerm.optionMatch_isStronglyNormalizing
#print axioms LeanFX2.Term.optionMatch_isStronglyNormalizing
#print axioms LeanFX2.Term.optionMatch_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_optionMatch_sn

-- K12.22 eitherMatch (generic ι recursor with inl-fire + inr-fire contractum closures)
#print axioms LeanFX2.RawTerm.eitherMatch_isStronglyNormalizing
#print axioms LeanFX2.Term.eitherMatch_isStronglyNormalizing
#print axioms LeanFX2.Term.eitherMatch_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_eitherMatch_sn

-- K12.21 app (β-redex; contractum closure consumes body+argument SN)
#print axioms LeanFX2.RawTerm.lam_body_isStronglyNormalizing
#print axioms LeanFX2.RawTerm.app_isStronglyNormalizing
#print axioms LeanFX2.Term.app_isStronglyNormalizing
#print axioms LeanFX2.Term.app_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_app_sn

-- K12.21 appPi (dependent-Π β-redex; reuses raw β rule from app)
#print axioms LeanFX2.Term.appPi_isStronglyNormalizing
#print axioms LeanFX2.Term.appPi_strong_normalization_via_kripke
#print axioms LeanFX2.ReducibleK.fundamental_appPi_sn

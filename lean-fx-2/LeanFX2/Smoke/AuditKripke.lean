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

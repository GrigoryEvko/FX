import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.TermSN

Tait reducibility — Term-level SN gates for every introducer
and elimination form (var, unit, bool, nat, list, option,
either, interval, modal, subsume, oeqFunext, session, effect,
cumulUp, equivRefl, ua, boolElim, idJ, oeqJ, idStrictRec,
recordProj, refineElim, glueElim, equivApp), the
`step_preserves` closed-leaf arms, the `*_neutral_isStronglyNormalizing`
family, and `Term.app_lam_isStronglyNormalizing` + raw aux
helpers for refineIntro/glueIntro values.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms Term.funextRefl_isStronglyNormalizing_of_rawPayloads
#print axioms Term.funextReflAtId_isStronglyNormalizing_of_apply
#print axioms Term.funextReflAtId_isStronglyNormalizing_of_rawPayloads
#print axioms Term.funextIntroHet_isStronglyNormalizing_of_applyLeft
#print axioms Term.funextIntroHet_isStronglyNormalizing_of_rawPayloads
#print axioms Term.var_isStronglyNormalizing
#print axioms Term.unit_isStronglyNormalizing
#print axioms Term.boolTrue_isStronglyNormalizing
#print axioms Term.boolFalse_isStronglyNormalizing
#print axioms Term.natZero_isStronglyNormalizing
#print axioms Term.listNil_isStronglyNormalizing
#print axioms Term.optionNone_isStronglyNormalizing
#print axioms Term.interval0_isStronglyNormalizing
#print axioms Term.interval1_isStronglyNormalizing
#print axioms Term.natSucc_isStronglyNormalizing
#print axioms Term.listCons_isStronglyNormalizing
#print axioms Term.optionSome_isStronglyNormalizing
#print axioms Term.eitherInl_isStronglyNormalizing
#print axioms Term.eitherInr_isStronglyNormalizing
#print axioms Term.fst_isStronglyNormalizing
#print axioms Term.snd_isStronglyNormalizing
#print axioms Term.intervalOpp_isStronglyNormalizing
#print axioms Term.intervalMeet_isStronglyNormalizing
#print axioms Term.intervalJoin_isStronglyNormalizing
#print axioms Term.modIntro_isStronglyNormalizing
#print axioms Term.subsume_isStronglyNormalizing
#print axioms Term.oeqFunext_isStronglyNormalizing
#print axioms Term.sessionRecv_isStronglyNormalizing
#print axioms Term.sessionSend_isStronglyNormalizing
#print axioms Term.effectPerform_isStronglyNormalizing
#print axioms Term.cumulUp_isStronglyNormalizing
#print axioms Term.equivReflId_isStronglyNormalizing
#print axioms Term.equivReflIdAtId_isStronglyNormalizing
#print axioms Term.uaIntroHet_isStronglyNormalizing
#print axioms Term.uaToEquiv_isStronglyNormalizing
#print axioms Term.boolElim_isStronglyNormalizing
#print axioms Term.idJ_isStronglyNormalizing
#print axioms Term.oeqJ_isStronglyNormalizing
#print axioms Term.idStrictRec_isStronglyNormalizing
#print axioms Term.recordProj_isStronglyNormalizing
#print axioms RawTerm.refineIntro_value_isStronglyNormalizing_aux
#print axioms RawTerm.refineIntro_value_isStronglyNormalizing
#print axioms Term.refineElim_isStronglyNormalizing
#print axioms RawTerm.glueIntro_base_isStronglyNormalizing_aux
#print axioms RawTerm.glueIntro_base_isStronglyNormalizing
#print axioms Term.glueElim_isStronglyNormalizing
#print axioms Term.equivApp_isStronglyNormalizing
#print axioms Reducible.step_preserves_unit
#print axioms Reducible.step_preserves_bool
#print axioms Reducible.step_preserves_nat
#print axioms Reducible.step_preserves_empty
#print axioms Reducible.step_preserves_interval
#print axioms Reducible.step_preserves_universe
#print axioms Reducible.step_preserves_tyVar
#print axioms Reducible.step_preserves_session
#print axioms Reducible.step_preserves_effect
#print axioms Reducible.step_preserves_modal
#print axioms RawTerm.var_has_no_progress
#print axioms RawTerm.unit_has_no_progress
#print axioms RawTerm.boolTrue_has_no_progress
#print axioms RawTerm.boolFalse_has_no_progress
#print axioms RawTerm.natZero_has_no_progress
#print axioms RawTerm.app_neutral_isStronglyNormalizing
#print axioms RawTerm.fst_neutral_isStronglyNormalizing
#print axioms RawTerm.snd_neutral_isStronglyNormalizing
#print axioms RawTerm.pathApp_neutral_isStronglyNormalizing
#print axioms RawTerm.glueElim_neutral_isStronglyNormalizing
#print axioms RawTerm.refineElim_neutral_isStronglyNormalizing
#print axioms RawTerm.recordProj_neutral_isStronglyNormalizing
#print axioms RawTerm.codataDest_neutral_isStronglyNormalizing
#print axioms RawTerm.listElim_neutral_isStronglyNormalizing
#print axioms RawTerm.optionMatch_neutral_isStronglyNormalizing
#print axioms RawTerm.eitherMatch_neutral_isStronglyNormalizing
#print axioms RawTerm.idJ_neutral_isStronglyNormalizing
#print axioms RawTerm.oeqJ_neutral_isStronglyNormalizing
#print axioms RawTerm.idStrictRec_neutral_isStronglyNormalizing
#print axioms RawTerm.equivApp_neutral_isStronglyNormalizing
#print axioms Term.app_lam_isStronglyNormalizing
#print axioms Term.isStronglyNormalizing_of_varShape
#print axioms Reducible.of_neutral_progress_closure
#print axioms Reducible.of_type_eq_symm_cast
#print axioms Reducible.of_type_eq_cast
#print axioms Reducible.of_raw_eq_symm_cast

end LeanFX2.Smoke

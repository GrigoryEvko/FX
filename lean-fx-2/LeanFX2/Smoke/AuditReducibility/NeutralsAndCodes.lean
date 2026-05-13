import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.NeutralsAndCodes

Tait reducibility — `RawTerm.IsNeutral` predicate + every
`not_*` ctor-exclusion lemma + every `*_par_preserves`
preservation arm, plus the type-code SN family
(`universeCode`, `arrowCode`, `piTyCode`, `sigmaTyCode`,
`productCode`, `sumCode`, `eitherCode`, `equivCode`,
`listCode`, `optionCode`, `idCode`) at both raw and typed
levels, including their `_of_payloads` fundamentals and the
`identity_*Code_*_of_typeCode_payloads` companions.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms LeanFX2.RawTerm.IsNeutral
#print axioms RawTerm.IsNeutral.not_lam
#print axioms RawTerm.IsNeutral.not_pair
#print axioms RawTerm.IsNeutral.not_boolTrue
#print axioms RawTerm.IsNeutral.not_boolFalse
#print axioms RawTerm.IsNeutral.not_natZero
#print axioms RawTerm.IsNeutral.not_natSucc
#print axioms RawTerm.IsNeutral.not_listNil
#print axioms RawTerm.IsNeutral.not_listCons
#print axioms RawTerm.IsNeutral.not_optionNone
#print axioms RawTerm.IsNeutral.not_optionSome
#print axioms RawTerm.IsNeutral.not_eitherInl
#print axioms RawTerm.IsNeutral.not_eitherInr
#print axioms RawTerm.IsNeutral.not_pathLam
#print axioms RawTerm.IsNeutral.not_glueIntro
#print axioms RawTerm.IsNeutral.not_refl
#print axioms RawTerm.IsNeutral.not_oeqRefl
#print axioms RawTerm.IsNeutral.not_idStrictRefl
#print axioms RawTerm.IsNeutral.not_equivIntro
#print axioms RawTerm.IsNeutral.not_uaToEquiv
#print axioms RawTerm.IsNeutral.not_pathCompose
#print axioms RawTerm.IsNeutral.not_modIntro
#print axioms RawTerm.IsNeutral.not_refineIntro
#print axioms RawTerm.IsNeutral.not_recordIntro
#print axioms RawTerm.IsNeutral.not_codataUnfold
#print axioms RawTerm.IsNeutral.var_par_preserves
#print axioms RawTerm.IsNeutral.app_par_preserves
#print axioms RawTerm.IsNeutral.fst_par_preserves
#print axioms RawTerm.IsNeutral.snd_par_preserves
#print axioms RawTerm.IsNeutral.boolElim_par_preserves
#print axioms RawTerm.IsNeutral.natElim_par_preserves
#print axioms RawTerm.IsNeutral.natRec_par_preserves
#print axioms RawTerm.IsNeutral.listElim_par_preserves
#print axioms RawTerm.IsNeutral.optionMatch_par_preserves
#print axioms RawTerm.IsNeutral.eitherMatch_par_preserves
#print axioms RawTerm.IsNeutral.pathApp_par_preserves
#print axioms RawTerm.IsNeutral.glueElim_par_preserves
#print axioms RawTerm.IsNeutral.hcomp_par_preserves
#print axioms RawTerm.IsNeutral.transp_par_preserves
#print axioms RawTerm.IsNeutral.idJ_par_preserves
#print axioms RawTerm.IsNeutral.oeqJ_par_preserves
#print axioms RawTerm.IsNeutral.idStrictRec_par_preserves
#print axioms RawTerm.IsNeutral.equivApp_par_preserves
#print axioms RawTerm.IsNeutral.equivApply_par_preserves
#print axioms RawTerm.IsNeutral.modElim_par_preserves
#print axioms RawTerm.IsNeutral.subsume_par_preserves
#print axioms RawTerm.IsNeutral.refineElim_par_preserves
#print axioms RawTerm.IsNeutral.recordProj_par_preserves
#print axioms RawTerm.IsNeutral.codataDest_par_preserves
#print axioms RawTerm.IsNeutral.sessionSend_par_preserves
#print axioms RawTerm.IsNeutral.sessionRecv_par_preserves
#print axioms RawTerm.IsNeutral.effectPerform_par_preserves
#print axioms RawTerm.IsNeutral.par_preserves
#print axioms RawStep.par.universeCode_inv
#print axioms RawTerm.universeCode_isStronglyNormalizing
#print axioms Reducible.fundamental_universeCode
#print axioms Term.universeCode_isStronglyNormalizing
#print axioms RawTerm.arrowCode_isStronglyNormalizing
#print axioms Reducible.fundamental_arrowCode_of_payloads
#print axioms Term.arrowCode_isStronglyNormalizing
#print axioms RawTerm.piTyCode_isStronglyNormalizing
#print axioms Reducible.fundamental_piTyCode_of_payloads
#print axioms Term.piTyCode_isStronglyNormalizing
#print axioms RawTerm.sigmaTyCode_isStronglyNormalizing
#print axioms Reducible.fundamental_sigmaTyCode_of_payloads
#print axioms Term.sigmaTyCode_isStronglyNormalizing
#print axioms RawTerm.productCode_isStronglyNormalizing
#print axioms Reducible.fundamental_productCode_of_payloads
#print axioms Term.productCode_isStronglyNormalizing
#print axioms RawTerm.sumCode_isStronglyNormalizing
#print axioms Reducible.fundamental_sumCode_of_payloads
#print axioms Term.sumCode_isStronglyNormalizing
#print axioms RawTerm.eitherCode_isStronglyNormalizing
#print axioms Reducible.fundamental_eitherCode_of_payloads
#print axioms Term.eitherCode_isStronglyNormalizing
#print axioms RawTerm.equivCode_isStronglyNormalizing
#print axioms Reducible.fundamental_equivCode_of_payloads
#print axioms Term.equivCode_isStronglyNormalizing
#print axioms RawTerm.listCode_isStronglyNormalizing
#print axioms Reducible.fundamental_listCode_of_payload
#print axioms Term.listCode_isStronglyNormalizing
#print axioms RawTerm.optionCode_isStronglyNormalizing
#print axioms Reducible.fundamental_optionCode_of_payload
#print axioms Term.optionCode_isStronglyNormalizing
#print axioms RawTerm.idCode_isStronglyNormalizing
#print axioms Reducible.fundamental_idCode_of_payloads
#print axioms Term.idCode_isStronglyNormalizing
#print axioms RawTerm.IsStronglyNormalizingTypeCode
#print axioms RawTerm.isStronglyNormalizing_of_typeCode
#print axioms RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
#print axioms Term.HasStronglyNormalizingRawPayloads
#print axioms Reducible.fundamental_identity_arrowCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_piTyCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_sigmaTyCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_productCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_sumCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_eitherCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_equivCode_of_typeCode_payloads
#print axioms Reducible.fundamental_identity_listCode_of_typeCode_payload
#print axioms Reducible.fundamental_identity_optionCode_of_typeCode_payload
#print axioms Reducible.fundamental_identity_idCode_of_typeCode_payloads
#print axioms Term.identity_universeCode_isStronglyNormalizing
#print axioms Term.identity_arrowCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_piTyCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_sigmaTyCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_productCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_sumCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_eitherCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_equivCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_listCode_isStronglyNormalizing_of_typeCode_payload
#print axioms Term.identity_optionCode_isStronglyNormalizing_of_typeCode_payload
#print axioms Term.identity_idCode_isStronglyNormalizing_of_typeCode_payloads
#print axioms Term.identity_refl_isStronglyNormalizing_of_endpoint
#print axioms Term.identity_oeqRefl_isStronglyNormalizing_of_endpoint
#print axioms Term.identity_idStrictRefl_isStronglyNormalizing_of_endpoint
#print axioms Term.refl_isStronglyNormalizing
#print axioms Term.oeqRefl_isStronglyNormalizing
#print axioms Term.idStrictRefl_isStronglyNormalizing
#print axioms Term.identity_refl_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_oeqRefl_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_idStrictRefl_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_arrowCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_piTyCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_sigmaTyCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_productCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_sumCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_eitherCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_equivCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_listCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_optionCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.identity_idCode_isStronglyNormalizing_of_rawPayloads
#print axioms Term.funextRefl_isStronglyNormalizing_of_apply

end LeanFX2.Smoke

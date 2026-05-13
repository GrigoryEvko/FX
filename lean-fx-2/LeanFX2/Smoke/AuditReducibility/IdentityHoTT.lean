import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.IdentityHoTT

Tait reducibility — HoTT identity, observational identity,
strict identity, equivalence, and cubical path/glue/codata
fundamental cases.  Covers `refl`/`oeqRefl`/`idStrictRefl`
endpoints, funext refls + introHet, equivApp/equivApply/
equivIntroHet, oeqFunext, pathApp, glueElim/glueIntro, all
their `_identity_*_sn` companions, plus the natElim/natRec
introducer SN helpers and the natSucc cascade.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms Reducible.fundamental_glueElim_at_glue
#print axioms Reducible.fundamental_glueIntro_at_glue
#print axioms Reducible.fundamental_recordIntro_at_record
#print axioms Reducible.fundamental_refineIntro_at_refine
#print axioms Reducible.fundamental_codataUnfold_at_codata
#print axioms Reducible.fundamental_codataDest_at_codata
#print axioms Reducible.fundamental_identity_equivApp_at_equiv_sn
#print axioms Reducible.fundamental_identity_pathApp_at_path_sn
#print axioms Reducible.fundamental_identity_codataDest_at_codata_sn
#print axioms Reducible.fundamental_identity_equivApply_at_equiv_sn
#print axioms Reducible.fundamental_identity_equivIntroHet_at_equiv_sn
#print axioms Reducible.fundamental_identity_codataUnfold_at_codata_sn
#print axioms Reducible.fundamental_identity_glueIntro_at_glue_sn
#print axioms Reducible.fundamental_identity_recordIntro_at_record_sn
#print axioms Reducible.fundamental_identity_refineIntro_at_refine_sn
#print axioms Reducible.fundamental_identity_boolElim_at_bool_sn
#print axioms Reducible.fundamental_identity_natElim_at_nat_sn
#print axioms Reducible.fundamental_identity_natRec_at_nat_sn
#print axioms Reducible.fundamental_identity_listElim_at_listType_sn
#print axioms Reducible.fundamental_identity_optionMatch_at_optionType_sn
#print axioms Reducible.fundamental_identity_eitherMatch_at_eitherType_sn
#print axioms Reducible.fundamental_identity_modIntro_sn
#print axioms Reducible.fundamental_identity_modElim_sn
#print axioms Reducible.fundamental_identity_subsume_sn
#print axioms Reducible.fundamental_identity_idJ_at_id_sn
#print axioms Reducible.fundamental_identity_oeqJ_at_oeq_sn
#print axioms Reducible.fundamental_identity_idStrictRec_at_idStrict_sn
#print axioms Term.codataDest_isStronglyNormalizing
#print axioms RawTerm.natSucc_isStronglyNormalizing
#print axioms RawTerm.optionSome_isStronglyNormalizing
#print axioms RawTerm.optionMatch_optionSome_isStronglyNormalizing
#print axioms Term.optionMatch_optionSome_isStronglyNormalizing
#print axioms RawTerm.eitherInl_isStronglyNormalizing
#print axioms RawTerm.eitherMatch_eitherInl_isStronglyNormalizing
#print axioms Term.eitherMatch_eitherInl_isStronglyNormalizing
#print axioms RawTerm.eitherInr_isStronglyNormalizing
#print axioms RawTerm.eitherMatch_eitherInr_isStronglyNormalizing
#print axioms Term.eitherMatch_eitherInr_isStronglyNormalizing
#print axioms RawTerm.modIntro_isStronglyNormalizing
#print axioms RawTerm.modElim_isStronglyNormalizing
#print axioms Term.modElim_isStronglyNormalizing
#print axioms RawTerm.pair_isStronglyNormalizing
#print axioms RawTerm.fst_pair_isStronglyNormalizing
#print axioms RawTerm.snd_pair_isStronglyNormalizing
#print axioms Term.pair_isStronglyNormalizing
#print axioms Term.fst_pair_isStronglyNormalizing
#print axioms Term.snd_pair_isStronglyNormalizing

end LeanFX2.Smoke

import LeanFX2.Foundation.RawPartialRename.IsSomeInversion

/-! # Smoke/AuditRawIsSomeInversion

Reviewer-facing `#print axioms` gate for the zero-axiom
`RawTerm.partialRename?_<ctor>_isSome` inversion lemmas in
`Foundation/RawPartialRename/IsSomeInversion.lean`.

Raw-side siblings of the Ty inversion lemmas; current coverage
spans binder (lam), Option.mapTwo binary (app, pair, listCons),
direct-match single-child (fst, snd), and 10 additional
single-child non-binder ctors (natSucc, optionSome, eitherInl,
eitherInr, refl, modIntro, modElim, subsume, intervalOpp,
glueElim).

Each `#print axioms` line below must report
"does not depend on any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditRawIsSomeInversion

#print axioms LeanFX2.RawTerm.partialRename?_lam_isSome
#print axioms LeanFX2.RawTerm.partialRename?_app_isSome
#print axioms LeanFX2.RawTerm.partialRename?_pair_isSome
#print axioms LeanFX2.RawTerm.partialRename?_fst_isSome
#print axioms LeanFX2.RawTerm.partialRename?_snd_isSome
#print axioms LeanFX2.RawTerm.partialRename?_listCons_isSome
#print axioms LeanFX2.RawTerm.partialRename?_natSucc_isSome
#print axioms LeanFX2.RawTerm.partialRename?_optionSome_isSome
#print axioms LeanFX2.RawTerm.partialRename?_eitherInl_isSome
#print axioms LeanFX2.RawTerm.partialRename?_eitherInr_isSome
#print axioms LeanFX2.RawTerm.partialRename?_refl_isSome
#print axioms LeanFX2.RawTerm.partialRename?_modIntro_isSome
#print axioms LeanFX2.RawTerm.partialRename?_modElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_subsume_isSome
#print axioms LeanFX2.RawTerm.partialRename?_intervalOpp_isSome
#print axioms LeanFX2.RawTerm.partialRename?_glueElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_idJ_isSome
#print axioms LeanFX2.RawTerm.partialRename?_intervalMeet_isSome
#print axioms LeanFX2.RawTerm.partialRename?_intervalJoin_isSome
#print axioms LeanFX2.RawTerm.partialRename?_pathApp_isSome
#print axioms LeanFX2.RawTerm.partialRename?_glueIntro_isSome
#print axioms LeanFX2.RawTerm.partialRename?_transp_isSome
#print axioms LeanFX2.RawTerm.partialRename?_boolElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_natElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_natRec_isSome
#print axioms LeanFX2.RawTerm.partialRename?_listElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_optionMatch_isSome
#print axioms LeanFX2.RawTerm.partialRename?_eitherMatch_isSome
#print axioms LeanFX2.RawTerm.partialRename?_oeqRefl_isSome
#print axioms LeanFX2.RawTerm.partialRename?_oeqFunext_isSome
#print axioms LeanFX2.RawTerm.partialRename?_idStrictRefl_isSome
#print axioms LeanFX2.RawTerm.partialRename?_refineElim_isSome
#print axioms LeanFX2.RawTerm.partialRename?_recordIntro_isSome
#print axioms LeanFX2.RawTerm.partialRename?_recordProj_isSome
#print axioms LeanFX2.RawTerm.partialRename?_codataDest_isSome
#print axioms LeanFX2.RawTerm.partialRename?_sessionRecv_isSome
#print axioms LeanFX2.RawTerm.partialRename?_listCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_optionCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_cumulUpMarker_isSome
#print axioms LeanFX2.RawTerm.partialRename?_uaToEquiv_isSome
#print axioms LeanFX2.RawTerm.partialRename?_idToEquiv_isSome
#print axioms LeanFX2.RawTerm.partialRename?_hcomp_isSome
#print axioms LeanFX2.RawTerm.partialRename?_oeqJ_isSome
#print axioms LeanFX2.RawTerm.partialRename?_idStrictRec_isSome
#print axioms LeanFX2.RawTerm.partialRename?_equivIntro_isSome
#print axioms LeanFX2.RawTerm.partialRename?_equivApp_isSome
#print axioms LeanFX2.RawTerm.partialRename?_refineIntro_isSome
#print axioms LeanFX2.RawTerm.partialRename?_codataUnfold_isSome
#print axioms LeanFX2.RawTerm.partialRename?_sessionSend_isSome
#print axioms LeanFX2.RawTerm.partialRename?_effectPerform_isSome
#print axioms LeanFX2.RawTerm.partialRename?_arrowCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_productCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_sumCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_eitherCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_equivCode_isSome
#print axioms LeanFX2.RawTerm.partialRename?_equivApply_isSome
#print axioms LeanFX2.RawTerm.partialRename?_pathCompose_isSome
#print axioms LeanFX2.RawTerm.partialRename?_oeqTrans_isSome
#print axioms LeanFX2.RawTerm.partialRename?_equivCompose_isSome

end LeanFX2.Smoke.AuditRawIsSomeInversion

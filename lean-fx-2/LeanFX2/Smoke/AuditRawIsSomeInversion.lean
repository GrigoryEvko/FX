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

end LeanFX2.Smoke.AuditRawIsSomeInversion

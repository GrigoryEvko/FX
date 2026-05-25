import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2.Reducibility

namespace LeanFX2.Tools

/-! ## AuditReducibility — curated kernel gate for the Kripke
step-indexed strong-normalization cascade.

The Kripke Tait reducibility predicate (`ReducibleK`) plus its
fundamental theorem closures + per-Ty SN extractors + headline
SN-via-Kripke wrappers form the bypass-free Layer-3 metatheory
that replaced the legacy `Reducible` cascade in K12.20.  The
broad `#audit_namespace LeanFX2` sweep covers these declarations
automatically, but per CLAUDE.md the load-bearing kernel
declarations warrant explicit `#assert_no_axioms` gates so a
silent breakage in one of them surfaces at the per-decl level
rather than as a generic namespace failure. -/

/-! ### Strong-normalization foundation -/

#assert_no_axioms LeanFX2.RawStep.parProgress
#assert_no_axioms LeanFX2.RawTerm.isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.isStronglyNormalizing

/-! ### Raw SN preservation atoms (NeutralSNFoundation) -/

#assert_no_axioms LeanFX2.RawTerm.var_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.boolElim_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.equivApp_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.equivApply_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.optionSome_isStronglyNormalizing

/-! ### SN preservation helpers + CR2 forward closure

TODO POLYCELL: the backward-direction weaken/image helpers were
preserved only inside a disabled block in `Reducibility/SN/Helpers.lean`
after the cascade bulldoze.  They are listed below as stale missing
targets until the PolyCell view replaces the old raw-image route. -/

#assert_no_axioms LeanFX2.RawTerm.unit_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.boolTrue_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.boolFalse_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.natZero_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.lam_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.isStronglyNormalizing.step_preserves
-- TODO POLYCELL stale missing:
-- #assert_no_axioms LeanFX2.RawTerm.isStronglyNormalizing_weaken
#assert_no_axioms LeanFX2.RawStep.parProgress.rename_compatible
#assert_no_axioms LeanFX2.RawStep.parProgress.weaken_compatible
-- TODO POLYCELL stale missing:
-- #assert_no_axioms LeanFX2.RawStep.parProgress.target_in_rename_image
-- #assert_no_axioms LeanFX2.RawStep.parProgress.target_in_rename_image_of_source_eq
-- #assert_no_axioms LeanFX2.RawStep.parProgress.target_in_weaken_image
-- #assert_no_axioms LeanFX2.RawStep.parProgress.target_in_weaken_image_of_source_eq
#assert_no_axioms LeanFX2.RawTerm.cumulUpMarker_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.natSucc_predecessor_isStronglyNormalizing

/-! ### Typed SN endpoints (Term.SN.DirectCases) -/

#assert_no_axioms LeanFX2.Term.var_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.unit_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.boolTrue_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.boolFalse_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.natZero_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.listNil_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.optionNone_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.interval0_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.interval1_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.modIntro_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.subsume_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.sessionRecv_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.sessionSend_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.lam_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.lamPi_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.refl_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.oeqRefl_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.idStrictRefl_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.boolElim_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.idJ_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.oeqJ_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.idStrictRec_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.equivReflId_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.equivReflIdAtId_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.uaIntroHet_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.uaToEquiv_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.funextRefl_isStronglyNormalizing_of_apply
#assert_no_axioms LeanFX2.Term.funextReflAtId_isStronglyNormalizing_of_apply
#assert_no_axioms LeanFX2.Term.funextIntroHet_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.oeqFunext_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.effectPerform_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.cumulUp_isStronglyNormalizing
#assert_no_axioms LeanFX2.Term.hcompPath_isStronglyNormalizing

/-! ### Kripke step-indexed reducibility predicate -/

#assert_no_axioms LeanFX2.ReducibleKBody
#assert_no_axioms LeanFX2.ReducibleK

/-! ### Kripke fundamental theorem cases (Predicate.lean closures
applied at identity renaming + SN extraction) -/

#assert_no_axioms LeanFX2.ReducibleK.fundamental_unit
#assert_no_axioms LeanFX2.ReducibleK.fundamental_boolTrue
#assert_no_axioms LeanFX2.ReducibleK.fundamental_boolFalse
#assert_no_axioms LeanFX2.ReducibleK.fundamental_natZero
#assert_no_axioms LeanFX2.ReducibleK.fundamental_natSucc
#assert_no_axioms LeanFX2.ReducibleK.fundamental_var_unit
#assert_no_axioms LeanFX2.ReducibleK.fundamental_var_bool
#assert_no_axioms LeanFX2.ReducibleK.fundamental_var_nat
#assert_no_axioms LeanFX2.ReducibleK.fundamental_var_empty
#assert_no_axioms LeanFX2.ReducibleK.fundamental_var_interval
#assert_no_axioms LeanFX2.ReducibleK.fundamental_interval0
#assert_no_axioms LeanFX2.ReducibleK.fundamental_interval1
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalOpp
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalMeet
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalJoin
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idJ
#assert_no_axioms LeanFX2.ReducibleK.fundamental_oeqJ
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idStrictRec
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivApply
#assert_no_axioms LeanFX2.ReducibleK.fundamental_pathApp
#assert_no_axioms LeanFX2.ReducibleK.fundamental_glueElim

/-! ### Kripke fundamental-theorem SN-extraction cases (the `_sn`
family in `Fundamental/StructuralSN.lean`, `Fundamental/SNEliminators.lean`,
and `Fundamental/HoTTCodesAndEffects.lean`).  Each `fundamental_X_sn`
discharges the Kripke reducibility predicate at the identity renaming
for constructor `X` and extracts strong normalization from it; together
they are the per-constructor body of the fundamental theorem and feed
the SN-via-Kripke headlines below.  The broad `#audit_namespace LeanFX2`
sweep already covers them; promoted to explicit per-decl gates here so a
future axiom regression in any single case fails `lake build LeanFX2Audit`
at the decl level.  Added 2026-05-23 to close the 51-case delta between
the curated gate and the current fundamental-theorem surface. -/

#assert_no_axioms LeanFX2.ReducibleK.fundamental_refl_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_oeqRefl_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idStrictRefl_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_pair_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_fst_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_snd_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_lam_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_lamPi_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_recordIntro_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_recordProj_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_refineIntro_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_refineElim_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_modIntro_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_modElim_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_subsume_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_cumulUp_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_codataUnfold_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_sessionRecv_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_sessionSend_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_effectPerform_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_boolElim_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idJ_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_oeqJ_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idStrictRec_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_pathLam_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_glueIntro_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_glueElim_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivApp_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivApply_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivReflId_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivReflIdAtId_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivIntroHet_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_uaToEquiv_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_uaIntroHet_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_funextRefl_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_funextReflAtId_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_funextIntroHet_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_oeqFunext_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_universeCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_arrowCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_piTyCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_sigmaTyCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_productCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_sumCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_listCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_optionCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_eitherCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idCode_sn
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivCode_sn

/-! ### Kripke SN-via-Kripke headlines (Headline.lean) -/

#assert_no_axioms LeanFX2.Term.unit_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.boolTrue_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.boolFalse_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.natZero_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.natSucc_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.var_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.pair_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.fst_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.snd_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.lam_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.lamPi_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.codataDest_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.listElim_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.optionMatch_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.eitherMatch_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.app_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.appPi_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.pathApp_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.interval0_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.interval1_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.universeCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.piTyCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.sigmaTyCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.productCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.sumCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.funextIntroHet_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.glueIntro_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.glueElim_strong_normalization_via_kripke

/-! ### Kripke SN-via-Kripke headlines — closed-leaf intros, parametric
intros, and HoTT/cubical/modal eliminators.  These ship in
`Headline.lean` and the per-Ty closure files; smoke entries in
`AuditKripke.lean` already cover them via `#print axioms`.  Strict-gate
coverage promoted here so `lake build LeanFX2Audit` fails on any
future axiom regression.  Added 2026-05-15 to close the 47-headline
delta between the smoke log and the machine-enforced gate. -/

#assert_no_axioms LeanFX2.Term.intervalOpp_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.intervalMeet_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.intervalJoin_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.listNil_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.optionNone_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.listCons_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.optionSome_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.eitherInl_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.eitherInr_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.recordIntro_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.recordProj_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.refineIntro_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.refineElim_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.codataUnfold_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.sessionRecv_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.sessionSend_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.effectPerform_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.modIntro_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.subsume_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.modElim_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.cumulUp_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.refl_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.oeqRefl_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.idStrictRefl_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivReflId_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivReflIdAtId_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivIntroHet_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.uaToEquiv_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.uaIntroHet_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.funextRefl_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.funextReflAtId_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.oeqFunext_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.pathLam_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.arrowCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.eitherCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.idCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.listCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.optionCode_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.boolElim_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.idJ_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.oeqJ_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.idStrictRec_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivApp_strong_normalization_via_kripke
#assert_no_axioms LeanFX2.Term.equivApply_strong_normalization_via_kripke

end LeanFX2.Tools

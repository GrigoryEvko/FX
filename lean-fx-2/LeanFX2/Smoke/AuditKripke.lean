import LeanFX2.Reducibility.Kripke.Predicate
import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.Kripke.Weaken
import LeanFX2.Reducibility.Kripke.Monotone
import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.SNClosure
import LeanFX2.Reducibility.Kripke.Fundamental
import LeanFX2.Reducibility.Kripke.Headline
import LeanFX2.Reducibility.Kripke.Arrow
import LeanFX2.Reducibility.Kripke.SNExtraction

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
-- introducer-direction fundamental_{listNil,optionNone,listCons,optionSome,
-- eitherInl,eitherInr}_sn DELETED — they shipped over banned
-- contractum/closure postulates symmetric to the eliminator-side family.
-- Restored once the M04 fundamental theorem lands.
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
-- Eliminator SN-extraction cases (boolElim / idJ / oeqJ / idStrictRec /
-- modElim / equivApp / equivApply).  Added 2026-05-23 to align the smoke
-- log with the full fundamental-theorem `_sn` surface.
#print axioms LeanFX2.ReducibleK.fundamental_boolElim_sn
#print axioms LeanFX2.ReducibleK.fundamental_idJ_sn
#print axioms LeanFX2.ReducibleK.fundamental_oeqJ_sn
#print axioms LeanFX2.ReducibleK.fundamental_idStrictRec_sn
#print axioms LeanFX2.ReducibleK.fundamental_modElim_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivApp_sn
#print axioms LeanFX2.ReducibleK.fundamental_equivApply_sn
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
-- natElim_strong_normalization_via_kripke / natRec_strong_normalization_via_kripke
-- DELETED — they shipped over a banned `succAppIsSN` / `contractumIsSN`
-- universally-quantified raw-SN postulate.  Restored by the M04
-- fundamental theorem once it lands.

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

-- K12.25 codataDest (codata destructor; live Kripke headline only)
#print axioms LeanFX2.RawTerm.codataUnfold_state_isStronglyNormalizing
#print axioms LeanFX2.RawTerm.codataUnfold_transition_isStronglyNormalizing
#print axioms LeanFX2.Term.codataDest_strong_normalization_via_kripke
-- DELETED — RawTerm.codataDest_isStronglyNormalizing +
-- Term.codataDest_isStronglyNormalizing carried a banned
-- `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.22 listElim (generic ι recursor; live Kripke headline only)
#print axioms LeanFX2.Term.listElim_strong_normalization_via_kripke
-- DELETED — RawTerm/Term.listElim_isStronglyNormalizing carried
-- a banned `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.22 optionMatch (generic ι recursor; live Kripke headline only)
#print axioms LeanFX2.Term.optionMatch_strong_normalization_via_kripke
-- DELETED — RawTerm/Term.optionMatch_isStronglyNormalizing carried
-- a banned `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.22 eitherMatch (generic ι recursor; live Kripke headline only)
#print axioms LeanFX2.Term.eitherMatch_strong_normalization_via_kripke
-- DELETED — RawTerm/Term.eitherMatch_isStronglyNormalizing carried
-- two banned `inlContractumIsSN`/`inrContractumIsSN` postulates.

-- K12.21 app (β-redex; live Kripke headline only)
#print axioms LeanFX2.RawTerm.lam_body_isStronglyNormalizing
#print axioms LeanFX2.Term.app_strong_normalization_via_kripke
-- DELETED — RawTerm/Term.app_isStronglyNormalizing carried a
-- banned `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.21 appPi (dependent-Π β-redex; live Kripke headline only)
#print axioms LeanFX2.Term.appPi_strong_normalization_via_kripke
-- DELETED — Term.appPi_isStronglyNormalizing carried a banned
-- `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.24 pathApp (cubical-mode path application β-redex)
#print axioms LeanFX2.RawTerm.pathLam_body_isStronglyNormalizing
#print axioms LeanFX2.Term.pathApp_strong_normalization_via_kripke
-- DELETED — RawTerm/Term.pathApp_isStronglyNormalizing carried a
-- banned `contractumIsSN` Pi-type postulate over raw scopes.

-- K12.24 transp DELETED — RawTerm/Term.transp_isStronglyNormalizing
-- carried banned `uaContractumIsSN` / `composeContractumIsSN`
-- postulates over arbitrary raw scopes.  The proper Kripke transp
-- headline lands when `Ty.path` closure is extended (pending M04
-- fundamental theorem cascade, see
-- feedback_kripke_predicate_partial_closure.md).

-- K12.24 hcomp (raw / Term SN helpers; the Term-level
-- _strong_normalization_via_kripke headline was deleted with the
-- ReducibleK.fundamental_hcomp_sn wrapper — congruence-only headline
-- added no information beyond the underlying SN helper)
#print axioms LeanFX2.RawTerm.hcomp_isStronglyNormalizing
#print axioms LeanFX2.Term.hcomp_isStronglyNormalizing

-- ReducibleK.fundamental_{codataDest,listElim,optionMatch,eitherMatch,
-- app,appPi,pathApp,transp,hcomp}_sn DELETED — each shipped over a
-- banned `contractumIsSN` / `inlContractumIsSN` / `inrContractumIsSN` /
-- `uaContractumIsSN` / `composeContractumIsSN` Pi-type postulate over
-- arbitrary raw scopes (structurally false in general).  Restored by
-- the M04 fundamental theorem once it lands.

-- K12.27 Kripke real Tait closures for piTy / sigmaTy / listType /
-- optionType / eitherType.  Each closure is SN of the term plus a
-- Kripke clause exposing the eliminator's reducible-output structure
-- under any future-world renaming.
#print axioms LeanFX2.ReducibleK.sn_of_piTy
#print axioms LeanFX2.ReducibleK.piTy_apply
#print axioms LeanFX2.ReducibleK.sn_of_sigmaTy
#print axioms LeanFX2.ReducibleK.sigmaTy_fst
#print axioms LeanFX2.ReducibleK.sigmaTy_snd
#print axioms LeanFX2.ReducibleK.sn_of_listType
#print axioms LeanFX2.ReducibleK.listType_elim
#print axioms LeanFX2.ReducibleK.sn_of_optionType
#print axioms LeanFX2.ReducibleK.optionType_match
#print axioms LeanFX2.ReducibleK.sn_of_eitherType
#print axioms LeanFX2.ReducibleK.eitherType_match

-- Kripke real Tait closure for effect arm: SN of the effect value
-- plus uniform renaming-stability (no typed eliminator exists for
-- Ty.effect, so the closure is renaming-stability at the same head).
#print axioms LeanFX2.ReducibleK.sn_of_effect
#print axioms LeanFX2.ReducibleK.effect_rename

-- 9 SN-extractor wrappers added 2026-05-15 to complete the per-Ty
-- SN projection family: 7 closed-leaf (unit/bool/nat/empty/interval
-- already shipped; universe/tyVar added) + 7 conjunction-closure
-- (arrow/id/oeq/idStrict/equiv/path/glue).  Together with the
-- existing 7 conjunction-closure projections (refine/record/codata/
-- session/modal/piTy/sigmaTy/listType/optionType/eitherType/effect)
-- the project covers every Ty arm.
#print axioms LeanFX2.ReducibleK.sn_of_universe
#print axioms LeanFX2.ReducibleK.sn_of_tyVar
#print axioms LeanFX2.ReducibleK.sn_of_arrow
#print axioms LeanFX2.ReducibleK.sn_of_id
#print axioms LeanFX2.ReducibleK.sn_of_oeq
#print axioms LeanFX2.ReducibleK.sn_of_idStrict
#print axioms LeanFX2.ReducibleK.sn_of_equiv
#print axioms LeanFX2.ReducibleK.sn_of_path
#print axioms LeanFX2.ReducibleK.sn_of_glue

-- Universal SN dispatcher + partial M04 headline (added 2026-05-15).
-- `sn_of_any` dispatches case-by-case on Ty via the per-Ty `sn_of_X`
-- family; `strong_normalization_from_reducibility` is the M04 partial
-- corollary closing the SN-extraction half of the Tait pattern.
#print axioms LeanFX2.ReducibleK.sn_of_any
#print axioms LeanFX2.Term.strong_normalization_from_reducibility

-- Priority-1 Kripke closure-application fundamentals (added
-- 2026-05-15).  Eliminator-direction fundamentals for the remaining
-- Ty arms not already covered by `arrow_apply`/`piTy_apply`/
-- `sigmaTy_fst`/`sigmaTy_snd`/`listType_elim`/`optionType_match`/
-- `eitherType_match`/`refine_elim`/`record_proj`/`codata_dest`/
-- `session_recv`/`mod_elim`/`effect_rename`.  Direct projections from
-- the `ReducibleK` predicate closures defined in `Predicate.lean`.
#print axioms LeanFX2.ReducibleK.fundamental_idJ
#print axioms LeanFX2.ReducibleK.fundamental_oeqJ
#print axioms LeanFX2.ReducibleK.fundamental_idStrictRec
#print axioms LeanFX2.ReducibleK.fundamental_equivApply
#print axioms LeanFX2.ReducibleK.fundamental_pathApp
#print axioms LeanFX2.ReducibleK.fundamental_glueElim

-- AGENT STRIP HELPERS (2026-05-15): identity-renaming TermRenaming
-- + Ty-eq transport used to discharge Kripke closure clauses at the
-- source context for stripping `contractumIsSN` hypotheses in
-- `Headline.lean`.
#print axioms LeanFX2.TermRenaming.identity
#print axioms LeanFX2.ReducibleK.transport

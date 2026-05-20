import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.Subst
import LeanFX2.Term.RenameInjective
import LeanFX2.Term.Inversion
import LeanFX2.Term.Bridge
import LeanFX2.Algo.Progress
import LeanFX2.Term.PolyToTerm
import LeanFX2.Term.ToPoly
import LeanFX2.Term.PolyRename
import LeanFX2.Term.PolySubst
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermRename
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermSubst

/-! # AuditTerm.BaseAndPoly — core Term, progress, and polygraph bridge gates. -/

namespace LeanFX2.Tools

#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
#assert_no_axioms LeanFX2.Term.rename_injective_atVar
#assert_no_axioms LeanFX2.Term.rename_injective_lam_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_app_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_lamPi_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_appPi_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_effectPerform_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_effectPerform_ctor_proofIrrel
#assert_no_axioms LeanFX2.Term.rename_injective_universeCode_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_equivReflId_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_funextRefl_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_equivReflIdAtId_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_funextReflAtId_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_funextIntroHet_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_equivIntroHet_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_uaIntroHet_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_pathLam_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_atPathLam_of_inner
#assert_no_axioms LeanFX2.Term.lam_raw_inv
#assert_no_axioms LeanFX2.Term.lam_arrow_inv
#assert_no_axioms LeanFX2.Term.lam_pi_inv
#assert_no_axioms LeanFX2.Term.lam_arrow_id_inv
#assert_no_axioms LeanFX2.Term.rename_injective_atLamArrow_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atLamPi_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atLamArrowId
#assert_no_axioms LeanFX2.Term.rename_injective_atUnit
#assert_no_axioms LeanFX2.Term.rename_injective_atBoolTrue
#assert_no_axioms LeanFX2.Term.rename_injective_atBoolFalse
#assert_no_axioms LeanFX2.Term.rename_injective_atNatZero
#assert_no_axioms LeanFX2.Term.rename_injective_atNatSucc_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atNatElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atNatRec_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atListNil
#assert_no_axioms LeanFX2.Term.rename_injective_atListCons_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atPair_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atFst_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_snd_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_atGlueIntro_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atGlueElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atTransp_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atHcompFamily_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atListElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionNone
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionSome_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionMatch_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherInl_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherInr_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherMatch_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_boolElim_ctor
#assert_no_axioms LeanFX2.Term.rename_injective_atIdJ_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOEqJ_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOEqFunext_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIdStrictRec_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atOEqRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atIdStrictRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atInterval0
#assert_no_axioms LeanFX2.Term.rename_injective_atInterval1
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalOpp_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalMeet_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalJoin_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atPathApp_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atModIntro_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atModElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atSubsume_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRecordIntro_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRecordProj_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRefineIntro_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRefineElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atCodataUnfold_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atCodataDest_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atSessionSend_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atSessionRecv_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atArrowCode
#assert_no_axioms LeanFX2.Term.rename_injective_atPiTyCode
#assert_no_axioms LeanFX2.Term.rename_injective_atSigmaTyCode
#assert_no_axioms LeanFX2.Term.rename_injective_atProductCode
#assert_no_axioms LeanFX2.Term.rename_injective_atSumCode
#assert_no_axioms LeanFX2.Term.rename_injective_atListCode
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionCode
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherCode
#assert_no_axioms LeanFX2.Term.rename_injective_atIdCode
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivCode
#assert_no_axioms LeanFX2.Term.rename_injective_atCumulUp_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atUaToEquiv_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivApply_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivApp_of_inner
#assert_no_axioms LeanFX2.Term.equivIntro_inv
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivIntroEquiv_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivIntroUniverseId_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEquivIntro_of_inner
#assert_no_axioms LeanFX2.Term.toRaw_rename
#assert_no_axioms LeanFX2.Term.toRaw_subst
#assert_no_axioms LeanFX2.Term.toRaw_weaken
#assert_no_axioms LeanFX2.Term.toRaw_subst0
#assert_no_axioms LeanFX2.Term.toRaw_universeCode
#assert_no_axioms LeanFX2.Term.toRaw_cumulUp
#assert_no_axioms LeanFX2.Term.toRaw_equivReflId
#assert_no_axioms LeanFX2.Term.toRaw_funextRefl
#assert_no_axioms LeanFX2.Term.toRaw_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.toRaw_funextReflAtId
#assert_no_axioms LeanFX2.Term.toRaw_equivIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_uaIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_funextIntroHet
-- D3.6-P3: typed univalence-β extractor (Term.uaToEquiv).
#assert_no_axioms LeanFX2.Term.toRaw_uaToEquiv
-- D3.6-P4: typed univalence-β application (Term.equivApply).
#assert_no_axioms LeanFX2.Term.toRaw_equivApply
#assert_no_axioms LeanFX2.Term.toRaw_arrowCode
#assert_no_axioms LeanFX2.Term.toRaw_piTyCode
#assert_no_axioms LeanFX2.Term.toRaw_sigmaTyCode
#assert_no_axioms LeanFX2.Term.toRaw_productCode
#assert_no_axioms LeanFX2.Term.toRaw_sumCode
#assert_no_axioms LeanFX2.Term.toRaw_listCode
#assert_no_axioms LeanFX2.Term.toRaw_optionCode
#assert_no_axioms LeanFX2.Term.toRaw_eitherCode
#assert_no_axioms LeanFX2.Term.toRaw_idCode
#assert_no_axioms LeanFX2.Term.toRaw_equivCode
#assert_no_axioms LeanFX2.Term.toRaw_interval0
#assert_no_axioms LeanFX2.Term.toRaw_interval1
#assert_no_axioms LeanFX2.Term.toRaw_intervalOpp
#assert_no_axioms LeanFX2.Term.toRaw_intervalMeet
#assert_no_axioms LeanFX2.Term.toRaw_intervalJoin
#assert_no_axioms LeanFX2.Term.toRaw_pathLam
#assert_no_axioms LeanFX2.Term.toRaw_pathApp
#assert_no_axioms LeanFX2.Term.toRaw_glueIntro
#assert_no_axioms LeanFX2.Term.toRaw_glueElim
#assert_no_axioms LeanFX2.Term.headCtor
#assert_no_axioms LeanFX2.Term.isWHNF
#assert_no_axioms LeanFX2.Term.toRaw_transp
#assert_no_axioms LeanFX2.Term.toRaw_hcomp
#assert_no_axioms LeanFX2.Term.toRaw_oeqRefl
#assert_no_axioms LeanFX2.Term.toRaw_oeqJ
#assert_no_axioms LeanFX2.Term.toRaw_oeqFunext
#assert_no_axioms LeanFX2.Term.toRaw_recordIntro
#assert_no_axioms LeanFX2.Term.toRaw_recordProj
#assert_no_axioms LeanFX2.Term.toRaw_idStrictRefl
#assert_no_axioms LeanFX2.Term.toRaw_idStrictRec
#assert_no_axioms LeanFX2.Term.toRaw_equivApp
#assert_no_axioms LeanFX2.Term.toRaw_refineIntro
#assert_no_axioms LeanFX2.Term.toRaw_refineElim
#assert_no_axioms LeanFX2.Term.toRaw_codataUnfold
#assert_no_axioms LeanFX2.Term.toRaw_codataDest
#assert_no_axioms LeanFX2.Term.toRaw_sessionSend
#assert_no_axioms LeanFX2.Term.toRaw_sessionRecv
#assert_no_axioms LeanFX2.Term.toRaw_effectPerform
-- M05 Progress canonical-form raw inversions (Phase 7.D).
#assert_no_axioms LeanFX2.Term.headCtor_lam_raw
#assert_no_axioms LeanFX2.Term.headCtor_pair_raw
#assert_no_axioms LeanFX2.Term.headCtor_refl_raw
#assert_no_axioms LeanFX2.Term.headCtor_lamPi_raw
#assert_no_axioms LeanFX2.Term.headCtor_modIntro_raw
#assert_no_axioms LeanFX2.Term.headCtor_recordIntro_raw
#assert_no_axioms LeanFX2.Term.headCtor_pathLam_raw
#assert_no_axioms LeanFX2.Term.headCtor_glueIntro_raw
#assert_no_axioms LeanFX2.Term.headCtor_refineIntro_raw
#assert_no_axioms LeanFX2.Term.headCtor_codataUnfold_raw
#assert_no_axioms LeanFX2.Term.headCtor_universeCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_arrowCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_piTyCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_sigmaTyCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_productCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_sumCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_listCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_optionCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_eitherCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_idCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_equivCode_raw
#assert_no_axioms LeanFX2.Term.headCtor_interval0_raw
#assert_no_axioms LeanFX2.Term.headCtor_interval1_raw
#assert_no_axioms LeanFX2.Term.headCtor_intervalOpp_raw
#assert_no_axioms LeanFX2.Term.headCtor_intervalMeet_raw
#assert_no_axioms LeanFX2.Term.headCtor_intervalJoin_raw
#assert_no_axioms LeanFX2.Term.headCtor_equivReflId_raw
#assert_no_axioms LeanFX2.Term.headCtor_funextRefl_raw
#assert_no_axioms LeanFX2.Term.headCtor_equivReflIdAtId_raw
#assert_no_axioms LeanFX2.Term.headCtor_funextReflAtId_raw
#assert_no_axioms LeanFX2.Term.headCtor_equivIntroHet_raw
#assert_no_axioms LeanFX2.Term.headCtor_uaIntroHet_raw
#assert_no_axioms LeanFX2.Term.headCtor_funextIntroHet_raw
#assert_no_axioms LeanFX2.Term.headCtor_oeqRefl_raw
#assert_no_axioms LeanFX2.Term.headCtor_idStrictRefl_raw
#assert_no_axioms LeanFX2.Term.app_lam_steps
#assert_no_axioms LeanFX2.Term.appPi_lamPi_steps
#assert_no_axioms LeanFX2.Term.fst_pair_steps
#assert_no_axioms LeanFX2.Term.snd_pair_steps
#assert_no_axioms LeanFX2.Term.boolElim_boolTrue_steps
#assert_no_axioms LeanFX2.Term.boolElim_boolFalse_steps
#assert_no_axioms LeanFX2.Term.natElim_natZero_steps
#assert_no_axioms LeanFX2.Term.natElim_natSucc_steps
#assert_no_axioms LeanFX2.Term.natRec_natZero_steps
#assert_no_axioms LeanFX2.Term.natRec_natSucc_steps
#assert_no_axioms LeanFX2.Term.listElim_listNil_steps
#assert_no_axioms LeanFX2.Term.listElim_listCons_steps
#assert_no_axioms LeanFX2.Term.optionMatch_optionNone_steps
#assert_no_axioms LeanFX2.Term.optionMatch_optionSome_steps
#assert_no_axioms LeanFX2.Term.eitherMatch_eitherInl_steps
#assert_no_axioms LeanFX2.Term.eitherMatch_eitherInr_steps
#assert_no_axioms LeanFX2.Term.idJ_refl_steps
#assert_no_axioms LeanFX2.Term.idStrictRec_idStrictRefl_steps
#assert_no_axioms LeanFX2.Term.modElim_modIntro_steps
#assert_no_axioms LeanFX2.Term.pathApp_pathLam_steps
#assert_no_axioms LeanFX2.Term.glueElim_glueIntro_steps
#assert_no_axioms LeanFX2.Term.transp_pathRefl_steps
#assert_no_axioms LeanFX2.Term.recordProj_recordIntro_steps
#assert_no_axioms LeanFX2.Term.refineElim_refineIntro_steps
#assert_no_axioms LeanFX2.Term.codataDest_codataUnfold_steps
#assert_no_axioms LeanFX2.Term.cumulUp_inner_steps
-- M05.C cong-rule lifters (Phase 7.D, #1644).
#assert_no_axioms LeanFX2.Term.app_function_steps_lift
#assert_no_axioms LeanFX2.Term.appPi_function_steps_lift
#assert_no_axioms LeanFX2.Term.fst_pair_steps_lift
#assert_no_axioms LeanFX2.Term.snd_pair_steps_lift
#assert_no_axioms LeanFX2.Term.boolElim_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.natElim_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.natRec_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.listElim_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.optionMatch_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.eitherMatch_scrutinee_steps_lift
#assert_no_axioms LeanFX2.Term.idJ_witness_steps_lift
#assert_no_axioms LeanFX2.Term.modElim_inner_steps_lift
#assert_no_axioms LeanFX2.Term.pathApp_path_steps_lift
#assert_no_axioms LeanFX2.Term.glueElim_value_steps_lift
#assert_no_axioms LeanFX2.Term.recordProj_record_steps_lift
#assert_no_axioms LeanFX2.Term.refineElim_value_steps_lift
#assert_no_axioms LeanFX2.Term.codataDest_value_steps_lift
-- M05.D partial headline progress (Phase 7.D, #1645).
#assert_no_axioms LeanFX2.Term.value_or_cong_only_progress
#assert_no_axioms LeanFX2.Term.app_progress_or_step
-- M05.D.2 unified Wright-Felleisen progress headline (#1565, #1737).
#assert_no_axioms LeanFX2.Term.progress_or_step

-- K11.10-A (#1752): RawTerm.toRawPoly raw-level forward map.
#assert_no_axioms LeanFX2.RawTerm.toRawPoly

-- K11.11 (#1748): PolyTerm.toTerm typed backward bijection (77 ctors).
#assert_no_axioms LeanFX2.PolyTerm.toTerm

-- K11.10-B (#1752): Term.toPoly typed forward bijection (77 ctors,
-- 11 K11.12-driven `▸` casts on raw-in-Ty constructors).
#assert_no_axioms LeanFX2.Term.toPoly

-- K11.13 Phase A (#1745): raw-layer `RawPolyTerm.rename` + commute
-- with `RawTerm.toRawPoly`.
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.rename
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.weaken
#assert_no_axioms LeanFX2.RawTerm.rename_toRawPoly_commute
#assert_no_axioms LeanFX2.RawTerm.weaken_toRawPoly_commute

-- K11.13 Phase B (#1745): raw-layer `RawPolyTerm.subst` + commute
-- with `RawTerm.toRawPoly` along the pointwise-converted
-- substitution.
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.subst
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.subst0
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermSubst.lift_pointwise
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.subst_pointwise
#assert_no_axioms LeanFX2.RawTermSubst.toRawPolySubst
#assert_no_axioms LeanFX2.RawTermSubst.lift_toRawPolySubst_commute
#assert_no_axioms LeanFX2.RawTerm.subst_toRawPoly_commute
#assert_no_axioms LeanFX2.RawTerm.subst0_toRawPoly_commute

-- K11.13 Phase C-1 (#1745): reverse-direction rename commute —
-- `RawPolyTerm.toRawTerm` commutes with `RawPolyTerm.rename`.  Bridge
-- lemma for the typed `PolyTerm.rename` Phase C-2 follow-up, where 11
-- raw-in-Ty ctors embed `argumentPolyRaw.toRawTerm` inside their
-- kernel `Ty` index and need a single rewrite at the cast.
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.toRawTerm_rename_commute
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.weaken_toRawTerm_commute

-- K11.13 Phase C-2 (#1745): typed `PolyTerm.rename` via composition
-- through `Term.rename`.  Routes `polyTerm` → `toTerm` → `Term.rename`
-- → `.toPoly` and casts the raw-payload index from
-- `(rawPoly.toRawTerm.rename rho).toRawPoly` to `rawPoly.rename rho`
-- using Phase A's commute + K11.12's roundtrip.  `PolyTerm.weaken` is
-- the canonical single-binder corollary.
#assert_no_axioms LeanFX2.PolyTerm.rename
#assert_no_axioms LeanFX2.PolyTerm.weaken

-- K11.13 Phase D (#1745): typed `PolyTerm.subst` via composition
-- through `Term.subst`.  Mirrors Phase C-2's pattern: routes
-- `polyTerm` → `toTerm` → `Term.subst` → `.toPoly` and casts the
-- raw-payload index from `(rawPoly.toRawTerm.subst sigma.forRaw).toRawPoly`
-- to `rawPoly.subst sigma.forRaw.toRawPolySubst` using Phase B's
-- commute + K11.12's roundtrip.  `PolyTerm.subst0` is the canonical
-- β-reduction corollary.
#assert_no_axioms LeanFX2.PolyTerm.subst
#assert_no_axioms LeanFX2.PolyTerm.subst0

-- K11.13 Phase C-1S (#1745): reverse-direction subst commute —
-- `RawPolyTerm.toRawTerm` commutes with `RawPolyTerm.subst`.  Mirror
-- of Phase C-1 for subst.  Bridge `RawPolyTermSubst.toRawTermSubst`
-- projects each substituent through `toRawTerm`; `lift_*_commute` uses
-- Phase C-1's rename commute for the succ-position weakening case;
-- 73-case structural induction headline uses the lift commute for
-- binder cases (lam / pathLam / piTyCode / sigmaTyCode); `subst0`
-- corollary closes the β-reduction singleton form.
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermSubst.toRawTermSubst
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermSubst.lift_toRawTermSubst_commute
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.toRawTerm_subst_commute
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.subst0_toRawTerm_commute

end LeanFX2.Tools

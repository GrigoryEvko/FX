import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.Term.PolyToTerm
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditTerm — 378 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
#assert_no_axioms LeanFX2.Term.rename_injective_atVar
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
#assert_no_axioms LeanFX2.Term.rename_injective_atGlueIntro_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atGlueElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atListElim_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionNone
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionSome_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOptionMatch_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherInl_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherInr_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atEitherMatch_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIdJ_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atOEqJ_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIdStrictRec_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atOEqRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atIdStrictRefl
#assert_no_axioms LeanFX2.Term.rename_injective_atInterval0
#assert_no_axioms LeanFX2.Term.rename_injective_atInterval1
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalOpp_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalMeet_of_inner
#assert_no_axioms LeanFX2.Term.rename_injective_atIntervalJoin_of_inner
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

/-! ## Phase 2 HEq Congruence Lemmas — 77 `#assert_no_axioms` checks.

Promotion of `Smoke/AuditPhase2HEqCongr.lean`'s `#print axioms` entries
to per-decl machine-enforced strict gate.  These 77 ctor congruence
lemmas are the foundational scaffolding for all HEq cascades in
downstream Compat / Confluence / Bridge layers; each must remain
zero-axiom to maintain kernel discipline.

Closes the Phase 2 strict-gate coverage gap mirroring the same
pattern as commits f3df931 (RawStep.par inversions) and d2e9d4a
(RawStep.par cong/inv/beta). -/

#assert_no_axioms LeanFX2.Term.app_HEq_congr
#assert_no_axioms LeanFX2.Term.lam_HEq_congr
#assert_no_axioms LeanFX2.Term.appPi_HEq_congr
#assert_no_axioms LeanFX2.Term.lamPi_HEq_congr
#assert_no_axioms LeanFX2.Term.pair_HEq_congr
#assert_no_axioms LeanFX2.Term.fst_HEq_congr
#assert_no_axioms LeanFX2.Term.snd_HEq_congr
#assert_no_axioms LeanFX2.Term.boolElim_HEq_congr
#assert_no_axioms LeanFX2.Term.natSucc_HEq_congr
#assert_no_axioms LeanFX2.Term.natElim_HEq_congr
#assert_no_axioms LeanFX2.Term.natRec_HEq_congr
#assert_no_axioms LeanFX2.Term.listCons_HEq_congr
#assert_no_axioms LeanFX2.Term.listElim_HEq_congr
#assert_no_axioms LeanFX2.Term.optionSome_HEq_congr
#assert_no_axioms LeanFX2.Term.optionMatch_HEq_congr
#assert_no_axioms LeanFX2.Term.eitherInl_HEq_congr
#assert_no_axioms LeanFX2.Term.eitherInr_HEq_congr
#assert_no_axioms LeanFX2.Term.eitherMatch_HEq_congr
#assert_no_axioms LeanFX2.Term.refl_HEq_congr
#assert_no_axioms LeanFX2.Term.idJ_HEq_congr
#assert_no_axioms LeanFX2.Term.modIntro_HEq_congr
#assert_no_axioms LeanFX2.Term.modElim_HEq_congr
#assert_no_axioms LeanFX2.Term.subsume_HEq_congr
#assert_no_axioms LeanFX2.Term.cumulUp_HEq_congr
#assert_no_axioms LeanFX2.Term.equivReflId_HEq_congr
#assert_no_axioms LeanFX2.Term.funextRefl_HEq_congr
#assert_no_axioms LeanFX2.Term.equivReflIdAtId_HEq_congr
#assert_no_axioms LeanFX2.Term.funextReflAtId_HEq_congr
#assert_no_axioms LeanFX2.Term.uaToEquiv_HEq_congr
#assert_no_axioms LeanFX2.Term.equivApply_HEq_congr
#assert_no_axioms LeanFX2.Term.var_HEq_congr
#assert_no_axioms LeanFX2.Term.unit_HEq_congr
#assert_no_axioms LeanFX2.Term.boolTrue_HEq_congr
#assert_no_axioms LeanFX2.Term.boolFalse_HEq_congr
#assert_no_axioms LeanFX2.Term.natZero_HEq_congr
#assert_no_axioms LeanFX2.Term.listNil_HEq_congr
#assert_no_axioms LeanFX2.Term.optionNone_HEq_congr
#assert_no_axioms LeanFX2.Term.interval0_HEq_congr
#assert_no_axioms LeanFX2.Term.interval1_HEq_congr
#assert_no_axioms LeanFX2.Term.intervalOpp_HEq_congr
#assert_no_axioms LeanFX2.Term.intervalMeet_HEq_congr
#assert_no_axioms LeanFX2.Term.intervalJoin_HEq_congr
#assert_no_axioms LeanFX2.Term.pathLam_HEq_congr
#assert_no_axioms LeanFX2.Term.pathApp_HEq_congr
#assert_no_axioms LeanFX2.Term.glueIntro_HEq_congr
#assert_no_axioms LeanFX2.Term.glueElim_HEq_congr
#assert_no_axioms LeanFX2.Term.hcomp_HEq_congr
#assert_no_axioms LeanFX2.Term.recordIntro_HEq_congr
#assert_no_axioms LeanFX2.Term.recordProj_HEq_congr
#assert_no_axioms LeanFX2.Term.refineElim_HEq_congr
#assert_no_axioms LeanFX2.Term.codataDest_HEq_congr
#assert_no_axioms LeanFX2.Term.sessionRecv_HEq_congr
#assert_no_axioms LeanFX2.Term.equivApp_HEq_congr
#assert_no_axioms LeanFX2.Term.oeqRefl_HEq_congr
#assert_no_axioms LeanFX2.Term.oeqJ_HEq_congr
#assert_no_axioms LeanFX2.Term.oeqFunext_HEq_congr
#assert_no_axioms LeanFX2.Term.idStrictRefl_HEq_congr
#assert_no_axioms LeanFX2.Term.idStrictRec_HEq_congr
#assert_no_axioms LeanFX2.Term.universeCode_HEq_congr
#assert_no_axioms LeanFX2.Term.arrowCode_HEq_congr
#assert_no_axioms LeanFX2.Term.piTyCode_HEq_congr
#assert_no_axioms LeanFX2.Term.sigmaTyCode_HEq_congr
#assert_no_axioms LeanFX2.Term.productCode_HEq_congr
#assert_no_axioms LeanFX2.Term.sumCode_HEq_congr
#assert_no_axioms LeanFX2.Term.listCode_HEq_congr
#assert_no_axioms LeanFX2.Term.optionCode_HEq_congr
#assert_no_axioms LeanFX2.Term.eitherCode_HEq_congr
#assert_no_axioms LeanFX2.Term.idCode_HEq_congr
#assert_no_axioms LeanFX2.Term.equivCode_HEq_congr
#assert_no_axioms LeanFX2.Term.transp_HEq_congr
#assert_no_axioms LeanFX2.Term.refineIntro_HEq_congr
#assert_no_axioms LeanFX2.Term.codataUnfold_HEq_congr
#assert_no_axioms LeanFX2.Term.sessionSend_HEq_congr
#assert_no_axioms LeanFX2.Term.effectPerform_HEq_congr
#assert_no_axioms LeanFX2.Term.equivIntroHet_HEq_congr
#assert_no_axioms LeanFX2.Term.uaIntroHet_HEq_congr
#assert_no_axioms LeanFX2.Term.funextIntroHet_HEq_congr

-- Term/WeakenInverse foundation — typed strengthening primitives.
-- Layer 1: raw inversion helpers for the most common ctor shapes.
#assert_no_axioms LeanFX2.RawTerm.weakenInverse_var
#assert_no_axioms LeanFX2.RawTerm.weakenInverse_lam
#assert_no_axioms LeanFX2.RawTerm.weakenInverse_app
-- Layer 2: typed weaken inversions at canonical-form raw shapes.
#assert_no_axioms LeanFX2.Term.weakenInverse_atUnit
#assert_no_axioms LeanFX2.Term.weakenInverse_atBoolTrue
#assert_no_axioms LeanFX2.Term.weakenInverse_atBoolFalse
#assert_no_axioms LeanFX2.Term.weakenInverse_atNatZero
#assert_no_axioms LeanFX2.Term.weakenInverse_atVar
-- Layer 3: cascade construction + projection helpers.
#assert_no_axioms LeanFX2.Term.eta_shape_construct
#assert_no_axioms LeanFX2.Term.weaken_var_unfolds
#assert_no_axioms LeanFX2.Term.weaken_app_toRaw
-- Term/TypedInversion — typed app-shape structural inversions.
-- Universal + arrow/Π specializations.  Prerequisite for typed-eta
-- redesign per feedback_typed_eta_lam_inv_cascade_blocker_2026_05_16.md.
#assert_no_axioms LeanFX2.Term.app_inv
#assert_no_axioms LeanFX2.Term.app_inv_arrow
#assert_no_axioms LeanFX2.Term.app_inv_pi
-- Typed weaken inversion at arrow type (Option form).  See
-- LeanFX2.Term.TypedInversion section "weaken_inv_arrow" for the
-- gap analysis on the universal existence form.
#assert_no_axioms LeanFX2.Term.weaken_inv_arrow_option
-- Supporting infrastructure for the typed weaken inversion cascade.
#assert_no_axioms LeanFX2.Ty.weaken_inj
#assert_no_axioms LeanFX2.Term.weakenInverse_atVarZero
-- Semantic / partial strengthening raw-index certificates.
#assert_no_axioms LeanFX2.ContextStrengthening
#assert_no_axioms LeanFX2.ContextStrengthening.toTermRenaming
#assert_no_axioms LeanFX2.ContextStrengthening.dropNewest
#assert_no_axioms LeanFX2.ContextStrengthening.dropNewest_toTermRenaming
#assert_no_axioms LeanFX2.ContextStrengthening.lift
#assert_no_axioms LeanFX2.Term.StrengtheningResult
#assert_no_axioms LeanFX2.Term.StrengtheningResult.renamedTarget
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedVarOfSurvives
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUnit
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolTrue
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolFalse
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatZero
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedInterval0
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedInterval1
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListNilOfType
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionNoneOfType
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatSucc
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionSome
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatRec
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedModIntro
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedModElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSubsume
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalOpp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalMeet
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalJoin
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedApp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedAppPi
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedLam
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedLamPi
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathLam
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathApp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListCons
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListElimOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherInlOfRightType
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherInrOfLeftType
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionMatch
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionMatchOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherMatch
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherMatchOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineIntro
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineElimOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefl
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqRefl
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRefl
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdJ
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdJOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqJ
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqJOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRec
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRecOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPair
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFst
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSnd
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordIntro
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordProj
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordProjOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataUnfold
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataUnfoldOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataDest
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataDestOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSessionSend
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSessionRecv
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCumulUp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUniverseCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedArrowCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPiTyCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSigmaTyCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedProductCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSumCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivReflId
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivReflIdAtId
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextRefl
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextReflAtId
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivAppOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApply
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApplyOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUaToEquiv
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqFunext
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUaIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueIntro
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueElimOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedTransp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcomp
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPath
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEffectPerform
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?
#assert_no_axioms LeanFX2.Term.strengthenTyped?
#assert_no_axioms LeanFX2.Term.strengthenTyped?_imp_indices_weaken
#assert_no_axioms LeanFX2.Term.usesNewestSlotTyped?
#assert_no_axioms LeanFX2.Term.unweaken?
#assert_no_axioms LeanFX2.Term.not_usesNewestSlotTyped?_imp_strengthenTyped?_some
#assert_no_axioms LeanFX2.Term.partialStrengthen?
#assert_no_axioms LeanFX2.Term.partialStrengthen?_imp_indices_rename
#assert_no_axioms LeanFX2.Term.strengthen?
#assert_no_axioms LeanFX2.Term.usesNewestSlot?
#assert_no_axioms LeanFX2.Term.strengthen?_imp_indices_weaken
#assert_no_axioms LeanFX2.Term.not_usesNewestSlot?_imp_indices_weaken

/-! ## Typed strengthening image soundness scaffold.

These declarations start the term-level soundness layer above
`StrengtheningResult`: successful typed strengthening results re-rename to
their source term.  Recursive producer coverage is intentionally
constructor-granular so the full image theorem can land without changing the
existing computational dispatcher. -/

#assert_no_axioms LeanFX2.Term.StrengtheningSoundness
#assert_no_axioms LeanFX2.Term.heq_cast_right
#assert_no_axioms LeanFX2.Term.heq_cast_left
#assert_no_axioms LeanFX2.Term.rename_var_heq
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedVarOfSurvives_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUnit_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolTrue_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolFalse_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatZero_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedInterval0_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedInterval1_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListNilOfType_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionNoneOfType_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatSucc_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionSome_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedBoolElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedAppOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedApp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedAppPiOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedAppPi_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedNatRec_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedModIntro_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedModElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSubsume_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListCons_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherInlOfRightType_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherInrOfLeftType_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPair_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFst_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSnd_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalOpp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalMeet_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIntervalJoin_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUniverseCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedArrowCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPiTyCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSigmaTyCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedProductCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSumCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivCode_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefl_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqRefl_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRefl_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivReflId_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivReflIdAtId_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextRefl_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextReflAtId_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListElimOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionMatchOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherMatchOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineIntro_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineElimOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordIntro_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordProjOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataUnfoldOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataDestOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSessionSend_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedSessionRecv_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCumulUp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUaToEquiv_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedFunextIntroHet_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedUaIntroHet_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueIntro_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqFunext_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdJOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqJOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRecOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApplyOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivAppOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueElimOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedLamPi_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedLam_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathLam_sound
#assert_no_axioms LeanFX2.Term.pathLam_HEq_congr
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathAppOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathAppOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedTranspOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedTranspOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedTransp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcomp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHetOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHetOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEffectPerformOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEffectPerformOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataUnfold_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEffectPerform_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRecordProj_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedRefineElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedCodataDest_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedGlueElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPath_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedPathApp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedListElim_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOptionMatch_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEitherMatch_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdJ_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedOeqJ_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedIdStrictRec_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivApply_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHet_sound

#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atUnit_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atBoolTrue_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atBoolFalse_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atNatZero_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atInterval0_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atInterval1_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atVar_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atNatSucc_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOptionSome_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atModIntro_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atModElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSubsume_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalOpp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalMeet_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalJoin_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atListCons_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atListNil_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOptionNone_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEitherInl_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEitherInr_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atPair_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atFst_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSnd_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atApp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atAppPi_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atBoolElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atNatElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atNatRec_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atListElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOptionMatch_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEitherMatch_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atRefl_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOeqRefl_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIdJ_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOeqJ_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOeqFunext_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIdStrictRefl_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIdStrictRec_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atPathApp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atGlueElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atRecordIntro_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atRecordProj_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atRefineIntro_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atRefineElim_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atCumulUp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atCodataUnfold_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atCodataDest_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSessionSend_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSessionRecv_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivReflId_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atArrowCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atPiTyCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSigmaTyCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atProductCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atSumCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atListCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atOptionCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEitherCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atIdCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atUniverseCode_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atFunextRefl_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivReflIdAtId_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atFunextReflAtId_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivApp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivApply_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atUaToEquiv_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEquivIntroHet_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atUaIntroHet_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atFunextIntroHet_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atEffectPerform_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atGlueIntro_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atPathLam_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atLam_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atLamPi_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atHcomp_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atHcompPath_imp_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_atTransp_imp_sound

#assert_no_axioms LeanFX2.Term.isAggregatorSound_var
#assert_no_axioms LeanFX2.Term.isAggregatorSound_unit
#assert_no_axioms LeanFX2.Term.isAggregatorSound_boolTrue
#assert_no_axioms LeanFX2.Term.isAggregatorSound_boolFalse
#assert_no_axioms LeanFX2.Term.isAggregatorSound_natZero
#assert_no_axioms LeanFX2.Term.isAggregatorSound_interval0
#assert_no_axioms LeanFX2.Term.isAggregatorSound_interval1
#assert_no_axioms LeanFX2.Term.isAggregatorSound_listNil
#assert_no_axioms LeanFX2.Term.isAggregatorSound_optionNone
#assert_no_axioms LeanFX2.Term.isAggregatorSound_refl
#assert_no_axioms LeanFX2.Term.isAggregatorSound_oeqRefl
#assert_no_axioms LeanFX2.Term.isAggregatorSound_idStrictRefl
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivReflId
#assert_no_axioms LeanFX2.Term.isAggregatorSound_arrowCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_piTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_sigmaTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_productCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_sumCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_listCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_optionCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_eitherCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_idCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_universeCode
#assert_no_axioms LeanFX2.Term.isAggregatorSound_funextRefl
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.isAggregatorSound_funextReflAtId
#assert_no_axioms LeanFX2.Term.isAggregatorSound_funextIntroHet
#assert_no_axioms LeanFX2.Term.isAggregatorSound_natSucc
#assert_no_axioms LeanFX2.Term.isAggregatorSound_optionSome
#assert_no_axioms LeanFX2.Term.isAggregatorSound_modIntro
#assert_no_axioms LeanFX2.Term.isAggregatorSound_modElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_subsume
#assert_no_axioms LeanFX2.Term.isAggregatorSound_eitherInl
#assert_no_axioms LeanFX2.Term.isAggregatorSound_eitherInr
#assert_no_axioms LeanFX2.Term.isAggregatorSound_recordIntro
#assert_no_axioms LeanFX2.Term.isAggregatorSound_recordProj
#assert_no_axioms LeanFX2.Term.isAggregatorSound_refineElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_cumulUp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_fst
#assert_no_axioms LeanFX2.Term.isAggregatorSound_snd
#assert_no_axioms LeanFX2.Term.isAggregatorSound_pair
#assert_no_axioms LeanFX2.Term.isAggregatorSound_refineIntro
#assert_no_axioms LeanFX2.Term.isAggregatorSound_intervalOpp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_intervalMeet
#assert_no_axioms LeanFX2.Term.isAggregatorSound_intervalJoin
#assert_no_axioms LeanFX2.Term.isAggregatorSound_listCons
#assert_no_axioms LeanFX2.Term.isAggregatorSound_codataDest
#assert_no_axioms LeanFX2.Term.isAggregatorSound_codataUnfold
#assert_no_axioms LeanFX2.Term.isAggregatorSound_pathApp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_glueElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_uaToEquiv
#assert_no_axioms LeanFX2.Term.isAggregatorSound_transp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_app
#assert_no_axioms LeanFX2.Term.isAggregatorSound_appPi
#assert_no_axioms LeanFX2.Term.isAggregatorSound_sessionSend
#assert_no_axioms LeanFX2.Term.isAggregatorSound_sessionRecv
#assert_no_axioms LeanFX2.Term.isAggregatorSound_glueIntro
#assert_no_axioms LeanFX2.Term.isAggregatorSound_lam
#assert_no_axioms LeanFX2.Term.isAggregatorSound_lamPi
#assert_no_axioms LeanFX2.Term.isAggregatorSound_pathLam
#assert_no_axioms LeanFX2.Term.isAggregatorSound_boolElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_natElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_natRec
#assert_no_axioms LeanFX2.Term.isAggregatorSound_listElim
#assert_no_axioms LeanFX2.Term.isAggregatorSound_optionMatch
#assert_no_axioms LeanFX2.Term.isAggregatorSound_eitherMatch
#assert_no_axioms LeanFX2.Term.isAggregatorSound_idJ
#assert_no_axioms LeanFX2.Term.isAggregatorSound_oeqJ
#assert_no_axioms LeanFX2.Term.isAggregatorSound_idStrictRec
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivApp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivApply
#assert_no_axioms LeanFX2.Term.isAggregatorSound_equivIntroHet
#assert_no_axioms LeanFX2.Term.isAggregatorSound_oeqFunext
#assert_no_axioms LeanFX2.Term.isAggregatorSound_uaIntroHet
#assert_no_axioms LeanFX2.Term.isAggregatorSound_effectPerform
#assert_no_axioms LeanFX2.Term.isAggregatorSound_hcomp
#assert_no_axioms LeanFX2.Term.isAggregatorSound_hcompPath

-- HEADLINE: universal aggregator soundness over all 78 Term ctors.
-- Composes every isAggregatorSound_<ctor> wrapper via structural
-- induction; unblocks the Phase A image theorem trio and the
-- downstream Step.eta cascade per extended-roadmap.md Day 32.
#assert_no_axioms LeanFX2.Term.isAggregatorSound_universal

-- Image Step 1: right-inverse soundness — direct corollary of the
-- universal aggregator headline.  Consumed by Step 3 iff headline
-- and by the Phase B+ Step.eta SR cascade.
#assert_no_axioms LeanFX2.Term.weaken_inv_of_strengthenTyped?_some

-- Image Step 2: unweaken?-to-strengthenTyped? success direction.
-- Tautological bijection — both witnesses succeed under identical
-- conditions per unweaken?'s definitional pattern-match.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_some_of_unweaken?_some

-- Image Step 3: headline iff between unweaken? and strengthenTyped?
-- success.  Tautological bijection (see Step 2).  Unconditional
-- totality on the weakening image requires a separate 78-case
-- structural induction.
#assert_no_axioms LeanFX2.Term.weaken_image_iff_strengthenTyped?_some

-- Phase A close-out (Step.eta integration plan): conditional
-- existence-form companion to `Term.weaken_inv_arrow_option`.
-- Packages soundness via `weaken_inv_of_strengthenTyped?_some`
-- and reduces `Term.unweaken?` success to `HEq weakenedFn (Term.weaken
-- newType originalFn)`.  Consumed by Phase B `lift_lam` η-disjunct.
#assert_no_axioms LeanFX2.Term.weaken_inv_arrow

-- BIG-ASS THEOREM (closed-atomic foundation): `IsTotalOnWeaken`
-- predicate and the 7 closed-atomic ctor totality witnesses.  Each
-- atomic case shipped as a direct `rfl` proof both at the
-- `(strengthenTyped? (Term.weaken nt _)).isSome` level and at the
-- user-facing `unweaken?_weaken_<ctor>` level.  The recursive 71
-- ctors land in a follow-up via `IsTotalOnWeaken`'s composition rule.

#assert_no_axioms LeanFX2.Term.IsTotalOnWeaken

#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_unit
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolTrue
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolFalse
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natZero
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_interval0
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_interval1
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_var

-- True 0-IH parametric atomic: universeCode (no scope-indexed payload).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_universeCode

-- 1-IH non-binder ctor totality (compositional rules — natSucc and
-- intervalOpp as canonical templates; remaining 13 single-IH ctors
-- follow the same unfold + split + ▸ pattern).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natSucc
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalOpp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionSome
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_modIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_modElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_subsume
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_cumulUp

-- Wave A: parametric atomic 0-IH ctors (no Term IH; sub-payloads
-- strengthen via Ty.strengthen?_weaken / RawTerm.strengthen?_weaken).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listNil
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionNone
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqRefl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idStrictRefl

-- Wave A.2: universe-code 0-IH ctors (only outer-scope RawTerm payloads).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_arrowCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_productCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sumCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivCode

-- Wave B.1: 1-IH non-binder ctors (single Term recursion + zero or
-- more Ty/RawTerm payloads).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_recordIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_recordProj
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherInl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherInr
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sessionRecv
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_codataDest

-- Wave C.1: 2-IH non-binder ctors.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listCons
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalMeet
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalJoin
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_app
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_codataUnfold
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sessionSend

-- Wave C.2: more 2-IH non-binder ctors + 3-IH identity-elimination
-- ctors (idJ, oeqJ, idStrictRec) with carrier+leftEndpoint+rightEndpoint
-- + baseCase + witness chains.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivApp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivApply
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idJ
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqJ
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idStrictRec

-- Wave D: cubical / HoTT non-binder ctors.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivReflId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_glueElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_hcomp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_glueIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_transp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_uaToEquiv
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_pathApp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_hcompPath
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_uaIntroHet

-- Wave E: eliminator ctors (3-IH non-binder pattern).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natRec
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionMatch
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherMatch

-- Wave F: effects ctor (operation signature carrier strengthening
-- via OperationSignature.map definitional unfolding).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_effectPerform

-- Wave G: lift-based universe-code ctors (codomain at scope+1).
-- Use the lift-after-lift composition (lift_dropNewest_weaken_lift)
-- + RawTerm.partialStrengthen?_rename_some + rename_identity.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_piTyCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sigmaTyCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_fst
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refineIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refineElim

-- Wave H: HoTT canonical-witness ctors with scope+1 applyRaw payloads.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextReflAtId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextIntroHet

-- Wave I: Eq.mpr-blocked ctor totality via weaken_<ctor>_eq + cast invariance.
-- These ctors' Term.rename arms wrap the constructed value in (eq).symm ▸ ...
-- which blocks the standard unfold+split template; resolved via per-ctor
-- rewrite lemmas + strengthenTyped?_isSome_castInvariant.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_isSome_castInvariant
#assert_no_axioms LeanFX2.Term.weaken_snd_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_snd
#assert_no_axioms LeanFX2.Term.weaken_funextRefl_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextRefl
#assert_no_axioms LeanFX2.Term.weaken_appPi_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_appPi
#assert_no_axioms LeanFX2.Term.weaken_pair_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_pair
#assert_no_axioms LeanFX2.Term.weaken_oeqFunext_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqFunext
#assert_no_axioms LeanFX2.Term.weaken_equivIntroHet_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivIntroHet
#assert_no_axioms LeanFX2.Term.weaken_boolElim_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolElim

-- User-facing unweaken?_weaken_<ctor> headline theorems.  Each is a
-- direct `rfl` witness — concrete totality for the closed atomic
-- ctors, consumable by Step.eta-cascade SR proofs.
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_unit
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_boolTrue
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_boolFalse
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_natZero
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_interval0
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_interval1
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_var
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_universeCode

-- Genuine (non-tautological) iff for the closed-atomic unit case.
-- Augments the existing tautological iff with concrete totality
-- content on a closed source.
#assert_no_axioms LeanFX2.Term.weaken_image_iff_strengthenTyped?_some_TRUE_unit

-- Universal-strengthening totality predicate `IsAggregatorTotal` and
-- its per-ctor wrappers.  The 3 binder wrappers close the
-- architectural gap that the narrow `IsTotalOnWeaken` predicate
-- could not bridge.
#assert_no_axioms LeanFX2.Term.IsAggregatorTotal
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_unit
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_boolTrue
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_boolFalse
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_natZero
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_interval0
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_interval1
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_var
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_lam
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_lamPi
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_pathLam
-- Phase 1.C Wave 1: 1-IH non-binder totality wrappers
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_natSucc
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_intervalOpp
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_modIntro
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_modElim
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_subsume
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionSome
-- Phase 1.C Wave 2: more 1-IH wrappers
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_eitherInl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_eitherInr
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_recordIntro
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_recordProj
-- Phase 1.C Wave 3: sessionRecv + parametric atomics
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sessionRecv
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listNil
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionNone
-- Phase 1.C Wave 4: interval pair + refl family
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_intervalMeet
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_intervalJoin
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listCons
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_refl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_oeqRefl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idStrictRefl
-- Phase 1.C Wave 5: type codes + cumulUp + universeCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_universeCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_cumulUp
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_arrowCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_piTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sigmaTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_productCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sumCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_eitherCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivCode
-- Phase 1.C Wave 6: 2-IH dependent pair (uses Ty.subst0 reconstruction)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_pair
-- Phase 1.C Wave 7: equivReflId + refineIntro
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivReflId
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_refineIntro
-- Phase 1.C Wave 8: codataUnfold (mapTwo of stateType + outputType)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_codataUnfold
-- Phase Y.1 Wave 1: funextRefl + funextReflAtId (piTy/id/weaken_lift)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_funextRefl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_funextReflAtId
-- Phase Y.1 Wave 2: hcomp + glueIntro (carrier-direct / glue.mapTwo)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_hcomp
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_glueIntro
-- Phase Y.1 Wave 3: oeqFunext (oeq+arrow+lift-app construction)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_oeqFunext
-- Phase Y.1 Wave 4: funextIntroHet (0-IH, id+arrow+lam decomposition)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_funextIntroHet
-- Phase Y.2 Wave 1: pathApp bridge (endpoint witnesses as hypotheses)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_pathApp_with_endpoints
-- Phase Y.2 Wave 2: hcompPath + glueElim + codataDest bridges
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_hcompPath_with_endpoints
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_glueElim_with_boundary
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_codataDest_with_state
-- Phase Y.2 Wave 3: fst (secondType.back.lift bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_fst_with_second
-- Phase Y.2 Wave 4: equivApp + equivApply (carrierA bridges)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivApp_with_carrierA
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivApply_with_carrierA
-- Phase Y.2 Wave 5: refineElim (predicate.back.lift bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_refineElim_with_predicate
-- Phase Y.2 Wave 6: app + idJ + oeqJ + idStrictRec bridges
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_app_with_domain
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idJ_with_id_components
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_oeqJ_with_oeq_components
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idStrictRec_with_idStrict_components
-- Phase Y.2 Wave 7: equivReflIdAtId + uaToEquiv (HoTT family bridges)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivReflIdAtId_with_carrier
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_uaToEquiv_with_carrier_raws
-- Phase Y.2 Wave 8: uaIntroHet + equivIntroHet (HoTT family bridges)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_uaIntroHet_with_carriers
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivIntroHet_with_inv_raws
-- Phase Y.2 Wave 9: sessionSend (payload type bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sessionSend_with_payload
-- Phase Y.2 Wave 10: boolElim (motive bridge with subst0 reconstruction)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_boolElim_with_motive
-- Phase Y.1 Wave 5: natElim + natRec (no aux witnesses, universal)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_natElim
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_natRec
-- Phase Y.2 Wave 11: listElim + optionMatch + eitherMatch (element/lr bridges)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listElim_with_element
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionMatch_with_element
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_eitherMatch_with_lr_types
-- Phase Y.2 Wave 12: snd (sigma witnesses bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_snd_with_sigma_witnesses
-- Phase Y.2 Wave 13: appPi (Pi witnesses bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_appPi_with_pi_witnesses
-- Phase Y.2 Wave 14: transp (path witnesses bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_transp_with_path_witnesses
-- Phase Y.2 Wave 15: effectPerform (op-sig witness bridge)
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_effectPerform_with_opsig_witness

-- Phase X: bridge from `IsAggregatorTotal (Term.weaken ...)` to
-- `IsTotalOnWeaken` and the three binder wrappers that close the
-- IsTotalOnWeaken cascade from 75/78 to 78/78.  Each wrapper applies
-- the bridge to a per-newType `IsAggregatorTotal` hypothesis on the
-- weakened binder term; downstream constructions of that hypothesis
-- combine body's `IsAggregatorTotal` IH with the typed rename-
-- compatibility transport and `isAggregatorTotal_<binder>`.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_of_weaken_isAggregatorTotal
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_lam
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_lamPi
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_pathLam

-- strength-T1: per-ctor renaming-image dispatcher equations.
-- Closed-atomic (7): unit / boolTrue / boolFalse / natZero / interval0 /
-- interval1 / universeCode.  Each closes by `rfl`.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_unit
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_boolTrue
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_boolFalse
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natZero
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_interval0
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_interval1
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_universeCode
-- strength-T1 parametric-atomic (7): subst-via-witness pattern.  Each
-- ctor with Ty (or Ty + RawTerm) payload but no Term children — the
-- dispatcher's match-with-binding is unblocked by `subst`-ing the
-- propositional equality between the bound witness and the original
-- (derived from `Ty.partialStrengthen?_rename_some` / `Ty.rename_identity`
-- and their raw companions).
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listNil
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionNone
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivReflId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_oeqRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idStrictRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivReflIdAtId
-- strength-T1 1-IH non-binder atomic: subst-via-witness on inner Term IH.
-- Each ctor wraps a single Term sub-result (optionally with Ty / RawTerm
-- payloads, or value-level data) via the partialStrengthenTyped helpers'
-- match-then-construct shape.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natSucc
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalOpp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_modIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_modElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_subsume
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherInl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherInr
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sessionRecv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_cumulUp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_recordProj
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_codataDest
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_recordIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_glueElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listCons
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_app
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_oeqJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idStrictRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalMeet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalJoin
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_hcomp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_arrowCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sumCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_productCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_piTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sigmaTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_funextReflAtId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refineIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refineElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sessionSend
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_transp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_hcompPath
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_glueIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_pathApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_codataUnfold
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_fst
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivApply
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_uaToEquiv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_uaIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_funextIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_effectPerform

-- strength-T1 cast-invariance helper lemmas used to peel Eq.mpr casts in
-- the 11 cast-wrapped ctors (lam, lamPi, appPi, snd, pair, boolElim,
-- pathLam, oeqFunext, funextRefl, equivIntroHet, var).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_castInvariant
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_castInvariantHEq
#assert_no_axioms LeanFX2.Term.termTypeCastHEq
#assert_no_axioms LeanFX2.Term.rename_oeqFunext_unfolds

-- strength-T1 cast-wrapped ctors (HEq-form pivot — Eq-form structurally
-- blocked because the named cast equations like funextReflType_rename are
-- non-rfl, so `cases castProof` fails past Eq.mpr ▸).  Pivot ships as HEq
-- via partialStrengthenTyped?_castInvariantHEq; downstream consumers bridge
-- HEq → Eq via the named cast equation when needed.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_var
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_appPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_snd
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_pair
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_lam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_lamPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_pathLam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_oeqFunext
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_equivIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_boolElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_funextRefl

end LeanFX2.Tools

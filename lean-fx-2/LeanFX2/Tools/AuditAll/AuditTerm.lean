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

/-! ## AuditTerm — 348 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
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
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess_sound
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess
#assert_no_axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess_sound

end LeanFX2.Tools

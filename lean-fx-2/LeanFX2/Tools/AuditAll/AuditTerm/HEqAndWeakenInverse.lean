import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.WeakenInverse
import LeanFX2.Term.TypedInversion

/-! # AuditTerm.HEqAndWeakenInverse — HEq congruence and typed inversion gates. -/

namespace LeanFX2.Tools

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
#assert_no_axioms LeanFX2.Term.eta_lam_shape_construct
#assert_no_axioms LeanFX2.Term.eta_shape_construct
#assert_no_axioms LeanFX2.Term.eta_path_shape_construct
#assert_no_axioms LeanFX2.Term.eta_lam_shape_toRaw
#assert_no_axioms LeanFX2.Term.eta_path_shape_toRaw
#assert_no_axioms LeanFX2.Term.weaken_var_unfolds
#assert_no_axioms LeanFX2.Term.weaken_app_toRaw
#assert_no_axioms LeanFX2.Term.weaken_pathApp_toRaw
-- Raw/type-index strengthening facade built from the weaken-inverse layer.
#assert_no_axioms LeanFX2.Term.partialStrengthen?
#assert_no_axioms LeanFX2.Term.partialStrengthen?_imp_indices_rename
#assert_no_axioms LeanFX2.Term.strengthen?
#assert_no_axioms LeanFX2.Term.usesNewestSlot?
#assert_no_axioms LeanFX2.Term.strengthen?_imp_indices_weaken
#assert_no_axioms LeanFX2.Term.not_usesNewestSlot?_imp_indices_weaken
-- Term/TypedInversion — typed app-shape structural inversions.
-- Universal + arrow/Π specializations.  Prerequisite for typed-eta
-- redesign per feedback_typed_eta_lam_inv_cascade_blocker_2026_05_16.md.
#assert_no_axioms LeanFX2.Term.app_inv
#assert_no_axioms LeanFX2.Term.app_inv_arrow
#assert_no_axioms LeanFX2.Term.app_inv_pi
-- Typed weaken inversion at arrow type (Option form).
#assert_no_axioms LeanFX2.Term.weaken_inv_arrow_option
-- Supporting infrastructure for typed weaken inversion and eta-shape builders.
#assert_no_axioms LeanFX2.Ty.weaken_inj
#assert_no_axioms LeanFX2.Term.weakenInverse_atVarZero

end LeanFX2.Tools

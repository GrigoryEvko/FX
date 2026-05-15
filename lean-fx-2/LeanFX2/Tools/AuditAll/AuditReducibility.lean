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

/-! ### SN preservation helpers + CR2 forward closure -/

#assert_no_axioms LeanFX2.RawTerm.unit_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.boolTrue_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.boolFalse_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.natZero_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.lam_isStronglyNormalizing
#assert_no_axioms LeanFX2.RawTerm.isStronglyNormalizing.step_preserves
#assert_no_axioms LeanFX2.RawTerm.isStronglyNormalizing_weaken
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
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalOpp
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalMeet
#assert_no_axioms LeanFX2.ReducibleK.fundamental_intervalJoin
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idJ
#assert_no_axioms LeanFX2.ReducibleK.fundamental_oeqJ
#assert_no_axioms LeanFX2.ReducibleK.fundamental_idStrictRec
#assert_no_axioms LeanFX2.ReducibleK.fundamental_equivApply
#assert_no_axioms LeanFX2.ReducibleK.fundamental_pathApp
#assert_no_axioms LeanFX2.ReducibleK.fundamental_glueElim

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

end LeanFX2.Tools

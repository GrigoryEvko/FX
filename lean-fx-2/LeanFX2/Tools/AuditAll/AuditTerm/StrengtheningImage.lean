import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage

/-! # AuditTerm.StrengtheningImage — image and weaken-inversion headline gates. -/

namespace LeanFX2.Tools

-- HEADLINE: universal aggregator soundness over all 78 Term ctors.
-- Composes every isAggregatorSound_<ctor> wrapper via structural
-- induction; unblocks the Phase A image theorem trio and the
-- downstream Step.eta cascade per extended-roadmap.md Day 32.
#assert_no_axioms LeanFX2.Term.isAggregatorSound_universal

-- Image Step 1: right-inverse soundness — direct corollary of the
-- universal aggregator headline.  Consumed by Step 3 iff headline
-- and by the Phase B+ Step.eta SR cascade.
#assert_no_axioms LeanFX2.Term.weaken_inv_of_strengthenTyped?_some
#assert_no_axioms LeanFX2.Term.weaken_inv_of_unweaken?_some
#assert_no_axioms LeanFX2.Term.weaken_inv_unit
#assert_no_axioms LeanFX2.Term.weaken_inv_bool
#assert_no_axioms LeanFX2.Term.weaken_inv_nat
#assert_no_axioms LeanFX2.Term.weaken_inv_empty
#assert_no_axioms LeanFX2.Term.weaken_inv_interval
#assert_no_axioms LeanFX2.Term.weaken_inv_universe
#assert_no_axioms LeanFX2.Term.weaken_inv_pi
#assert_no_axioms LeanFX2.Term.weaken_inv_sigma
#assert_no_axioms LeanFX2.Term.weaken_inv_path
#assert_no_axioms LeanFX2.Term.weaken_inv_refine
#assert_no_axioms LeanFX2.Term.weaken_inv_tyVar
#assert_no_axioms LeanFX2.Term.weaken_inv_listType
#assert_no_axioms LeanFX2.Term.weaken_inv_optionType
#assert_no_axioms LeanFX2.Term.weaken_inv_eitherType
#assert_no_axioms LeanFX2.Term.weaken_inv_id
#assert_no_axioms LeanFX2.Term.weaken_inv_oeq
#assert_no_axioms LeanFX2.Term.weaken_inv_idStrict
#assert_no_axioms LeanFX2.Term.weaken_inv_equiv
#assert_no_axioms LeanFX2.Term.weaken_inv_glue
#assert_no_axioms LeanFX2.Term.weaken_inv_record
#assert_no_axioms LeanFX2.Term.weaken_inv_codata
#assert_no_axioms LeanFX2.Term.weaken_inv_session
#assert_no_axioms LeanFX2.Term.weaken_inv_effect
#assert_no_axioms LeanFX2.Term.weaken_inv_modal
#assert_no_axioms LeanFX2.Term.rename_image_of_strengthenTyped?_some
#assert_no_axioms LeanFX2.RawRenamingInjective.of_partialInverseLeft
#assert_no_axioms LeanFX2.Term.rename_image_iff_strengthenTyped?_some
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_result_target_heq
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_result_eq_fromRename
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq
#assert_no_axioms LeanFX2.Term.strengthenTyped?_weaken_eq
#assert_no_axioms LeanFX2.Term.strengthenTyped?_weaken_isSome
#assert_no_axioms LeanFX2.Term.unweaken?_weaken
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_some
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_var
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_unit
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolTrue
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolFalse
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natZero
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_interval0
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_interval1
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_universeCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listNil
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionNone
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivReflId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idStrictRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natSucc_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalOpp_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modIntro_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modElim_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_subsume_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionSome_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInl_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInr_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionRecv_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_cumulUp_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordProj_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataDest_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordIntro_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueElim_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCons_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natElim_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natRec_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_app_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listElim_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionMatch_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherMatch_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalMeet_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalJoin_of_childIsSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natSucc
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalOpp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_subsume
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInr
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionRecv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_cumulUp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordProj
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataDest
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCons
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_app
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalMeet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalJoin
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_arrowCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sumCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_productCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_piTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sigmaTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idStrictRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_hcomp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextReflAtId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refineIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refineElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionSend
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_fst
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataUnfold
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivApply
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_uaToEquiv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_uaIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_appPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_snd
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pair
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_lam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_lamPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pathLam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqFunext
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_transp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_hcompPath
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pathApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_isSome_effectPerform

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

end LeanFX2.Tools

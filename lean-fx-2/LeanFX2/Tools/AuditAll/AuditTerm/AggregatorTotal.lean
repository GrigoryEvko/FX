import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage

/-! # AuditTerm.AggregatorTotal — universal strengthening totality gates. -/

namespace LeanFX2.Tools

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

end LeanFX2.Tools

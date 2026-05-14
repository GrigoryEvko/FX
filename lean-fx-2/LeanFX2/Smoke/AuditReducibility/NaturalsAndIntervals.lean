import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.NaturalsAndIntervals

Tait reducibility — Nat eliminators, list/option/either matchers,
modal intro/elim, pair/record/refine/glue introducer SN gates,
plus the interval/path/equiv/sessionRecv/sessionSend/effectPerform
introducer SN gates and their fundamental headlines.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms RawTerm.recordProj_recordIntro_isStronglyNormalizing
#print axioms Term.recordProj_recordIntro_isStronglyNormalizing
#print axioms RawTerm.refineElim_refineIntro_isStronglyNormalizing
#print axioms Term.refineElim_refineIntro_isStronglyNormalizing
#print axioms RawTerm.listCons_isStronglyNormalizing
#print axioms RawTerm.subsume_isStronglyNormalizing
#print axioms RawTerm.listNil_isStronglyNormalizing
#print axioms RawTerm.listElim_listNil_isStronglyNormalizing
#print axioms Term.listElim_listNil_isStronglyNormalizing
#print axioms RawTerm.listElim_listCons_isStronglyNormalizing
#print axioms Term.listElim_listCons_isStronglyNormalizing
#print axioms RawTerm.optionNone_isStronglyNormalizing
#print axioms RawTerm.optionMatch_optionNone_isStronglyNormalizing
#print axioms Term.optionMatch_optionNone_isStronglyNormalizing
#print axioms RawTerm.natSucc_predecessor_isStronglyNormalizing_aux
#print axioms RawTerm.natSucc_predecessor_isStronglyNormalizing
#print axioms RawTerm.natElim_natZero_isStronglyNormalizing
#print axioms Term.natElim_natZero_isStronglyNormalizing
#print axioms RawTerm.natElim_natSucc_isStronglyNormalizing
#print axioms Term.natElim_natSucc_isStronglyNormalizing
#print axioms RawTerm.natElim_isStronglyNormalizing
#print axioms Term.natElim_isStronglyNormalizing
#print axioms Reducible.fundamental_natElimZero_at_nat
#print axioms Reducible.fundamental_natElimSucc_at_nat
#print axioms Reducible.fundamental_natElim_at_nat
#print axioms RawTerm.natRec_natZero_isStronglyNormalizing
#print axioms Term.natRec_natZero_isStronglyNormalizing
#print axioms Reducible.fundamental_natRecZero_at_nat
#print axioms RawTerm.natRec_natSucc_isStronglyNormalizing
#print axioms Term.natRec_natSucc_isStronglyNormalizing
#print axioms Reducible.fundamental_natRecSucc_at_nat
#print axioms RawTerm.natRec_isStronglyNormalizing
#print axioms Term.natRec_isStronglyNormalizing
#print axioms Reducible.fundamental_natRec_at_nat
#print axioms RawTerm.refl_isStronglyNormalizing
#print axioms RawTerm.oeqRefl_isStronglyNormalizing
#print axioms RawTerm.idStrictRefl_isStronglyNormalizing
#print axioms RawTerm.interval0_isStronglyNormalizing
#print axioms RawTerm.interval1_isStronglyNormalizing
#print axioms RawTerm.intervalOpp_isStronglyNormalizing
#print axioms RawTerm.intervalMeet_isStronglyNormalizing
#print axioms RawTerm.intervalJoin_isStronglyNormalizing
#print axioms RawTerm.pathLam_isStronglyNormalizing
#print axioms Term.pathLam_isStronglyNormalizing
#print axioms RawTerm.equivIntro_isStronglyNormalizing
#print axioms Term.equivIntroHet_isStronglyNormalizing
#print axioms RawTerm.equivApply_isStronglyNormalizing
#print axioms Term.equivApply_isStronglyNormalizing
#print axioms RawTerm.uaToEquiv_isStronglyNormalizing
#print axioms RawTerm.oeqFunext_isStronglyNormalizing
#print axioms RawTerm.boolElim_isStronglyNormalizing
#print axioms RawTerm.recordIntro_isStronglyNormalizing
#print axioms Term.recordIntro_isStronglyNormalizing
#print axioms RawTerm.refineIntro_isStronglyNormalizing
#print axioms Term.refineIntro_isStronglyNormalizing
#print axioms RawTerm.codataUnfold_isStronglyNormalizing
#print axioms Term.codataUnfold_isStronglyNormalizing
#print axioms RawTerm.pathCompose_isStronglyNormalizing
#print axioms RawTerm.oeqTrans_isStronglyNormalizing
#print axioms RawTerm.equivCompose_isStronglyNormalizing
#print axioms RawTerm.sessionRecv_isStronglyNormalizing
#print axioms RawTerm.sessionSend_isStronglyNormalizing
#print axioms RawTerm.effectPerform_isStronglyNormalizing
#print axioms RawTerm.glueIntro_isStronglyNormalizing
#print axioms Term.glueIntro_isStronglyNormalizing
#print axioms RawTerm.glueElim_glueIntro_isStronglyNormalizing
#print axioms Term.glueElim_glueIntro_isStronglyNormalizing
#print axioms Reducible.fundamental_intervalOpp
#print axioms Reducible.fundamental_intervalMeet
#print axioms Reducible.fundamental_intervalJoin
#print axioms Reducible.fundamental_sessionRecv
#print axioms Reducible.fundamental_sessionSend
#print axioms Reducible.fundamental_effectPerform

end LeanFX2.Smoke

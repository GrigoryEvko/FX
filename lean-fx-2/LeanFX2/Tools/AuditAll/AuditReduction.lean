import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
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

/-! ## AuditReduction — 99 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Step.castSourceRaw
#assert_no_axioms LeanFX2.Step.castTargetRaw
#assert_no_axioms LeanFX2.Step.par.castSourceRaw
#assert_no_axioms LeanFX2.Step.par.castTargetRaw
#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.par.glueElim_inv
#assert_no_axioms LeanFX2.RawStep.par.pathLam_inv
#assert_no_axioms LeanFX2.RawStep.par.betaPathApp
#assert_no_axioms LeanFX2.RawStep.par.betaPathAppDeep
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfold
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfoldDeep
#assert_no_axioms LeanFX2.Step.par.pathLam
#assert_no_axioms LeanFX2.Step.par.pathLamCong
#assert_no_axioms LeanFX2.Step.par.pathApp
#assert_no_axioms LeanFX2.Step.par.pathAppCong
#assert_no_axioms LeanFX2.Step.betaModElimIntro
#assert_no_axioms LeanFX2.Step.par.betaModElimIntro
#assert_no_axioms LeanFX2.Step.par.betaModElimIntroDeep
#assert_no_axioms LeanFX2.Step.toConvCumul
#assert_no_axioms LeanFX2.RawStep.par.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.RawStep.par.iotaIdStrictRecReflDeep
#assert_no_axioms LeanFX2.Step.intervalOppInner
#assert_no_axioms LeanFX2.Step.intervalMeetLeft
#assert_no_axioms LeanFX2.Step.intervalMeetRight
#assert_no_axioms LeanFX2.Step.intervalJoinLeft
#assert_no_axioms LeanFX2.Step.intervalJoinRight
#assert_no_axioms LeanFX2.Step.par.intervalOppCong
#assert_no_axioms LeanFX2.Step.par.intervalMeetCong
#assert_no_axioms LeanFX2.Step.par.intervalJoinCong
#assert_no_axioms LeanFX2.Step.par.betaPathApp
#assert_no_axioms LeanFX2.Step.par.betaPathAppDeep
#assert_no_axioms LeanFX2.Step.par.toRawBridge
#assert_no_axioms LeanFX2.Step.par.rename_toRawBridge
#assert_no_axioms LeanFX2.Step.par.subst_toRawBridge
#assert_no_axioms LeanFX2.RawStep.par.rename_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible_same
#assert_no_axioms LeanFX2.Step.par.glueIntro
#assert_no_axioms LeanFX2.Step.par.glueIntroCong
#assert_no_axioms LeanFX2.Step.par.glueElim
#assert_no_axioms LeanFX2.Step.par.glueElimCong
#assert_no_axioms LeanFX2.Step.par.transpCong
#assert_no_axioms LeanFX2.Step.par.hcompCong
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.Step.par.transp
#assert_no_axioms LeanFX2.Step.par.hcomp
#assert_no_axioms LeanFX2.Step.oeqJBase
#assert_no_axioms LeanFX2.Step.oeqJWitness
#assert_no_axioms LeanFX2.Step.oeqFunextPointwise
#assert_no_axioms LeanFX2.Step.par.oeqReflCong
#assert_no_axioms LeanFX2.Step.par.oeqJCong
#assert_no_axioms LeanFX2.Step.par.oeqFunextCong
#assert_no_axioms LeanFX2.Step.recordIntroField
#assert_no_axioms LeanFX2.Step.recordProjRecord
#assert_no_axioms LeanFX2.Step.betaRecordProjIntro
#assert_no_axioms LeanFX2.Step.par.recordIntroCong
#assert_no_axioms LeanFX2.Step.par.recordProjCong
#assert_no_axioms LeanFX2.Step.par.betaRecordProjIntro
#assert_no_axioms LeanFX2.Step.par.betaRecordProjIntroDeep
#assert_no_axioms LeanFX2.Step.idStrictRecBase
#assert_no_axioms LeanFX2.Step.idStrictRecWitness
#assert_no_axioms LeanFX2.Step.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.Step.par.idStrictReflCong
#assert_no_axioms LeanFX2.Step.par.idStrictRecCong
#assert_no_axioms LeanFX2.Step.par.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.Step.par.iotaIdStrictRecReflDeep
#assert_no_axioms LeanFX2.Step.equivAppEquiv
#assert_no_axioms LeanFX2.Step.equivAppArgument
#assert_no_axioms LeanFX2.Step.par.equivAppCong
#assert_no_axioms LeanFX2.Step.refineIntroValue
#assert_no_axioms LeanFX2.Step.refineIntroProof
#assert_no_axioms LeanFX2.Step.refineElimValue
#assert_no_axioms LeanFX2.Step.betaRefineElimIntro
#assert_no_axioms LeanFX2.Step.par.refineIntroCong
#assert_no_axioms LeanFX2.Step.par.refineElimCong
#assert_no_axioms LeanFX2.Step.par.betaRefineElimIntro
#assert_no_axioms LeanFX2.Step.par.betaRefineElimIntroDeep
#assert_no_axioms LeanFX2.Step.codataUnfoldState
#assert_no_axioms LeanFX2.Step.codataUnfoldTransition
#assert_no_axioms LeanFX2.Step.codataDestValue
#assert_no_axioms LeanFX2.Step.betaCodataDestUnfold
#assert_no_axioms LeanFX2.Step.par.codataUnfoldCong
#assert_no_axioms LeanFX2.Step.par.betaCodataDestUnfold
#assert_no_axioms LeanFX2.Step.par.betaCodataDestUnfoldDeep
#assert_no_axioms LeanFX2.Step.par.codataDestCong
#assert_no_axioms LeanFX2.Step.sessionSendChannel
#assert_no_axioms LeanFX2.Step.sessionSendPayload
#assert_no_axioms LeanFX2.Step.sessionRecvChannel
#assert_no_axioms LeanFX2.Step.effectPerformOperation
#assert_no_axioms LeanFX2.Step.effectPerformArguments
#assert_no_axioms LeanFX2.Step.par.sessionSendCong
#assert_no_axioms LeanFX2.Step.par.sessionRecvCong
#assert_no_axioms LeanFX2.Step.par.effectPerformCong

-- D2.10 typed compositional compat — exemplar `intervalOppCong`.
#assert_no_axioms LeanFX2.Step.par.intervalOppCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.intervalOppCong.subst_compatible

-- D2.10 typed compositional compat — BATCH 12: 12 cong rules
-- following the `intervalOppCong` exemplar.  Seven unary cong rules
-- (one inner Step.par premise; `oeqReflCong` takes a RawStep.par
-- since its constructor's inner is a raw witness, not a typed term)
-- plus five binary cong rules (two inner Step.par premises).
#assert_no_axioms LeanFX2.Step.par.oeqReflCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.oeqReflCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.glueElimCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.glueElimCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.refineElimCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.refineElimCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.codataDestCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.codataDestCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.sessionRecvCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.sessionRecvCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.cumulUpInnerCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.cumulUpInnerCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.effectPerformCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.effectPerformCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.intervalMeetCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.intervalMeetCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.intervalJoinCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.intervalJoinCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.pathAppCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.pathAppCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.equivAppCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.equivAppCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.sessionSendCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.sessionSendCong.subst_compatible

-- D2.10 typed compositional compat — incremental rule:
-- `idStrictReflCong` (raw-witness inner premise, mode-strict gated).
-- Mirrors `oeqReflCong` with `modeIsStrict` threaded through.
#assert_no_axioms LeanFX2.Step.par.idStrictReflCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.idStrictReflCong.subst_compatible

-- D2.10 typed compositional compat — incremental rule:
-- `recordProjCong` (unary, single-field record projection).
#assert_no_axioms LeanFX2.Step.par.recordProjCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.recordProjCong.subst_compatible

-- D2.10 typed compositional compat — incremental rule:
-- `recordIntroCong` (unary, single-field record introduction).
#assert_no_axioms LeanFX2.Step.par.recordIntroCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.recordIntroCong.subst_compatible

-- D2.10 typed compositional compat — BATCH 7: 7 more cong rules
-- following the compositional exemplar.  All zero-axiom direct
-- applications of the corresponding `Step.par.*Cong` constructor
-- to renamed/substituted inner steps.
#assert_no_axioms LeanFX2.Step.par.refineIntroCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.refineIntroCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.codataUnfoldCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.codataUnfoldCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.hcompCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.hcompCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.glueIntroCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.glueIntroCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.oeqJCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.oeqJCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.idStrictRecCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.idStrictRecCong.subst_compatible

-- D2.10 typed compositional compat — BATCH 3: transpCong (binary,
-- mode-univalent, multi-arg cubical transport), equivIntroCong, and
-- equivIntroHetCong (alias-pair producing Term.equivIntroHet).
#assert_no_axioms LeanFX2.Step.par.transpCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.transpCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.equivIntroCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.equivIntroCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.equivIntroHetCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.equivIntroHetCong.subst_compatible

-- D2.10 typed compositional compat — uaIntroHetCong (unary, structured
-- raw index `RawTerm.equivIntro forwardRaw backwardRaw` renames/substs
-- structurally through the corresponding RawSubst equations).
#assert_no_axioms LeanFX2.Step.par.uaIntroHetCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.uaIntroHetCong.subst_compatible

-- D2.10 typed compositional compat — oeqFunextCong (unary, computed
-- pointwise type `oeqFunextPointwiseType` requires explicit ▸ cast on
-- the inner Step.par premise via `oeqFunextPointwiseType_rename` /
-- `_subst` commute lemmas).
#assert_no_axioms LeanFX2.Step.par.oeqFunextCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.oeqFunextCong.subst_compatible

-- D2.10 typed compositional compat — pathLamCong (unary, binder rule;
-- body lives under `(context.cons Ty.interval)` at `carrierType.weaken`,
-- requires `Ty.weaken_rename_commute` / `Ty.weaken_subst_commute` ▸
-- cast surfaced in the inner Step.par premise).
#assert_no_axioms LeanFX2.Step.par.pathLamCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.pathLamCong.subst_compatible

-- D3.6-P5 typed compositional compat — uaToEquivCong (unary, single
-- typed subterm `proof` at `Ty.id (Ty.universe ...) leftTyRaw rightTyRaw`)
-- and equivApplyCong (binary, `equivTerm + argumentTerm` at non-binder
-- `Ty.equiv carrierA carrierB` / `carrierA`).  Closes the deferral
-- from D3.6-P3+P4 (`step.par compat coverage` budget 2 → 0); both
-- cong rules are non-binder so no `Ty.weaken_*_commute` cast needed.
#assert_no_axioms LeanFX2.Step.par.uaToEquivCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.uaToEquivCong.subst_compatible
#assert_no_axioms LeanFX2.Step.par.equivApplyCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.equivApplyCong.subst_compatible

end LeanFX2.Tools

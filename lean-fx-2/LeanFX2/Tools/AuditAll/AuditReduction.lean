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

/-! ## AuditReduction — 170 `#assert_no_axioms` checks. -/

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
-- D2.5.4 transpReflBeta cascade (closes #1555).  Cubical-β rule
-- "transp at constant path = identity" — the kernel-internal analog
-- of `transp refl A x ⟶ x` from observational type theory.  Phase G
-- activated this rule across raw + typed + cd cascade in commit
-- cd77f91; the headline rule and its cascade have lived under the
-- reviewer-facing log `Smoke/AuditPhase12A2D254.lean` only — this
-- block (D3.6-S2 verification, #1683) brings the cascade up to the
-- canonical strict-harness audit-gate standard alongside D3.6-S1
-- `uaBeta` above.  The deep raw-only ctor `transpReflBetaDeep` is
-- documented raw-only via `isDocumentedRawOnlyParity` (no typed
-- mirror — see Section C of `Tools/StrictHarness/Common.lean`).
#assert_no_axioms LeanFX2.RawStep.par.transpReflBeta
#assert_no_axioms LeanFX2.RawStep.par.transpReflBetaDeep
#assert_no_axioms LeanFX2.Step.transpReflBeta
#assert_no_axioms LeanFX2.Step.par.transpReflBeta
-- D2.5.2 hcompBeta cascade.  Cubical-β rule "hcomp at constant-path
-- sides = cap" — homogeneous composition with constant-path sides
-- reduces to the cap (the boundary box is trivially filled).
-- Phase A activated this rule across raw + cd cascade (RawPar /
-- RawParRename / RawParCompatible / RawParInversion / RawCdRename /
-- RawCdDominates / RawCdLemma).  Phase B (typed Step.hcompBeta,
-- Step.par.hcompBeta, ConvCumul.betaHcompPathCumul, bridge arms in
-- ParStepLift / ConvBridge / Bridge) extends the cascade to the
-- typed layer, mirroring the D2.5.4 transpReflBeta cascade.  The
-- deep raw-only ctor `hcompBetaDeep` is documented raw-only via
-- `isDocumentedRawOnlyParity` Section I (no typed mirror — same
-- precedent as `transpReflBetaDeep`).
#assert_no_axioms LeanFX2.RawStep.par.hcompBeta
#assert_no_axioms LeanFX2.RawStep.par.hcompBetaDeep
#assert_no_axioms LeanFX2.RawTerm.cdHcompCase
#assert_no_axioms LeanFX2.RawTerm.cdHcompCase_rename
-- D2.5.5 transpPi β-rule Phase F prep (cdTranspPiCase helper + rename
-- commute).  Standalone confluence-layer helper consumed by future
-- atomic Phase F+G+I cascade landing.  Disjoint-premise design with
-- `transpReflBeta` (the caller's outer `unweaken?` check enforces
-- ordering — see #1951 dispatch RFC).  Builds on the foundation
-- primitives `matchTranspPiBetaShape?` + `transpPiBetaContractum`
-- gated under `AuditFoundation.lean`.
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_rename
-- D2.5.5 transpPi β-rule Phase G prep: par-step cong over the
-- contractum's source argument.  Future cd_lemma transpPiBetaDeep
-- arm calls this to discharge `par (contractum cd-source) (contractum
-- IH-target)` from a par-step hypothesis on the source.  Proven via
-- the lam/transp/app cong rules with `RawStep.par.rename` lifting
-- the source-step under `weaken`.
#assert_no_axioms LeanFX2.RawTerm.transpPiBetaContractum_par_cong
-- D2.5.5 transpPi β-rule Phase G prep: bi-directional par-step cong
-- where BOTH the path-codomain code AND the developed source step
-- simultaneously.  Future cd_lemma transpCong arm calls this when
-- the recognizer fires on the cd-developed pathLam body AND the
-- source has a non-refl par step.  Extends `_par_cong` with a
-- `pathLamCong` arm and a `rename swap01` lift on the codomain step.
#assert_no_axioms LeanFX2.RawTerm.transpPiBetaContractum_par_bi_cong
-- D2.5.5 transpPi β-rule Phase G prep: recognizer survives par-step.
-- When `matchTranspPiBetaShape? pathBody = some` and `par pathBody
-- pathBody'`, the recognizer fires on `pathBody'` too with a
-- par-related codomain witness.  Chains piTyCode_inv + weaken_inv +
-- recognizer completeness.  Future cd_lemma transpCong arm uses
-- this to lift the recognizer hit from the source pathBody to the
-- cd-target pathBody before firing the transpPiBetaDeep rule.
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?_par_some
#assert_no_axioms LeanFX2.RawStep.par.hcomp_inv
#assert_no_axioms LeanFX2.Step.hcompBeta
#assert_no_axioms LeanFX2.Step.par.hcompBeta
#assert_no_axioms LeanFX2.ConvCumul.betaHcompPathCumul
-- D2.5.8 betaPathReflApp cascade (companion to D2.5.4, same shape).
-- "(λ i ⇒ value) @ i ⟶ value" for value independent of i — the
-- cubical path analog of `transpReflBeta`.  Shipped in commit b453df6
-- as `Step.betaPathReflApp` + raw mirror.  No deep variant required
-- because `betaPathApp` / `betaPathAppDeep` + cd's collapsing through
-- `RawTerm.weaken_subst_singleton` already covers cd-developed cases.
#assert_no_axioms LeanFX2.RawStep.par.betaPathReflApp
#assert_no_axioms LeanFX2.Step.betaPathReflApp
#assert_no_axioms LeanFX2.Step.par.betaPathReflApp
-- D3.6-S1 univalence-β raw rules (kernel-internal univalence-β —
-- raw-only confluence-closure mechanism, listed in
-- `isDocumentedRawOnlyParity` since `Term.uaToEquiv` produces
-- `Ty.equiv` not `Ty.path`, blocking a typed `Term.transp` mirror).
#assert_no_axioms LeanFX2.RawStep.par.uaBeta
#assert_no_axioms LeanFX2.RawStep.par.uaBetaDeep
#assert_no_axioms LeanFX2.RawStep.par.uaToEquiv_inv
-- D3.6-S3 compose-β raw rules (kernel-internal cubical compose-β —
-- raw-only confluence-closure mechanism mounted on the new
-- `RawTerm.pathCompose` ctor, listed in `isDocumentedRawOnlyParity`
-- since typed `Term.pathCompose` is the v1.1 D3.10 follow-up — once
-- it lands, the typed mirrors `Step.pathComposeCong` /
-- `Step.transpCompose` / `Step.par.transpCompose` will ship and these
-- arms will move out of the raw-only whitelist).  Activated through
-- `cdTranspCase`'s `pathCompose` arm in `Confluence/RawCd.lean`.
#assert_no_axioms LeanFX2.RawStep.par.pathComposeCong
#assert_no_axioms LeanFX2.RawStep.par.transpCompose
#assert_no_axioms LeanFX2.RawStep.par.transpComposeDeep
#assert_no_axioms LeanFX2.RawStep.par.pathCompose_inv
-- D3.6-S4 univalence-refl-β raw rules (kernel-internal idToEquiv refl-β —
-- raw-only confluence-closure mechanism mounted on the new
-- `RawTerm.idToEquiv` ctor, listed in `isDocumentedRawOnlyParity`
-- since typed `Term.idToEquiv` is the v1.1 follow-up — once it lands,
-- the typed mirrors `Step.idToEquivCong` / `Step.idToEquivRefl` /
-- `Step.par.idToEquivRefl` will ship and these arms will move out of
-- the raw-only whitelist).  Activated through `cdIdToEquivCase`'s
-- `refl` arm in `Confluence/RawCd.lean`.
#assert_no_axioms LeanFX2.RawStep.par.idToEquivCong
#assert_no_axioms LeanFX2.RawStep.par.idToEquivRefl
#assert_no_axioms LeanFX2.RawStep.par.idToEquivReflDeep
#assert_no_axioms LeanFX2.RawStep.par.idToEquiv_inv
-- D3.6-S5 univalence-compose-β raw rules (kernel-internal idToEquiv
-- compose-β — raw-only confluence-closure mechanism mounted on the
-- two new ctors `RawTerm.oeqTrans` (binary, observational-equality
-- transitivity) and `RawTerm.equivCompose` (binary, equivalence
-- composition).  Listed in `isDocumentedRawOnlyParity` Section G
-- since typed mirrors require typed Term.{idToEquiv,oeqTrans,
-- equivCompose} ctors which are v1.1 follow-ups.  Activated through
-- `cdIdToEquivCase`'s `oeqTrans` arm in `Confluence/RawCd.lean`. -/
#assert_no_axioms LeanFX2.RawStep.par.oeqTransCong
#assert_no_axioms LeanFX2.RawStep.par.equivComposeCong
#assert_no_axioms LeanFX2.RawStep.par.idToEquivCompose
#assert_no_axioms LeanFX2.RawStep.par.idToEquivComposeDeep
#assert_no_axioms LeanFX2.RawStep.par.oeqTrans_inv
#assert_no_axioms LeanFX2.RawStep.par.equivCompose_inv
-- D3.6-S6 univalence-refl round-trip-β raw rules (kernel-internal
-- `equivApply (uaToEquiv (oeqRefl _)) source ⟶ source` — raw-only
-- confluence-closure mechanism mounted on existing `RawTerm.equivApply`
-- + `RawTerm.uaToEquiv` + `RawTerm.oeqRefl` ctors.  Listed in
-- `isDocumentedRawOnlyParity` Section H since typed `Term.equivApply`
-- cannot have an equiv-raw of `RawTerm.uaToEquiv (RawTerm.oeqRefl _)`
-- (typed `Term.uaToEquiv` produces `Ty.id`-typed proofs while typed
-- `Term.oeqRefl` produces `Ty.oeqType`-typed witnesses — different
-- typed-Ty heads, no typed bridge until v1.1's D3.10 unifies them).
-- Activated through `cdEquivApplyCase`'s `uaToEquiv` arm (+ the inner
-- `cdUaToEquivApplyCase`'s `oeqRefl` headline arm) in
-- `Confluence/RawCd.lean`.
#assert_no_axioms LeanFX2.RawStep.par.uaReflEquivApply
#assert_no_axioms LeanFX2.RawStep.par.uaReflEquivApplyDeep
#assert_no_axioms LeanFX2.RawStep.par.oeqRefl_inv
#assert_no_axioms LeanFX2.RawTerm.cdEquivApplyCase
#assert_no_axioms LeanFX2.RawTerm.cdUaToEquivApplyCase
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

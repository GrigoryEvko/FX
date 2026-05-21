import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2.Bridge
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Confluence.PreEtaStarInversion
import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Confluence.ConvBridge
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility
import LeanFX2.Reduction.Compat.Cubical
import LeanFX2.Reduction.Compat.HoTT.IdentityFamily
import LeanFX2.Reduction.Compat.HoTT.EquivalenceFamily
import LeanFX2.Reduction.Compat.HoTT.FunextFamily
import LeanFX2.Reduction.Compat.HoTT.UnivalenceFamily
import LeanFX2.Reduction.Compat.Effects
import LeanFX2.Reduction.Compat.Misc
import LeanFX2.Reduction.Compat.TypeCodes
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.ParRed.CongAliases
import LeanFX2.Reduction.ParRed.PreEtaInversion
import LeanFX2.Reduction.Step.Casts
import LeanFX2.Reduction.ParRed.ParCasts
import LeanFX2.Reduction.RawParWeakenInv.Weaken
import LeanFX2.Reduction.TranspPiContractumPar

namespace LeanFX2.Tools

/-! ## AuditReduction — 498 `#assert_no_axioms` checks. -/

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
-- Step.par exact-name congruence aliases.  These do not add reduction
-- behavior; they expose legacy congruence constructors under the
-- `Step.par.<TermCtor>Cong` names used by the strict dashboard.
#assert_no_axioms LeanFX2.Step.par.appCong
#assert_no_axioms LeanFX2.Step.par.lamCong
#assert_no_axioms LeanFX2.Step.par.lamPiCong
#assert_no_axioms LeanFX2.Step.par.appPiCong
#assert_no_axioms LeanFX2.Step.par.pairCong
#assert_no_axioms LeanFX2.Step.par.fstCong
#assert_no_axioms LeanFX2.Step.par.sndCong
#assert_no_axioms LeanFX2.Step.par.boolElimCong
#assert_no_axioms LeanFX2.Step.par.natSuccCong
#assert_no_axioms LeanFX2.Step.par.natElimCong
#assert_no_axioms LeanFX2.Step.par.natRecCong
#assert_no_axioms LeanFX2.Step.par.listConsCong
#assert_no_axioms LeanFX2.Step.par.listElimCong
#assert_no_axioms LeanFX2.Step.par.optionSomeCong
#assert_no_axioms LeanFX2.Step.par.optionMatchCong
#assert_no_axioms LeanFX2.Step.par.eitherInlCong
#assert_no_axioms LeanFX2.Step.par.eitherInrCong
#assert_no_axioms LeanFX2.Step.par.eitherMatchCong
#assert_no_axioms LeanFX2.Step.par.idJCong
#assert_no_axioms LeanFX2.Step.par.modIntroCong
#assert_no_axioms LeanFX2.Step.par.modElimCong
#assert_no_axioms LeanFX2.Step.par.subsumeCong
#assert_no_axioms LeanFX2.Step.par.cumulUpCong
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
-- D2.5.5 transpPi β-rule Phase F prep: explicit unfolding equations
-- for cdTranspPiCase.  Future cd_lemma transpCong arm uses these
-- to rewrite the dispatcher to its target shape before firing the
-- new β rule.  The `_of_some` equation collapses to the contractum
-- when the recognizer fires; the `_of_none` equation falls through
-- to the transp cong rebuild.  Both are zero-axiom direct unfoldings.
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_eq_contractum_of_some
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_eq_transp_of_none
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
#assert_no_axioms LeanFX2.Step.par.renamed_source_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.Step.par.weakened_source_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.Step.par.subst_toRawBridge
#assert_no_axioms LeanFX2.Term.toRaw_subst0_rename_commute
#assert_no_axioms LeanFX2.Term.toRaw_subst0_weaken_commute
#assert_no_axioms LeanFX2.RawStep.par.rename_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible_same
#assert_no_axioms LeanFX2.Step.par.glueIntro
#assert_no_axioms LeanFX2.Step.par.glueIntroCong
#assert_no_axioms LeanFX2.Step.par.glueElim
#assert_no_axioms LeanFX2.Step.par.glueElimCong
#assert_no_axioms LeanFX2.Step.par.transpCong
#assert_no_axioms LeanFX2.Step.par.hcompCong
#assert_no_axioms LeanFX2.Step.par.hcompPathCong
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

-- Value-constructor reflexive cong wrappers (no inner Step-reducible
-- sub-terms; canonical mirror is `Step.par.refl`).  These close the
-- remaining 12 slots in the `Step.par` cong-coverage matrix.
#assert_no_axioms LeanFX2.Step.par.varCong
#assert_no_axioms LeanFX2.Step.par.unitCong
#assert_no_axioms LeanFX2.Step.par.boolTrueCong
#assert_no_axioms LeanFX2.Step.par.boolFalseCong
#assert_no_axioms LeanFX2.Step.par.natZeroCong
#assert_no_axioms LeanFX2.Step.par.listNilCong
#assert_no_axioms LeanFX2.Step.par.optionNoneCong
#assert_no_axioms LeanFX2.Step.par.interval0Cong
#assert_no_axioms LeanFX2.Step.par.interval1Cong
#assert_no_axioms LeanFX2.Step.par.universeCodeCong
#assert_no_axioms LeanFX2.Step.par.equivReflIdCong
#assert_no_axioms LeanFX2.Step.par.equivReflIdAtIdCong

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
#assert_no_axioms LeanFX2.Step.par.hcompPathCong.rename_compatible
#assert_no_axioms LeanFX2.Step.par.hcompPathCong.subst_compatible
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
#assert_no_axioms LeanFX2.Step.par.lam_targetRaw_inv_congr
#assert_no_axioms LeanFX2.Step.par.lamPi_targetRaw_inv_congr
#assert_no_axioms LeanFX2.Step.par.pathLam_targetRaw_inv_congr

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

/-! ### Raw-cascade ctor strict-gate coverage closure

Promotes 53 `RawStep.par.*` ctors from smoke-only `#print axioms`
coverage in `Smoke/AuditPhase12A2Day2.lean` to machine-enforced
per-decl `#assert_no_axioms`.  All entries already report "does not
depend on any axioms" under the smoke audit; this commit closes the
strict-gate coverage gap so a future regression that introduces an
axiom dependency fails the build rather than only the smoke log.

Same shape as the K12.26 Kripke promotion (commit `3032f5b`) and
the D3.6-P5 typed cong promotion above. -/

-- Cubical interval ops — symmetry inverse, join, meet, and the two
-- endpoint constants.  Cong arms preserve interval-level steps; the
-- `_inv` lemmas invert a par-step on the head ctor to recover its
-- argument's par-step (used by `cd_lemma` interval arms).
#assert_no_axioms LeanFX2.RawStep.par.intervalOppCong
#assert_no_axioms LeanFX2.RawStep.par.intervalOpp_inv
#assert_no_axioms LeanFX2.RawStep.par.intervalMeetCong
#assert_no_axioms LeanFX2.RawStep.par.intervalMeet_inv
#assert_no_axioms LeanFX2.RawStep.par.intervalJoinCong
#assert_no_axioms LeanFX2.RawStep.par.intervalJoin_inv
#assert_no_axioms LeanFX2.RawStep.par.interval0_inv
#assert_no_axioms LeanFX2.RawStep.par.interval1_inv

-- Cubical path / glue / transp / hcomp cong + inv.  `pathApp` /
-- `glueIntro` / `transp` carry inversion lemmas consumed by the
-- cd cascade; `hcompCong` / `glueElimCong` / `pathLamCong` ship the
-- cong premises only (their `_inv` counterparts already strict-gated
-- above as `pathLam_inv` / `glueElim_inv`).
#assert_no_axioms LeanFX2.RawStep.par.pathLamCong
#assert_no_axioms LeanFX2.RawStep.par.pathAppCong
#assert_no_axioms LeanFX2.RawStep.par.pathApp_inv
#assert_no_axioms LeanFX2.RawStep.par.glueIntroCong
#assert_no_axioms LeanFX2.RawStep.par.glueIntro_inv
#assert_no_axioms LeanFX2.RawStep.par.glueElimCong
#assert_no_axioms LeanFX2.RawStep.par.transpCong
#assert_no_axioms LeanFX2.RawStep.par.transp_inv
#assert_no_axioms LeanFX2.RawStep.par.hcompCong

-- HOTT observational equality + strict-id family — cong + inversion
-- for refl / J / funext / strictRec / strictRefl.  `oeqReflCong` has
-- no inversion (zero-arity ctor); the others carry both arms.
#assert_no_axioms LeanFX2.RawStep.par.oeqReflCong
#assert_no_axioms LeanFX2.RawStep.par.oeqJCong
#assert_no_axioms LeanFX2.RawStep.par.oeqJ_inv
#assert_no_axioms LeanFX2.RawStep.par.oeqFunextCong
#assert_no_axioms LeanFX2.RawStep.par.oeqFunext_inv
#assert_no_axioms LeanFX2.RawStep.par.idStrictReflCong
#assert_no_axioms LeanFX2.RawStep.par.idStrictRefl_inv
#assert_no_axioms LeanFX2.RawStep.par.idStrictRecCong
#assert_no_axioms LeanFX2.RawStep.par.idStrictRec_inv

-- Equivalence cong + inversion.  `equivIntro` / `equivApp` mirror
-- the Σ-type intro/elim shape (closed by `betaEquivAppIntro` β rule
-- already strict-gated under the typed mirror block above).
#assert_no_axioms LeanFX2.RawStep.par.equivIntroCong
#assert_no_axioms LeanFX2.RawStep.par.equivIntro_inv
#assert_no_axioms LeanFX2.RawStep.par.equivAppCong
#assert_no_axioms LeanFX2.RawStep.par.equivApp_inv

-- Record + refine: β rules (intro then project / intro then elim
-- reduce to the inner content), plus cong + inv per ctor.
#assert_no_axioms LeanFX2.RawStep.par.betaRecordProjIntro
#assert_no_axioms LeanFX2.RawStep.par.betaRecordProjIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.recordIntroCong
#assert_no_axioms LeanFX2.RawStep.par.recordIntro_inv
#assert_no_axioms LeanFX2.RawStep.par.recordProjCong
#assert_no_axioms LeanFX2.RawStep.par.recordProj_inv
#assert_no_axioms LeanFX2.RawStep.par.betaRefineElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaRefineElimIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.refineIntroCong
#assert_no_axioms LeanFX2.RawStep.par.refineIntro_inv
#assert_no_axioms LeanFX2.RawStep.par.refineElimCong
#assert_no_axioms LeanFX2.RawStep.par.refineElim_inv

-- Codata destruct / unfold cong + inversion (corecursive eliminator
-- + introducer for `Ty.codata` shape).
#assert_no_axioms LeanFX2.RawStep.par.codataDestCong
#assert_no_axioms LeanFX2.RawStep.par.codataDest_inv
#assert_no_axioms LeanFX2.RawStep.par.codataUnfoldCong
#assert_no_axioms LeanFX2.RawStep.par.codataUnfold_inv

-- Session-typed channel send / receive cong + inversion (linear
-- protocol-state advancement for `Ty.session` chains).
#assert_no_axioms LeanFX2.RawStep.par.sessionSendCong
#assert_no_axioms LeanFX2.RawStep.par.sessionSend_inv
#assert_no_axioms LeanFX2.RawStep.par.sessionRecvCong
#assert_no_axioms LeanFX2.RawStep.par.sessionRecv_inv

-- Algebraic-effect perform cong + inversion (`Ty.effect` operation
-- invocation), plus the modal-elim inversion arm (cong already
-- gated as part of the modal cascade above).
#assert_no_axioms LeanFX2.RawStep.par.effectPerformCong
#assert_no_axioms LeanFX2.RawStep.par.effectPerform_inv
#assert_no_axioms LeanFX2.RawStep.par.modElim_inv

/-! ### Phase 6B inversion-lemma coverage closure

Phase 6 of confluence ships inversion lemmas `RawStep.par.X_inv`
that take `RawStep.par (X args) target` and produce a structural
witness on `args` — the inverse pattern of the cong rules above.
These are load-bearing for `cd_lemma` / `diamond` proofs because
they let the proof "peel" a par-step on a head ctor down to its
arguments.

All 49 entries below already verify clean in
`Smoke/AuditPhase6BInversion.lean` (50 `#print axioms`); promoting
to per-decl `#assert_no_axioms` closes the strict-gate coverage
gap so a regression that introduces an axiom dependency into the
inversion infrastructure fails the build rather than only the
smoke log. -/

-- RawStep.par inversion: variable, closed leaves, and atomic
-- literals.  All zero-arity head ctors carry vacuous inversions
-- (the source has no inner par-steps to recover).
#assert_no_axioms LeanFX2.RawStep.par.var_inv
#assert_no_axioms LeanFX2.RawStep.par.unit_inv
#assert_no_axioms LeanFX2.RawStep.par.universeCode_inv
#assert_no_axioms LeanFX2.RawStep.par.boolFalse_inv
#assert_no_axioms LeanFX2.RawStep.par.boolTrue_inv
#assert_no_axioms LeanFX2.RawStep.par.natZero_inv
#assert_no_axioms LeanFX2.RawStep.par.listNil_inv
#assert_no_axioms LeanFX2.RawStep.par.optionNone_inv

-- RawStep.par inversion: builder ctors (successor + cons + some +
-- inl/inr), Π / Σ intro+elim (lam / app / pair / fst / snd), and
-- HoTT identity (refl / idJ + equivApply).
#assert_no_axioms LeanFX2.RawStep.par.natSucc_inv
#assert_no_axioms LeanFX2.RawStep.par.listCons_inv
#assert_no_axioms LeanFX2.RawStep.par.optionSome_inv
#assert_no_axioms LeanFX2.RawStep.par.eitherInl_inv
#assert_no_axioms LeanFX2.RawStep.par.eitherInr_inv
#assert_no_axioms LeanFX2.RawStep.par.lam_inv
#assert_no_axioms LeanFX2.RawStep.par.app_inv
#assert_no_axioms LeanFX2.RawStep.par.pair_inv
#assert_no_axioms LeanFX2.RawStep.par.fst_inv
#assert_no_axioms LeanFX2.RawStep.par.snd_inv
#assert_no_axioms LeanFX2.RawStep.par.refl_inv
#assert_no_axioms LeanFX2.RawStep.par.idJ_inv
#assert_no_axioms LeanFX2.RawStep.par.equivApply_inv

-- RawStep.par inversion: eliminator ctors (boolElim / natElim /
-- natRec / listElim / optionMatch / eitherMatch).
#assert_no_axioms LeanFX2.RawStep.par.boolElim_inv
#assert_no_axioms LeanFX2.RawStep.par.natElim_inv
#assert_no_axioms LeanFX2.RawStep.par.natRec_inv
#assert_no_axioms LeanFX2.RawStep.par.listElim_inv
#assert_no_axioms LeanFX2.RawStep.par.optionMatch_inv
#assert_no_axioms LeanFX2.RawStep.par.eitherMatch_inv

-- RawStep.par inversion: type-code ctors (10 internal Ty-formers
-- exposed as terms — arrow / idCode / equivCode / listCode /
-- optionCode / eitherCode / sumCode / productCode / piTyCode /
-- sigmaTyCode).
#assert_no_axioms LeanFX2.RawStep.par.arrowCode_inv
#assert_no_axioms LeanFX2.RawStep.par.idCode_inv
#assert_no_axioms LeanFX2.RawStep.par.equivCode_inv
#assert_no_axioms LeanFX2.RawStep.par.listCode_inv
#assert_no_axioms LeanFX2.RawStep.par.optionCode_inv
#assert_no_axioms LeanFX2.RawStep.par.eitherCode_inv
#assert_no_axioms LeanFX2.RawStep.par.sumCode_inv
#assert_no_axioms LeanFX2.RawStep.par.productCode_inv
#assert_no_axioms LeanFX2.RawStep.par.piTyCode_inv
#assert_no_axioms LeanFX2.RawStep.par.sigmaTyCode_inv

-- RawStep.par inversion: cumul + modal + weaken helper.
#assert_no_axioms LeanFX2.RawStep.par.cumulUpMarker_inv
#assert_no_axioms LeanFX2.RawStep.par.modIntro_inv
#assert_no_axioms LeanFX2.RawStep.par.subsume_inv
#assert_no_axioms LeanFX2.RawStep.par.weaken_inv

-- RawStep.parStar inversion: transitive-reflexive-closure
-- inversions for the closed leaves and var (no parStar step can
-- alter a closed atomic ctor's head; recovers `source = target`
-- for the trivial reflexive case).
#assert_no_axioms LeanFX2.RawStep.parStar.var_inv
#assert_no_axioms LeanFX2.RawStep.parStar.unit_inv
#assert_no_axioms LeanFX2.RawStep.parStar.universeCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.boolFalse_inv
#assert_no_axioms LeanFX2.RawStep.parStar.boolTrue_inv
#assert_no_axioms LeanFX2.RawStep.parStar.boolElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.natZero_inv
#assert_no_axioms LeanFX2.RawStep.parStar.interval0_inv
#assert_no_axioms LeanFX2.RawStep.parStar.interval1_inv
#assert_no_axioms LeanFX2.RawStep.parStar.natSucc_inv
#assert_no_axioms LeanFX2.RawStep.parStar.natElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.natRec_inv
#assert_no_axioms LeanFX2.RawStep.parStar.optionSome_inv
#assert_no_axioms LeanFX2.RawStep.parStar.optionMatch_inv
#assert_no_axioms LeanFX2.RawStep.parStar.eitherInl_inv
#assert_no_axioms LeanFX2.RawStep.parStar.eitherInr_inv
#assert_no_axioms LeanFX2.RawStep.parStar.eitherMatch_inv
#assert_no_axioms LeanFX2.RawStep.parStar.app_inv
#assert_no_axioms LeanFX2.RawStep.parStar.refl_inv
#assert_no_axioms LeanFX2.RawStep.parStar.idJ_inv
#assert_no_axioms LeanFX2.RawStep.parStar.pair_inv
#assert_no_axioms LeanFX2.RawStep.parStar.fst_inv
#assert_no_axioms LeanFX2.RawStep.parStar.snd_inv
#assert_no_axioms LeanFX2.RawStep.parStar.listCons_inv
#assert_no_axioms LeanFX2.RawStep.parStar.listElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.listCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.optionCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.arrowCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.piTyCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.sigmaTyCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.productCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.sumCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.eitherCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.equivCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.idCode_inv
#assert_no_axioms LeanFX2.RawStep.parStar.idToEquiv_inv
#assert_no_axioms LeanFX2.RawStep.parStar.equivApply_inv
#assert_no_axioms LeanFX2.RawStep.parStar.intervalOpp_inv
#assert_no_axioms LeanFX2.RawStep.parStar.intervalMeet_inv
#assert_no_axioms LeanFX2.RawStep.parStar.intervalJoin_inv
#assert_no_axioms LeanFX2.RawStep.parStar.uaToEquiv_inv
#assert_no_axioms LeanFX2.RawStep.parStar.pathCompose_inv
#assert_no_axioms LeanFX2.RawStep.parStar.pathApp_inv
#assert_no_axioms LeanFX2.RawStep.parStar.oeqTrans_inv
#assert_no_axioms LeanFX2.RawStep.parStar.equivCompose_inv
#assert_no_axioms LeanFX2.RawStep.parStar.glueIntro_inv
#assert_no_axioms LeanFX2.RawStep.parStar.glueElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.oeqRefl_inv
#assert_no_axioms LeanFX2.RawStep.parStar.oeqFunext_inv
#assert_no_axioms LeanFX2.RawStep.parStar.oeqJ_inv
#assert_no_axioms LeanFX2.RawStep.parStar.idStrictRefl_inv
#assert_no_axioms LeanFX2.RawStep.parStar.idStrictRec_inv
#assert_no_axioms LeanFX2.RawStep.parStar.equivIntro_inv
#assert_no_axioms LeanFX2.RawStep.parStar.equivApp_inv
#assert_no_axioms LeanFX2.RawStep.parStar.transpFill_inv
#assert_no_axioms LeanFX2.RawStep.parStar.transp_inv
#assert_no_axioms LeanFX2.RawStep.parStar.hcomp_inv
#assert_no_axioms LeanFX2.RawStep.parStar.modIntro_inv
#assert_no_axioms LeanFX2.RawStep.parStar.modElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.subsume_inv
#assert_no_axioms LeanFX2.RawStep.parStar.cumulUpMarker_inv
#assert_no_axioms LeanFX2.RawStep.parStar.refineIntro_inv
#assert_no_axioms LeanFX2.RawStep.parStar.refineElim_inv
#assert_no_axioms LeanFX2.RawStep.parStar.recordIntro_inv
#assert_no_axioms LeanFX2.RawStep.parStar.recordProj_inv
#assert_no_axioms LeanFX2.RawStep.parStar.codataUnfold_inv
#assert_no_axioms LeanFX2.RawStep.parStar.codataDest_inv
#assert_no_axioms LeanFX2.RawStep.parStar.sessionSend_inv
#assert_no_axioms LeanFX2.RawStep.parStar.sessionRecv_inv
#assert_no_axioms LeanFX2.RawStep.parStar.effectPerform_inv
#assert_no_axioms LeanFX2.RawStep.parStar.lam_inv
#assert_no_axioms LeanFX2.RawStep.parStar.pathLam_inv
#assert_no_axioms LeanFX2.RawStep.parStar.listNil_inv
#assert_no_axioms LeanFX2.RawStep.parStar.optionNone_inv

/-! ### Phase G rename-injectivity weaken-inversion infrastructure

29 per-ctor `RawTerm.rename_eq_<ctor>_imp` shape-inversion lemmas
plus the `RawStep.par.rename_inj_inv` headline.  Each shape lemma
proves: if `rho` is injective and `rename rho someTerm = <ctor> args`,
then `someTerm` has the corresponding constructor head with
rename-recovered arguments.  Propext-clean via toRaw-shape match
(per `feedback_lean_zero_axiom_match.md`).

Used pervasively by:
* `RawStep.par.weaken_inv` (already gated) — Phase G inversion
* `RawStep.par.rename_inj_inv` — headline rename-injection inversion
* `RawTerm.cd_rename` cubical arms (cdTranspCase_rename,
  cdTranspPiCase_rename, cdHcompCase_rename) — already gated in
  AuditConfluence (commit 46f83e7).

Atom-shape lemmas (closed/zero-arity ctors): 7 in AtomShape1, 5 in
AtomShape2.  Binder-shape lemmas (arity-bearing ctors with binders
or compound payloads): 12 in BinderShape.  Cubical/HoTT-specific
shapes: 5 in CubicalShape. -/

#assert_no_axioms LeanFX2.RawStep.par.rename_inj_inv
#assert_no_axioms LeanFX2.RawStep.par.target_in_rename_image
#assert_no_axioms LeanFX2.RawStep.par.target_in_rename_image_of_source_eq
#assert_no_axioms LeanFX2.RawStep.par.target_in_weaken_image
#assert_no_axioms LeanFX2.RawStep.par.target_in_weaken_image_of_source_eq
#assert_no_axioms LeanFX2.RawStep.parStar.rename_compatible
#assert_no_axioms LeanFX2.RawStep.parStar.target_in_rename_image
#assert_no_axioms LeanFX2.RawStep.parStar.target_in_rename_image_of_source_eq
#assert_no_axioms LeanFX2.RawStep.parStar.target_in_weaken_image
#assert_no_axioms LeanFX2.RawStep.parStar.target_in_weaken_image_of_source_eq
#assert_no_axioms LeanFX2.Step.par.sourceRaw_in_rename_image_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.Step.par.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.Step.parStar.rename_toRawBridge
#assert_no_axioms LeanFX2.Step.parStar.renamed_source_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.Step.parStar.weakened_source_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.Step.parStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.Step.parStar.lam_targetRaw_inv_congr
#assert_no_axioms LeanFX2.Step.parStar.lamPi_targetRaw_inv_congr
#assert_no_axioms LeanFX2.Step.parStar.pathLam_targetRaw_inv_congr
#assert_no_axioms LeanFX2.StepStar.rename_toRawBridge
#assert_no_axioms LeanFX2.StepStar.renamed_source_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.StepStar.weakened_source_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.StepStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
#assert_no_axioms LeanFX2.StepStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
#assert_no_axioms LeanFX2.StepStar.lam_targetRaw_inv_congr
#assert_no_axioms LeanFX2.StepStar.lamPi_targetRaw_inv_congr
#assert_no_axioms LeanFX2.StepStar.pathLam_targetRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.rename_toRawJoin
#assert_no_axioms LeanFX2.Conv.weaken_toRawJoin
#assert_no_axioms LeanFX2.Conv.lam_left_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.lamPi_left_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.pathLam_left_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.lam_right_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.lamPi_right_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.pathLam_right_commonRaw_inv_congr
#assert_no_axioms LeanFX2.Conv.renamed_left_commonRaw_in_rename_image
#assert_no_axioms LeanFX2.Conv.weakened_left_commonRaw_in_weaken_image
#assert_no_axioms LeanFX2.Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq
#assert_no_axioms LeanFX2.Conv.left_commonRaw_in_weaken_image_of_sourceRaw_eq
#assert_no_axioms LeanFX2.Conv.renamed_right_commonRaw_in_rename_image
#assert_no_axioms LeanFX2.Conv.weakened_right_commonRaw_in_weaken_image
#assert_no_axioms LeanFX2.Conv.right_commonRaw_in_rename_image_of_targetRaw_eq
#assert_no_axioms LeanFX2.Conv.right_commonRaw_in_weaken_image_of_targetRaw_eq

-- AtomShape1: 7 closed-leaf shape inversions
#assert_no_axioms LeanFX2.RawTerm.rename_eq_boolTrue_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_boolFalse_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_natZero_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_listNil_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_optionNone_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_interval0_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_interval1_imp

-- AtomShape2: 5 unary-payload shape inversions
#assert_no_axioms LeanFX2.RawTerm.rename_eq_natSucc_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_optionSome_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_eitherInl_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_eitherInr_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_refl_imp

-- BinderShape: 12 binder-bearing or compound-payload shape inversions
#assert_no_axioms LeanFX2.RawTerm.rename_eq_modIntro_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_idStrictRefl_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_recordIntro_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_pathLam_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_lam_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_pair_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_listCons_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_refineIntro_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_glueIntro_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_codataUnfold_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_transp_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_piTyCode_imp

-- CubicalShape: 5 cubical/HoTT-specific shape inversions
#assert_no_axioms LeanFX2.RawTerm.rename_eq_uaToEquiv_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_pathCompose_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_idToEquiv_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_oeqTrans_imp
#assert_no_axioms LeanFX2.RawTerm.rename_eq_equivCompose_imp

/-! ### Compatibility headline theorems (D2.5 cascade load-bearing)

`RawStep.par.rename` is the headline rename-compat: every parallel
step is preserved under arbitrary renaming.  `RawStep.par.subst_par`
and `RawStep.par.subst0_par` are the substitution analogs.  The
three supporting lemmas (`RawTerm.subst0_subst_commute`,
`RawTermSubst.par_lift`, `RawTerm.subst_par_pointwise`) are the
beta-substitution arithmetic that subst_par lifts.  Used pervasively
by the typed Term cascade and by every D2.5 cubical β rule's
compat arm. -/

#assert_no_axioms LeanFX2.RawStep.par.rename
#assert_no_axioms LeanFX2.RawStep.par.subst_par
#assert_no_axioms LeanFX2.RawStep.par.subst0_par
#assert_no_axioms LeanFX2.RawTerm.subst0_subst_commute
#assert_no_axioms LeanFX2.RawTermSubst.par_lift
#assert_no_axioms LeanFX2.RawTerm.subst_par_pointwise

end LeanFX2.Tools

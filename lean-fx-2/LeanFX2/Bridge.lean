import LeanFX2.Reduction.RawParCompatible.Substitution
import LeanFX2.Reduction.RawParWeakenInv.Weaken
import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Term.Bridge

/-! # Bridge — typed↔raw correspondence (Phase 5).

The architectural payoff of raw-aware Term: bridging a typed
parallel-reduction step to its raw-side counterpart is a one-line
case split per ctor.

## Headline theorem

```lean
theorem Step.par.toRawBridge
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par sourceRaw targetRaw
```

Each case is a single `exact RawStep.par.<ctor> <ihs>` — the raw
indices align by construction because `Term.toRaw t = raw` is rfl
in lean-fx-2.  No `Step.par.isBi` filter is required since
`Step.par` carries no η rules (η lives in opt-in
`Reduction/Eta.lean` per the architectural commitment).

## Why this works in lean-fx-2 but not in lean-fx

* lean-fx had `Term.toRaw : Term ctx ty → RawTerm scope` as a
  recursive function, so projecting through a β-redex required
  proving `Term.toRaw_subst0` as an HEq cascade.  The non-dep vs
  dep β-cases needed two separate flavours (`subst0_term` /
  `subst0`) because `Subst.singleton` substituted unit at the
  raw position — the `dropNewest` family.
* lean-fx-2 makes `RawTerm scope` a type-level index of `Term`,
  so `Term.subst0 bodyTerm argTerm` has its raw target literally
  pinned to `bodyRaw.subst0 argRaw`.  Both `Term.toRaw_subst0`
  and `Term.toRaw_rename` are therefore `rfl`.

The forward bridge collapses to a one-liner per ctor.

## Constructors covered

58 total: refl + 23 cong + 5 shallow β + 13 shallow ι + 5 deep β
+ 12 deep ι.  Modal cong cases (`modIntro`, `modElim`, `subsume`)
included for forward compatibility with Layer 6.

## Future work

* `Bridge.backward` — partial inversion from raw to typed
  (decidable on canonical forms, used by Algo).  Needs typing
  judgment infrastructure first.
* Source/target inversion lemmas — direct from typed Step.par
  ctors using HEq+toRaw refutation (commit later when consumed).
-/

namespace LeanFX2

/-- Forward bridge: every typed parallel-reduction step lifts to a
raw-side parallel-reduction step on the projected raw indices.
54 cases, one line each. -/
theorem Step.par.toRawBridge
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par sourceRaw targetRaw := by
  induction parallelStep with
  -- Reflexivity
  | refl someTerm => exact RawStep.par.refl _
  -- Cong: non-dep app + lam
  | app _ _ ihFunction ihArgument =>
      exact RawStep.par.app ihFunction ihArgument
  | lam _ ihBody => exact RawStep.par.lam ihBody
  -- Cong: dep Π app + lam (collapse to RawStep.par.app / .lam)
  | lamPi _ ihBody => exact RawStep.par.lam ihBody
  | appPi _ _ ihFunction ihArgument =>
      exact RawStep.par.app ihFunction ihArgument
  -- Cong: pair + projections
  | pair _ _ ihFirst ihSecond =>
      exact RawStep.par.pair ihFirst ihSecond
  | fst _ ihPair => exact RawStep.par.fst ihPair
  | snd _ ihPair => exact RawStep.par.snd ihPair
  -- Cong: bool eliminator
  | boolElim _ _ _ ihScrutinee ihThen ihElse =>
      exact RawStep.par.boolElim ihScrutinee ihThen ihElse
  -- Cong: nat
  | natSucc _ ihPredecessor => exact RawStep.par.natSucc ihPredecessor
  | natElim _ _ _ ihScrutinee ihZero ihSucc =>
      exact RawStep.par.natElim ihScrutinee ihZero ihSucc
  | natRec _ _ _ ihScrutinee ihZero ihSucc =>
      exact RawStep.par.natRec ihScrutinee ihZero ihSucc
  -- Cong: list
  | listCons _ _ ihHead ihTail =>
      exact RawStep.par.listCons ihHead ihTail
  | listElim _ _ _ ihScrutinee ihNil ihCons =>
      exact RawStep.par.listElim ihScrutinee ihNil ihCons
  -- Cong: option
  | optionSome _ ihValue => exact RawStep.par.optionSome ihValue
  | optionMatch _ _ _ ihScrutinee ihNone ihSome =>
      exact RawStep.par.optionMatch ihScrutinee ihNone ihSome
  -- Cong: either
  | eitherInl _ ihValue => exact RawStep.par.eitherInl ihValue
  | eitherInr _ ihValue => exact RawStep.par.eitherInr ihValue
  | eitherMatch _ _ _ ihScrutinee ihLeft ihRight =>
      exact RawStep.par.eitherMatch ihScrutinee ihLeft ihRight
  -- Cong: identity (Term.refl is frozen, so no reflCong; idJ has cong)
  | idJ _ _ ihBase ihWitness =>
      exact RawStep.par.idJ ihBase ihWitness
  | oeqReflCong witnessStep =>
      exact RawStep.par.oeqReflCong witnessStep
  | oeqJCong _ _ ihBase ihWitness =>
      exact RawStep.par.oeqJCong ihBase ihWitness
  | oeqFunextCong _ _ _ _ _ ihPointwise =>
      exact RawStep.par.oeqFunextCong ihPointwise
  | idStrictReflCong _ witnessStep =>
      exact RawStep.par.idStrictReflCong witnessStep
  | idStrictRecCong _ _ _ ihBase ihWitness =>
      exact RawStep.par.idStrictRecCong ihBase ihWitness
  -- Cong: modal
  | modIntro _ ihInner => exact RawStep.par.modIntro ihInner
  | modElim _ ihInner => exact RawStep.par.modElim ihInner
  | subsume _ ihInner => exact RawStep.par.subsume ihInner
  -- Cong: cubical path fragment
  | pathLam _ _ ihBody => exact RawStep.par.pathLamCong ihBody
  | pathApp _ _ _ ihPath ihInterval =>
      exact RawStep.par.pathAppCong ihPath ihInterval
  | glueIntro _ _ _ ihBase ihPartial =>
      exact RawStep.par.glueIntroCong ihBase ihPartial
  | glueElim _ _ ihGlued =>
      exact RawStep.par.glueElimCong ihGlued
  | transp _ _ _ _ _ _ _ _ _ ihPath ihSource =>
      exact RawStep.par.transpCong ihPath ihSource
  | transpReflBeta _ _ _ _ _ _ ihSource =>
      exact RawStep.par.transpReflBeta (RawStep.par.refl _) ihSource
  | hcompBeta _ _ _ ihCap =>
      exact RawStep.par.hcompBeta (RawStep.par.refl _) ihCap
  | hcomp _ _ _ ihSides ihCap =>
      exact RawStep.par.hcompCong ihSides ihCap
  | recordIntroCong _ ihFirst =>
      exact RawStep.par.recordIntroCong ihFirst
  | recordProjCong _ ihRecord =>
      exact RawStep.par.recordProjCong ihRecord
  | refineIntroCong _ _ ihValue ihProof =>
      exact RawStep.par.refineIntroCong ihValue ihProof
  | refineElimCong _ ihRefined =>
      exact RawStep.par.refineElimCong ihRefined
  | intervalOppCong _ ihInner =>
      exact RawStep.par.intervalOppCong ihInner
  | intervalMeetCong _ _ ihLeft ihRight =>
      exact RawStep.par.intervalMeetCong ihLeft ihRight
  | intervalJoinCong _ _ ihLeft ihRight =>
      exact RawStep.par.intervalJoinCong ihLeft ihRight
  | pathLamCong _ _ ihBody => exact RawStep.par.pathLamCong ihBody
  | pathAppCong _ _ _ ihPath ihInterval =>
      exact RawStep.par.pathAppCong ihPath ihInterval
  | glueIntroCong _ _ _ ihBase ihPartial =>
      exact RawStep.par.glueIntroCong ihBase ihPartial
  | glueElimCong _ _ ihGlued =>
      exact RawStep.par.glueElimCong ihGlued
  | transpCong _ _ _ _ _ _ _ _ _ ihPath ihSource =>
      exact RawStep.par.transpCong ihPath ihSource
  | hcompCong _ _ _ ihSides ihCap =>
      exact RawStep.par.hcompCong ihSides ihCap
  | hcompPathCong _ _ _ _ _ ihSides ihCap =>
      exact RawStep.par.hcompCong ihSides ihCap
  -- β shallow (5)
  | betaApp _ _ ihBody ihArgument =>
      exact RawStep.par.betaApp ihBody ihArgument
  | betaAppPi _ _ ihBody ihArgument =>
      exact RawStep.par.betaApp ihBody ihArgument
  | betaModElimIntro _ ihInner =>
      exact RawStep.par.betaModElimIntro ihInner
  | betaModElimIntroDeep _ ihInner =>
      exact RawStep.par.betaModElimIntroDeep ihInner
  | betaPathApp _ _ _ ihBody ihInterval =>
      exact RawStep.par.betaPathApp ihBody ihInterval
  | betaPathReflApp _ _ _ _ _ _ ihValue ihInterval =>
      -- Source raw: pathApp (pathLam valueRawSource.weaken) intervalRawSource.
      -- Target raw: valueRawTarget.
      -- ihValue : RawStep.par valueRawSource valueRawTarget.
      -- ihInterval : RawStep.par intervalRawSource intervalRawTarget.
      -- Direct lift to the new raw ctor.
      exact RawStep.par.betaPathReflApp ihValue ihInterval
  | betaGlueElimIntro _ _ _ ihBase ihPartial =>
      exact RawStep.par.betaGlueElimIntro ihBase ihPartial
  | betaRecordProjIntro _ ihFirst =>
      exact RawStep.par.betaRecordProjIntro ihFirst
  | betaRefineElimIntro _ _ ihValue ihProof =>
      exact RawStep.par.betaRefineElimIntro ihValue ihProof
  | codataUnfoldCong _ _ ihState ihTransition =>
      exact RawStep.par.codataUnfoldCong ihState ihTransition
  | betaCodataDestUnfold _ _ ihState ihTransition =>
      exact RawStep.par.betaCodataDestUnfold ihState ihTransition
  | betaCodataDestUnfoldDeep _ ihCodata =>
      exact RawStep.par.betaCodataDestUnfoldDeep ihCodata
  | codataDestCong _ ihCodata =>
      exact RawStep.par.codataDestCong ihCodata
  | sessionSendCong _ _ ihChannel ihPayload =>
      exact RawStep.par.sessionSendCong ihChannel ihPayload
  | sessionRecvCong _ ihChannel =>
      exact RawStep.par.sessionRecvCong ihChannel
  | effectPerformCong _ _ ihOperation ihArguments =>
      exact RawStep.par.effectPerformCong ihOperation ihArguments
  | betaFstPair secondValue _ ihFirst =>
      exact RawStep.par.betaFstPair _ ihFirst
  | betaSndPair firstValue _ ihSecond =>
      exact RawStep.par.betaSndPair _ ihSecond
  -- ι shallow (13)
  | iotaBoolElimTrue elseBranch _ ihThen =>
      exact RawStep.par.iotaBoolElimTrue _ ihThen
  | iotaBoolElimFalse thenBranch _ ihElse =>
      exact RawStep.par.iotaBoolElimFalse _ ihElse
  | iotaNatElimZero succBranch _ ihZero =>
      exact RawStep.par.iotaNatElimZero _ ihZero
  | iotaNatElimSucc zeroBranch _ _ ihPredecessor ihSucc =>
      exact RawStep.par.iotaNatElimSucc _ ihPredecessor ihSucc
  | iotaNatRecZero succBranch _ ihZero =>
      exact RawStep.par.iotaNatRecZero _ ihZero
  | iotaNatRecSucc _ _ _ ihPredecessor ihZero ihSucc =>
      exact RawStep.par.iotaNatRecSucc ihPredecessor ihZero ihSucc
  | iotaListElimNil consBranch _ ihNil =>
      exact RawStep.par.iotaListElimNil _ ihNil
  | iotaListElimCons nilBranch _ _ _ ihHead ihTail ihCons =>
      exact RawStep.par.iotaListElimCons _ ihHead ihTail ihCons
  | iotaOptionMatchNone someBranch _ ihNone =>
      exact RawStep.par.iotaOptionMatchNone _ ihNone
  | iotaOptionMatchSome noneBranch _ _ ihValue ihSome =>
      exact RawStep.par.iotaOptionMatchSome _ ihValue ihSome
  | iotaEitherMatchInl rightBranch _ _ ihValue ihLeft =>
      exact RawStep.par.iotaEitherMatchInl _ ihValue ihLeft
  | iotaEitherMatchInr leftBranch _ _ ihValue ihRight =>
      exact RawStep.par.iotaEitherMatchInr _ ihValue ihRight
  | iotaIdJRefl carrier endpoint _ ihBase =>
      exact RawStep.par.iotaIdJRefl _ ihBase
  | iotaIdStrictRecRefl _ carrier endpoint _ ihBase =>
      exact RawStep.par.iotaIdStrictRecRefl _ ihBase
  -- β deep (5)
  | betaAppDeep _ _ ihFunction ihArgument =>
      exact RawStep.par.betaAppDeep ihFunction ihArgument
  | betaAppPiDeep _ _ ihFunction ihArgument =>
      exact RawStep.par.betaAppDeep ihFunction ihArgument
  | betaPathAppDeep _ _ _ ihPath ihInterval =>
      exact RawStep.par.betaPathAppDeep ihPath ihInterval
  | betaGlueElimIntroDeep _ _ ihGlued =>
      exact RawStep.par.betaGlueElimIntroDeep ihGlued
  | betaRecordProjIntroDeep _ ihRecord =>
      exact RawStep.par.betaRecordProjIntroDeep ihRecord
  | betaRefineElimIntroDeep _ ihRefined =>
      exact RawStep.par.betaRefineElimIntroDeep ihRefined
  | betaFstPairDeep _ ihPair =>
      exact RawStep.par.betaFstPairDeep ihPair
  | betaSndPairDeep _ ihPair =>
      exact RawStep.par.betaSndPairDeep ihPair
  -- ι deep (12)
  | iotaBoolElimTrueDeep elseBranch _ _ ihScrutinee ihThen =>
      exact RawStep.par.iotaBoolElimTrueDeep _ ihScrutinee ihThen
  | iotaBoolElimFalseDeep thenBranch _ _ ihScrutinee ihElse =>
      exact RawStep.par.iotaBoolElimFalseDeep _ ihScrutinee ihElse
  | iotaNatElimZeroDeep succBranch _ _ ihScrutinee ihZero =>
      exact RawStep.par.iotaNatElimZeroDeep _ ihScrutinee ihZero
  | iotaNatElimSuccDeep zeroBranch _ _ ihScrutinee ihSucc =>
      exact RawStep.par.iotaNatElimSuccDeep _ ihScrutinee ihSucc
  | iotaNatRecZeroDeep succBranch _ _ ihScrutinee ihZero =>
      exact RawStep.par.iotaNatRecZeroDeep _ ihScrutinee ihZero
  | iotaNatRecSuccDeep _ _ _ ihScrutinee ihZero ihSucc =>
      exact RawStep.par.iotaNatRecSuccDeep ihScrutinee ihZero ihSucc
  | iotaListElimNilDeep consBranch _ _ ihScrutinee ihNil =>
      exact RawStep.par.iotaListElimNilDeep _ ihScrutinee ihNil
  | iotaListElimConsDeep nilBranch _ _ ihScrutinee ihCons =>
      exact RawStep.par.iotaListElimConsDeep _ ihScrutinee ihCons
  | iotaOptionMatchNoneDeep someBranch _ _ ihScrutinee ihNone =>
      exact RawStep.par.iotaOptionMatchNoneDeep _ ihScrutinee ihNone
  | iotaOptionMatchSomeDeep noneBranch _ _ ihScrutinee ihSome =>
      exact RawStep.par.iotaOptionMatchSomeDeep _ ihScrutinee ihSome
  | iotaEitherMatchInlDeep rightBranch _ _ ihScrutinee ihLeft =>
      exact RawStep.par.iotaEitherMatchInlDeep _ ihScrutinee ihLeft
  | iotaEitherMatchInrDeep leftBranch _ _ ihScrutinee ihRight =>
      exact RawStep.par.iotaEitherMatchInrDeep _ ihScrutinee ihRight
  | iotaIdJReflDeep _ _ ihWitness ihBase =>
      exact RawStep.par.iotaIdJReflDeep ihWitness ihBase
  | iotaIdStrictRecReflDeep _ _ _ ihWitness ihBase =>
      exact RawStep.par.iotaIdStrictRecReflDeep ihWitness ihBase
  -- cumulUpInnerCong — Phase CUMUL-2.6 Design D: source projects to
  -- `RawTerm.cumulUpMarker codeSourceRaw`, target to
  -- `RawTerm.cumulUpMarker codeTargetRaw`.  The inner-step IH is a
  -- `RawStep.par codeSourceRaw codeTargetRaw`; wrap via the new
  -- `RawStep.par.cumulUpMarkerCong` cong rule (Phase A5).
  | cumulUpInnerCong _ _ _ _ _ _ innerIH =>
      exact RawStep.par.cumulUpMarkerCong innerIH
  -- Univalence rfl-fragment: source `Term.equivReflIdAtId` and target
  -- `Term.equivReflId` BOTH project to the same raw form
  -- `RawTerm.equivIntro (lam (var 0)) (lam (var 0))`, so the bridge
  -- discharges with `RawStep.par.refl _`.  This is the architectural
  -- payoff of pre-aligning the source ctor's raw with the target's
  -- raw (Phase 12.A.B8.1 prep): no `RawStep.par.eqType` ctor needed,
  -- raw confluence inherits the rule for free.
  | eqType _ _ _ _ => exact RawStep.par.refl _
  -- Funext rfl-fragment: same trick — source `Term.funextReflAtId`
  -- and target `Term.funextRefl` BOTH project to
  -- `RawTerm.lam (RawTerm.refl applyRaw)`.  RawStep.par.refl _
  -- discharges (Phase 12.A.B8.2 prep).
  | eqArrow _ _ _ => exact RawStep.par.refl _
  -- Heterogeneous equivIntroHet cong: both subterms parallel-reduce.
  -- Source raw `RawTerm.equivIntro forwardRawSource backwardRawSource`,
  -- target raw `RawTerm.equivIntro forwardRawTarget backwardRawTarget`.
  -- The bridge collapses to `RawStep.par.equivIntroCong (forwardIH)
  -- (backwardIH)` — raw indices align by construction.  Phase 12.A.B8.5.
  | equivIntroHetCong _ _ ihForward ihBackward =>
      exact RawStep.par.equivIntroCong ihForward ihBackward
  | equivIntroCong _ _ ihForward ihBackward =>
      exact RawStep.par.equivIntroCong ihForward ihBackward
  | equivAppCong _ _ ihEquiv ihArgument =>
      exact RawStep.par.equivAppCong ihEquiv ihArgument
  -- Heterogeneous uaIntroHet cong (Phase 12.A.B8.5b): the source and
  -- target Terms BOTH project to `RawTerm.equivIntro forwardRaw...
  -- backwardRaw...` (same as their packaged equivWitness's raw — the
  -- architectural raw-alignment trick).  The IH gives a raw parallel
  -- step from `RawTerm.equivIntro forwardRawSource backwardRawSource`
  -- to `RawTerm.equivIntro forwardRawTarget backwardRawTarget`, which
  -- IS the bridge result we need.  No `RawStep.par.uaIntroCong` ctor
  -- exists (or is needed) — we reuse the equivWitness's raw-side step
  -- directly, mirroring the `eqType` / `cumulUpInnerCong` collapse.
  | uaIntroHetCong _ _ _ _ _ ihEquivWitness => exact ihEquivWitness
  -- Phase D3.6-P3: univalence-β extractor cong.  Source `Term.uaToEquiv
  -- ... proofSource` and target `Term.uaToEquiv ... proofTarget` BOTH
  -- project to `RawTerm.uaToEquiv proofRaw...`.  The IH gives a raw
  -- parallel step on the proof raws; wrap in `RawStep.par.uaToEquivCong`.
  | uaToEquivCong _ _ _ _ _ _ _ ihProof =>
      exact RawStep.par.uaToEquivCong ihProof
  -- Phase D3.6-P4: univalence-β application cong.  Source
  -- `Term.equivApply equivSource argumentSource` and target
  -- `Term.equivApply equivTarget argumentTarget` project to
  -- `RawTerm.equivApply equivRaw... argumentRaw...`.  The IHs give
  -- raw parallel steps on the equiv and arg raws; wrap in
  -- `RawStep.par.equivApplyCong`.
  | equivApplyCong _ _ ihEquiv ihArgument =>
      exact RawStep.par.equivApplyCong ihEquiv ihArgument
  -- Heterogeneous Univalence reduction (Phase 12.A.B8.6): both source
  -- `Term.uaIntroHet ... equivWitness` and target `equivWitness`
  -- project to the SAME raw form `RawTerm.equivIntro forwardRaw
  -- backwardRaw` (the architectural raw-alignment trick — `uaIntroHet`
  -- ctor's raw is by construction the same as its packaged
  -- equivWitness's raw).  The bridge therefore collapses to
  -- `RawStep.par.refl _` — no new `RawStep.par.eqTypeHet` ctor needed,
  -- the rule is purely a typed-level type change with raw preserved.
  -- Same architectural payoff as `cumulUpInnerCong` / `eqType` /
  -- `eqArrow`.
  | eqTypeHet _ _ _ _ _ => exact RawStep.par.refl _
  -- Heterogeneous funext reduction (Phase 12.A.B8.B): both source
  -- `Term.funextIntroHet ... applyARaw applyBRaw` and target
  -- `Term.funextRefl ... applyARaw` project to the SAME raw form
  -- `RawTerm.lam (RawTerm.refl applyARaw)` (the architectural raw-
  -- alignment trick — `funextIntroHet`'s raw uses `applyARaw` and
  -- coincides with `funextRefl`'s raw at the same payload).  The
  -- bridge therefore collapses to `RawStep.par.refl _` — no new
  -- `RawStep.par.eqArrowHet` ctor needed, the rule is purely a
  -- typed-level type change with raw preserved.  Same architectural
  -- payoff as `cumulUpInnerCong` / `eqType` / `eqArrow` / `eqTypeHet`.
  | eqArrowHet _ _ _ _ => exact RawStep.par.refl _
  -- New schematic-payload value cong rules + type-code cong rules
  -- (Phase juggernaut Day 2 close-out).  Each maps to its raw mirror
  -- via the matching RawStep.par.*Cong rule.
  | reflCong _ witnessStep =>
      exact RawStep.par.reflCong witnessStep
  | funextReflCong _ _ applyStep =>
      exact RawStep.par.funextReflCong applyStep
  | funextReflAtIdCong _ _ applyStep =>
      exact RawStep.par.funextReflAtIdCong applyStep
  | funextIntroHetCong _ _ applyAStep _ =>
      exact RawStep.par.funextIntroHetCong applyAStep
  | arrowCodeCong _ _ ihDomain ihCodomain =>
      exact RawStep.par.arrowCodeCong ihDomain ihCodomain
  | piTyCodeCong _ _ ihDomain ihCodomain =>
      exact RawStep.par.piTyCodeCong ihDomain ihCodomain
  | sigmaTyCodeCong _ _ ihFirst ihSecond =>
      exact RawStep.par.sigmaTyCodeCong ihFirst ihSecond
  | productCodeCong _ _ ihFirst ihSecond =>
      exact RawStep.par.productCodeCong ihFirst ihSecond
  | sumCodeCong _ _ ihLeft ihRight =>
      exact RawStep.par.sumCodeCong ihLeft ihRight
  | listCodeCong _ _ ihElement =>
      exact RawStep.par.listCodeCong ihElement
  | optionCodeCong _ _ ihElement =>
      exact RawStep.par.optionCodeCong ihElement
  | eitherCodeCong _ _ ihLeft ihRight =>
      exact RawStep.par.eitherCodeCong ihLeft ihRight
  | idCodeCong _ _ ihCarrier ihLeft ihRight =>
      exact RawStep.par.idCodeCong ihCarrier ihLeft ihRight
  | equivCodeCong _ _ ihCarrierA ihCarrierB =>
      exact RawStep.par.equivCodeCong ihCarrierA ihCarrierB

/-- Raw-image compatibility for typed parallel reduction after a typed
renaming.

This is deliberately weaker than a full typed
`Step.par (Term.rename ...) (Term.rename ...)` theorem: it only states the
projected raw terms are parallel-related.  That is the bridge-layer endpoint
needed by raw confluence while the dependent typed compatibility proof remains
in `Reduction/Compat.lean`'s phase plan. -/
theorem Step.par.rename_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par (Term.toRaw (Term.rename termRenaming sourceTerm))
                (Term.toRaw (Term.rename termRenaming targetTerm)) := by
  rw [Term.toRaw_rename termRenaming sourceTerm,
      Term.toRaw_rename termRenaming targetTerm]
  exact RawStep.par.rename rawRenaming
    (Step.par.toRawBridge parallelStep)

/-- Typed-entrypoint raw image preservation for a renamed source.

If a typed parallel step starts at `Term.rename termRenaming sourceTerm`
and the underlying raw renaming is injective, the target raw index is in
the same raw renaming image.  This is the raw/index half of roadmap T5;
it deliberately stops before reconstructing a typed target term in the
source context. -/
theorem Step.par.renamed_source_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (parallelStep : Step.par (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  RawStep.par.target_in_rename_image rawRenaming rawRenamingInjective
    (Step.par.toRawBridge parallelStep)

/-- Canonical-weaken specialization of
`Step.par.renamed_source_targetRaw_in_rename_image`.

This is the typed entrypoint most weakening consumers need: when a
typed parallel step starts from `Term.weaken newType sourceTerm`, the
target raw index is still in the canonical weaken image.  It remains a
raw/index theorem, not the full typed T5 payload. -/
theorem Step.par.weakened_source_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (parallelStep : Step.par (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  RawStep.par.target_in_weaken_image
    (Step.par.toRawBridge parallelStep)

/-- Typed-entrypoint raw image preservation from a raw source equality.

This is the one-step roadmap shape for typed consumers that know only that the
source raw projection is a rename image, not that the typed source is literally
a `Term.rename`. -/
theorem Step.par.sourceRaw_in_rename_image_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (parallelStep : Step.par sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  RawStep.par.target_in_rename_image_of_source_eq rawRenaming
    rawRenamingInjective sourceEq (Step.par.toRawBridge parallelStep)

/-- Canonical-weaken specialization of
`Step.par.sourceRaw_in_rename_image_targetRaw_in_rename_image`. -/
theorem Step.par.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (parallelStep : Step.par sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  RawStep.par.target_in_weaken_image_of_source_eq sourceEq
    (Step.par.toRawBridge parallelStep)

/-! ## Direct raw-step packaging for rename-image consumers -/

/-- Direct raw-step packaging of
`Step.par.renamed_source_targetRaw_in_rename_image`.

If a typed parallel step starts at a renamed typed term, its raw projection can
be targeted directly at a raw term in the same renaming image. -/
theorem Step.par.renamed_source_toRawBridge_target_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (parallelStep : Step.par (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.par
        (Term.toRaw (Term.rename termRenaming sourceTerm))
        (targetInnerRaw.rename rawRenaming) := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.par.renamed_source_targetRaw_in_rename_image
      termRenaming rawRenamingInjective parallelStep
  cases targetEq
  exact ⟨targetInnerRaw, Step.par.toRawBridge parallelStep⟩

/-- Canonical-weaken specialization of
`Step.par.renamed_source_toRawBridge_target_in_rename_image`. -/
theorem Step.par.weakened_source_toRawBridge_target_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (parallelStep : Step.par (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.par
        (Term.toRaw (Term.weaken newType sourceTerm))
        targetInnerRaw.weaken := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.par.weakened_source_targetRaw_in_weaken_image newType parallelStep
  cases targetEq
  exact ⟨targetInnerRaw, Step.par.toRawBridge parallelStep⟩

/-- Direct raw-step packaging of
`Step.par.sourceRaw_in_rename_image_targetRaw_in_rename_image`. -/
theorem Step.par.toRawBridge_target_in_rename_image_of_sourceRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (parallelStep : Step.par sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.par sourceRaw (targetInnerRaw.rename rawRenaming) := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.par.sourceRaw_in_rename_image_targetRaw_in_rename_image
      rawRenamingInjective sourceEq parallelStep
  cases targetEq
  exact ⟨targetInnerRaw, Step.par.toRawBridge parallelStep⟩

/-- Canonical-weaken specialization of
`Step.par.toRawBridge_target_in_rename_image_of_sourceRaw_eq`. -/
theorem Step.par.toRawBridge_target_in_weaken_image_of_sourceRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (parallelStep : Step.par sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.par sourceRaw targetInnerRaw.weaken := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.par.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
      sourceEq parallelStep
  cases targetEq
  exact ⟨targetInnerRaw, Step.par.toRawBridge parallelStep⟩

/-- Raw-image compatibility for typed parallel reduction after a typed
substitution.

Like `Step.par.rename_toRawBridge`, this is a raw projection theorem, not the
still-pending full typed substitution compatibility theorem for `Step.par`. -/
theorem Step.par.subst_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    RawStep.par (Term.toRaw (Term.subst termSubst sourceTerm))
                (Term.toRaw (Term.subst termSubst targetTerm)) := by
  rw [Term.toRaw_subst termSubst sourceTerm,
      Term.toRaw_subst termSubst targetTerm]
  exact RawStep.par.subst_par
    (fun position => RawStep.par.refl (sigma.forRaw position))
    (Step.par.toRawBridge parallelStep)

/-- Raw projection of the Tier-3 `subst0`/rename commutation law.

The full typed theorem also has to relate the intrinsic `Term` values
across the casts generated by `Ty.subst0_rename_commute`.  This bridge
records the raw β endpoint now: after projection, renaming a singleton
substitution result is exactly singleton substitution after renaming the
body under the lifted renaming and renaming the argument. -/
theorem Term.toRaw_subst0_rename_commute
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {substituent : Ty level sourceScope}
    {argumentRaw : RawTerm sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyTerm : Term (sourceCtx.cons substituent) codomainType bodyRaw)
    (argumentTerm : Term sourceCtx substituent argumentRaw) :
    (Term.rename termRenaming (Term.subst0 bodyTerm argumentTerm)).toRaw =
      (Term.subst0
        (Term.rename (termRenaming.lift substituent) bodyTerm)
        (Term.rename termRenaming argumentTerm)).toRaw := by
  change (bodyRaw.subst0 argumentRaw).rename rawRenaming =
    (bodyRaw.rename rawRenaming.lift).subst0 (argumentRaw.rename rawRenaming)
  exact RawTerm.subst0_rename_commute bodyRaw argumentRaw rawRenaming

/-- Canonical-weaken specialization of `Term.toRaw_subst0_rename_commute`.

This is the raw β endpoint used by η/weakening consumers: weakening a
singleton-substitution result has the same raw projection as singleton
substitution after weakening the argument and weakening the body under the
lifted binder renaming. -/
theorem Term.toRaw_subst0_weaken_commute
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {substituent : Ty level scope}
    {argumentRaw : RawTerm scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm : Term (context.cons substituent) codomainType bodyRaw)
    (argumentTerm : Term context substituent argumentRaw) :
    (Term.weaken newType (Term.subst0 bodyTerm argumentTerm)).toRaw =
      (Term.subst0
        (Term.rename ((TermRenaming.weakenStep context newType).lift
          substituent) bodyTerm)
        (Term.weaken newType argumentTerm)).toRaw :=
  Term.toRaw_subst0_rename_commute
    (TermRenaming.weakenStep context newType) bodyTerm argumentTerm

end LeanFX2

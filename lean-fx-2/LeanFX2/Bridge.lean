import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawPar
import LeanFX2.Term.Bridge
import LeanFX2.Term.ToRaw

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
  | idStrictReflCong witnessStep =>
      exact RawStep.par.idStrictReflCong witnessStep
  | idStrictRecCong _ _ ihBase ihWitness =>
      exact RawStep.par.idStrictRecCong ihBase ihWitness
  -- Cong: modal
  | modIntro _ ihInner => exact RawStep.par.modIntro ihInner
  | modElim _ ihInner => exact RawStep.par.modElim ihInner
  | subsume _ ihInner => exact RawStep.par.subsume ihInner
  -- Cong: cubical path fragment
  | pathLam _ ihBody => exact RawStep.par.pathLamCong ihBody
  | pathApp _ _ ihPath ihInterval =>
      exact RawStep.par.pathAppCong ihPath ihInterval
  | glueIntro _ _ ihBase ihPartial =>
      exact RawStep.par.glueIntroCong ihBase ihPartial
  | glueElim _ ihGlued =>
      exact RawStep.par.glueElimCong ihGlued
  | transp _ _ _ _ _ _ _ _ ihPath ihSource =>
      exact RawStep.par.transpCong ihPath ihSource
  | hcomp _ _ ihSides ihCap =>
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
  | pathLamCong _ ihBody => exact RawStep.par.pathLamCong ihBody
  | pathAppCong _ _ ihPath ihInterval =>
      exact RawStep.par.pathAppCong ihPath ihInterval
  | glueIntroCong _ _ ihBase ihPartial =>
      exact RawStep.par.glueIntroCong ihBase ihPartial
  | glueElimCong _ ihGlued =>
      exact RawStep.par.glueElimCong ihGlued
  | transpCong _ _ _ _ _ _ _ _ ihPath ihSource =>
      exact RawStep.par.transpCong ihPath ihSource
  | hcompCong _ _ ihSides ihCap =>
      exact RawStep.par.hcompCong ihSides ihCap
  -- β shallow (5)
  | betaApp _ _ ihBody ihArgument =>
      exact RawStep.par.betaApp ihBody ihArgument
  | betaAppPi _ _ ihBody ihArgument =>
      exact RawStep.par.betaApp ihBody ihArgument
  | betaPathApp _ _ ihBody ihInterval =>
      exact RawStep.par.betaPathApp ihBody ihInterval
  | betaGlueElimIntro _ _ ihBase ihPartial =>
      exact RawStep.par.betaGlueElimIntro ihBase ihPartial
  | betaRecordProjIntro _ ihFirst =>
      exact RawStep.par.betaRecordProjIntro ihFirst
  | betaRefineElimIntro _ _ ihValue ihProof =>
      exact RawStep.par.betaRefineElimIntro ihValue ihProof
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
  -- β deep (5)
  | betaAppDeep _ _ ihFunction ihArgument =>
      exact RawStep.par.betaAppDeep ihFunction ihArgument
  | betaAppPiDeep _ _ ihFunction ihArgument =>
      exact RawStep.par.betaAppDeep ihFunction ihArgument
  | betaPathAppDeep _ _ ihPath ihInterval =>
      exact RawStep.par.betaPathAppDeep ihPath ihInterval
  | betaGlueElimIntroDeep _ ihGlued =>
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

end LeanFX2

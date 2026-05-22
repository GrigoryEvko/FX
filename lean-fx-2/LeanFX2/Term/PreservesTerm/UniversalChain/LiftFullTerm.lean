import LeanFX2.Term.PreservesTerm.UniversalChain.Core
import LeanFX2.Term.PreservesTerm.BetaCastWallDemolition
import LeanFX2.Term.PreservesTerm.SchematicValueCtors
import LeanFX2.Term.PreservesTerm.TypeCodeLifts
import LeanFX2.Term.PreservesTerm.TwoTyAtomsAndCong
import LeanFX2.Term.PreservesTerm.TwoTyEliminators
import LeanFX2.Term.PreservesTerm.HeterogeneousElim
import LeanFX2.Term.PreservesTerm.EliminatorFunextFamily
import LeanFX2.Term.SubjectReductionPar

/-! # LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullTerm

Driver theorem for the CONVTRANS-C universal chain lift.  The domain
predicate lives in `UniversalChain.Core`; this file contains only the
per-dispatcher proof routing through the existing `lift_full_*` leaves.
-/

namespace LeanFX2

/-- **CONVTRANS-C Phase A1 headline** — universal per-step dispatcher
restricted to dispatchable ctors.

For each ctor enumerated by `DispatchAtom`, calls the matching
`lift_full_<ctor>` to produce the typed existential witness.

Phase A1 follow-up commits extend `DispatchAtom` and add new dispatch
arms here as additional ctors become dispatchable. -/
theorem RawStep.par.lift_full_term
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (dispatch : DispatchAtom sourceTerm)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par sourceRaw targetRaw) :
    StepParExists sourceTerm targetRaw := by
  induction dispatch with
  | unit =>
    exact RawStep.par.lift_full_unit Term.unit rawStep
  | boolTrue =>
    exact RawStep.par.lift_full_boolTrue Term.boolTrue rawStep
  | boolFalse =>
    exact RawStep.par.lift_full_boolFalse Term.boolFalse rawStep
  | natZero =>
    exact RawStep.par.lift_full_natZero Term.natZero rawStep
  | interval0 =>
    exact RawStep.par.lift_full_interval0 Term.interval0 rawStep
  | interval1 =>
    exact RawStep.par.lift_full_interval1 Term.interval1 rawStep
  | listNil =>
    exact RawStep.par.lift_full_listNil Term.listNil rawStep
  | optionNone =>
    exact RawStep.par.lift_full_optionNone Term.optionNone rawStep
  | var position =>
    exact RawStep.par.lift_full_var (Term.var position) rawStep
  | universeCode innerLevel outerLevel cumulOk levelLe =>
    exact RawStep.par.lift_full_universeCode
            (Term.universeCode innerLevel outerLevel cumulOk levelLe)
            rawStep
  | arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_arrowCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_piTyCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_sigmaTyCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
    exact RawStep.par.lift_full_productCode outerLevel levelLe
            firstCodeRaw secondCodeRaw
            (Term.productCode outerLevel levelLe firstCodeRaw secondCodeRaw)
            rawStep
  | sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
    exact RawStep.par.lift_full_sumCode outerLevel levelLe
            leftCodeRaw rightCodeRaw
            (Term.sumCode outerLevel levelLe leftCodeRaw rightCodeRaw)
            rawStep
  | listCode outerLevel levelLe elementCodeRaw =>
    exact RawStep.par.lift_full_listCode outerLevel levelLe
            elementCodeRaw
            (Term.listCode outerLevel levelLe elementCodeRaw)
            rawStep
  | optionCode outerLevel levelLe elementCodeRaw =>
    exact RawStep.par.lift_full_optionCode outerLevel levelLe
            elementCodeRaw
            (Term.optionCode outerLevel levelLe elementCodeRaw)
            rawStep
  | eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
    exact RawStep.par.lift_full_eitherCode outerLevel levelLe
            leftCodeRaw rightCodeRaw
            (Term.eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw)
            rawStep
  | idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
    exact RawStep.par.lift_full_idCode outerLevel levelLe
            typeCodeRaw leftRaw rightRaw
            (Term.idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw)
            rawStep
  | equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
    exact RawStep.par.lift_full_equivCode outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw
            (Term.equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)
            rawStep
  | oeqRefl carrier rawWitness =>
    exact RawStep.par.lift_full_oeqRefl carrier rawWitness
            (Term.oeqRefl carrier rawWitness) rawStep
  | refl carrier rawWitness =>
    exact RawStep.par.lift_full_refl carrier rawWitness
            (Term.refl carrier rawWitness) rawStep
  | idStrictRefl modeIsStrict carrier rawWitness =>
    exact RawStep.par.lift_full_idStrictRefl modeIsStrict carrier rawWitness
            (Term.idStrictRefl modeIsStrict carrier rawWitness) rawStep
  | equivReflId carrier =>
    exact RawStep.par.lift_full_equivReflId carrier
            (Term.equivReflId carrier) rawStep
  | equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
    exact RawStep.par.lift_full_equivReflIdAtId innerLevel innerLevelLt
            carrier carrierRaw
            (Term.equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw)
            rawStep
  | intervalOpp innerValue _innerDispatch ihInner =>
    -- ihInner : ∀ {targetRaw}, RawStep.par innerValue.toRaw targetRaw →
    --            StepParExists innerValue targetRaw
    -- lift_full_intervalOpp wants a fixed-Ty callback
    --   ∀ {tgt}, RawStep.par innerRaw tgt → ∃ innerTarget : Term ctx Ty.interval tgt,
    --      Step.par innerValue innerTarget
    -- Bridge two-Ty → fixed-Ty via Step.par.preserves_isClosedTy IsClosedTy.interval.
    refine RawStep.par.lift_full_intervalOpp innerValue ?_ rawStep
    intro _ innerRawStep
    obtain ⟨innerTargetType, innerTarget, innerStep⟩ := ihInner innerRawStep
    have intervalEq : innerTargetType = Ty.interval :=
      Step.par.preserves_isClosedTy IsClosedTy.interval innerStep rfl
    subst intervalEq
    exact ⟨innerTarget, innerStep⟩
  | intervalJoin leftValue rightValue _ _ ihLeft ihRight =>
    refine RawStep.par.lift_full_intervalJoin leftValue rightValue ?_ ?_ rawStep
    · intro _ leftRawStep
      obtain ⟨leftTargetType, leftTarget, leftStep⟩ := ihLeft leftRawStep
      have intervalEq : leftTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval leftStep rfl
      subst intervalEq
      exact ⟨leftTarget, leftStep⟩
    · intro _ rightRawStep
      obtain ⟨rightTargetType, rightTarget, rightStep⟩ := ihRight rightRawStep
      have intervalEq : rightTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval rightStep rfl
      subst intervalEq
      exact ⟨rightTarget, rightStep⟩
  | intervalMeet leftValue rightValue _ _ ihLeft ihRight =>
    refine RawStep.par.lift_full_intervalMeet leftValue rightValue ?_ ?_ rawStep
    · intro _ leftRawStep
      obtain ⟨leftTargetType, leftTarget, leftStep⟩ := ihLeft leftRawStep
      have intervalEq : leftTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval leftStep rfl
      subst intervalEq
      exact ⟨leftTarget, leftStep⟩
    · intro _ rightRawStep
      obtain ⟨rightTargetType, rightTarget, rightStep⟩ := ihRight rightRawStep
      have intervalEq : rightTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval rightStep rfl
      subst intervalEq
      exact ⟨rightTarget, rightStep⟩
  | natSucc predecessor _predDispatch ihPred =>
    refine RawStep.par.lift_full_natSucc predecessor ?_ rawStep
    intro _ predRawStep
    obtain ⟨predTargetType, predTarget, predStep⟩ := ihPred predRawStep
    have natEq : predTargetType = Ty.nat :=
      Step.par.preserves_isClosedTy IsClosedTy.nat predStep rfl
    subst natEq
    exact ⟨predTarget, predStep⟩
  | listCons elementClosed headTerm tailTerm _ _ ihHead ihTail =>
    refine RawStep.par.lift_full_listCons headTerm tailTerm ?_ ?_ rawStep
    · intro _ headRawStep
      obtain ⟨headTargetType, headTarget, headStep⟩ := ihHead headRawStep
      have elemEq : headTargetType = _ :=
        Step.par.preserves_isClosedTy elementClosed headStep rfl
      subst elemEq
      exact ⟨headTarget, headStep⟩
    · intro _ tailRawStep
      obtain ⟨tailTargetType, tailTarget, tailStep⟩ := ihTail tailRawStep
      have listEq : tailTargetType = _ :=
        Step.par.preserves_isClosedTy (IsClosedTy.listType elementClosed)
                                      tailStep rfl
      subst listEq
      exact ⟨tailTarget, tailStep⟩
  | optionSome elementClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_optionSome valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have elemEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy elementClosed valueStep rfl
    subst elemEq
    exact ⟨valueTarget, valueStep⟩
  | eitherInl leftClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_eitherInl valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have leftEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy leftClosed valueStep rfl
    subst leftEq
    exact ⟨valueTarget, valueStep⟩
  | eitherInr rightClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_eitherInr valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have rightEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy rightClosed valueStep rfl
    subst rightEq
    exact ⟨valueTarget, valueStep⟩
  | natElim motiveClosed scrutinee zeroBranch succBranch _ _ _
            ihScrut ihZero ihSucc =>
    refine RawStep.par.lift_full_natElim scrutinee zeroBranch succBranch
                                          ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have natEq : scrutTargetType = Ty.nat :=
        Step.par.preserves_isClosedTy IsClosedTy.nat scrutStep rfl
      subst natEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ zeroRawStep
      obtain ⟨zeroTargetType, zeroTarget, zeroStep⟩ := ihZero zeroRawStep
      have motiveEq : zeroTargetType = _ :=
        Step.par.preserves_isClosedTy motiveClosed zeroStep rfl
      subst motiveEq
      exact ⟨zeroTarget, zeroStep⟩
    · intro _ succRawStep
      obtain ⟨succTargetType, succTarget, succStep⟩ := ihSucc succRawStep
      have arrowEq : succTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow IsClosedTy.nat motiveClosed) succStep rfl
      subst arrowEq
      exact ⟨succTarget, succStep⟩
  | natRec motiveClosed scrutinee zeroBranch succBranch _ _ _
           ihScrut ihZero ihSucc =>
    refine RawStep.par.lift_full_natRec scrutinee zeroBranch succBranch
                                         ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have natEq : scrutTargetType = Ty.nat :=
        Step.par.preserves_isClosedTy IsClosedTy.nat scrutStep rfl
      subst natEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ zeroRawStep
      obtain ⟨zeroTargetType, zeroTarget, zeroStep⟩ := ihZero zeroRawStep
      have motiveEq : zeroTargetType = _ :=
        Step.par.preserves_isClosedTy motiveClosed zeroStep rfl
      subst motiveEq
      exact ⟨zeroTarget, zeroStep⟩
    · intro _ succRawStep
      obtain ⟨succTargetType, succTarget, succStep⟩ := ihSucc succRawStep
      have nestedArrowEq : succTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow IsClosedTy.nat
            (IsClosedTy.arrow motiveClosed motiveClosed))
          succStep rfl
      subst nestedArrowEq
      exact ⟨succTarget, succStep⟩
  | listElim elementClosed motiveClosed scrutinee nilBranch consBranch
             _ _ _ ihScrut ihNil ihCons =>
    refine RawStep.par.lift_full_listElim scrutinee nilBranch consBranch
                                           ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have listEq : scrutTargetType = _ :=
        Step.par.preserves_isClosedTy (IsClosedTy.listType elementClosed)
                                       scrutStep rfl
      subst listEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ nilRawStep
      obtain ⟨nilTargetType, nilTarget, nilStep⟩ := ihNil nilRawStep
      have motiveEq : nilTargetType = _ :=
        Step.par.preserves_isClosedTy motiveClosed nilStep rfl
      subst motiveEq
      exact ⟨nilTarget, nilStep⟩
    · intro _ consRawStep
      obtain ⟨consTargetType, consTarget, consStep⟩ := ihCons consRawStep
      have nestedArrowEq : consTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow elementClosed
            (IsClosedTy.arrow (IsClosedTy.listType elementClosed) motiveClosed))
          consStep rfl
      subst nestedArrowEq
      exact ⟨consTarget, consStep⟩
  | optionMatch elementClosed motiveClosed scrutinee noneBranch someBranch
                _ _ _ ihScrut ihNone ihSome =>
    refine RawStep.par.lift_full_optionMatch scrutinee noneBranch someBranch
                                              ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have optionEq : scrutTargetType = _ :=
        Step.par.preserves_isClosedTy (IsClosedTy.optionType elementClosed)
                                       scrutStep rfl
      subst optionEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ noneRawStep
      obtain ⟨noneTargetType, noneTarget, noneStep⟩ := ihNone noneRawStep
      have motiveEq : noneTargetType = _ :=
        Step.par.preserves_isClosedTy motiveClosed noneStep rfl
      subst motiveEq
      exact ⟨noneTarget, noneStep⟩
    · intro _ someRawStep
      obtain ⟨someTargetType, someTarget, someStep⟩ := ihSome someRawStep
      have arrowEq : someTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow elementClosed motiveClosed) someStep rfl
      subst arrowEq
      exact ⟨someTarget, someStep⟩
  | eitherMatch leftClosed rightClosed motiveClosed scrutinee
                leftBranch rightBranch _ _ _ ihScrut ihLeft ihRight =>
    refine RawStep.par.lift_full_eitherMatch scrutinee leftBranch rightBranch
                                              ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have eitherEq : scrutTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.eitherType leftClosed rightClosed) scrutStep rfl
      subst eitherEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ leftRawStep
      obtain ⟨leftTargetType, leftTarget, leftStep⟩ := ihLeft leftRawStep
      have arrowEq : leftTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow leftClosed motiveClosed) leftStep rfl
      subst arrowEq
      exact ⟨leftTarget, leftStep⟩
    · intro _ rightRawStep
      obtain ⟨rightTargetType, rightTarget, rightStep⟩ := ihRight rightRawStep
      have arrowEq : rightTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow rightClosed motiveClosed) rightStep rfl
      subst arrowEq
      exact ⟨rightTarget, rightStep⟩
  | modIntro innerClosed innerTerm _ ihInner =>
    refine RawStep.par.lift_full_modIntro innerTerm ?_ rawStep
    intro _ innerRawStep
    obtain ⟨innerTargetType, innerTarget, innerStep⟩ := ihInner innerRawStep
    have innerEq : innerTargetType = _ :=
      Step.par.preserves_isClosedTy innerClosed innerStep rfl
    subst innerEq
    exact ⟨innerTarget, innerStep⟩
  | modElim innerClosed innerTerm _ ihInner =>
    refine RawStep.par.lift_full_modElim innerTerm ?_ rawStep
    intro _ innerRawStep
    obtain ⟨innerTargetType, innerTarget, innerStep⟩ := ihInner innerRawStep
    have innerEq : innerTargetType = _ :=
      Step.par.preserves_isClosedTy innerClosed innerStep rfl
    subst innerEq
    exact ⟨innerTarget, innerStep⟩
  | subsume innerClosed innerTerm _ ihInner =>
    refine RawStep.par.lift_full_subsume innerTerm ?_ rawStep
    intro _ innerRawStep
    obtain ⟨innerTargetType, innerTarget, innerStep⟩ := ihInner innerRawStep
    have innerEq : innerTargetType = _ :=
      Step.par.preserves_isClosedTy innerClosed innerStep rfl
    subst innerEq
    exact ⟨innerTarget, innerStep⟩
  | recordIntro fieldClosed firstField _ ihField =>
    refine RawStep.par.lift_full_recordIntro firstField ?_ rawStep
    intro _ fieldRawStep
    obtain ⟨fieldTargetType, fieldTarget, fieldStep⟩ := ihField fieldRawStep
    have fieldEq : fieldTargetType = _ :=
      Step.par.preserves_isClosedTy fieldClosed fieldStep rfl
    subst fieldEq
    exact ⟨fieldTarget, fieldStep⟩
  | recordProj fieldClosed recordValue _ ihRecord =>
    refine RawStep.par.lift_full_recordProj recordValue ?_ rawStep
    intro _ recordRawStep
    obtain ⟨recordTargetType, recordTarget, recordStep⟩ :=
      ihRecord recordRawStep
    have recordEq : recordTargetType = _ :=
      Step.par.preserves_isClosedTy (IsClosedTy.record fieldClosed)
                                     recordStep rfl
    subst recordEq
    exact ⟨recordTarget, recordStep⟩
  | codataDest stateClosed outputClosed codataValue _ ihCodata =>
    refine RawStep.par.lift_full_codataDest codataValue ?_ rawStep
    intro _ codataRawStep
    obtain ⟨codataTargetType, codataTarget, codataStep⟩ :=
      ihCodata codataRawStep
    have codataEq : codataTargetType = _ :=
      Step.par.preserves_isClosedTy
        (IsClosedTy.codata stateClosed outputClosed) codataStep rfl
    subst codataEq
    exact ⟨codataTarget, codataStep⟩
  | cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh
            typeCode _ ihCode =>
    refine RawStep.par.lift_full_cumulUp lowerLevel higherLevel cumulMonotone
                                          levelLeLow levelLeHigh typeCode ?_
                                          rawStep
    intro _ codeRawStep
    obtain ⟨codeTargetType, codeTarget, codeStep⟩ := ihCode codeRawStep
    have universeEq : codeTargetType = _ :=
      Step.par.preserves_isClosedTy (IsClosedTy.universe lowerLevel levelLeLow)
                                     codeStep rfl
    subst universeEq
    exact ⟨codeTarget, codeStep⟩
  | glueIntro modeIsUnivalent baseClosed boundaryWitness baseValue partialValue
              _ _ ihBase ihPartial =>
    refine RawStep.par.lift_full_glueIntro modeIsUnivalent _ boundaryWitness
                                            baseValue partialValue ?_ ?_ rawStep
    · intro _ baseRawStep
      obtain ⟨baseTargetType, baseTarget, baseStep⟩ := ihBase baseRawStep
      have baseEq : baseTargetType = _ :=
        Step.par.preserves_isClosedTy baseClosed baseStep rfl
      subst baseEq
      exact ⟨baseTarget, baseStep⟩
    · intro _ partialRawStep
      obtain ⟨partialTargetType, partialTarget, partialStep⟩ :=
        ihPartial partialRawStep
      have partialEq : partialTargetType = _ :=
        Step.par.preserves_isClosedTy baseClosed partialStep rfl
      subst partialEq
      exact ⟨partialTarget, partialStep⟩
  | codataUnfold stateClosed outputClosed initialState transition
                 _ _ ihState ihTransition =>
    refine RawStep.par.lift_full_codataUnfold initialState transition
                                               ?_ ?_ rawStep
    · intro _ stateRawStep
      obtain ⟨stateTargetType, stateTarget, stateStep⟩ := ihState stateRawStep
      have stateEq : stateTargetType = _ :=
        Step.par.preserves_isClosedTy stateClosed stateStep rfl
      subst stateEq
      exact ⟨stateTarget, stateStep⟩
    · intro _ transitionRawStep
      obtain ⟨transitionTargetType, transitionTarget, transitionStep⟩ :=
        ihTransition transitionRawStep
      have arrowEq : transitionTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow stateClosed outputClosed) transitionStep rfl
      subst arrowEq
      exact ⟨transitionTarget, transitionStep⟩
  | equivApp carrierAClosed carrierBClosed equivTerm argumentTerm
             _ _ ihEquiv ihArgument =>
    refine RawStep.par.lift_full_equivApp equivTerm argumentTerm ?_ ?_ rawStep
    · intro _ equivRawStep
      obtain ⟨equivTargetType, equivTarget, equivStep⟩ := ihEquiv equivRawStep
      have equivEq : equivTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.equiv carrierAClosed carrierBClosed) equivStep rfl
      subst equivEq
      exact ⟨equivTarget, equivStep⟩
    · intro _ argumentRawStep
      obtain ⟨argumentTargetType, argumentTarget, argumentStep⟩ :=
        ihArgument argumentRawStep
      have argumentEq : argumentTargetType = _ :=
        Step.par.preserves_isClosedTy carrierAClosed argumentStep rfl
      subst argumentEq
      exact ⟨argumentTarget, argumentStep⟩
  | refineIntro baseClosed predicate baseValue predicateProof
                _ _ ihValue ihProof =>
    refine RawStep.par.lift_full_refineIntro predicate baseValue
                                              predicateProof ?_ ?_ rawStep
    · intro _ valueRawStep
      obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
      have valueEq : valueTargetType = _ :=
        Step.par.preserves_isClosedTy baseClosed valueStep rfl
      subst valueEq
      exact ⟨valueTarget, valueStep⟩
    · intro _ proofRawStep
      obtain ⟨proofTargetType, proofTarget, proofStep⟩ := ihProof proofRawStep
      have unitEq : proofTargetType = Ty.unit :=
        Step.par.preserves_isClosedTy IsClosedTy.unit proofStep rfl
      subst unitEq
      exact ⟨proofTarget, proofStep⟩
  | lam codomainClosed body _ ihBody =>
    refine RawStep.par.lift_full_lam body ?_ rawStep
    intro _ bodyRawStep
    obtain ⟨bodyTargetType, bodyTarget, bodyStep⟩ := ihBody bodyRawStep
    have weakenedEq : bodyTargetType = _ :=
      Step.par.preserves_isClosedTy (IsClosedTy.weaken codomainClosed)
                                     bodyStep rfl
    subst weakenedEq
    exact ⟨bodyTarget, bodyStep⟩
  | lamPi codomainClosed body _ ihBody =>
    refine RawStep.par.lift_full_lamPi body ?_ rawStep
    intro _ bodyRawStep
    obtain ⟨bodyTargetType, bodyTarget, bodyStep⟩ := ihBody bodyRawStep
    have codomainEq : bodyTargetType = _ :=
      Step.par.preserves_isClosedTy codomainClosed bodyStep rfl
    subst codomainEq
    exact ⟨bodyTarget, bodyStep⟩
  | pathLam modeIsUnivalent carrierType carrierClosed leftEndpoint
            rightEndpoint body _ ihBody =>
    refine RawStep.par.lift_full_pathLam modeIsUnivalent carrierType
                                          leftEndpoint rightEndpoint body
                                          ?_ rawStep
    intro _ bodyRawStep
    obtain ⟨bodyTargetType, bodyTarget, bodyStep⟩ := ihBody bodyRawStep
    have weakenedEq : bodyTargetType = _ :=
      Step.par.preserves_isClosedTy (IsClosedTy.weaken carrierClosed)
                                     bodyStep rfl
    subst weakenedEq
    exact ⟨bodyTarget, bodyStep⟩
  | app domainClosed codomainClosed functionTerm argumentTerm
        _ _ ihFunction ihArgument =>
    refine RawStep.par.lift_full_app functionTerm argumentTerm ?_ ?_ rawStep
    · intro _ functionRawStep
      obtain ⟨functionTargetType, functionTarget, functionStep⟩ :=
        ihFunction functionRawStep
      have arrowEq : functionTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow domainClosed codomainClosed)
          functionStep rfl
      subst arrowEq
      exact ⟨functionTarget, functionStep⟩
    · intro _ argumentRawStep
      obtain ⟨argumentTargetType, argumentTarget, argumentStep⟩ :=
        ihArgument argumentRawStep
      have domainEq : argumentTargetType = _ :=
        Step.par.preserves_isClosedTy domainClosed argumentStep rfl
      subst domainEq
      exact ⟨argumentTarget, argumentStep⟩
  | uaIntroHet innerLevel innerLevelLt carrierAClosed carrierBClosed
               carrierARaw carrierBRaw equivWitness _ ihEquivWitness =>
    refine RawStep.par.lift_full_uaIntroHet innerLevel innerLevelLt
                                             carrierARaw carrierBRaw
                                             equivWitness ?_ rawStep
    intro _ equivWitnessRawStep
    obtain ⟨equivWitnessTargetType, equivWitnessTarget, equivWitnessStep⟩ :=
      ihEquivWitness equivWitnessRawStep
    have equivEq : equivWitnessTargetType = _ :=
      Step.par.preserves_isClosedTy
        (IsClosedTy.equiv carrierAClosed carrierBClosed)
        equivWitnessStep rfl
    subst equivEq
    exact ⟨equivWitnessTarget, equivWitnessStep⟩
  | boolElim thenTypeClosed elseTypeClosed scrutinee thenBranch elseBranch
             _ _ _ ihScrut ihThen ihElse =>
    refine RawStep.par.lift_full_boolElim scrutinee thenBranch elseBranch
                                           ?_ ?_ ?_ rawStep
    · intro _ scrutRawStep
      obtain ⟨scrutTargetType, scrutTarget, scrutStep⟩ := ihScrut scrutRawStep
      have boolEq : scrutTargetType = Ty.bool :=
        Step.par.preserves_isClosedTy IsClosedTy.bool scrutStep rfl
      subst boolEq
      exact ⟨scrutTarget, scrutStep⟩
    · intro _ thenRawStep
      obtain ⟨thenTargetType, thenTarget, thenStep⟩ := ihThen thenRawStep
      have thenEq : thenTargetType = _ :=
        Step.par.preserves_isClosedTy thenTypeClosed thenStep rfl
      subst thenEq
      exact ⟨thenTarget, thenStep⟩
    · intro _ elseRawStep
      obtain ⟨elseTargetType, elseTarget, elseStep⟩ := ihElse elseRawStep
      have elseEq : elseTargetType = _ :=
        Step.par.preserves_isClosedTy elseTypeClosed elseStep rfl
      subst elseEq
      exact ⟨elseTarget, elseStep⟩
  | equivIntroHet carrierAClosed carrierBClosed forward backward leftInv rightInv
                  leftInvRetarget rightInvRetarget _ _ ihForward ihBackward =>
    refine RawStep.par.lift_full_equivIntroHet forward backward leftInv rightInv
                                                ?_ ?_ leftInvRetarget
                                                rightInvRetarget rawStep
    · intro _ forwardRawStep
      obtain ⟨forwardTargetType, forwardTarget, forwardStep⟩ :=
        ihForward forwardRawStep
      have arrowEq : forwardTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow carrierAClosed carrierBClosed) forwardStep rfl
      subst arrowEq
      exact ⟨forwardTarget, forwardStep⟩
    · intro _ backwardRawStep
      obtain ⟨backwardTargetType, backwardTarget, backwardStep⟩ :=
        ihBackward backwardRawStep
      have arrowEq : backwardTargetType = _ :=
        Step.par.preserves_isClosedTy
          (IsClosedTy.arrow carrierBClosed carrierAClosed) backwardStep rfl
      subst arrowEq
      exact ⟨backwardTarget, backwardStep⟩
  | funextRefl domainType codomainType applyRaw =>
    exact RawStep.par.lift_funextRefl domainType codomainType applyRaw rawStep
  | funextReflAtId domainType codomainType applyRaw =>
    exact RawStep.par.lift_funextReflAtId domainType codomainType applyRaw
            rawStep

end LeanFX2

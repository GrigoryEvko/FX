import LeanFX2.Reduction.ParRed.ParInductive.Inductive

/-! # LeanFX2.Reduction.ParRed.ParStepLift

Lifts a single `Step` to a `Step.par` by inserting `Step.par.refl`
at unchanged positions.  Used in Layer 3 to lift `StepStar` chains
into `Step.par` chains for the confluence proof.

A single tactic-mode theorem with one induction-case per `Step`
constructor (~200 arms).

## Root status

Zero-axiom — pure structural induction over `Step`. -/

namespace LeanFX2


/-! ## Step.toPar — single-step ⇒ parallel.

Each `Step` ctor lifts to `Step.par` by inserting `Step.par.refl` at
positions left unchanged.  Used in Layer 3 to lift `StepStar` chains
into `Step.par` chains. -/

theorem Step.toPar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step.par sourceTerm targetTerm := by
  induction singleStep with
  | appLeft singleStep singleStepIH =>
      exact Step.par.app singleStepIH (Step.par.refl _)
  | appRight singleStep singleStepIH =>
      exact Step.par.app (Step.par.refl _) singleStepIH
  | lamBody singleStep singleStepIH => exact Step.par.lam singleStepIH
  | appPiLeft singleStep singleStepIH =>
      exact Step.par.appPi singleStepIH (Step.par.refl _)
  | appPiRight singleStep singleStepIH =>
      exact Step.par.appPi (Step.par.refl _) singleStepIH
  | lamPiBody singleStep singleStepIH => exact Step.par.lamPi singleStepIH
  | pairRight singleStep singleStepIH =>
      exact Step.par.pair (Step.par.refl _) singleStepIH
  | fstCong singleStep singleStepIH => exact Step.par.fst singleStepIH
  | sndCong singleStep singleStepIH => exact Step.par.snd singleStepIH
  | betaApp body arg =>
      exact Step.par.betaApp (Step.par.refl body) (Step.par.refl arg)
  | betaAppPi body arg =>
      exact Step.par.betaAppPi (Step.par.refl body) (Step.par.refl arg)
  | betaFstPair fv sv =>
      exact Step.par.betaFstPair sv (Step.par.refl fv)
  | betaSndPair fv sv =>
      exact Step.par.betaSndPair fv (Step.par.refl sv)
  | boolElimScrutinee singleStep singleStepIH =>
      exact Step.par.boolElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | boolElimThen singleStep singleStepIH =>
      exact Step.par.boolElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | boolElimElse singleStep singleStepIH =>
      exact Step.par.boolElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaBoolElimTrue thenBranch elseBranch =>
      exact Step.par.iotaBoolElimTrue elseBranch (Step.par.refl thenBranch)
  | iotaBoolElimFalse thenBranch elseBranch =>
      exact Step.par.iotaBoolElimFalse thenBranch (Step.par.refl elseBranch)
  | natSuccPred singleStep singleStepIH => exact Step.par.natSucc singleStepIH
  | natElimScrutinee singleStep singleStepIH =>
      exact Step.par.natElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | natElimZero singleStep singleStepIH =>
      exact Step.par.natElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | natElimSucc singleStep singleStepIH =>
      exact Step.par.natElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaNatElimZero zeroBranch succBranch =>
      exact Step.par.iotaNatElimZero succBranch (Step.par.refl zeroBranch)
  | iotaNatElimSucc predecessor zeroBranch succBranch =>
      exact Step.par.iotaNatElimSucc zeroBranch
              (Step.par.refl predecessor) (Step.par.refl succBranch)
  | natRecScrutinee singleStep singleStepIH =>
      exact Step.par.natRec singleStepIH (Step.par.refl _) (Step.par.refl _)
  | natRecZero singleStep singleStepIH =>
      exact Step.par.natRec (Step.par.refl _) singleStepIH (Step.par.refl _)
  | natRecSucc singleStep singleStepIH =>
      exact Step.par.natRec (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaNatRecZero zeroBranch succBranch =>
      exact Step.par.iotaNatRecZero succBranch (Step.par.refl zeroBranch)
  | iotaNatRecSucc predecessor zeroBranch succBranch =>
      exact Step.par.iotaNatRecSucc
              (Step.par.refl predecessor)
              (Step.par.refl zeroBranch)
              (Step.par.refl succBranch)
  | listConsHead singleStep singleStepIH =>
      exact Step.par.listCons singleStepIH (Step.par.refl _)
  | listConsTail singleStep singleStepIH =>
      exact Step.par.listCons (Step.par.refl _) singleStepIH
  | listElimScrutinee singleStep singleStepIH =>
      exact Step.par.listElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | listElimNil singleStep singleStepIH =>
      exact Step.par.listElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | listElimCons singleStep singleStepIH =>
      exact Step.par.listElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaListElimNil nilBranch consBranch =>
      exact Step.par.iotaListElimNil consBranch (Step.par.refl nilBranch)
  | iotaListElimCons headTerm tailTerm nilBranch consBranch =>
      exact Step.par.iotaListElimCons nilBranch
              (Step.par.refl headTerm)
              (Step.par.refl tailTerm)
              (Step.par.refl consBranch)
  | optionSomeValue singleStep singleStepIH =>
      exact Step.par.optionSome singleStepIH
  | optionMatchScrutinee singleStep singleStepIH =>
      exact Step.par.optionMatch singleStepIH
              (Step.par.refl _) (Step.par.refl _)
  | optionMatchNone singleStep singleStepIH =>
      exact Step.par.optionMatch (Step.par.refl _) singleStepIH (Step.par.refl _)
  | optionMatchSome singleStep singleStepIH =>
      exact Step.par.optionMatch (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaOptionMatchNone noneBranch someBranch =>
      exact Step.par.iotaOptionMatchNone someBranch (Step.par.refl noneBranch)
  | iotaOptionMatchSome valueTerm noneBranch someBranch =>
      exact Step.par.iotaOptionMatchSome noneBranch
              (Step.par.refl valueTerm)
              (Step.par.refl someBranch)
  | eitherInlValue singleStep singleStepIH =>
      exact Step.par.eitherInl singleStepIH
  | eitherInrValue singleStep singleStepIH =>
      exact Step.par.eitherInr singleStepIH
  | eitherMatchScrutinee singleStep singleStepIH =>
      exact Step.par.eitherMatch singleStepIH
              (Step.par.refl _) (Step.par.refl _)
  | eitherMatchLeft singleStep singleStepIH =>
      exact Step.par.eitherMatch (Step.par.refl _) singleStepIH (Step.par.refl _)
  | eitherMatchRight singleStep singleStepIH =>
      exact Step.par.eitherMatch (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaEitherMatchInl valueTerm leftBranch rightBranch =>
      exact Step.par.iotaEitherMatchInl rightBranch
              (Step.par.refl valueTerm)
              (Step.par.refl leftBranch)
  | iotaEitherMatchInr valueTerm leftBranch rightBranch =>
      exact Step.par.iotaEitherMatchInr leftBranch
              (Step.par.refl valueTerm)
              (Step.par.refl rightBranch)
  | idJBase singleStep singleStepIH =>
      exact Step.par.idJ singleStepIH (Step.par.refl _)
  | idJWitness baseCase singleStep singleStepIH =>
      exact Step.par.idJ (Step.par.refl baseCase) singleStepIH
  | oeqJBase singleStep singleStepIH =>
      exact Step.par.oeqJCong singleStepIH (Step.par.refl _)
  | oeqJWitness baseCase singleStep singleStepIH =>
      exact Step.par.oeqJCong (Step.par.refl baseCase) singleStepIH
  | oeqFunextPointwise domainType codomainType
      leftFunctionRaw rightFunctionRaw singleStep singleStepIH =>
      exact Step.par.oeqFunextCong domainType codomainType
        leftFunctionRaw rightFunctionRaw singleStepIH
  | idStrictRecBase modeIsStrict singleStep singleStepIH =>
      exact Step.par.idStrictRecCong modeIsStrict singleStepIH (Step.par.refl _)
  | idStrictRecWitness modeIsStrict baseCase singleStep singleStepIH =>
      exact Step.par.idStrictRecCong modeIsStrict (Step.par.refl baseCase) singleStepIH
  | iotaIdJRefl carrier endpoint baseCase =>
      exact Step.par.iotaIdJRefl carrier endpoint (Step.par.refl baseCase)
  | iotaIdStrictRecRefl modeIsStrict carrier endpoint baseCase =>
      exact Step.par.iotaIdStrictRecRefl modeIsStrict carrier endpoint
        (Step.par.refl baseCase)
  | modIntroInner singleStep singleStepIH =>
      exact Step.par.modIntro singleStepIH
  | modElimInner singleStep singleStepIH =>
      exact Step.par.modElim singleStepIH
  | betaModElimIntro innerTerm =>
      exact Step.par.betaModElimIntro (Step.par.refl innerTerm)
  | subsumeInner singleStep singleStepIH =>
      exact Step.par.subsume singleStepIH
  | pathLamBody modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.pathLamCong modeIsUnivalent singleStepIH
  | pathAppPath modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.pathAppCong modeIsUnivalent singleStepIH (Step.par.refl _)
  | pathAppInterval modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.pathAppCong modeIsUnivalent (Step.par.refl _) singleStepIH
  | betaPathApp modeIsUnivalent bodyTerm intervalTerm =>
      exact Step.par.betaPathApp modeIsUnivalent
        (Step.par.refl bodyTerm) (Step.par.refl intervalTerm)
  | betaPathReflApp modeIsUnivalent carrierType leftEndpoint rightEndpoint
      valueTerm intervalTerm =>
      exact Step.par.betaPathReflApp modeIsUnivalent carrierType
        leftEndpoint rightEndpoint
        (Step.par.refl valueTerm) (Step.par.refl intervalTerm)
  | glueIntroBase modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.glueIntroCong modeIsUnivalent
        singleStepIH (Step.par.refl _)
  | glueIntroPartial modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.glueIntroCong modeIsUnivalent
        (Step.par.refl _) singleStepIH
  | glueElimValue modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.glueElimCong modeIsUnivalent singleStepIH
  | betaGlueElimIntro modeIsUnivalent baseValue partialValue =>
      exact Step.par.betaGlueElimIntro modeIsUnivalent
        (Step.par.refl baseValue) (Step.par.refl partialValue)
  | intervalOppInner singleStep singleStepIH =>
      exact Step.par.intervalOppCong singleStepIH
  | intervalMeetLeft singleStep singleStepIH =>
      exact Step.par.intervalMeetCong singleStepIH (Step.par.refl _)
  | intervalMeetRight singleStep singleStepIH =>
      exact Step.par.intervalMeetCong (Step.par.refl _) singleStepIH
  | intervalJoinLeft singleStep singleStepIH =>
      exact Step.par.intervalJoinCong singleStepIH (Step.par.refl _)
  | intervalJoinRight singleStep singleStepIH =>
      exact Step.par.intervalJoinCong (Step.par.refl _) singleStepIH
  | recordIntroField singleStep singleStepIH =>
      exact Step.par.recordIntroCong singleStepIH
  | recordProjRecord singleStep singleStepIH =>
      exact Step.par.recordProjCong singleStepIH
  | betaRecordProjIntro firstField =>
      exact Step.par.betaRecordProjIntro (Step.par.refl firstField)
  | refineIntroValue singleStep singleStepIH =>
      exact Step.par.refineIntroCong singleStepIH (Step.par.refl _)
  | refineIntroProof singleStep singleStepIH =>
      exact Step.par.refineIntroCong (Step.par.refl _) singleStepIH
  | refineElimValue singleStep singleStepIH =>
      exact Step.par.refineElimCong singleStepIH
  | betaRefineElimIntro predicate baseValue predicateProof =>
      exact Step.par.betaRefineElimIntro
        (Step.par.refl baseValue) (Step.par.refl predicateProof)
  | codataUnfoldState singleStep singleStepIH =>
      exact Step.par.codataUnfoldCong singleStepIH (Step.par.refl _)
  | codataUnfoldTransition singleStep singleStepIH =>
      exact Step.par.codataUnfoldCong (Step.par.refl _) singleStepIH
  | codataDestValue singleStep singleStepIH =>
      exact Step.par.codataDestCong singleStepIH
  | betaCodataDestUnfold initialState transition =>
      exact Step.par.betaCodataDestUnfold
        (Step.par.refl initialState) (Step.par.refl transition)
  | sessionSendChannel singleStep singleStepIH =>
      exact Step.par.sessionSendCong singleStepIH (Step.par.refl _)
  | sessionSendPayload singleStep singleStepIH =>
      exact Step.par.sessionSendCong (Step.par.refl _) singleStepIH
  | sessionRecvChannel singleStep singleStepIH =>
      exact Step.par.sessionRecvCong singleStepIH
  | effectPerformOperation singleStep singleStepIH =>
      exact Step.par.effectPerformCong singleStepIH (Step.par.refl _)
  | effectPerformArguments singleStep singleStepIH =>
      exact Step.par.effectPerformCong (Step.par.refl _) singleStepIH
  | transpPath modeIsUnivalent universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw singleStep singleStepIH =>
      exact Step.par.transpCong modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        singleStepIH (Step.par.refl _)
  | transpSource modeIsUnivalent universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw singleStep singleStepIH =>
      exact Step.par.transpCong modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        (Step.par.refl _) singleStepIH
  | transpReflBeta modeIsUnivalent universeLevel universeLevelLt sourceType
      typePath sourceValue =>
      exact Step.par.transpReflBeta modeIsUnivalent universeLevel
        universeLevelLt sourceType typePath (Step.par.refl sourceValue)
  | hcompBeta modeIsUnivalent capValue sidesPath =>
      exact Step.par.hcompBeta modeIsUnivalent sidesPath
        (Step.par.refl capValue)
  | hcompSides modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.hcompCong modeIsUnivalent
        singleStepIH (Step.par.refl _)
  | hcompCap modeIsUnivalent singleStep singleStepIH =>
      exact Step.par.hcompCong modeIsUnivalent
        (Step.par.refl _) singleStepIH
  | equivIntroHetForward singleStep singleStepIH =>
      exact Step.par.equivIntroHetCong singleStepIH (Step.par.refl _)
  | equivIntroHetBackward singleStep singleStepIH =>
      exact Step.par.equivIntroHetCong (Step.par.refl _) singleStepIH
  | equivAppEquiv singleStep singleStepIH =>
      exact Step.par.equivAppCong singleStepIH (Step.par.refl _)
  | equivAppArgument equivTerm singleStep singleStepIH =>
      exact Step.par.equivAppCong (Step.par.refl equivTerm) singleStepIH
  | uaIntroHetWitness innerLevel innerLevelLt carrierARaw carrierBRaw
      singleStep singleStepIH =>
      exact Step.par.uaIntroHetCong innerLevel innerLevelLt
        carrierARaw carrierBRaw singleStepIH
  | uaToEquivProof innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw singleStep singleStepIH =>
      exact Step.par.uaToEquivCong innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw singleStepIH
  -- Phase D3.6-P4: equivApply equiv-side cong → equivApplyCong with
  -- argument refl; equivApply argument-side cong → equivApplyCong
  -- with equiv refl.  Same pattern as equivAppEquiv / equivAppArgument.
  | equivApplyEquiv singleStep singleStepIH =>
      exact Step.par.equivApplyCong singleStepIH (Step.par.refl _)
  | equivApplyArgument equivTerm singleStep singleStepIH =>
      exact Step.par.equivApplyCong (Step.par.refl equivTerm) singleStepIH
  | cumulUpInner lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh _ singleStepIH =>
      exact Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
                                       levelLeLow levelLeHigh
                                       singleStepIH
  -- Univalence rfl-fragment lift to par: source has no inner steps
  -- (it's a leaf-canonical ctor), so we apply Step.par.eqType directly.
  | eqType innerLevel innerLevelLt carrier carrierRaw =>
      exact Step.par.eqType innerLevel innerLevelLt carrier carrierRaw
  -- Funext rfl-fragment lift to par: source has no inner steps; apply
  -- Step.par.eqArrow directly.
  | eqArrow domainType codomainType applyRaw =>
      exact Step.par.eqArrow domainType codomainType applyRaw
  -- Heterogeneous Univalence lift to par: source `Term.uaIntroHet
  -- ... equivWitness` has no inner steps relevant to this rule (the
  -- whole packaged Term reduces to its underlying equivWitness via a
  -- single par step), so apply `Step.par.eqTypeHet` directly.
  | eqTypeHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness =>
      exact Step.par.eqTypeHet innerLevel innerLevelLt
                                carrierARaw carrierBRaw equivWitness
  -- Heterogeneous funext lift to par: source `Term.funextIntroHet
  -- ... applyARaw applyBRaw` has no inner steps (it's a leaf-
  -- canonical VALUE ctor, like `funextReflAtId`), so apply
  -- `Step.par.eqArrowHet` directly.
  | eqArrowHet domainType codomainType applyARaw applyBRaw =>
      exact Step.par.eqArrowHet domainType codomainType applyARaw applyBRaw


end LeanFX2

import LeanFX2.Reduction.RawParCompatible.PointwiseSubst

namespace LeanFX2

/-! ## Joint substitution: parallel terms + parallel substs → parallel. -/

/-- Joint substitution lemma: parallel reduction is preserved by
substitution where both the substituted term and the substitution
itself step in parallel.  cd_lemma's β-case workhorse. -/
theorem RawStep.par.subst_par {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    {beforeTerm afterTerm : RawTerm sourceScope} :
    RawStep.par beforeTerm afterTerm →
    RawStep.par (beforeTerm.subst firstSubst)
                (afterTerm.subst secondSubst) := by
  intro parallelStep
  induction parallelStep generalizing targetScope with
  -- Reflexivity: same term, related substs ⇒ subst_par_pointwise.
  | refl term =>
      exact RawTerm.subst_par_pointwise term substsRelated
  -- Cong cases.
  | lam _ bodyIH =>
      exact RawStep.par.lam (bodyIH (RawTermSubst.par_lift substsRelated))
  | app _ _ functionIH argumentIH =>
      exact RawStep.par.app (functionIH substsRelated) (argumentIH substsRelated)
  | pair _ _ firstIH secondIH =>
      exact RawStep.par.pair (firstIH substsRelated) (secondIH substsRelated)
  | fst _ pairIH => exact RawStep.par.fst (pairIH substsRelated)
  | snd _ pairIH => exact RawStep.par.snd (pairIH substsRelated)
  | boolElim _ _ _ scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim (scrutineeIH substsRelated)
        (thenIH substsRelated) (elseIH substsRelated)
  | natSucc _ predecessorIH =>
      exact RawStep.par.natSucc (predecessorIH substsRelated)
  | natElim _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim (scrutineeIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | natRec _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec (scrutineeIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | listCons _ _ headIH tailIH =>
      exact RawStep.par.listCons (headIH substsRelated) (tailIH substsRelated)
  | listElim _ _ _ scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim (scrutineeIH substsRelated)
        (nilIH substsRelated) (consIH substsRelated)
  | optionSome _ valueIH =>
      exact RawStep.par.optionSome (valueIH substsRelated)
  | optionMatch _ _ _ scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch (scrutineeIH substsRelated)
        (noneIH substsRelated) (someIH substsRelated)
  | eitherInl _ valueIH =>
      exact RawStep.par.eitherInl (valueIH substsRelated)
  | eitherInr _ valueIH =>
      exact RawStep.par.eitherInr (valueIH substsRelated)
  | eitherMatch _ _ _ scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch (scrutineeIH substsRelated)
        (leftIH substsRelated) (rightIH substsRelated)
  | reflCong _ witnessIH =>
      exact RawStep.par.reflCong (witnessIH substsRelated)
  | idJ _ _ baseIH witnessIH =>
      exact RawStep.par.idJ (baseIH substsRelated) (witnessIH substsRelated)
  | modIntro _ innerIH =>
      exact RawStep.par.modIntro (innerIH substsRelated)
  | modElim _ innerIH =>
      exact RawStep.par.modElim (innerIH substsRelated)
  | betaModElimIntro _ innerIH =>
      exact RawStep.par.betaModElimIntro (innerIH substsRelated)
  | betaModElimIntroDeep _ innerIH =>
      exact RawStep.par.betaModElimIntroDeep (innerIH substsRelated)
  | subsume _ innerIH =>
      exact RawStep.par.subsume (innerIH substsRelated)
  -- Shallow β rules: reshape via subst0_subst_commute.
  | betaApp _ _ bodyIH argumentIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaApp
        (bodyIH (RawTermSubst.par_lift substsRelated))
        (argumentIH substsRelated)
  | betaFstPair secondValue _ firstIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaFstPair (secondValue.subst firstSubst)
        (firstIH substsRelated)
  | betaSndPair firstValue _ secondIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaSndPair (firstValue.subst firstSubst)
        (secondIH substsRelated)
  -- Shallow ι rules.
  | iotaBoolElimTrue elseBranch _ thenIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrue (elseBranch.subst firstSubst)
        (thenIH substsRelated)
  | iotaBoolElimFalse thenBranch _ elseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalse (thenBranch.subst firstSubst)
        (elseIH substsRelated)
  | iotaNatElimZero succBranch _ zeroIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZero (succBranch.subst firstSubst)
        (zeroIH substsRelated)
  | iotaNatElimSucc zeroBranch _ _ predecessorIH succIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSucc (zeroBranch.subst firstSubst)
        (predecessorIH substsRelated) (succIH substsRelated)
  | iotaNatRecZero succBranch _ zeroIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZero (succBranch.subst firstSubst)
        (zeroIH substsRelated)
  | iotaNatRecSucc _ _ _ predecessorIH zeroIH succIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSucc (predecessorIH substsRelated)
        (zeroIH substsRelated) (succIH substsRelated)
  | iotaListElimNil consBranch _ nilIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNil (consBranch.subst firstSubst)
        (nilIH substsRelated)
  | iotaListElimCons nilBranch _ _ _ headIH tailIH consIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaListElimCons (nilBranch.subst firstSubst)
        (headIH substsRelated) (tailIH substsRelated) (consIH substsRelated)
  | iotaOptionMatchNone someBranch _ noneIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNone (someBranch.subst firstSubst)
        (noneIH substsRelated)
  | iotaOptionMatchSome noneBranch _ _ valueIH someIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSome (noneBranch.subst firstSubst)
        (valueIH substsRelated) (someIH substsRelated)
  | iotaEitherMatchInl rightBranch _ _ valueIH leftIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInl (rightBranch.subst firstSubst)
        (valueIH substsRelated) (leftIH substsRelated)
  | iotaEitherMatchInr leftBranch _ _ valueIH rightIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInr (leftBranch.subst firstSubst)
        (valueIH substsRelated) (rightIH substsRelated)
  | iotaIdJRefl witnessRaw _ baseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaIdJRefl (witnessRaw.subst firstSubst)
        (baseIH substsRelated)
  | iotaIdStrictRecRefl witnessRaw _ baseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaIdStrictRecRefl (witnessRaw.subst firstSubst)
        (baseIH substsRelated)
  -- Deep β rules.
  | betaAppDeep _ _ functionIH argumentIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaAppDeep
        (functionIH substsRelated)
        (argumentIH substsRelated)
  | betaFstPairDeep _ pairIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaFstPairDeep (pairIH substsRelated)
  | betaSndPairDeep _ pairIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaSndPairDeep (pairIH substsRelated)
  -- Deep ι rules.
  | iotaBoolElimTrueDeep elseBranch _ _ scrutineeIH thenIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimTrueDeep (elseBranch.subst firstSubst)
        (scrutineeIH substsRelated) (thenIH substsRelated)
  | iotaBoolElimFalseDeep thenBranch _ _ scrutineeIH elseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaBoolElimFalseDeep (thenBranch.subst firstSubst)
        (scrutineeIH substsRelated) (elseIH substsRelated)
  | iotaNatElimZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimZeroDeep (succBranch.subst firstSubst)
        (scrutineeIH substsRelated) (zeroIH substsRelated)
  | iotaNatElimSuccDeep zeroBranch _ _ scrutineeIH succIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatElimSuccDeep (zeroBranch.subst firstSubst)
        (scrutineeIH substsRelated) (succIH substsRelated)
  | iotaNatRecZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecZeroDeep (succBranch.subst firstSubst)
        (scrutineeIH substsRelated) (zeroIH substsRelated)
  | iotaNatRecSuccDeep _ _ _ scrutineeIH zeroIH succIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaNatRecSuccDeep
        (scrutineeIH substsRelated) (zeroIH substsRelated) (succIH substsRelated)
  | iotaListElimNilDeep consBranch _ _ scrutineeIH nilIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaListElimNilDeep (consBranch.subst firstSubst)
        (scrutineeIH substsRelated) (nilIH substsRelated)
  | iotaListElimConsDeep nilBranch _ _ scrutineeIH consIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaListElimConsDeep (nilBranch.subst firstSubst)
        (scrutineeIH substsRelated) (consIH substsRelated)
  | iotaOptionMatchNoneDeep someBranch _ _ scrutineeIH noneIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchNoneDeep (someBranch.subst firstSubst)
        (scrutineeIH substsRelated) (noneIH substsRelated)
  | iotaOptionMatchSomeDeep noneBranch _ _ scrutineeIH someIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaOptionMatchSomeDeep (noneBranch.subst firstSubst)
        (scrutineeIH substsRelated) (someIH substsRelated)
  | iotaEitherMatchInlDeep rightBranch _ _ scrutineeIH leftIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInlDeep (rightBranch.subst firstSubst)
        (scrutineeIH substsRelated) (leftIH substsRelated)
  | iotaEitherMatchInrDeep leftBranch _ _ scrutineeIH rightIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaEitherMatchInrDeep (leftBranch.subst firstSubst)
        (scrutineeIH substsRelated) (rightIH substsRelated)
  | iotaIdJReflDeep _ _ witnessIH baseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaIdJReflDeep
        (witnessIH substsRelated) (baseIH substsRelated)
  | iotaIdStrictRecReflDeep _ _ witnessIH baseIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.iotaIdStrictRecReflDeep
        (witnessIH substsRelated) (baseIH substsRelated)
  -- D1.6: cong cases for the 27 new RawTerm ctors.
  | intervalOppCong _ intervalIH =>
      exact RawStep.par.intervalOppCong (intervalIH substsRelated)
  | intervalMeetCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalMeetCong (leftIH substsRelated) (rightIH substsRelated)
  | intervalJoinCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalJoinCong (leftIH substsRelated) (rightIH substsRelated)
  | pathLamCong _ bodyIH =>
      exact RawStep.par.pathLamCong (bodyIH (RawTermSubst.par_lift substsRelated))
  | pathAppCong _ _ pathIH intervalIH =>
      exact RawStep.par.pathAppCong (pathIH substsRelated) (intervalIH substsRelated)
  | betaPathApp _ _ bodyIH intervalIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaPathApp
        (bodyIH (RawTermSubst.par_lift substsRelated))
        (intervalIH substsRelated)
  | betaPathAppDeep _ _ pathIH intervalIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.subst0_subst_commute _ _ secondSubst]
      exact RawStep.par.betaPathAppDeep
        (pathIH substsRelated)
        (intervalIH substsRelated)
  | @betaPathReflApp _ valueRawSource _ _ _ _ _ valueIH intervalIH =>
      -- Source: pathApp (pathLam valueRawSource.weaken) intervalRawSource.
      -- After subst rho: pathApp (pathLam (valueRawSource.weaken.subst rho.lift))
      --                          (intervalRawSource.subst rho)
      -- We need: valueRawSource.weaken.subst rho.lift =
      --            (valueRawSource.subst rho).weaken.
      -- That is `weaken_subst_commute`, mirroring the transpReflBeta arm.
      dsimp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst valueRawSource]
      exact RawStep.par.betaPathReflApp
        (valueIH substsRelated) (intervalIH substsRelated)
  | glueIntroCong _ _ baseIH partialIH =>
      exact RawStep.par.glueIntroCong (baseIH substsRelated) (partialIH substsRelated)
  | betaGlueElimIntro _ _ baseIH partialIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaGlueElimIntro
        (baseIH substsRelated)
        (partialIH substsRelated)
  | betaGlueElimIntroDeep _ gluedIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaGlueElimIntroDeep (gluedIH substsRelated)
  | glueElimCong _ gluedIH =>
      exact RawStep.par.glueElimCong (gluedIH substsRelated)
  | transpCong _ _ pathIH sourceIH =>
      exact RawStep.par.transpCong (pathIH substsRelated) (sourceIH substsRelated)
  | transpFillCong _ _ _ pathIH intervalIH sourceIH =>
      exact RawStep.par.transpFillCong
        (pathIH substsRelated) (intervalIH substsRelated) (sourceIH substsRelated)
  | @transpReflBeta _ typeRawSource _ _ _ _ _ typeIH sourceIH =>
      dsimp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst typeRawSource]
      exact RawStep.par.transpReflBeta
        (typeIH substsRelated) (sourceIH substsRelated)
  | @transpReflBetaDeep _ _ typeRawTarget _ _ _ _ pathIH sourceIH =>
      dsimp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      simp only [RawTerm.subst, RawTerm.weaken_subst_commute] at pathSubstStep
      exact RawStep.par.transpReflBetaDeep pathSubstStep
        (sourceIH substsRelated)
  | @hcompBeta _ pathBodyRawSource _ _ _ _ _ pathBodyIH capIH =>
      -- Source: hcomp (pathLam pathBodyRawSource.weaken) capRawSource.
      -- After subst rho: hcomp (pathLam (pathBodyRawSource.weaken.subst rho.lift))
      --                        (capRawSource.subst rho).
      -- Need: pathBodyRawSource.weaken.subst rho.lift =
      --         (pathBodyRawSource.subst rho).weaken
      -- via `weaken_subst_commute`, mirroring the transpReflBeta arm.
      dsimp only [RawTerm.subst]
      rw [RawTerm.weaken_subst_commute firstSubst pathBodyRawSource]
      exact RawStep.par.hcompBeta
        (pathBodyIH substsRelated) (capIH substsRelated)
  | @hcompBetaDeep _ _ _ _ _ _ _ sidesIH capIH =>
      -- sidesIH : par sidesRawSource (pathLam pathBodyRawTarget.weaken).
      -- After subst rho, the IH gives par on substituted sides; the target
      -- becomes pathLam ((pathBodyRawTarget.weaken).subst rho.lift), rewritten via
      -- weaken_subst_commute to pathLam (pathBodyRawTarget.subst rho).weaken.
      dsimp only [RawTerm.subst]
      have sidesSubstStep := sidesIH substsRelated
      simp only [RawTerm.subst, RawTerm.weaken_subst_commute] at sidesSubstStep
      exact RawStep.par.hcompBetaDeep sidesSubstStep
        (capIH substsRelated)
  | hcompCong _ _ sidesIH capIH =>
      exact RawStep.par.hcompCong (sidesIH substsRelated) (capIH substsRelated)
  | oeqReflCong _ witnessIH =>
      exact RawStep.par.oeqReflCong (witnessIH substsRelated)
  | oeqJCong _ _ baseIH witnessIH =>
      exact RawStep.par.oeqJCong (baseIH substsRelated) (witnessIH substsRelated)
  | oeqFunextCong _ pointwiseIH =>
      exact RawStep.par.oeqFunextCong (pointwiseIH substsRelated)
  | idStrictReflCong _ witnessIH =>
      exact RawStep.par.idStrictReflCong (witnessIH substsRelated)
  | idStrictRecCong _ _ baseIH witnessIH =>
      exact RawStep.par.idStrictRecCong (baseIH substsRelated) (witnessIH substsRelated)
  | equivIntroCong _ _ forwardIH backwardIH =>
      exact RawStep.par.equivIntroCong (forwardIH substsRelated) (backwardIH substsRelated)
  | equivAppCong _ _ equivIH argumentIH =>
      exact RawStep.par.equivAppCong (equivIH substsRelated) (argumentIH substsRelated)
  | refineIntroCong _ _ valueIH proofIH =>
      exact RawStep.par.refineIntroCong (valueIH substsRelated) (proofIH substsRelated)
  | betaRefineElimIntro _ _ valueIH proofIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaRefineElimIntro
        (valueIH substsRelated)
        (proofIH substsRelated)
  | betaRefineElimIntroDeep _ refinedIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaRefineElimIntroDeep (refinedIH substsRelated)
  | refineElimCong _ refinedIH =>
      exact RawStep.par.refineElimCong (refinedIH substsRelated)
  | recordIntroCong _ firstIH =>
      exact RawStep.par.recordIntroCong (firstIH substsRelated)
  | betaRecordProjIntro _ firstIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaRecordProjIntro (firstIH substsRelated)
  | betaRecordProjIntroDeep _ recordIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaRecordProjIntroDeep (recordIH substsRelated)
  | recordProjCong _ recordIH =>
      exact RawStep.par.recordProjCong (recordIH substsRelated)
  | codataUnfoldCong _ _ stateIH transitionIH =>
      exact RawStep.par.codataUnfoldCong (stateIH substsRelated) (transitionIH substsRelated)
  | betaCodataDestUnfold _ _ stateIH transitionIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaCodataDestUnfold
        (stateIH substsRelated)
        (transitionIH substsRelated)
  | betaCodataDestUnfoldDeep _ codataIH =>
      dsimp only [RawTerm.subst]
      exact RawStep.par.betaCodataDestUnfoldDeep
        (codataIH substsRelated)
  | codataDestCong _ codataIH =>
      exact RawStep.par.codataDestCong (codataIH substsRelated)
  | sessionSendCong _ _ channelIH payloadIH =>
      exact RawStep.par.sessionSendCong (channelIH substsRelated) (payloadIH substsRelated)
  | sessionRecvCong _ channelIH =>
      exact RawStep.par.sessionRecvCong (channelIH substsRelated)
  | effectPerformCong _ _ operationIH argumentsIH =>
      exact RawStep.par.effectPerformCong (operationIH substsRelated) (argumentsIH substsRelated)
  -- CUMUL-2.1 per-shape type-code cong rules.  Binder-shape ctors
  -- (`piTyCode`, `sigmaTyCode`) recurse with `RawTermSubst.par_lift
  -- substsRelated` to thread parallelism under the binder.
  | arrowCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.arrowCodeCong (domainIH substsRelated) (codomainIH substsRelated)
  | piTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.piTyCodeCong
        (domainIH substsRelated)
        (codomainIH (RawTermSubst.par_lift substsRelated))
  | sigmaTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.sigmaTyCodeCong
        (domainIH substsRelated)
        (codomainIH (RawTermSubst.par_lift substsRelated))
  | productCodeCong _ _ firstIH secondIH =>
      exact RawStep.par.productCodeCong (firstIH substsRelated) (secondIH substsRelated)
  | sumCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.sumCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | listCodeCong _ elementIH =>
      exact RawStep.par.listCodeCong (elementIH substsRelated)
  | optionCodeCong _ elementIH =>
      exact RawStep.par.optionCodeCong (elementIH substsRelated)
  | eitherCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.eitherCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | idCodeCong _ _ _ typeIH leftIH rightIH =>
      exact RawStep.par.idCodeCong
        (typeIH substsRelated) (leftIH substsRelated) (rightIH substsRelated)
  | equivCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.equivCodeCong (leftIH substsRelated) (rightIH substsRelated)
  | cumulUpMarkerCong _ innerIH =>
      exact RawStep.par.cumulUpMarkerCong (innerIH substsRelated)
  | uaToEquivCong _ innerIH =>
      exact RawStep.par.uaToEquivCong (innerIH substsRelated)
  | equivApplyCong _ _ equivIH argIH =>
      exact RawStep.par.equivApplyCong
        (equivIH substsRelated) (argIH substsRelated)
  | uaBeta _ _ proofIH sourceIH =>
      -- D3.6-S1: parallel substitution preserves the univalence-β
      -- contractum.  LHS subst pushes through transp/uaToEquiv heads;
      -- RHS subst pushes through equivApply/uaToEquiv heads.  Both
      -- sides are mechanical via the definition of `RawTerm.subst`
      -- on the involved ctors (no binder shift since none of the
      -- involved ctors carry binders at this level).
      dsimp only [RawTerm.subst]
      exact RawStep.par.uaBeta (proofIH substsRelated) (sourceIH substsRelated)
  | uaBetaDeep _ _ pathIH sourceIH =>
      -- D3.6-S1 deep variant: parallel substitution pushes through
      -- transp/equivApply/uaToEquiv heads.  Lift pathIH via subst on
      -- its uaToEquiv-headed target, then assemble.
      dsimp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      dsimp only [RawTerm.subst] at pathSubstStep
      exact RawStep.par.uaBetaDeep pathSubstStep (sourceIH substsRelated)
  | pathComposeCong _ _ leftIH rightIH =>
      -- D3.6-S3: parallel substitution distributes over the binary
      -- pathCompose ctor; each path raw gets the same substitution.
      exact RawStep.par.pathComposeCong
        (leftIH substsRelated) (rightIH substsRelated)
  | transpCompose _ _ _ leftIH rightIH sourceIH =>
      -- D3.6-S3: parallel substitution preserves the compose-β
      -- contractum.  LHS subst pushes through transp/pathCompose heads;
      -- RHS subst pushes through nested transp.  Mechanical via the
      -- definition of `RawTerm.subst` on the involved ctors (no binder
      -- shift since none of the involved ctors carry binders at this
      -- level).
      dsimp only [RawTerm.subst]
      exact RawStep.par.transpCompose
        (leftIH substsRelated) (rightIH substsRelated) (sourceIH substsRelated)
  | transpComposeDeep _ _ pathIH sourceIH =>
      -- D3.6-S3 deep variant: parallel substitution pushes through
      -- transp/pathCompose heads.  Lift pathIH via subst on its
      -- pathCompose-headed target, then assemble the nested-transp RHS.
      dsimp only [RawTerm.subst]
      have pathSubstStep := pathIH substsRelated
      dsimp only [RawTerm.subst] at pathSubstStep
      exact RawStep.par.transpComposeDeep pathSubstStep (sourceIH substsRelated)
  | idToEquivCong _ proofIH =>
      -- D3.6-S4: parallel substitution distributes over the unary
      -- idToEquiv ctor.
      exact RawStep.par.idToEquivCong (proofIH substsRelated)
  | idToEquivRefl _ witnessIH =>
      -- D3.6-S4: parallel substitution preserves the identity-equiv
      -- contractum.  LHS subst pushes through idToEquiv/refl heads;
      -- RHS subst over equivIntro/lam/var (var 0 is the bound binder
      -- variable, so it's unchanged by the outer subst).  Mechanical
      -- via the definition of `RawTerm.subst` on the involved ctors.
      dsimp only [RawTerm.subst]
      exact RawStep.par.idToEquivRefl (witnessIH substsRelated)
  | idToEquivReflDeep _ proofIH =>
      -- D3.6-S4 deep variant: parallel substitution pushes through
      -- idToEquiv heads.  proofIH substituted gives a par step on the
      -- substituted proof landing at refl of the substituted witness.
      dsimp only [RawTerm.subst]
      have proofSubstStep := proofIH substsRelated
      dsimp only [RawTerm.subst] at proofSubstStep
      exact RawStep.par.idToEquivReflDeep proofSubstStep
  | oeqTransCong _ _ firstIH secondIH =>
      -- D3.6-S5: parallel substitution distributes over the binary
      -- oeqTrans ctor.
      exact RawStep.par.oeqTransCong (firstIH substsRelated) (secondIH substsRelated)
  | equivComposeCong _ _ firstIH secondIH =>
      -- D3.6-S5: parallel substitution distributes over the binary
      -- equivCompose ctor.
      exact RawStep.par.equivComposeCong (firstIH substsRelated) (secondIH substsRelated)
  | idToEquivCompose _ _ firstIH secondIH =>
      -- D3.6-S5 shallow compose-β: parallel substitution preserves the
      -- equivCompose contractum.  LHS subst pushes through
      -- idToEquiv/oeqTrans heads; RHS subst over equivCompose/idToEquiv
      -- pushes through both arms.
      dsimp only [RawTerm.subst]
      exact RawStep.par.idToEquivCompose (firstIH substsRelated) (secondIH substsRelated)
  | idToEquivComposeDeep _ proofIH =>
      -- D3.6-S5 deep compose-β: parallel substitution pushes through
      -- idToEquiv heads.  proofIH substituted gives a par step on the
      -- substituted proof landing at oeqTrans of the substituted
      -- targets.
      dsimp only [RawTerm.subst]
      have proofSubstStep := proofIH substsRelated
      dsimp only [RawTerm.subst] at proofSubstStep
      exact RawStep.par.idToEquivComposeDeep proofSubstStep
  | uaReflEquivApply _ _ witnessIH sourceIH =>
      -- D3.6-S6 shallow round-trip-β: parallel substitution preserves
      -- the round-trip contractum.  LHS subst pushes through
      -- equivApply/uaToEquiv/oeqRefl heads; RHS subst pushes through
      -- bare source raw.  Both mechanical via `RawTerm.subst` on the
      -- involved ctors (no binder shift since none carry binders here).
      dsimp only [RawTerm.subst]
      exact RawStep.par.uaReflEquivApply
        (witnessIH substsRelated) (sourceIH substsRelated)
  | uaReflEquivApplyDeep _ _ equivIH sourceIH =>
      -- D3.6-S6 deep round-trip-β: parallel substitution pushes through
      -- equivApply heads.  equivIH substituted gives a par step on the
      -- substituted equiv landing at uaToEquiv (oeqRefl _) of the
      -- substituted witness, then assemble.
      dsimp only [RawTerm.subst]
      have equivSubstStep := equivIH substsRelated
      dsimp only [RawTerm.subst] at equivSubstStep
      exact RawStep.par.uaReflEquivApplyDeep
        equivSubstStep (sourceIH substsRelated)
  | funextReflCong _ applyIH =>
      exact RawStep.par.funextReflCong (applyIH (RawTermSubst.par_lift substsRelated))
  | funextReflAtIdCong _ applyIH =>
      exact RawStep.par.funextReflAtIdCong (applyIH (RawTermSubst.par_lift substsRelated))
  | funextIntroHetCong _ applyAIH =>
      exact RawStep.par.funextIntroHetCong (applyAIH (RawTermSubst.par_lift substsRelated))

/-! ## β-corollary: parallel substitution at position 0. -/

/-- Singleton corollary: parallel body + parallel arg ⇒ parallel β-redex. -/
theorem RawStep.par.subst0_par {scope : Nat}
    {bodySource bodyTarget : RawTerm (scope + 1)}
    {argumentSource argumentTarget : RawTerm scope}
    (bodyStep : RawStep.par bodySource bodyTarget)
    (argumentStep : RawStep.par argumentSource argumentTarget) :
    RawStep.par (bodySource.subst0 argumentSource)
                (bodyTarget.subst0 argumentTarget) := by
  apply RawStep.par.subst_par _ bodyStep
  intro position
  match position with
  | ⟨0, _⟩ => exact argumentStep
  | ⟨_ + 1, _⟩ => exact RawStep.par.refl _

end LeanFX2

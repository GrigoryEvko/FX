import LeanFX2.Confluence.RawCdLemma.ArrowFamily
import LeanFX2.Confluence.RawCdLemma.BoolNatArms
import LeanFX2.Confluence.RawCdLemma.CubicalAndEquiv
import LeanFX2.Confluence.RawCdLemma.IdentityArms
import LeanFX2.Confluence.RawCdLemma.ListOptionEitherArms
import LeanFX2.Confluence.RawCdLemma.ModalAndRefine
import LeanFX2.Confluence.RawCdLemma.RecordAndCodata
import LeanFX2.Confluence.RawCdLemma.SigmaArms
import LeanFX2.Confluence.RawCdLemma.TypeCodes
import LeanFX2.Reduction.RawParWeakenInv.Weaken

/-! # Confluence/RawCdLemma — every parallel reduct lands in `RawTerm.cd`

`RawStep.par.cd_lemma`: `RawStep.par source target → RawStep.par target (RawTerm.cd source)`.

The semantic helper modules under `Confluence/RawCdLemma/` own the
constructor-family proofs. This file is the public headline dispatcher and keeps
only the heavyweight head-shape dispatch arms inline.
-/

namespace LeanFX2

theorem RawStep.par.cd_lemma {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope} :
    RawStep.par sourceTerm targetTerm →
    RawStep.par targetTerm (RawTerm.cd sourceTerm) := by
  intro parallelStep
  induction parallelStep with
  | refl term => exact RawStep.par.cd_dominates term
  | lam _ bodyIH => exact RawStep.par.cd_lemma_lam bodyIH
  | app _ _ functionIH argumentIH =>
      exact RawStep.par.cd_lemma_app functionIH argumentIH
  | pair _ _ firstIH secondIH =>
      exact RawStep.par.cd_lemma_pair firstIH secondIH
  | fst _ pairIH => exact RawStep.par.cd_lemma_fst pairIH
  | snd _ pairIH => exact RawStep.par.cd_lemma_snd pairIH
  | boolElim _ _ _ scrutineeIH thenIH elseIH =>
      exact RawStep.par.cd_lemma_boolElim scrutineeIH thenIH elseIH
  | natSucc _ predIH => exact RawStep.par.cd_lemma_natSucc predIH
  | natElim _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.cd_lemma_natElim scrutineeIH zeroIH succIH
  | natRec _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.cd_lemma_natRec scrutineeIH zeroIH succIH
  | listCons _ _ headIH tailIH =>
      exact RawStep.par.cd_lemma_listCons headIH tailIH
  | listElim _ _ _ scrutineeIH nilIH consIH =>
      exact RawStep.par.cd_lemma_listElim scrutineeIH nilIH consIH
  | optionSome _ valueIH => exact RawStep.par.cd_lemma_optionSome valueIH
  | optionMatch _ _ _ scrutineeIH noneIH someIH =>
      exact RawStep.par.cd_lemma_optionMatch scrutineeIH noneIH someIH
  | eitherInl _ valueIH => exact RawStep.par.cd_lemma_eitherInl valueIH
  | eitherInr _ valueIH => exact RawStep.par.cd_lemma_eitherInr valueIH
  | eitherMatch _ _ _ scrutineeIH leftIH rightIH =>
      exact RawStep.par.cd_lemma_eitherMatch scrutineeIH leftIH rightIH
  | reflCong _ rawTermIH => exact RawStep.par.cd_lemma_reflCong rawTermIH
  | funextReflCong _ applyIH =>
      exact RawStep.par.cd_lemma_funextReflCong applyIH
  | funextReflAtIdCong _ applyIH =>
      exact RawStep.par.cd_lemma_funextReflAtIdCong applyIH
  | funextIntroHetCong _ applyAIH =>
      exact RawStep.par.cd_lemma_funextIntroHetCong applyAIH
  | idJ _ _ baseIH witnessIH =>
      exact RawStep.par.cd_lemma_idJ baseIH witnessIH
  | modIntro _ innerIH => exact RawStep.par.cd_lemma_modIntro innerIH
  | modElim _ innerIH => exact RawStep.par.cd_lemma_modElim innerIH
  | betaModElimIntro _ innerIH =>
      exact RawStep.par.cd_lemma_betaModElimIntro innerIH
  | betaModElimIntroDeep _ innerIH =>
      exact RawStep.par.cd_lemma_betaModElimIntroDeep innerIH
  | subsume _ innerIH => exact RawStep.par.cd_lemma_subsume innerIH
  | betaApp _ _ bodyIH argumentIH =>
      exact RawStep.par.cd_lemma_betaApp bodyIH argumentIH
  | betaFstPair secondVal _ firstIH =>
      exact RawStep.par.cd_lemma_betaFstPair secondVal firstIH
  | betaSndPair firstVal _ secondIH =>
      exact RawStep.par.cd_lemma_betaSndPair firstVal secondIH
  | iotaBoolElimTrue elseBranch _ thenIH =>
      exact RawStep.par.cd_lemma_iotaBoolElimTrue elseBranch thenIH
  | iotaBoolElimFalse thenBranch _ elseIH =>
      exact RawStep.par.cd_lemma_iotaBoolElimFalse thenBranch elseIH
  | iotaNatElimZero succBranch _ zeroIH =>
      exact RawStep.par.cd_lemma_iotaNatElimZero succBranch zeroIH
  | iotaNatElimSucc zeroBranch _ _ predIH succIH =>
      exact RawStep.par.cd_lemma_iotaNatElimSucc zeroBranch predIH succIH
  | iotaNatRecZero succBranch _ zeroIH =>
      exact RawStep.par.cd_lemma_iotaNatRecZero succBranch zeroIH
  | iotaNatRecSucc _ _ _ predIH zeroIH succIH =>
      exact RawStep.par.cd_lemma_iotaNatRecSucc predIH zeroIH succIH
  | iotaListElimNil consBranch _ nilIH =>
      exact RawStep.par.cd_lemma_iotaListElimNil consBranch nilIH
  | iotaListElimCons nilBranch _ _ _ headIH tailIH consIH =>
      exact RawStep.par.cd_lemma_iotaListElimCons nilBranch headIH tailIH consIH
  | iotaOptionMatchNone someBranch _ noneIH =>
      exact RawStep.par.cd_lemma_iotaOptionMatchNone someBranch noneIH
  | iotaOptionMatchSome noneBranch _ _ valueIH someIH =>
      exact RawStep.par.cd_lemma_iotaOptionMatchSome noneBranch valueIH someIH
  | iotaEitherMatchInl rightBranch _ _ valueIH leftIH =>
      exact RawStep.par.cd_lemma_iotaEitherMatchInl rightBranch valueIH leftIH
  | iotaEitherMatchInr leftBranch _ _ valueIH rightIH =>
      exact RawStep.par.cd_lemma_iotaEitherMatchInr leftBranch valueIH rightIH
  | iotaIdJRefl rawTerm _ baseIH =>
      exact RawStep.par.cd_lemma_iotaIdJRefl rawTerm baseIH
  | iotaIdStrictRecRefl rawTerm _ baseIH =>
      exact RawStep.par.cd_lemma_iotaIdStrictRecRefl rawTerm baseIH
  | betaAppDeep _ _ functionIH argumentIH =>
      exact RawStep.par.cd_lemma_betaAppDeep functionIH argumentIH
  | betaPathApp _ _ bodyIH intervalIH =>
      exact RawStep.par.cd_lemma_betaPathApp bodyIH intervalIH
  | betaPathAppDeep _ _ pathIH intervalIH =>
      exact RawStep.par.cd_lemma_betaPathAppDeep pathIH intervalIH
  | betaPathReflApp _ _ valueIH intervalIH =>
      exact RawStep.par.cd_lemma_betaPathReflApp valueIH intervalIH
  | betaFstPairDeep _ pairIH =>
      exact RawStep.par.cd_lemma_betaFstPairDeep pairIH
  | betaSndPairDeep _ pairIH =>
      exact RawStep.par.cd_lemma_betaSndPairDeep pairIH
  | iotaBoolElimTrueDeep elseBranch _ _ scrutineeIH thenIH =>
      exact RawStep.par.cd_lemma_iotaBoolElimTrueDeep elseBranch scrutineeIH thenIH
  | iotaBoolElimFalseDeep thenBranch _ _ scrutineeIH elseIH =>
      exact RawStep.par.cd_lemma_iotaBoolElimFalseDeep thenBranch scrutineeIH elseIH
  | iotaNatElimZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      exact RawStep.par.cd_lemma_iotaNatElimZeroDeep succBranch scrutineeIH zeroIH
  | iotaNatElimSuccDeep zeroBranch _ _ scrutineeIH succIH =>
      exact RawStep.par.cd_lemma_iotaNatElimSuccDeep zeroBranch scrutineeIH succIH
  | iotaNatRecZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      exact RawStep.par.cd_lemma_iotaNatRecZeroDeep succBranch scrutineeIH zeroIH
  | iotaNatRecSuccDeep _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.cd_lemma_iotaNatRecSuccDeep scrutineeIH zeroIH succIH
  | iotaListElimNilDeep consBranch _ _ scrutineeIH nilIH =>
      exact RawStep.par.cd_lemma_iotaListElimNilDeep consBranch scrutineeIH nilIH
  | iotaListElimConsDeep nilBranch _ _ scrutineeIH consIH =>
      exact RawStep.par.cd_lemma_iotaListElimConsDeep nilBranch scrutineeIH consIH
  | iotaOptionMatchNoneDeep someBranch _ _ scrutineeIH noneIH =>
      exact RawStep.par.cd_lemma_iotaOptionMatchNoneDeep someBranch scrutineeIH noneIH
  | iotaOptionMatchSomeDeep noneBranch _ _ scrutineeIH someIH =>
      exact RawStep.par.cd_lemma_iotaOptionMatchSomeDeep noneBranch scrutineeIH someIH
  | iotaEitherMatchInlDeep rightBranch _ _ scrutineeIH leftIH =>
      exact RawStep.par.cd_lemma_iotaEitherMatchInlDeep rightBranch scrutineeIH leftIH
  | iotaEitherMatchInrDeep leftBranch _ _ scrutineeIH rightIH =>
      exact RawStep.par.cd_lemma_iotaEitherMatchInrDeep leftBranch scrutineeIH rightIH
  | iotaIdJReflDeep _ _ witnessIH baseIH =>
      exact RawStep.par.cd_lemma_iotaIdJReflDeep witnessIH baseIH
  | iotaIdStrictRecReflDeep _ _ witnessIH baseIH =>
      exact RawStep.par.cd_lemma_iotaIdStrictRecReflDeep witnessIH baseIH
  | intervalOppCong _ intervalIH =>
      exact RawStep.par.cd_lemma_intervalOppCong intervalIH
  | intervalMeetCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_intervalMeetCong leftIH rightIH
  | intervalJoinCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_intervalJoinCong leftIH rightIH
  | pathLamCong _ bodyIH =>
      exact RawStep.par.cd_lemma_pathLamCong bodyIH
  | pathAppCong _ _ pathIH intervalIH =>
      exact RawStep.par.cd_lemma_pathAppCong pathIH intervalIH
  | glueIntroCong _ _ baseIH partialIH =>
      exact RawStep.par.cd_lemma_glueIntroCong baseIH partialIH
  | betaGlueElimIntro _ _ baseIH partialIH =>
      exact RawStep.par.cd_lemma_betaGlueElimIntro baseIH partialIH
  | betaGlueElimIntroDeep _ gluedIH =>
      exact RawStep.par.cd_lemma_betaGlueElimIntroDeep gluedIH
  | glueElimCong _ gluedIH =>
      exact RawStep.par.cd_lemma_glueElimCong gluedIH
  | @transpCong _ pathRawSource pathRawTarget _ _ pathStep sourceStep pathIH sourceIH =>
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      split
      case _ pathBody pathBodyEqn =>
          rw [pathBodyEqn] at pathIH
          split
          case _ innerType unwknEqn =>
              have hPath : pathBody = innerType.weaken :=
                RawTerm.unweaken?_imp_weaken pathBody innerType unwknEqn
              rw [hPath] at pathIH
              exact RawStep.par.transpReflBetaDeep pathIH sourceIH
          case _ _unwknEqn =>
              exact RawStep.par.transpCong pathIH sourceIH
      all_goals first
        | (rename_i proofRaw cdPathEqn
           rw [cdPathEqn] at pathIH
           exact RawStep.par.uaBetaDeep pathIH sourceIH)
        | (rename_i leftPathRaw rightPathRaw cdPathEqn
           rw [cdPathEqn] at pathIH
           exact RawStep.par.transpComposeDeep pathIH sourceIH)
        | exact RawStep.par.transpCong pathIH sourceIH
  | @uaBeta _ proofRawSource _ _ _ _ sourceStep proofIH sourceIH =>
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      exact RawStep.par.equivApplyCong
        (RawStep.par.uaToEquivCong proofIH) sourceIH
  | @uaBetaDeep _ pathRawSource _ _ _ pathStep sourceStep pathIH sourceIH =>
      obtain ⟨proofInner, cdPathEq, proofParStep⟩ :=
        RawStep.par.uaToEquiv_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      exact RawStep.par.equivApplyCong
        (RawStep.par.uaToEquivCong proofParStep) sourceIH
  | @transpReflBeta _ typeRawSource _ _ _ _ _ typeIH sourceIH =>
      simp only [RawTerm.cd, RawTerm.cdTranspCase, RawTerm.cd_weaken,
                 RawTerm.unweaken?_weaken]
      exact sourceIH
  | @transpReflBetaDeep _ pathRawSource _ _ _ pathStep sourceStep pathIH sourceIH =>
      obtain ⟨someBody, cdPathEq, bodyParStep⟩ := RawStep.par.pathLam_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      obtain ⟨innerType, hWeak⟩ := RawStep.par.weaken_inv bodyParStep
      rw [hWeak]
      simp only [RawTerm.unweaken?_weaken]
      exact sourceIH
  | transpFillCong _ _ _ pathIH intervalIH sourceIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.transpFillCong pathIH intervalIH sourceIH
  | hcompCong _ _ sidesIH capIH =>
      exact RawStep.par.cd_lemma_hcompCong sidesIH capIH
  | @hcompBeta _ pathBodyRawSource _ _ _ _ _ pathBodyIH capIH =>
      simp only [RawTerm.cd, RawTerm.cdHcompCase, RawTerm.cd_weaken,
                 RawTerm.unweaken?_weaken]
      exact capIH
  | @hcompBetaDeep _ sidesRawSource _ _ _ sidesStep capStep sidesIH capIH =>
      obtain ⟨someBody, cdSidesEq, bodyParStep⟩ := RawStep.par.pathLam_inv sidesIH
      simp only [RawTerm.cd, RawTerm.cdHcompCase]
      rw [cdSidesEq]
      obtain ⟨innerBody, hWeak⟩ := RawStep.par.weaken_inv bodyParStep
      rw [hWeak]
      simp only [RawTerm.unweaken?_weaken]
      exact capIH
  | oeqReflCong _ witnessIH =>
      exact RawStep.par.cd_lemma_oeqReflCong witnessIH
  | oeqJCong _ _ baseIH witnessIH =>
      exact RawStep.par.cd_lemma_oeqJCong baseIH witnessIH
  | oeqFunextCong _ pointwiseIH =>
      exact RawStep.par.cd_lemma_oeqFunextCong pointwiseIH
  | idStrictReflCong _ witnessIH =>
      exact RawStep.par.cd_lemma_idStrictReflCong witnessIH
  | idStrictRecCong _ _ baseIH witnessIH =>
      exact RawStep.par.cd_lemma_idStrictRecCong baseIH witnessIH
  | equivIntroCong _ _ forwardIH backwardIH =>
      exact RawStep.par.cd_lemma_equivIntroCong forwardIH backwardIH
  | equivAppCong _ _ equivIH argumentIH =>
      exact RawStep.par.cd_lemma_equivAppCong equivIH argumentIH
  | refineIntroCong _ _ valueIH proofIH =>
      exact RawStep.par.cd_lemma_refineIntroCong valueIH proofIH
  | betaRefineElimIntro _ _ valueIH proofIH =>
      exact RawStep.par.cd_lemma_betaRefineElimIntro valueIH proofIH
  | betaRefineElimIntroDeep _ refinedIH =>
      exact RawStep.par.cd_lemma_betaRefineElimIntroDeep refinedIH
  | refineElimCong _ refinedIH =>
      exact RawStep.par.cd_lemma_refineElimCong refinedIH
  | recordIntroCong _ firstIH =>
      exact RawStep.par.cd_lemma_recordIntroCong firstIH
  | betaRecordProjIntro _ firstIH =>
      exact RawStep.par.cd_lemma_betaRecordProjIntro firstIH
  | betaRecordProjIntroDeep _ recordIH =>
      exact RawStep.par.cd_lemma_betaRecordProjIntroDeep recordIH
  | recordProjCong _ recordIH =>
      exact RawStep.par.cd_lemma_recordProjCong recordIH
  | codataUnfoldCong _ _ stateIH transitionIH =>
      exact RawStep.par.cd_lemma_codataUnfoldCong stateIH transitionIH
  | codataDestCong _ codataIH =>
      exact RawStep.par.cd_lemma_codataDestCong codataIH
  | betaCodataDestUnfold _ _ stateIH transitionIH =>
      exact RawStep.par.cd_lemma_betaCodataDestUnfold stateIH transitionIH
  | betaCodataDestUnfoldDeep _ codataIH =>
      exact RawStep.par.cd_lemma_betaCodataDestUnfoldDeep codataIH
  | sessionSendCong _ _ channelIH payloadIH =>
      exact RawStep.par.cd_lemma_sessionSendCong channelIH payloadIH
  | sessionRecvCong _ channelIH =>
      exact RawStep.par.cd_lemma_sessionRecvCong channelIH
  | effectPerformCong _ _ tagIH argumentsIH =>
      exact RawStep.par.cd_lemma_effectPerformCong tagIH argumentsIH
  | arrowCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.cd_lemma_arrowCodeCong domainIH codomainIH
  | piTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.cd_lemma_piTyCodeCong domainIH codomainIH
  | sigmaTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.cd_lemma_sigmaTyCodeCong domainIH codomainIH
  | productCodeCong _ _ firstIH secondIH =>
      exact RawStep.par.cd_lemma_productCodeCong firstIH secondIH
  | sumCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_sumCodeCong leftIH rightIH
  | listCodeCong _ elementIH =>
      exact RawStep.par.cd_lemma_listCodeCong elementIH
  | optionCodeCong _ elementIH =>
      exact RawStep.par.cd_lemma_optionCodeCong elementIH
  | eitherCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_eitherCodeCong leftIH rightIH
  | idCodeCong _ _ _ typeIH leftIH rightIH =>
      exact RawStep.par.cd_lemma_idCodeCong typeIH leftIH rightIH
  | equivCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_equivCodeCong leftIH rightIH
  | cumulUpMarkerCong _ innerIH =>
      exact RawStep.par.cd_lemma_cumulUpMarkerCong innerIH
  | uaToEquivCong _ innerIH =>
      exact RawStep.par.cd_lemma_uaToEquivCong innerIH
  | @equivApplyCong _ equivRawSource _ argRawSource _ _ _ equivIH argIH =>
      simp only [RawTerm.cd]
      unfold RawTerm.cdEquivApplyCase
      match hCdEquiv : RawTerm.cd equivRawSource with
      | .uaToEquiv proof =>
          rw [hCdEquiv] at equivIH
          show RawStep.par _ (RawTerm.cdUaToEquivApplyCase proof (RawTerm.cd argRawSource))
          unfold RawTerm.cdUaToEquivApplyCase
          match proof with
          | .oeqRefl _ =>
              exact RawStep.par.uaReflEquivApplyDeep equivIH argIH
          | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
          | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
          | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
          | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
          | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .refl _
          | .idJ _ _ | .modIntro _ | .modElim _ | .subsume _
          | .interval0 | .interval1 | .intervalOpp _ | .intervalMeet _ _
          | .intervalJoin _ _ | .pathLam _ | .pathApp _ _ | .glueIntro _ _
          | .glueElim _ | .transp _ _ | .transpFill _ _ _
          | .hcomp _ _ | .oeqJ _ _ | .oeqFunext _
          | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _ | .equivApp _ _
          | .refineIntro _ _ | .refineElim _ | .recordIntro _ | .recordProj _
          | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _ | .sessionRecv _
          | .effectPerform _ _ | .universeCode _ | .arrowCode _ _ | .piTyCode _ _
          | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _ | .listCode _
          | .optionCode _ | .eitherCode _ _ | .idCode _ _ _ | .equivCode _ _
          | .cumulUpMarker _ | .uaToEquiv _ | .equivApply _ _ | .pathCompose _ _
          | .idToEquiv _ | .oeqTrans _ _ | .equivCompose _ _ =>
              exact RawStep.par.equivApplyCong equivIH argIH
      | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
      | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
      | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
      | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
      | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .refl _
      | .idJ _ _ | .modIntro _ | .modElim _ | .subsume _
      | .interval0 | .interval1 | .intervalOpp _ | .intervalMeet _ _
      | .intervalJoin _ _ | .pathLam _ | .pathApp _ _ | .glueIntro _ _
      | .glueElim _ | .transp _ _ | .transpFill _ _ _
      | .hcomp _ _ | .oeqRefl _ | .oeqJ _ _
      | .oeqFunext _ | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _
      | .equivApp _ _ | .refineIntro _ _ | .refineElim _ | .recordIntro _
      | .recordProj _ | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _
      | .sessionRecv _ | .effectPerform _ _ | .universeCode _ | .arrowCode _ _
      | .piTyCode _ _ | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _
      | .listCode _ | .optionCode _ | .eitherCode _ _ | .idCode _ _ _
      | .equivCode _ _ | .cumulUpMarker _ | .equivApply _ _ | .pathCompose _ _
      | .idToEquiv _ | .oeqTrans _ _ | .equivCompose _ _ =>
          rw [hCdEquiv] at equivIH
          exact RawStep.par.equivApplyCong equivIH argIH
  | pathComposeCong _ _ leftIH rightIH =>
      exact RawStep.par.cd_lemma_pathComposeCong leftIH rightIH
  | @transpCompose _ leftRawSource _ rightRawSource _ _ _
                   leftStep rightStep sourceStep
                   leftIH rightIH sourceIH =>
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      exact RawStep.par.transpCong rightIH (RawStep.par.transpCong leftIH sourceIH)
  | @transpComposeDeep _ pathRawSource _ _ _ _
                       pathStep sourceStep pathIH sourceIH =>
      obtain ⟨leftInner, rightInner, cdPathEq, leftParStep, rightParStep⟩ :=
        RawStep.par.pathCompose_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      exact RawStep.par.transpCong rightParStep
        (RawStep.par.transpCong leftParStep sourceIH)
  | @idToEquivCong _ proofRawSource _ _ proofIH =>
      simp only [RawTerm.cd]
      match hCd : RawTerm.cd proofRawSource with
      | .refl witnessRaw =>
          rw [hCd] at proofIH
          show RawStep.par (RawTerm.idToEquiv _)
                           (RawTerm.cdIdToEquivCase (RawTerm.refl witnessRaw))
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivReflDeep proofIH
      | .oeqTrans firstRaw secondRaw =>
          rw [hCd] at proofIH
          show RawStep.par (RawTerm.idToEquiv _)
                           (RawTerm.cdIdToEquivCase
                             (RawTerm.oeqTrans firstRaw secondRaw))
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivComposeDeep proofIH
      | .var _ | .unit | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
      | .boolTrue | .boolFalse | .boolElim _ _ _ | .natZero | .natSucc _
      | .natElim _ _ _ | .natRec _ _ _ | .listNil | .listCons _ _
      | .listElim _ _ _ | .optionNone | .optionSome _ | .optionMatch _ _ _
      | .eitherInl _ | .eitherInr _ | .eitherMatch _ _ _ | .idJ _ _
      | .modIntro _ | .modElim _ | .subsume _ | .interval0 | .interval1
      | .intervalOpp _ | .intervalMeet _ _ | .intervalJoin _ _
      | .pathLam _ | .pathApp _ _ | .glueIntro _ _ | .glueElim _
      | .transp _ _ | .transpFill _ _ _
      | .hcomp _ _ | .oeqRefl _ | .oeqJ _ _ | .oeqFunext _
      | .idStrictRefl _ | .idStrictRec _ _ | .equivIntro _ _ | .equivApp _ _
      | .refineIntro _ _ | .refineElim _ | .recordIntro _ | .recordProj _
      | .codataUnfold _ _ | .codataDest _ | .sessionSend _ _ | .sessionRecv _
      | .effectPerform _ _ | .universeCode _ | .arrowCode _ _ | .piTyCode _ _
      | .sigmaTyCode _ _ | .productCode _ _ | .sumCode _ _ | .listCode _
      | .optionCode _ | .eitherCode _ _ | .idCode _ _ _ | .equivCode _ _
      | .cumulUpMarker _ | .uaToEquiv _ | .equivApply _ _ | .pathCompose _ _
      | .idToEquiv _ | .equivCompose _ _ =>
          rw [hCd] at proofIH
          show RawStep.par (RawTerm.idToEquiv _)
                           (RawTerm.cdIdToEquivCase _)
          unfold RawTerm.cdIdToEquivCase
          exact RawStep.par.idToEquivCong proofIH
  | @idToEquivRefl _ witnessSource _ witnessStep witnessIH =>
      simp only [RawTerm.cd, RawTerm.cdIdToEquivCase]
      exact RawStep.par.refl _
  | @idToEquivReflDeep _ proofRawSource _ proofStep proofIH =>
      obtain ⟨witnessFinal, hCdEq, _witnessStep⟩ :=
        RawStep.par.refl_inv proofIH
      simp only [RawTerm.cd]
      rw [hCdEq]
      simp only [RawTerm.cdIdToEquivCase]
      exact RawStep.par.refl _
  | oeqTransCong _ _ firstIH secondIH =>
      exact RawStep.par.cd_lemma_oeqTransCong firstIH secondIH
  | equivComposeCong _ _ firstIH secondIH =>
      exact RawStep.par.cd_lemma_equivComposeCong firstIH secondIH
  | @idToEquivCompose _ firstSource _ secondSource _ firstStep secondStep firstIH secondIH =>
      simp only [RawTerm.cd, RawTerm.cdIdToEquivCase]
      exact RawStep.par.equivComposeCong
        (RawStep.par.idToEquivCong firstIH)
        (RawStep.par.idToEquivCong secondIH)
  | @idToEquivComposeDeep _ proofRawSource firstTarget secondTarget proofStep proofIH =>
      obtain ⟨firstFinal, secondFinal, hCdEq, firstStep, secondStep⟩ :=
        RawStep.par.oeqTrans_inv proofIH
      simp only [RawTerm.cd]
      rw [hCdEq]
      simp only [RawTerm.cdIdToEquivCase]
      exact RawStep.par.equivComposeCong
        (RawStep.par.idToEquivCong firstStep)
        (RawStep.par.idToEquivCong secondStep)
  | @uaReflEquivApply _ witnessSource _ sourceRawSource sourceRawTarget
      _ _ _ sourceIH =>
      simp only [RawTerm.cd, RawTerm.cdEquivApplyCase,
        RawTerm.cdUaToEquivApplyCase]
      exact sourceIH
  | @uaReflEquivApplyDeep _ equivRawSource _ sourceRawSource sourceRawTarget
      _ _ equivIH sourceIH =>
      obtain ⟨innerCd, hCdEquivEq, innerStep⟩ :=
        RawStep.par.uaToEquiv_inv equivIH
      obtain ⟨witnessFinal, hInnerEq, _witnessStep⟩ :=
        RawStep.par.oeqRefl_inv innerStep
      simp only [RawTerm.cd]
      rw [hCdEquivEq, hInnerEq]
      simp only [RawTerm.cdEquivApplyCase, RawTerm.cdUaToEquivApplyCase]
      exact sourceIH

end LeanFX2

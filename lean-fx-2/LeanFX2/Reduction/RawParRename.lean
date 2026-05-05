import LeanFX2.Reduction.RawPar
import LeanFX2.Foundation.RawSubst

/-! # Reduction/RawParRename — RawStep.par closed under renaming

Renaming compatibility for `RawStep.par`: applying a fixed
`RawRenaming` to both source and target preserves the parallel
reduction.

```lean
theorem RawStep.par.rename
    (rho : RawRenaming scope targetScope) :
    RawStep.par t t' →
    RawStep.par (t.rename rho) (t'.rename rho)
```

Mirrors lean-fx's `RawStep.par.rename` from `RawParCompatible.lean`,
extended with cong cases for the 3 modal ctors (modIntro, modElim,
subsume) absent in lean-fx.

## Proof shape

Induction on the parallel-step derivation; 53 cases.  Cong cases
descend via IH.  β cases use `RawTerm.subst0_rename_commute`
(Foundation) to reshape the renamed body.subst0 before applying the
β rule on the renamed body / argument IHs.

## Zero-axiom

Each case is `simp only [RawTerm.rename]; exact <ctor> ihs`.  No
propext leaks because RawTerm and RawStep.par are single-Nat-indexed.
-/

namespace LeanFX2

/-- `RawStep.par` is closed under arbitrary `RawRenaming`. -/
theorem RawStep.par.rename {scope targetScope : Nat}
    (rawRenaming : RawRenaming scope targetScope)
    {beforeTerm afterTerm : RawTerm scope} :
    RawStep.par beforeTerm afterTerm →
    RawStep.par (beforeTerm.rename rawRenaming)
                (afterTerm.rename rawRenaming) := by
  intro parallelStep
  induction parallelStep generalizing targetScope with
  -- Reflexivity
  | refl _ => exact RawStep.par.refl _
  -- Cong cases
  | lam _ bodyIH => exact RawStep.par.lam (bodyIH _)
  | app _ _ functionIH argumentIH =>
      exact RawStep.par.app (functionIH _) (argumentIH _)
  | pair _ _ firstIH secondIH =>
      exact RawStep.par.pair (firstIH _) (secondIH _)
  | fst _ pairIH => exact RawStep.par.fst (pairIH _)
  | snd _ pairIH => exact RawStep.par.snd (pairIH _)
  | boolElim _ _ _ scrutineeIH thenIH elseIH =>
      exact RawStep.par.boolElim (scrutineeIH _) (thenIH _) (elseIH _)
  | natSucc _ predecessorIH =>
      exact RawStep.par.natSucc (predecessorIH _)
  | natElim _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natElim (scrutineeIH _) (zeroIH _) (succIH _)
  | natRec _ _ _ scrutineeIH zeroIH succIH =>
      exact RawStep.par.natRec (scrutineeIH _) (zeroIH _) (succIH _)
  | listCons _ _ headIH tailIH =>
      exact RawStep.par.listCons (headIH _) (tailIH _)
  | listElim _ _ _ scrutineeIH nilIH consIH =>
      exact RawStep.par.listElim (scrutineeIH _) (nilIH _) (consIH _)
  | optionSome _ valueIH => exact RawStep.par.optionSome (valueIH _)
  | optionMatch _ _ _ scrutineeIH noneIH someIH =>
      exact RawStep.par.optionMatch (scrutineeIH _) (noneIH _) (someIH _)
  | eitherInl _ valueIH => exact RawStep.par.eitherInl (valueIH _)
  | eitherInr _ valueIH => exact RawStep.par.eitherInr (valueIH _)
  | eitherMatch _ _ _ scrutineeIH leftIH rightIH =>
      exact RawStep.par.eitherMatch (scrutineeIH _) (leftIH _) (rightIH _)
  | reflCong _ witnessIH => exact RawStep.par.reflCong (witnessIH _)
  | idJ _ _ baseIH witnessIH =>
      exact RawStep.par.idJ (baseIH _) (witnessIH _)
  | modIntro _ innerIH => exact RawStep.par.modIntro (innerIH _)
  | modElim _ innerIH => exact RawStep.par.modElim (innerIH _)
  | subsume _ innerIH => exact RawStep.par.subsume (innerIH _)
  -- Shallow β rules: contractum side requires reshape via subst0_rename_commute.
  | betaApp _ _ bodyIH argumentIH =>
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute _ _ rawRenaming]
      exact RawStep.par.betaApp (bodyIH _) (argumentIH _)
  | betaFstPair secondValue _ firstIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaFstPair (RawTerm.rename secondValue rawRenaming)
        (firstIH _)
  | betaSndPair firstValue _ secondIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaSndPair (RawTerm.rename firstValue rawRenaming)
        (secondIH _)
  -- Shallow ι rules: simp + ctor with renamed extra branches.
  | iotaBoolElimTrue elseBranch _ thenIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimTrue
        (RawTerm.rename elseBranch rawRenaming) (thenIH _)
  | iotaBoolElimFalse thenBranch _ elseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimFalse
        (RawTerm.rename thenBranch rawRenaming) (elseIH _)
  | iotaNatElimZero succBranch _ zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimZero
        (RawTerm.rename succBranch rawRenaming) (zeroIH _)
  | iotaNatElimSucc zeroBranch _ _ predecessorIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimSucc
        (RawTerm.rename zeroBranch rawRenaming) (predecessorIH _) (succIH _)
  | iotaNatRecZero succBranch _ zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecZero
        (RawTerm.rename succBranch rawRenaming) (zeroIH _)
  | iotaNatRecSucc _ _ _ predecessorIH zeroIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecSucc (predecessorIH _) (zeroIH _) (succIH _)
  | iotaListElimNil consBranch _ nilIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimNil
        (RawTerm.rename consBranch rawRenaming) (nilIH _)
  | iotaListElimCons nilBranch _ _ _ headIH tailIH consIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimCons
        (RawTerm.rename nilBranch rawRenaming)
        (headIH _) (tailIH _) (consIH _)
  | iotaOptionMatchNone someBranch _ noneIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchNone
        (RawTerm.rename someBranch rawRenaming) (noneIH _)
  | iotaOptionMatchSome noneBranch _ _ valueIH someIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchSome
        (RawTerm.rename noneBranch rawRenaming) (valueIH _) (someIH _)
  | iotaEitherMatchInl rightBranch _ _ valueIH leftIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInl
        (RawTerm.rename rightBranch rawRenaming) (valueIH _) (leftIH _)
  | iotaEitherMatchInr leftBranch _ _ valueIH rightIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInr
        (RawTerm.rename leftBranch rawRenaming) (valueIH _) (rightIH _)
  | iotaIdJRefl witnessRaw _ baseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaIdJRefl
        (RawTerm.rename witnessRaw rawRenaming) (baseIH _)
  -- Deep β rules.
  | betaAppDeep _ _ functionIH argumentIH =>
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute _ _ rawRenaming]
      exact RawStep.par.betaAppDeep (functionIH _) (argumentIH _)
  | betaFstPairDeep _ pairIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaFstPairDeep (pairIH _)
  | betaSndPairDeep _ pairIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaSndPairDeep (pairIH _)
  -- Deep ι rules.
  | iotaBoolElimTrueDeep elseBranch _ _ scrutineeIH thenIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimTrueDeep
        (RawTerm.rename elseBranch rawRenaming) (scrutineeIH _) (thenIH _)
  | iotaBoolElimFalseDeep thenBranch _ _ scrutineeIH elseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaBoolElimFalseDeep
        (RawTerm.rename thenBranch rawRenaming) (scrutineeIH _) (elseIH _)
  | iotaNatElimZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimZeroDeep
        (RawTerm.rename succBranch rawRenaming) (scrutineeIH _) (zeroIH _)
  | iotaNatElimSuccDeep zeroBranch _ _ scrutineeIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatElimSuccDeep
        (RawTerm.rename zeroBranch rawRenaming) (scrutineeIH _) (succIH _)
  | iotaNatRecZeroDeep succBranch _ _ scrutineeIH zeroIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecZeroDeep
        (RawTerm.rename succBranch rawRenaming) (scrutineeIH _) (zeroIH _)
  | iotaNatRecSuccDeep _ _ _ scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaNatRecSuccDeep
        (scrutineeIH _) (zeroIH _) (succIH _)
  | iotaListElimNilDeep consBranch _ _ scrutineeIH nilIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimNilDeep
        (RawTerm.rename consBranch rawRenaming) (scrutineeIH _) (nilIH _)
  | iotaListElimConsDeep nilBranch _ _ scrutineeIH consIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaListElimConsDeep
        (RawTerm.rename nilBranch rawRenaming) (scrutineeIH _) (consIH _)
  | iotaOptionMatchNoneDeep someBranch _ _ scrutineeIH noneIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchNoneDeep
        (RawTerm.rename someBranch rawRenaming) (scrutineeIH _) (noneIH _)
  | iotaOptionMatchSomeDeep noneBranch _ _ scrutineeIH someIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaOptionMatchSomeDeep
        (RawTerm.rename noneBranch rawRenaming) (scrutineeIH _) (someIH _)
  | iotaEitherMatchInlDeep rightBranch _ _ scrutineeIH leftIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInlDeep
        (RawTerm.rename rightBranch rawRenaming) (scrutineeIH _) (leftIH _)
  | iotaEitherMatchInrDeep leftBranch _ _ scrutineeIH rightIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaEitherMatchInrDeep
        (RawTerm.rename leftBranch rawRenaming) (scrutineeIH _) (rightIH _)
  | iotaIdJReflDeep _ _ witnessIH baseIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.iotaIdJReflDeep (witnessIH _) (baseIH _)
  -- D1.6 cong rules for the 27 new RawTerm ctors (pure cong; no β/ι).
  | intervalOppCong _ intervalIH =>
      exact RawStep.par.intervalOppCong (intervalIH _)
  | intervalMeetCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalMeetCong (leftIH _) (rightIH _)
  | intervalJoinCong _ _ leftIH rightIH =>
      exact RawStep.par.intervalJoinCong (leftIH _) (rightIH _)
  | pathLamCong _ bodyIH =>
      exact RawStep.par.pathLamCong (bodyIH _)
  | pathAppCong _ _ pathIH intervalIH =>
      exact RawStep.par.pathAppCong (pathIH _) (intervalIH _)
  | betaPathApp _ _ bodyIH intervalIH =>
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute _ _ rawRenaming]
      exact RawStep.par.betaPathApp (bodyIH _) (intervalIH _)
  | betaPathAppDeep _ _ pathIH intervalIH =>
      simp only [RawTerm.rename]
      rw [RawTerm.subst0_rename_commute _ _ rawRenaming]
      exact RawStep.par.betaPathAppDeep (pathIH _) (intervalIH _)
  | glueIntroCong _ _ baseIH partialIH =>
      exact RawStep.par.glueIntroCong (baseIH _) (partialIH _)
  | betaGlueElimIntro _ _ baseIH partialIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaGlueElimIntro (baseIH _) (partialIH _)
  | betaGlueElimIntroDeep _ gluedIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaGlueElimIntroDeep (gluedIH _)
  | glueElimCong _ gluedIH =>
      exact RawStep.par.glueElimCong (gluedIH _)
  | transpCong _ _ pathIH sourceIH =>
      exact RawStep.par.transpCong (pathIH _) (sourceIH _)
  | hcompCong _ _ sidesIH capIH =>
      exact RawStep.par.hcompCong (sidesIH _) (capIH _)
  | oeqReflCong _ witnessIH =>
      exact RawStep.par.oeqReflCong (witnessIH _)
  | oeqJCong _ _ baseIH witnessIH =>
      exact RawStep.par.oeqJCong (baseIH _) (witnessIH _)
  | oeqFunextCong _ pointwiseIH =>
      exact RawStep.par.oeqFunextCong (pointwiseIH _)
  | idStrictReflCong _ witnessIH =>
      exact RawStep.par.idStrictReflCong (witnessIH _)
  | idStrictRecCong _ _ baseIH witnessIH =>
      exact RawStep.par.idStrictRecCong (baseIH _) (witnessIH _)
  | equivIntroCong _ _ forwardIH backwardIH =>
      exact RawStep.par.equivIntroCong (forwardIH _) (backwardIH _)
  | equivAppCong _ _ equivIH argumentIH =>
      exact RawStep.par.equivAppCong (equivIH _) (argumentIH _)
  | refineIntroCong _ _ valueIH proofIH =>
      exact RawStep.par.refineIntroCong (valueIH _) (proofIH _)
  | betaRefineElimIntro _ _ valueIH proofIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaRefineElimIntro (valueIH _) (proofIH _)
  | betaRefineElimIntroDeep _ refinedIH =>
      simp only [RawTerm.rename]
      exact RawStep.par.betaRefineElimIntroDeep (refinedIH _)
  | refineElimCong _ refinedIH =>
      exact RawStep.par.refineElimCong (refinedIH _)
  | recordIntroCong _ firstIH =>
      exact RawStep.par.recordIntroCong (firstIH _)
  | recordProjCong _ recordIH =>
      exact RawStep.par.recordProjCong (recordIH _)
  | codataUnfoldCong _ _ stateIH transitionIH =>
      exact RawStep.par.codataUnfoldCong (stateIH _) (transitionIH _)
  | codataDestCong _ codataIH =>
      exact RawStep.par.codataDestCong (codataIH _)
  | sessionSendCong _ _ channelIH payloadIH =>
      exact RawStep.par.sessionSendCong (channelIH _) (payloadIH _)
  | sessionRecvCong _ channelIH =>
      exact RawStep.par.sessionRecvCong (channelIH _)
  | effectPerformCong _ _ operationIH argumentsIH =>
      exact RawStep.par.effectPerformCong (operationIH _) (argumentsIH _)
  -- CUMUL-2.1 per-shape type-code cong rules.  Each arm threads
  -- `rawRenaming` through the appropriate `*CodeCong` constructor.
  -- Binder-shape ctors (`piTyCodeCong`, `sigmaTyCodeCong`) recurse
  -- with `rawRenaming.lift` automatically since the IH was set up
  -- by `induction parallelStep generalizing targetScope` over the
  -- body — the unifier picks up the lifted scope from the codomain
  -- argument.
  | arrowCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.arrowCodeCong (domainIH _) (codomainIH _)
  | piTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.piTyCodeCong (domainIH _) (codomainIH _)
  | sigmaTyCodeCong _ _ domainIH codomainIH =>
      exact RawStep.par.sigmaTyCodeCong (domainIH _) (codomainIH _)
  | productCodeCong _ _ firstIH secondIH =>
      exact RawStep.par.productCodeCong (firstIH _) (secondIH _)
  | sumCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.sumCodeCong (leftIH _) (rightIH _)
  | listCodeCong _ elementIH =>
      exact RawStep.par.listCodeCong (elementIH _)
  | optionCodeCong _ elementIH =>
      exact RawStep.par.optionCodeCong (elementIH _)
  | eitherCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.eitherCodeCong (leftIH _) (rightIH _)
  | idCodeCong _ _ _ typeIH leftIH rightIH =>
      exact RawStep.par.idCodeCong (typeIH _) (leftIH _) (rightIH _)
  | equivCodeCong _ _ leftIH rightIH =>
      exact RawStep.par.equivCodeCong (leftIH _) (rightIH _)
  | cumulUpMarkerCong _ innerIH =>
      exact RawStep.par.cumulUpMarkerCong (innerIH _)

end LeanFX2

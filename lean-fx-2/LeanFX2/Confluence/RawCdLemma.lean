import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # Confluence/RawCdLemma — every parallel reduct lands in `RawTerm.cd`

`RawStep.par.cd_lemma`: `RawStep.par s s' → RawStep.par s' (RawTerm.cd s)`.

Together with `cd_dominates` (`par t (cd t)` for all t), this is
the Tait–Martin-Löf complete-development pair: `cd s` is the
join point of all parallel reductions from `s`.  Diamond and
confluence follow via the strip-lemma argument (Layer 6.C).

Proof shape: induction on the parallel-step derivation.

* `refl t`: `cd_dominates t` directly.
* Pure cong (lam/pair/listCons/optionSome/eitherInl/Inr/natSucc
  /reflCong/modIntro/modElim/subsume): apply cong rule with IHs.
* Redex-bearing cong (app/pathApp/glueElim/refineElim/fst/snd
  /boolElim/natElim/natRec/listElim/optionMatch/eitherMatch/idJ):
  unfold cd via simp + split.  Redex arms fire the deep rule with
  `heq ▸ IH`; cong fallthrough closes via `all_goals`.
* Shallow β: cd contracts the same redex; `subst0_par` for
  betaApp; direct IH for betaFst/SndPair.
* Shallow ι: cd contracts the redex; pick the appropriate IH or
  rebuild via cong.
* Deep β/ι: invert the deep premise's IH via Phase 6.B.1
  inversion lemmas to extract redex shape, then close as for
  the shallow case.

## Modal cases

`modIntro`/`modElim`/`subsume` are pure cong with IHs that lift
to cd — one-line proofs (no inversion, no β/ι).
-/

namespace LeanFX2

theorem RawStep.par.cd_lemma {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope} :
    RawStep.par sourceTerm targetTerm →
    RawStep.par targetTerm (RawTerm.cd sourceTerm) := by
  intro parallelStep
  induction parallelStep with
  | refl t => exact RawStep.par.cd_dominates t
  | lam bodyStep bodyIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.lam bodyIH
  | app functionStep argumentStep functionIH argumentIH =>
      simp only [RawTerm.cd, RawTerm.cdAppCase]
      split
      case _ body cdFunctionEq =>
          exact RawStep.par.betaAppDeep
            (cdFunctionEq ▸ functionIH) argumentIH
      all_goals exact RawStep.par.app functionIH argumentIH
  | pair firstStep secondStep firstIH secondIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.pair firstIH secondIH
  | fst pairStep pairIH =>
      simp only [RawTerm.cd, RawTerm.cdFstCase]
      split
      case _ firstVal secondVal cdPairEq =>
          exact RawStep.par.betaFstPairDeep (cdPairEq ▸ pairIH)
      all_goals exact RawStep.par.fst pairIH
  | snd pairStep pairIH =>
      simp only [RawTerm.cd, RawTerm.cdSndCase]
      split
      case _ firstVal secondVal cdPairEq =>
          exact RawStep.par.betaSndPairDeep (cdPairEq ▸ pairIH)
      all_goals exact RawStep.par.snd pairIH
  | boolElim scrutineeStep thenStep elseStep
        scrutineeIH thenIH elseIH =>
      simp only [RawTerm.cd, RawTerm.cdBoolElimCase]
      split
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaBoolElimTrueDeep _
            (cdScrutineeEq ▸ scrutineeIH) thenIH
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaBoolElimFalseDeep _
            (cdScrutineeEq ▸ scrutineeIH) elseIH
      all_goals exact RawStep.par.boolElim scrutineeIH thenIH elseIH
  | natSucc predStep predIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.natSucc predIH
  | natElim scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.cd, RawTerm.cdNatElimCase]
      split
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaNatElimZeroDeep _
            (cdScrutineeEq ▸ scrutineeIH) zeroIH
      case _ pred cdScrutineeEq =>
          exact RawStep.par.iotaNatElimSuccDeep _
            (cdScrutineeEq ▸ scrutineeIH) succIH
      all_goals exact RawStep.par.natElim scrutineeIH zeroIH succIH
  | natRec scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.cd, RawTerm.cdNatRecCase]
      split
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaNatRecZeroDeep _
            (cdScrutineeEq ▸ scrutineeIH) zeroIH
      case _ pred cdScrutineeEq =>
          exact RawStep.par.iotaNatRecSuccDeep
            (cdScrutineeEq ▸ scrutineeIH) zeroIH succIH
      all_goals exact RawStep.par.natRec scrutineeIH zeroIH succIH
  | listCons headStep tailStep headIH tailIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.listCons headIH tailIH
  | listElim scrutineeStep nilStep consStep
        scrutineeIH nilIH consIH =>
      simp only [RawTerm.cd, RawTerm.cdListElimCase]
      split
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaListElimNilDeep _
            (cdScrutineeEq ▸ scrutineeIH) nilIH
      case _ head tail cdScrutineeEq =>
          exact RawStep.par.iotaListElimConsDeep _
            (cdScrutineeEq ▸ scrutineeIH) consIH
      all_goals exact RawStep.par.listElim scrutineeIH nilIH consIH
  | optionSome valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.optionSome valueIH
  | optionMatch scrutineeStep noneStep someStep
        scrutineeIH noneIH someIH =>
      simp only [RawTerm.cd, RawTerm.cdOptionMatchCase]
      split
      case _ cdScrutineeEq =>
          exact RawStep.par.iotaOptionMatchNoneDeep _
            (cdScrutineeEq ▸ scrutineeIH) noneIH
      case _ value cdScrutineeEq =>
          exact RawStep.par.iotaOptionMatchSomeDeep _
            (cdScrutineeEq ▸ scrutineeIH) someIH
      all_goals exact RawStep.par.optionMatch scrutineeIH noneIH someIH
  | eitherInl valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInl valueIH
  | eitherInr valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInr valueIH
  | eitherMatch scrutineeStep leftStep rightStep
        scrutineeIH leftIH rightIH =>
      simp only [RawTerm.cd, RawTerm.cdEitherMatchCase]
      split
      case _ value cdScrutineeEq =>
          exact RawStep.par.iotaEitherMatchInlDeep _
            (cdScrutineeEq ▸ scrutineeIH) leftIH
      case _ value cdScrutineeEq =>
          exact RawStep.par.iotaEitherMatchInrDeep _
            (cdScrutineeEq ▸ scrutineeIH) rightIH
      all_goals exact RawStep.par.eitherMatch scrutineeIH leftIH rightIH
  | reflCong rawTermStep rawTermIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.reflCong rawTermIH
  | funextReflCong applyStep applyIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.funextReflCong applyIH
  | funextReflAtIdCong applyStep applyIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.funextReflAtIdCong applyIH
  | funextIntroHetCong applyAStep applyAIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.funextIntroHetCong applyAIH
  | idJ baseStep witnessStep baseIH witnessIH =>
      simp only [RawTerm.cd, RawTerm.cdIdJCase]
      split
      case _ rawTerm cdWitnessEq =>
          exact RawStep.par.iotaIdJReflDeep
            (cdWitnessEq ▸ witnessIH) baseIH
      all_goals exact RawStep.par.idJ baseIH witnessIH
  -- Modal cong rules: pure cong, no redex, IH lifts directly.
  | modIntro innerStep innerIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.modIntro innerIH
  | modElim innerStep innerIH =>
      simp only [RawTerm.cd, RawTerm.cdModElimCase]
      split
      case _ payloadTarget innerEqn =>
          exact RawStep.par.betaModElimIntroDeep
            (innerEqn ▸ innerIH)
      all_goals exact RawStep.par.modElim innerIH
  | betaModElimIntro innerStep innerIH =>
      simp only [RawTerm.cd, RawTerm.cdModElimCase]
      exact innerIH
  | betaModElimIntroDeep innerStep innerIH =>
      simp only [RawTerm.cd, RawTerm.cdModElimCase]
      obtain ⟨payloadAfter, cdInnerEq, payloadParStep⟩ :=
        RawStep.par.modIntro_inv innerIH
      rw [cdInnerEq]
      exact payloadParStep
  | subsume innerStep innerIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.subsume innerIH
  -- Shallow β: cd contracts the same redex via subst0_par.
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.subst0_par bodyIH argumentIH
  | betaFstPair secondVal firstStep firstIH =>
      simp only [RawTerm.cd]
      exact firstIH
  | betaSndPair firstVal secondStep secondIH =>
      simp only [RawTerm.cd]
      exact secondIH
  -- Shallow ι: cd contracts the same redex; close via the
  -- appropriate IH.
  | iotaBoolElimTrue elseBranch thenStep thenIH =>
      simp only [RawTerm.cd]
      exact thenIH
  | iotaBoolElimFalse thenBranch elseStep elseIH =>
      simp only [RawTerm.cd]
      exact elseIH
  | iotaNatElimZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.cd]
      exact zeroIH
  | iotaNatElimSucc zeroBranch predStep succStep predIH succIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app succIH predIH
  | iotaNatRecZero succBranch zeroStep zeroIH =>
      simp only [RawTerm.cd]
      exact zeroIH
  | iotaNatRecSucc predStep zeroStep succStep predIH zeroIH succIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app
        (RawStep.par.app succIH predIH)
        (RawStep.par.natRec predIH zeroIH succIH)
  | iotaListElimNil consBranch nilStep nilIH =>
      simp only [RawTerm.cd]
      exact nilIH
  | iotaListElimCons nilBranch headStep tailStep consStep
        headIH tailIH consIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app
        (RawStep.par.app consIH headIH) tailIH
  | iotaOptionMatchNone someBranch noneStep noneIH =>
      simp only [RawTerm.cd]
      exact noneIH
  | iotaOptionMatchSome noneBranch valueStep someStep valueIH someIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app someIH valueIH
  | iotaEitherMatchInl rightBranch valueStep leftStep valueIH leftIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app leftIH valueIH
  | iotaEitherMatchInr leftBranch valueStep rightStep valueIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.app rightIH valueIH
  | iotaIdJRefl rawTerm baseStep baseIH =>
      simp only [RawTerm.cd]
      exact baseIH
  | iotaIdStrictRecRefl rawTerm baseStep baseIH =>
      simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
      exact baseIH
  -- Deep β: invert IH on deep premise to extract redex shape.
  | betaAppDeep functionStep argumentStep functionIH argumentIH =>
      simp only [RawTerm.cd]
      obtain ⟨bodyAfter, cdFunctionEq, bodyParStep⟩ :=
        RawStep.par.lam_inv functionIH
      rw [cdFunctionEq]
      exact RawStep.par.subst0_par bodyParStep argumentIH
  | betaPathApp bodyStep intervalStep bodyIH intervalIH =>
      simp only [RawTerm.cd, RawTerm.cdPathAppCase]
      exact RawStep.par.subst0_par bodyIH intervalIH
  | betaPathAppDeep pathStep intervalStep pathIH intervalIH =>
      simp only [RawTerm.cd, RawTerm.cdPathAppCase]
      obtain ⟨bodyAfter, cdPathEq, bodyParStep⟩ :=
        RawStep.par.pathLam_inv pathIH
      rw [cdPathEq]
      exact RawStep.par.subst0_par bodyParStep intervalIH
  | betaPathReflApp valueStep intervalStep valueIH intervalIH =>
      -- Source: pathApp (pathLam valueRawSource.weaken) intervalRawSource.
      -- Target: valueRawTarget.
      -- valueIH : par valueRawTarget (cd valueRawSource)
      -- intervalIH : par intervalRawTarget (cd intervalRawSource)
      -- Goal: par valueRawTarget
      --   (cd (pathApp (pathLam valueRawSource.weaken) intervalRawSource))
      --   = par valueRawTarget
      --     (cdPathAppCase (cd (pathLam valueRawSource.weaken)) (cd intervalRawSource))
      --   = par valueRawTarget
      --     (cdPathAppCase (pathLam (cd valueRawSource.weaken)) (cd intervalRawSource))
      --   = par valueRawTarget
      --     ((cd valueRawSource.weaken).subst0 (cd intervalRawSource))
      -- By RawTerm.cd_weaken: cd valueRawSource.weaken = (cd valueRawSource).weaken.
      -- Then (cd valueRawSource).weaken.subst0 (cd intervalRawSource) =
      --   cd valueRawSource (by RawTerm.weaken_subst_singleton).
      -- Goal collapses to par valueRawTarget (cd valueRawSource) = valueIH.
      simp only [RawTerm.cd, RawTerm.cdPathAppCase, RawTerm.cd_weaken,
                 RawTerm.weaken_subst_singleton]
      exact valueIH
  | betaFstPairDeep pairStep pairIH =>
      simp only [RawTerm.cd]
      obtain ⟨firstAfter, secondAfter, cdPairEq, firstParStep, _⟩ :=
        RawStep.par.pair_inv pairIH
      rw [cdPairEq]
      exact firstParStep
  | betaSndPairDeep pairStep pairIH =>
      simp only [RawTerm.cd]
      obtain ⟨firstAfter, secondAfter, cdPairEq, _, secondParStep⟩ :=
        RawStep.par.pair_inv pairIH
      rw [cdPairEq]
      exact secondParStep
  -- Deep ι: invert scrutinee/witness IH to extract canonical shape.
  | iotaBoolElimTrueDeep elseBranch scrutineeStep thenStep
        scrutineeIH thenIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.boolTrue_inv scrutineeIH
      rw [cdScrutinee]
      exact thenIH
  | iotaBoolElimFalseDeep thenBranch scrutineeStep elseStep
        scrutineeIH elseIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.boolFalse_inv scrutineeIH
      rw [cdScrutinee]
      exact elseIH
  | iotaNatElimZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.natZero_inv scrutineeIH
      rw [cdScrutinee]
      exact zeroIH
  | iotaNatElimSuccDeep zeroBranch scrutineeStep succStep
        scrutineeIH succIH =>
      simp only [RawTerm.cd]
      obtain ⟨predAfter, cdScrutineeEq, predParStep⟩ :=
        RawStep.par.natSucc_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app succIH predParStep
  | iotaNatRecZeroDeep succBranch scrutineeStep zeroStep
        scrutineeIH zeroIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.natZero_inv scrutineeIH
      rw [cdScrutinee]
      exact zeroIH
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.cd]
      obtain ⟨predAfter, cdScrutineeEq, predParStep⟩ :=
        RawStep.par.natSucc_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app
        (RawStep.par.app succIH predParStep)
        (RawStep.par.natRec predParStep zeroIH succIH)
  | iotaListElimNilDeep consBranch scrutineeStep nilStep
        scrutineeIH nilIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.listNil_inv scrutineeIH
      rw [cdScrutinee]
      exact nilIH
  | iotaListElimConsDeep nilBranch scrutineeStep consStep
        scrutineeIH consIH =>
      simp only [RawTerm.cd]
      obtain ⟨headAfter, tailAfter, cdScrutineeEq, headParStep, tailParStep⟩ :=
        RawStep.par.listCons_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app
        (RawStep.par.app consIH headParStep) tailParStep
  | iotaOptionMatchNoneDeep someBranch scrutineeStep noneStep
        scrutineeIH noneIH =>
      simp only [RawTerm.cd]
      have cdScrutinee := RawStep.par.optionNone_inv scrutineeIH
      rw [cdScrutinee]
      exact noneIH
  | iotaOptionMatchSomeDeep noneBranch scrutineeStep someStep
        scrutineeIH someIH =>
      simp only [RawTerm.cd]
      obtain ⟨valueAfter, cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.optionSome_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app someIH valueParStep
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      simp only [RawTerm.cd]
      obtain ⟨valueAfter, cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.eitherInl_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app leftIH valueParStep
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      simp only [RawTerm.cd]
      obtain ⟨valueAfter, cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.eitherInr_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app rightIH valueParStep
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      simp only [RawTerm.cd]
      obtain ⟨witnessAfter, cdWitnessEq, _⟩ :=
        RawStep.par.refl_inv witnessIH
      rw [cdWitnessEq]
      exact baseIH
  | iotaIdStrictRecReflDeep witnessStep baseStep witnessIH baseIH =>
      simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
      obtain ⟨witnessAfter, cdWitnessEq, _⟩ :=
        RawStep.par.idStrictRefl_inv witnessIH
      rw [cdWitnessEq]
      exact baseIH
  -- D1.6/D2.5/D2.7: most new raw ctors are pure cong. pathApp,
  -- glueElim, and refineElim also have β, so their cong proofs split
  -- on the developed head.
  | intervalOppCong _ intervalIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.intervalOppCong intervalIH
  | intervalMeetCong _ _ leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.intervalMeetCong leftIH rightIH
  | intervalJoinCong _ _ leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.intervalJoinCong leftIH rightIH
  | pathLamCong _ bodyIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.pathLamCong bodyIH
  | pathAppCong _ _ pathIH intervalIH =>
      simp only [RawTerm.cd, RawTerm.cdPathAppCase]
      split
      case _ bodyRawTarget pathEqn =>
          exact RawStep.par.betaPathAppDeep
            (pathEqn ▸ pathIH) intervalIH
      all_goals exact RawStep.par.pathAppCong pathIH intervalIH
  | glueIntroCong _ _ baseIH partialIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.glueIntroCong baseIH partialIH
  | betaGlueElimIntro baseStep partialStep baseIH partialIH =>
      simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
      exact baseIH
  | betaGlueElimIntroDeep gluedStep gluedIH =>
      simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
      obtain ⟨baseAfter, partialAfter, cdGluedEq, baseParStep, _⟩ :=
        RawStep.par.glueIntro_inv gluedIH
      rw [cdGluedEq]
      exact baseParStep
  | glueElimCong _ gluedIH =>
      simp only [RawTerm.cd, RawTerm.cdGlueElimCase]
      split
      case _ baseRawTarget partialRawTarget gluedEqn =>
          exact RawStep.par.betaGlueElimIntroDeep
            (gluedEqn ▸ gluedIH)
      all_goals exact RawStep.par.glueElimCong gluedIH
  | @transpCong _ pathRawSource pathRawTarget _ _ pathStep sourceStep pathIH sourceIH =>
      -- pathIH : par pathRawTarget (cd pathRawSource).
      -- Goal: par (transp pathRawTarget sourceRawTarget)
      --           (cdTranspCase (cd pathRawSource) (cd sourceRawSource)).
      -- Split on cdTranspCase result via cd pathRawSource's shape.
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      split
      case _ pathBody pathBodyEqn =>
          rw [pathBodyEqn] at pathIH
          split
          case _ innerType unwknEqn =>
              -- pathBody = innerType.weaken; β fires.
              have hPath : pathBody = innerType.weaken :=
                RawTerm.unweaken?_imp_weaken pathBody innerType unwknEqn
              rw [hPath] at pathIH
              exact RawStep.par.transpReflBetaDeep pathIH sourceIH
          case _ _unwknEqn =>
              exact RawStep.par.transpCong pathIH sourceIH
      -- D3.6-S1: when `cd pathRawSource = uaToEquiv proofRawTarget`,
      -- cdTranspCase fires the equivApply contractum.  Use uaBetaDeep
      -- with pathIH directly (par pathRawTarget (uaToEquiv ...)).
      -- D3.6-S3: when `cd pathRawSource = pathCompose left right`,
      -- cdTranspCase fires the nested-transp contractum.  Use
      -- transpComposeDeep with pathIH directly.
      -- The `first` block tries the uaToEquiv-specific tactic per
      -- remaining arm; only the uaToEquiv arm has `pathIH : par _
      -- (uaToEquiv _)` after the rewrite, only the pathCompose arm
      -- has `pathIH : par _ (pathCompose _ _)`, and all others fall
      -- through to the transpCong default.
      all_goals first
        | (rename_i proofRaw cdPathEqn
           rw [cdPathEqn] at pathIH
           exact RawStep.par.uaBetaDeep pathIH sourceIH)
        | (rename_i leftPathRaw rightPathRaw cdPathEqn
           rw [cdPathEqn] at pathIH
           exact RawStep.par.transpComposeDeep pathIH sourceIH)
        | exact RawStep.par.transpCong pathIH sourceIH
  | @uaBeta _ proofRawSource _ _ _ _ sourceStep proofIH sourceIH =>
      -- D3.6-S1 shallow: source = transp (uaToEquiv proofRawSource)
      --                            sourceRawSource.
      -- Target = equivApply (uaToEquiv proofRawTarget) sourceRawTarget.
      -- proofIH : par proofRawTarget (cd proofRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par (equivApply (uaToEquiv proofRawTarget) sourceRawTarget)
      --           (cd (transp (uaToEquiv proofRawSource) sourceRawSource))
      -- = par (equivApply (uaToEquiv proofRawTarget) sourceRawTarget)
      --       (cdTranspCase (uaToEquiv (cd proofRawSource)) (cd sourceRawSource))
      -- = par (equivApply (uaToEquiv proofRawTarget) sourceRawTarget)
      --       (equivApply (uaToEquiv (cd proofRawSource)) (cd sourceRawSource))
      -- Conclude via equivApplyCong + uaToEquivCong proofIH and sourceIH.
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      exact RawStep.par.equivApplyCong
        (RawStep.par.uaToEquivCong proofIH) sourceIH
  | @uaBetaDeep _ pathRawSource _ _ _ pathStep sourceStep pathIH sourceIH =>
      -- D3.6-S1 deep: source = transp pathRawSource sourceRawSource.
      -- Target = equivApply (uaToEquiv proofRawTarget) sourceRawTarget.
      -- pathStep : par pathRawSource (uaToEquiv proofRawTarget)
      -- pathIH : par (uaToEquiv proofRawTarget) (cd pathRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par (equivApply (uaToEquiv proofRawTarget) sourceRawTarget)
      --           (cdTranspCase (cd pathRawSource) (cd sourceRawSource))
      -- By uaToEquiv_inv on pathIH: cd pathRawSource = uaToEquiv X
      -- with par proofRawTarget X.  cdTranspCase fires the uaToEquiv arm
      -- yielding equivApply (uaToEquiv X) (cd sourceRawSource).
      obtain ⟨proofInner, cdPathEq, proofParStep⟩ :=
        RawStep.par.uaToEquiv_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      exact RawStep.par.equivApplyCong
        (RawStep.par.uaToEquivCong proofParStep) sourceIH
  | @transpReflBeta _ typeRawSource _ _ _ _ _ typeIH sourceIH =>
      -- Source = transp (pathLam typeRawSource.weaken) sourceRawSource.
      -- Target = sourceRawTarget.
      -- typeIH : par typeRawTarget (cd typeRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par sourceRawTarget (cd (transp (pathLam typeRawSource.weaken)
      --                                        sourceRawSource))
      -- = par sourceRawTarget (cdTranspCase (pathLam (cd typeRawSource).weaken)
      --                                       (cd sourceRawSource))
      -- = par sourceRawTarget (cd sourceRawSource) [β fires; via cd-rename
      --   commute, cd typeRawSource.weaken = (cd typeRawSource).weaken;
      --   unweaken? = some]
      -- = sourceIH ✓
      simp only [RawTerm.cd, RawTerm.cdTranspCase, RawTerm.cd_weaken,
                 RawTerm.unweaken?_weaken]
      exact sourceIH
  | @transpReflBetaDeep _ pathRawSource _ _ _ pathStep sourceStep pathIH sourceIH =>
      -- Source = transp pathRawSource sourceRawSource.
      -- Target = sourceRawTarget.
      -- pathStep : par pathRawSource (pathLam typeRawTarget.weaken)
      -- pathIH : par (pathLam typeRawTarget.weaken) (cd pathRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par sourceRawTarget (cd (transp pathRawSource sourceRawSource))
      -- = par sourceRawTarget (cdTranspCase (cd pathRawSource) (cd sourceRawSource))
      -- By pathLam_inv on pathIH: cd pathRawSource = pathLam someBody, par
      -- (typeRawTarget.weaken) someBody.  By weaken_inv: someBody = X.weaken;
      -- so unweaken? someBody = some X, β fires, target = cd sourceRawSource = sourceIH.
      obtain ⟨someBody, cdPathEq, bodyParStep⟩ := RawStep.par.pathLam_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      -- Goal: par sourceRawTarget
      --   (match unweaken? someBody with
      --    | some _ => cd sourceRawSource
      --    | none => transp (pathLam someBody) (cd sourceRawSource))
      -- Use weaken_inv to derive someBody = ?.weaken, so unweaken? someBody ≠ none.
      obtain ⟨innerType, hWeak⟩ := RawStep.par.weaken_inv bodyParStep
      rw [hWeak]
      simp only [RawTerm.unweaken?_weaken]
      exact sourceIH
  | hcompCong _ _ sidesIH capIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.hcompCong sidesIH capIH
  | oeqReflCong _ witnessIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.oeqReflCong witnessIH
  | oeqJCong _ _ baseIH witnessIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.oeqJCong baseIH witnessIH
  | oeqFunextCong _ pointwiseIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.oeqFunextCong pointwiseIH
  | idStrictReflCong _ witnessIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.idStrictReflCong witnessIH
  | idStrictRecCong _ _ baseIH witnessIH =>
      simp only [RawTerm.cd, RawTerm.cdIdStrictRecCase]
      split
      case _ rawTerm cdWitnessEq =>
          exact RawStep.par.iotaIdStrictRecReflDeep
            (cdWitnessEq ▸ witnessIH) baseIH
      all_goals exact RawStep.par.idStrictRecCong baseIH witnessIH
  | equivIntroCong _ _ forwardIH backwardIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivIntroCong forwardIH backwardIH
  | equivAppCong _ _ equivIH argumentIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivAppCong equivIH argumentIH
  | refineIntroCong _ _ valueIH proofIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.refineIntroCong valueIH proofIH
  | betaRefineElimIntro valueStep proofStep valueIH proofIH =>
      simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
      exact valueIH
  | betaRefineElimIntroDeep refinedStep refinedIH =>
      simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
      obtain ⟨valueAfter, proofAfter, cdRefinedEq, valueParStep, _⟩ :=
        RawStep.par.refineIntro_inv refinedIH
      rw [cdRefinedEq]
      exact valueParStep
  | refineElimCong _ refinedIH =>
      simp only [RawTerm.cd, RawTerm.cdRefineElimCase]
      split
      case _ valueRawTarget proofRawTarget refinedEqn =>
          exact RawStep.par.betaRefineElimIntroDeep
            (refinedEqn ▸ refinedIH)
      all_goals exact RawStep.par.refineElimCong refinedIH
  | recordIntroCong _ firstIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.recordIntroCong firstIH
  | betaRecordProjIntro firstStep firstIH =>
      simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
      exact firstIH
  | betaRecordProjIntroDeep recordStep recordIH =>
      simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
      obtain ⟨firstAfter, cdRecordEq, firstParStep⟩ :=
        RawStep.par.recordIntro_inv recordIH
      rw [cdRecordEq]
      exact firstParStep
  | recordProjCong _ recordIH =>
      simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
      split
      case _ firstRawTarget recordEqn =>
          exact RawStep.par.betaRecordProjIntroDeep
            (recordEqn ▸ recordIH)
      all_goals exact RawStep.par.recordProjCong recordIH
  | codataUnfoldCong _ _ stateIH transitionIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.codataUnfoldCong stateIH transitionIH
  | codataDestCong _ codataIH =>
      simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
      split
      case _ stateTarget transitionTarget codataEqn =>
          exact RawStep.par.betaCodataDestUnfoldDeep
            (codataEqn ▸ codataIH)
      all_goals exact RawStep.par.codataDestCong codataIH
  | betaCodataDestUnfold stateStep transitionStep stateIH transitionIH =>
      simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
      exact RawStep.par.app transitionIH stateIH
  | betaCodataDestUnfoldDeep codataStep codataIH =>
      simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
      obtain ⟨stateAfter, transitionAfter, cdCodataEq, stateParStep,
        transitionParStep⟩ := RawStep.par.codataUnfold_inv codataIH
      rw [cdCodataEq]
      exact RawStep.par.app transitionParStep stateParStep
  | sessionSendCong _ _ channelIH payloadIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sessionSendCong channelIH payloadIH
  | sessionRecvCong _ channelIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sessionRecvCong channelIH
  | effectPerformCong _ _ tagIH argumentsIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.effectPerformCong tagIH argumentsIH
  -- CUMUL-2.1 per-shape type-code cong rules.  Each arm `simp only
  -- [RawTerm.cd]` reduces `RawTerm.cd (XCode ...)` to `XCode (cd ...)`,
  -- then applies the `*CodeCong` rule with the inductive hypotheses.
  | arrowCodeCong _ _ domainIH codomainIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.arrowCodeCong domainIH codomainIH
  | piTyCodeCong _ _ domainIH codomainIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.piTyCodeCong domainIH codomainIH
  | sigmaTyCodeCong _ _ domainIH codomainIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sigmaTyCodeCong domainIH codomainIH
  | productCodeCong _ _ firstIH secondIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.productCodeCong firstIH secondIH
  | sumCodeCong _ _ leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sumCodeCong leftIH rightIH
  | listCodeCong _ elementIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.listCodeCong elementIH
  | optionCodeCong _ elementIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.optionCodeCong elementIH
  | eitherCodeCong _ _ leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.eitherCodeCong leftIH rightIH
  | idCodeCong _ _ _ typeIH leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.idCodeCong typeIH leftIH rightIH
  | equivCodeCong _ _ leftIH rightIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivCodeCong leftIH rightIH
  | cumulUpMarkerCong _ innerIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.cumulUpMarkerCong innerIH
  | uaToEquivCong _ innerIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.uaToEquivCong innerIH
  | equivApplyCong _ _ equivIH argIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivApplyCong equivIH argIH
  | pathComposeCong _ _ leftIH rightIH =>
      -- D3.6-S3: pure cong; cd recurses on both path raws.
      simp only [RawTerm.cd]
      exact RawStep.par.pathComposeCong leftIH rightIH
  | @transpCompose _ leftRawSource _ rightRawSource _ _ _
                   leftStep rightStep sourceStep
                   leftIH rightIH sourceIH =>
      -- D3.6-S3 shallow:
      -- Source = transp (pathCompose leftRawSource rightRawSource) sourceRawSource.
      -- Target = transp rightRawTarget (transp leftRawTarget sourceRawTarget).
      -- leftIH : par leftRawTarget (cd leftRawSource)
      -- rightIH : par rightRawTarget (cd rightRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par (transp rightRawTarget (transp leftRawTarget sourceRawTarget))
      --           (cd (transp (pathCompose leftRawSource rightRawSource)
      --                       sourceRawSource))
      -- The cd of `transp (pathCompose left right) source` unfolds to
      -- cdTranspCase, which fires the pathCompose arm yielding
      -- transp (cd right) (transp (cd left) (cd source)).  Conclude
      -- via two transpCong applications threading leftIH/rightIH/sourceIH.
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      exact RawStep.par.transpCong rightIH (RawStep.par.transpCong leftIH sourceIH)
  | @transpComposeDeep _ pathRawSource _ _ _ _
                       pathStep sourceStep pathIH sourceIH =>
      -- D3.6-S3 deep:
      -- Source = transp pathRawSource sourceRawSource.
      -- Target = transp rightRawTarget (transp leftRawTarget sourceRawTarget).
      -- pathStep : par pathRawSource (pathCompose leftRawTarget rightRawTarget)
      -- pathIH : par (pathCompose leftRawTarget rightRawTarget) (cd pathRawSource)
      -- sourceIH : par sourceRawTarget (cd sourceRawSource)
      -- Goal: par (transp rightRawTarget (transp leftRawTarget sourceRawTarget))
      --           (cdTranspCase (cd pathRawSource) (cd sourceRawSource))
      -- By pathCompose_inv on pathIH: cd pathRawSource = pathCompose lInner rInner
      -- with par leftRawTarget lInner and par rightRawTarget rInner.
      -- cdTranspCase fires the pathCompose arm yielding
      -- transp rInner (transp lInner (cd sourceRawSource)).
      obtain ⟨lInner, rInner, cdPathEq, leftParStep, rightParStep⟩ :=
        RawStep.par.pathCompose_inv pathIH
      simp only [RawTerm.cd, RawTerm.cdTranspCase]
      rw [cdPathEq]
      exact RawStep.par.transpCong rightParStep
        (RawStep.par.transpCong leftParStep sourceIH)
  | @idToEquivCong _ proofRawSource _ _ proofIH =>
      -- D3.6-S4/S5: pure cong on proof raw.
      -- Source = idToEquiv proofRawSource; Target = idToEquiv proofRawTarget.
      -- proofIH : par proofRawTarget (cd proofRawSource).
      -- cdIdToEquivCase splits on cd proofRawSource:
      --   * if cd proofRawSource = refl _, fire idToEquivReflDeep.
      --   * if cd proofRawSource = oeqTrans first second, fire
      --     idToEquivComposeDeep.
      --   * otherwise rebuild idToEquiv (cd proofRawSource), close
      --     with idToEquivCong.
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
      | .transp _ _ | .hcomp _ _ | .oeqRefl _ | .oeqJ _ _ | .oeqFunext _
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
      -- D3.6-S4 shallow refl: closed identity contractum, refl-by-refl.
      simp only [RawTerm.cd, RawTerm.cdIdToEquivCase]
      exact RawStep.par.refl _
  | @idToEquivReflDeep _ proofRawSource _ proofStep proofIH =>
      -- D3.6-S4 deep refl.  refl_inv on proofIH yields cd proofRawSource
      -- = refl X; cdIdToEquivCase fires the refl arm to the closed
      -- identity-equiv contractum.
      obtain ⟨witnessFinal, hCdEq, _witnessStep⟩ :=
        RawStep.par.refl_inv proofIH
      simp only [RawTerm.cd]
      rw [hCdEq]
      simp only [RawTerm.cdIdToEquivCase]
      exact RawStep.par.refl _
  | oeqTransCong _ _ firstIH secondIH =>
      -- D3.6-S5: pure cong on oeqTrans.
      simp only [RawTerm.cd]
      exact RawStep.par.oeqTransCong firstIH secondIH
  | equivComposeCong _ _ firstIH secondIH =>
      -- D3.6-S5: pure cong on equivCompose.
      simp only [RawTerm.cd]
      exact RawStep.par.equivComposeCong firstIH secondIH
  | @idToEquivCompose _ firstSource _ secondSource _ firstStep secondStep firstIH secondIH =>
      -- D3.6-S5 shallow compose-β:
      -- Source = idToEquiv (oeqTrans firstSource secondSource).
      -- Target = equivCompose (idToEquiv firstTarget) (idToEquiv secondTarget).
      -- firstIH : par firstTarget (cd firstSource).
      -- secondIH : par secondTarget (cd secondSource).
      -- Goal: par (equivCompose (idToEquiv firstTarget) (idToEquiv secondTarget))
      --           (cd (idToEquiv (oeqTrans firstSource secondSource)))
      --     = par (...) (cdIdToEquivCase (cd (oeqTrans firstSource secondSource)))
      --     = par (...) (cdIdToEquivCase (oeqTrans (cd firstSource) (cd secondSource)))
      --     = par (...) (equivCompose (idToEquiv (cd firstSource))
      --                                (idToEquiv (cd secondSource))).
      -- Closed via equivComposeCong (idToEquivCong firstIH) (idToEquivCong secondIH).
      simp only [RawTerm.cd, RawTerm.cdIdToEquivCase]
      exact RawStep.par.equivComposeCong
        (RawStep.par.idToEquivCong firstIH)
        (RawStep.par.idToEquivCong secondIH)
  | @idToEquivComposeDeep _ proofRawSource firstTarget secondTarget proofStep proofIH =>
      -- D3.6-S5 deep compose-β:
      -- Source = idToEquiv proofRawSource.
      -- Target = equivCompose (idToEquiv firstTarget) (idToEquiv secondTarget).
      -- proofStep : par proofRawSource (oeqTrans firstTarget secondTarget).
      -- proofIH : par (oeqTrans firstTarget secondTarget) (cd proofRawSource).
      -- By oeqTrans_inv on proofIH: cd proofRawSource = oeqTrans X Y
      -- with par firstTarget X and par secondTarget Y.  Then
      -- cdIdToEquivCase fires the oeqTrans arm to equivCompose
      -- (idToEquiv X) (idToEquiv Y).  Closed via equivComposeCong
      -- (idToEquivCong _) (idToEquivCong _).
      obtain ⟨firstFinal, secondFinal, hCdEq, firstStep, secondStep⟩ :=
        RawStep.par.oeqTrans_inv proofIH
      simp only [RawTerm.cd]
      rw [hCdEq]
      simp only [RawTerm.cdIdToEquivCase]
      exact RawStep.par.equivComposeCong
        (RawStep.par.idToEquivCong firstStep)
        (RawStep.par.idToEquivCong secondStep)

end LeanFX2

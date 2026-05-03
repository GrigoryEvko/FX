import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible

/-! # Confluence/RawCdLemma — every parallel reduct lands in `RawTerm.cd`

`RawStep.par.cd_lemma`: `RawStep.par s s' → RawStep.par s' (RawTerm.cd s)`.

Together with `cd_dominates` (`par t (cd t)` for all t), this is
the Tait–Martin-Löf complete-development pair: `cd s` is the
join point of all parallel reductions from `s`.  Diamond and
confluence follow via the strip-lemma argument (Layer 6.C).

Proof shape: induction on the parallel-step derivation (54 ctors).

* `refl t`: `cd_dominates t` directly.
* Pure cong (lam/pair/listCons/optionSome/eitherInl/Inr/natSucc
  /reflCong/modIntro/modElim/subsume): apply cong rule with IHs.
* Redex-bearing cong (app/fst/snd/boolElim/natElim/natRec
  /listElim/optionMatch/eitherMatch/idJ): unfold cd via simp +
  split.  Redex arms fire the deep rule with `heq ▸ IH`; cong
  fallthrough closes via `all_goals`.
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
      simp only [RawTerm.cd]
      exact RawStep.par.modElim innerIH
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
  -- Deep β: invert IH on deep premise to extract redex shape.
  | betaAppDeep functionStep argumentStep functionIH argumentIH =>
      simp only [RawTerm.cd]
      obtain ⟨bodyAfter, cdFunctionEq, bodyParStep⟩ :=
        RawStep.par.lam_inv functionIH
      rw [cdFunctionEq]
      exact RawStep.par.subst0_par bodyParStep argumentIH
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
  -- D1.6: 27 new pure-cong rules (no β/ι at raw level — these
  -- ctors all have only `*Cong` rules in `RawStep.par`).  Each is
  -- a one-line cong-with-IH; cd is pure cong on these, so simp +
  -- cong rule + IH composes directly.
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
      simp only [RawTerm.cd]
      exact RawStep.par.pathAppCong pathIH intervalIH
  | glueIntroCong _ _ baseIH partialIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.glueIntroCong baseIH partialIH
  | glueElimCong _ gluedIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.glueElimCong gluedIH
  | transpCong _ _ pathIH sourceIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.transpCong pathIH sourceIH
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
      simp only [RawTerm.cd]
      exact RawStep.par.idStrictRecCong baseIH witnessIH
  | equivIntroCong _ _ forwardIH backwardIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivIntroCong forwardIH backwardIH
  | equivAppCong _ _ equivIH argumentIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.equivAppCong equivIH argumentIH
  | refineIntroCong _ _ valueIH proofIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.refineIntroCong valueIH proofIH
  | refineElimCong _ refinedIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.refineElimCong refinedIH
  | recordIntroCong _ firstIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.recordIntroCong firstIH
  | recordProjCong _ recordIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.recordProjCong recordIH
  | codataUnfoldCong _ _ stateIH transitionIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.codataUnfoldCong stateIH transitionIH
  | codataDestCong _ codataIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.codataDestCong codataIH
  | sessionSendCong _ _ channelIH payloadIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sessionSendCong channelIH payloadIH
  | sessionRecvCong _ channelIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.sessionRecvCong channelIH
  | effectPerformCong _ _ tagIH argumentsIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.effectPerformCong tagIH argumentsIH

end LeanFX2

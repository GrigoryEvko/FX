import LeanFX.Syntax.RawCdDominates
import LeanFX.Syntax.Reduction.RawParInversion
import LeanFX.Syntax.Reduction.RawParCompatible

namespace LeanFX.Syntax

/-! ## `RawStep.par.cd_lemma`: every parallel reduct lands in `RawTerm.cd`.

Theorem: `RawStep.par s s' → RawStep.par s' (RawTerm.cd s)`.

Together with `cd_dominates` (`par t (cd t)` for all t), this is the
Tait–Martin-Löf complete-development pair: `cd s` is the join point
of all parallel reductions from `s`.  Diamond and confluence follow
from this pair via the standard strip-lemma argument.

The proof is by induction on the parallel-step derivation:
  * `refl t`: target = source = t; `cd_dominates t` closes.
  * Cong cases: rewrite cd via simp + split; in the redex arm fire the
    deep rule (or `subst0_par` for βApp); in the wildcard arm apply
    the cong rule with IHs.
  * β cases: cd contracts the same redex; apply `subst0_par`.
  * ι cases: cd contracts the same redex; close via the appropriate IH.
  * Deep cases: invert IH on deep premise to extract redex shape;
    then close as for the corresponding shallow case. -/

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
      simp only [RawTerm.cd]
      split
      case _ body heq =>
          -- functionIH : par function' (cd function)
          -- heq : cd function = lam body
          -- so par function' (lam body)
          exact RawStep.par.betaAppDeep
            (heq ▸ functionIH) argumentIH
      case _ =>
          exact RawStep.par.app functionIH argumentIH
  | pair firstStep secondStep firstIH secondIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.pair firstIH secondIH
  | fst pairStep pairIH =>
      simp only [RawTerm.cd]
      split
      case _ firstVal secondVal heq =>
          exact RawStep.par.betaFstPairDeep (heq ▸ pairIH)
      case _ =>
          exact RawStep.par.fst pairIH
  | snd pairStep pairIH =>
      simp only [RawTerm.cd]
      split
      case _ firstVal secondVal heq =>
          exact RawStep.par.betaSndPairDeep (heq ▸ pairIH)
      case _ =>
          exact RawStep.par.snd pairIH
  | boolElim scrutineeStep thenStep elseStep
        scrutineeIH thenIH elseIH =>
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaBoolElimTrueDeep _
            (heq ▸ scrutineeIH) thenIH
      case _ heq =>
          exact RawStep.par.iotaBoolElimFalseDeep _
            (heq ▸ scrutineeIH) elseIH
      case _ =>
          exact RawStep.par.boolElim scrutineeIH thenIH elseIH
  | natSucc predStep predIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.natSucc predIH
  | natElim scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaNatElimZeroDeep _
            (heq ▸ scrutineeIH) zeroIH
      case _ pred heq =>
          exact RawStep.par.iotaNatElimSuccDeep _
            (heq ▸ scrutineeIH) succIH
      case _ =>
          exact RawStep.par.natElim scrutineeIH zeroIH succIH
  | natRec scrutineeStep zeroStep succStep
        scrutineeIH zeroIH succIH =>
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaNatRecZeroDeep _
            (heq ▸ scrutineeIH) zeroIH
      case _ pred heq =>
          exact RawStep.par.iotaNatRecSuccDeep
            (heq ▸ scrutineeIH) zeroIH succIH
      case _ =>
          exact RawStep.par.natRec scrutineeIH zeroIH succIH
  | listCons headStep tailStep headIH tailIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.listCons headIH tailIH
  | listElim scrutineeStep nilStep consStep
        scrutineeIH nilIH consIH =>
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaListElimNilDeep _
            (heq ▸ scrutineeIH) nilIH
      case _ head tail heq =>
          exact RawStep.par.iotaListElimConsDeep _
            (heq ▸ scrutineeIH) consIH
      case _ =>
          exact RawStep.par.listElim scrutineeIH nilIH consIH
  | optionSome valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.optionSome valueIH
  | optionMatch scrutineeStep noneStep someStep
        scrutineeIH noneIH someIH =>
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaOptionMatchNoneDeep _
            (heq ▸ scrutineeIH) noneIH
      case _ value heq =>
          exact RawStep.par.iotaOptionMatchSomeDeep _
            (heq ▸ scrutineeIH) someIH
      case _ =>
          exact RawStep.par.optionMatch scrutineeIH noneIH someIH
  | eitherInl valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInl valueIH
  | eitherInr valueStep valueIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInr valueIH
  | eitherMatch scrutineeStep leftStep rightStep
        scrutineeIH leftIH rightIH =>
      simp only [RawTerm.cd]
      split
      case _ value heq =>
          exact RawStep.par.iotaEitherMatchInlDeep _
            (heq ▸ scrutineeIH) leftIH
      case _ value heq =>
          exact RawStep.par.iotaEitherMatchInrDeep _
            (heq ▸ scrutineeIH) rightIH
      case _ =>
          exact RawStep.par.eitherMatch scrutineeIH leftIH rightIH
  | idJ baseStep witnessStep baseIH witnessIH =>
      simp only [RawTerm.cd]
      split
      case _ rawTerm heq =>
          exact RawStep.par.iotaIdJReflDeep
            (heq ▸ witnessIH) baseIH
      case _ =>
          exact RawStep.par.idJ baseIH witnessIH
  | reflCong rawTermStep rawTermIH =>
      simp only [RawTerm.cd]
      exact RawStep.par.reflCong rawTermIH
  -- Shallow β rules: source is a literal redex.  cd contracts the
  -- same redex, and we close via subst0_par (combining body and arg
  -- IHs).
  | betaApp bodyStep argumentStep bodyIH argumentIH =>
      simp only [RawTerm.cd]
      -- Goal after cd unfolds: cd of (app (lam body) arg) reduces to
      -- (cd body).subst0 (cd arg) since cd of (lam body) = lam (cd body).
      -- Need: par (body'.subst0 arg') ((cd body).subst0 (cd arg))
      -- bodyIH : par body' (cd body)
      -- argumentIH : par arg' (cd arg)
      exact RawStep.par.subst0_par bodyIH argumentIH
  | betaFstPair secondVal firstStep firstIH =>
      simp only [RawTerm.cd]
      exact firstIH
  | betaSndPair firstVal secondStep secondIH =>
      simp only [RawTerm.cd]
      exact secondIH
  -- Shallow ι rules: cd contracts the same redex, IH closes.
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
      -- cd of (natElim (natSucc pred) zero succ) =
      --   match cd(natSucc pred) with natSucc p' => app (cd succ) p'
      --   = app (cd succ) (cd pred)
      -- target: app succ' pred'
      -- need: par (app succ' pred') (app (cd succ) (cd pred))
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
  -- Deep β rules: invert IH to extract redex shape, then close as
  -- per shallow case.
  | betaAppDeep functionStep argumentStep functionIH argumentIH =>
      -- functionIH : par (lam body) (cd function)
      -- Apply lam_inv: ∃ body', cd function = lam body' ∧ par body body'
      simp only [RawTerm.cd]
      obtain ⟨body', cdFunctionEq, bodyParStep⟩ :=
        RawStep.par.lam_inv functionIH
      rw [cdFunctionEq]
      -- Goal now: par (body.subst0 arg') (body'.subst0 (cd arg))
      exact RawStep.par.subst0_par bodyParStep argumentIH
  | betaFstPairDeep pairStep pairIH =>
      simp only [RawTerm.cd]
      obtain ⟨first', second', cdPairEq, firstParStep, _⟩ :=
        RawStep.par.pair_inv pairIH
      rw [cdPairEq]
      exact firstParStep
  | betaSndPairDeep pairStep pairIH =>
      simp only [RawTerm.cd]
      obtain ⟨first', second', cdPairEq, _, secondParStep⟩ :=
        RawStep.par.pair_inv pairIH
      rw [cdPairEq]
      exact secondParStep
  -- Deep ι rules: invert scrutinee/witness IH to extract redex shape.
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
      obtain ⟨pred', cdScrutineeEq, predParStep⟩ :=
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
      obtain ⟨pred', cdScrutineeEq, predParStep⟩ :=
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
      obtain ⟨head', tail', cdScrutineeEq, headParStep, tailParStep⟩ :=
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
      obtain ⟨value', cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.optionSome_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app someIH valueParStep
  | iotaEitherMatchInlDeep rightBranch scrutineeStep leftStep
        scrutineeIH leftIH =>
      simp only [RawTerm.cd]
      obtain ⟨value', cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.eitherInl_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app leftIH valueParStep
  | iotaEitherMatchInrDeep leftBranch scrutineeStep rightStep
        scrutineeIH rightIH =>
      simp only [RawTerm.cd]
      obtain ⟨value', cdScrutineeEq, valueParStep⟩ :=
        RawStep.par.eitherInr_inv scrutineeIH
      rw [cdScrutineeEq]
      exact RawStep.par.app rightIH valueParStep
  | iotaIdJReflDeep witnessStep baseStep witnessIH baseIH =>
      simp only [RawTerm.cd]
      obtain ⟨rawTerm', cdWitnessEq, _⟩ :=
        RawStep.par.refl_inv witnessIH
      rw [cdWitnessEq]
      exact baseIH

end LeanFX.Syntax

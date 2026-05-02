import LeanFX2.Confluence.RawCd
import LeanFX2.Reduction.RawPar

/-! # Confluence/RawCdDominates — every raw term parallel-reduces to its cd

`RawStep.par.cd_dominates : ∀ t, RawStep.par t (RawTerm.cd t)`.

Proof shape: structural induction on the raw term.  For each ctor:
* Atomic (var/unit/booleans/zero/Nil/None) — `RawStep.par.refl _`.
* Pure cong (lam/pair/listCons/optionSome/eitherInl/Inr/natSucc/refl
  /modIntro/modElim/subsume) — apply the cong rule with IH.
* Redex-bearing (app/fst/snd/boolElim/natElim/natRec/listElim
  /optionMatch/eitherMatch/idJ) — `simp only [RawTerm.cd]; split`
  produces one goal per ctor of the inner match's scrutinee; the
  redex case fires the appropriate Deep β/ι rule using the IH;
  `all_goals` discharges the cong-shape fallthrough.

Pairs with `cd_lemma` (every parallel reduct lands in cd t) to give
the Tait–Martin-Löf complete-development pair from which raw
diamond and confluence follow.

## Modal cases

`modIntro`/`modElim`/`subsume` are pure cong (no `iotaModal*` rule
in lean-fx-2's RawStep.par yet — Layer 6 will add modal reductions
when the modality theory ships).  Each modal arm is a one-line
`simp + cong rule + recursive call`.
-/

namespace LeanFX2

/-- Every raw term parallel-reduces to its complete development.
Pairs with `cd_lemma` to bound parallel-reduction chains: every
reduct of `t` reaches `cd t`, and `cd t` is a parallel-reduct of `t`. -/
theorem RawStep.par.cd_dominates :
    {scope : Nat} → (rawTerm : RawTerm scope) →
    RawStep.par rawTerm (RawTerm.cd rawTerm)
  | _, .var _ => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .unit => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .lam body => by
      simp only [RawTerm.cd]
      exact RawStep.par.lam (RawStep.par.cd_dominates body)
  | _, .app functionTerm argumentTerm => by
      let functionParStep := RawStep.par.cd_dominates functionTerm
      let argumentParStep := RawStep.par.cd_dominates argumentTerm
      simp only [RawTerm.cd]
      split
      case _ body bodyEqn =>
          exact RawStep.par.betaAppDeep
            (bodyEqn ▸ functionParStep) argumentParStep
      all_goals exact RawStep.par.app functionParStep argumentParStep
  | _, .pair firstValue secondValue => by
      simp only [RawTerm.cd]
      exact RawStep.par.pair
        (RawStep.par.cd_dominates firstValue)
        (RawStep.par.cd_dominates secondValue)
  | _, .fst pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      simp only [RawTerm.cd]
      split
      case _ firstValue secondValue pairEqn =>
          exact RawStep.par.betaFstPairDeep (pairEqn ▸ pairParStep)
      all_goals exact RawStep.par.fst pairParStep
  | _, .snd pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      simp only [RawTerm.cd]
      split
      case _ firstValue secondValue pairEqn =>
          exact RawStep.par.betaSndPairDeep (pairEqn ▸ pairParStep)
      all_goals exact RawStep.par.snd pairParStep
  | _, .boolTrue => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .boolFalse => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .boolElim scrutinee thenBranch elseBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let thenParStep := RawStep.par.cd_dominates thenBranch
      let elseParStep := RawStep.par.cd_dominates elseBranch
      simp only [RawTerm.cd]
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaBoolElimTrueDeep elseBranch
            (scrutineeEqn ▸ scrutineeParStep) thenParStep
      case _ scrutineeEqn =>
          exact RawStep.par.iotaBoolElimFalseDeep thenBranch
            (scrutineeEqn ▸ scrutineeParStep) elseParStep
      all_goals
        exact RawStep.par.boolElim scrutineeParStep thenParStep elseParStep
  | _, .natZero => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .natSucc predecessor => by
      simp only [RawTerm.cd]
      exact RawStep.par.natSucc (RawStep.par.cd_dominates predecessor)
  | _, .natElim scrutinee zeroBranch succBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let zeroParStep := RawStep.par.cd_dominates zeroBranch
      let succParStep := RawStep.par.cd_dominates succBranch
      simp only [RawTerm.cd]
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaNatElimZeroDeep succBranch
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep
      case _ predecessor scrutineeEqn =>
          exact RawStep.par.iotaNatElimSuccDeep zeroBranch
            (scrutineeEqn ▸ scrutineeParStep) succParStep
      all_goals
        exact RawStep.par.natElim scrutineeParStep zeroParStep succParStep
  | _, .natRec scrutinee zeroBranch succBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let zeroParStep := RawStep.par.cd_dominates zeroBranch
      let succParStep := RawStep.par.cd_dominates succBranch
      simp only [RawTerm.cd]
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaNatRecZeroDeep succBranch
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep
      case _ predecessor scrutineeEqn =>
          exact RawStep.par.iotaNatRecSuccDeep
            (scrutineeEqn ▸ scrutineeParStep) zeroParStep succParStep
      all_goals
        exact RawStep.par.natRec scrutineeParStep zeroParStep succParStep
  | _, .listNil => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .listCons headTerm tailTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.listCons
        (RawStep.par.cd_dominates headTerm)
        (RawStep.par.cd_dominates tailTerm)
  | _, .listElim scrutinee nilBranch consBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let nilParStep := RawStep.par.cd_dominates nilBranch
      let consParStep := RawStep.par.cd_dominates consBranch
      simp only [RawTerm.cd]
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaListElimNilDeep consBranch
            (scrutineeEqn ▸ scrutineeParStep) nilParStep
      case _ headTerm tailTerm scrutineeEqn =>
          exact RawStep.par.iotaListElimConsDeep nilBranch
            (scrutineeEqn ▸ scrutineeParStep) consParStep
      all_goals
        exact RawStep.par.listElim scrutineeParStep nilParStep consParStep
  | _, .optionNone => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .optionSome valueTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.optionSome (RawStep.par.cd_dominates valueTerm)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let noneParStep := RawStep.par.cd_dominates noneBranch
      let someParStep := RawStep.par.cd_dominates someBranch
      simp only [RawTerm.cd]
      split
      case _ scrutineeEqn =>
          exact RawStep.par.iotaOptionMatchNoneDeep someBranch
            (scrutineeEqn ▸ scrutineeParStep) noneParStep
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaOptionMatchSomeDeep noneBranch
            (scrutineeEqn ▸ scrutineeParStep) someParStep
      all_goals
        exact RawStep.par.optionMatch scrutineeParStep noneParStep someParStep
  | _, .eitherInl valueTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInl (RawStep.par.cd_dominates valueTerm)
  | _, .eitherInr valueTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInr (RawStep.par.cd_dominates valueTerm)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let leftParStep := RawStep.par.cd_dominates leftBranch
      let rightParStep := RawStep.par.cd_dominates rightBranch
      simp only [RawTerm.cd]
      split
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaEitherMatchInlDeep rightBranch
            (scrutineeEqn ▸ scrutineeParStep) leftParStep
      case _ valueTerm scrutineeEqn =>
          exact RawStep.par.iotaEitherMatchInrDeep leftBranch
            (scrutineeEqn ▸ scrutineeParStep) rightParStep
      all_goals
        exact RawStep.par.eitherMatch scrutineeParStep leftParStep rightParStep
  | _, .refl rawWitness => by
      simp only [RawTerm.cd]
      exact RawStep.par.reflCong (RawStep.par.cd_dominates rawWitness)
  | _, .idJ baseCase witness => by
      let baseParStep := RawStep.par.cd_dominates baseCase
      let witnessParStep := RawStep.par.cd_dominates witness
      simp only [RawTerm.cd]
      split
      case _ rawTerm witnessEqn =>
          exact RawStep.par.iotaIdJReflDeep
            (witnessEqn ▸ witnessParStep) baseParStep
      all_goals exact RawStep.par.idJ baseParStep witnessParStep
  | _, .modIntro innerTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.modIntro (RawStep.par.cd_dominates innerTerm)
  | _, .modElim innerTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.modElim (RawStep.par.cd_dominates innerTerm)
  | _, .subsume innerTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.subsume (RawStep.par.cd_dominates innerTerm)

end LeanFX2

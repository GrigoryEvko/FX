import LeanFX.Syntax.RawCompleteDevelopment
import LeanFX.Syntax.Reduction.RawPar

namespace LeanFX.Syntax

/-! ## `RawStep.par.cd_dominates`: every raw term parallel-reduces to its cd.

Mirrors the typed `Step.par.cd_dominates` but at the raw level.  The
proof structure is identical except simpler: no Ty casts, no
cd_idJ_redex helper (the iotaIdJ contraction is a direct match on
the raw `RawTerm.refl _` shape, since raw terms have no
endpoint-equality constraint to satisfy). -/

theorem RawStep.par.cd_dominates :
    {scope : Nat} → (term : RawTerm scope) →
    RawStep.par term (RawTerm.cd term)
  | _, .var _ => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .unit => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .lam body => by
      simp only [RawTerm.cd]
      exact RawStep.par.lam (RawStep.par.cd_dominates body)
  | _, .app function argument => by
      let functionParStep := RawStep.par.cd_dominates function
      let argumentParStep := RawStep.par.cd_dominates argument
      simp only [RawTerm.cd]
      split
      case _ body heq =>
          exact RawStep.par.betaAppDeep
            (heq ▸ functionParStep) argumentParStep
      all_goals exact RawStep.par.app functionParStep argumentParStep
  | _, .pair firstVal secondVal => by
      simp only [RawTerm.cd]
      exact RawStep.par.pair (RawStep.par.cd_dominates firstVal)
        (RawStep.par.cd_dominates secondVal)
  | _, .fst pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      simp only [RawTerm.cd]
      split
      case _ firstVal secondVal heq =>
          exact RawStep.par.betaFstPairDeep (heq ▸ pairParStep)
      all_goals exact RawStep.par.fst pairParStep
  | _, .snd pairTerm => by
      let pairParStep := RawStep.par.cd_dominates pairTerm
      simp only [RawTerm.cd]
      split
      case _ firstVal secondVal heq =>
          exact RawStep.par.betaSndPairDeep (heq ▸ pairParStep)
      all_goals exact RawStep.par.snd pairParStep
  | _, .boolTrue => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .boolFalse => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .boolElim scrutinee thenBranch elseBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let thenParStep := RawStep.par.cd_dominates thenBranch
      let elseParStep := RawStep.par.cd_dominates elseBranch
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaBoolElimTrueDeep elseBranch
            (heq ▸ scrutineeParStep) thenParStep
      case _ heq =>
          exact RawStep.par.iotaBoolElimFalseDeep thenBranch
            (heq ▸ scrutineeParStep) elseParStep
      all_goals exact RawStep.par.boolElim scrutineeParStep thenParStep elseParStep
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
      case _ heq =>
          exact RawStep.par.iotaNatElimZeroDeep succBranch
            (heq ▸ scrutineeParStep) zeroParStep
      case _ predecessor heq =>
          exact RawStep.par.iotaNatElimSuccDeep zeroBranch
            (heq ▸ scrutineeParStep) succParStep
      all_goals exact RawStep.par.natElim scrutineeParStep zeroParStep succParStep
  | _, .natRec scrutinee zeroBranch succBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let zeroParStep := RawStep.par.cd_dominates zeroBranch
      let succParStep := RawStep.par.cd_dominates succBranch
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaNatRecZeroDeep succBranch
            (heq ▸ scrutineeParStep) zeroParStep
      case _ predecessor heq =>
          exact RawStep.par.iotaNatRecSuccDeep
            (heq ▸ scrutineeParStep) zeroParStep succParStep
      all_goals exact RawStep.par.natRec scrutineeParStep zeroParStep succParStep
  | _, .listNil => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .listCons head tail => by
      simp only [RawTerm.cd]
      exact RawStep.par.listCons (RawStep.par.cd_dominates head)
        (RawStep.par.cd_dominates tail)
  | _, .listElim scrutinee nilBranch consBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let nilParStep := RawStep.par.cd_dominates nilBranch
      let consParStep := RawStep.par.cd_dominates consBranch
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaListElimNilDeep consBranch
            (heq ▸ scrutineeParStep) nilParStep
      case _ head tail heq =>
          exact RawStep.par.iotaListElimConsDeep nilBranch
            (heq ▸ scrutineeParStep) consParStep
      all_goals exact RawStep.par.listElim scrutineeParStep nilParStep consParStep
  | _, .optionNone => by unfold RawTerm.cd; exact RawStep.par.refl _
  | _, .optionSome value => by
      simp only [RawTerm.cd]
      exact RawStep.par.optionSome (RawStep.par.cd_dominates value)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let noneParStep := RawStep.par.cd_dominates noneBranch
      let someParStep := RawStep.par.cd_dominates someBranch
      simp only [RawTerm.cd]
      split
      case _ heq =>
          exact RawStep.par.iotaOptionMatchNoneDeep someBranch
            (heq ▸ scrutineeParStep) noneParStep
      case _ value heq =>
          exact RawStep.par.iotaOptionMatchSomeDeep noneBranch
            (heq ▸ scrutineeParStep) someParStep
      all_goals exact RawStep.par.optionMatch scrutineeParStep noneParStep someParStep
  | _, .eitherInl value => by
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInl (RawStep.par.cd_dominates value)
  | _, .eitherInr value => by
      simp only [RawTerm.cd]
      exact RawStep.par.eitherInr (RawStep.par.cd_dominates value)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      let scrutineeParStep := RawStep.par.cd_dominates scrutinee
      let leftParStep := RawStep.par.cd_dominates leftBranch
      let rightParStep := RawStep.par.cd_dominates rightBranch
      simp only [RawTerm.cd]
      split
      case _ value heq =>
          exact RawStep.par.iotaEitherMatchInlDeep rightBranch
            (heq ▸ scrutineeParStep) leftParStep
      case _ value heq =>
          exact RawStep.par.iotaEitherMatchInrDeep leftBranch
            (heq ▸ scrutineeParStep) rightParStep
      all_goals exact RawStep.par.eitherMatch scrutineeParStep leftParStep rightParStep
  | _, .refl rawTerm => by
      simp only [RawTerm.cd]
      exact RawStep.par.reflCong (RawStep.par.cd_dominates rawTerm)
  | _, .idJ baseCase witness => by
      let baseParStep := RawStep.par.cd_dominates baseCase
      let witnessParStep := RawStep.par.cd_dominates witness
      simp only [RawTerm.cd]
      split
      case _ rawTerm heq =>
          exact RawStep.par.iotaIdJReflDeep
            (heq ▸ witnessParStep) baseParStep
      all_goals exact RawStep.par.idJ baseParStep witnessParStep

end LeanFX.Syntax

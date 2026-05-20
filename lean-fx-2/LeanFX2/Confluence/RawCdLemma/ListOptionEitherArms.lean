import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawPar.Inductive
import LeanFX2.Reduction.RawParInversion.AtomicCtors

/-! # LeanFX2.Confluence.RawCdLemma.ListOptionEitherArms

Per-arm helpers for list / option / either eliminator arms inside
`RawStep.par.cd_lemma`: `listCons`, `listElim`, `optionSome`,
`optionMatch`, `eitherInl`, `eitherInr`, `eitherMatch`, plus their
shallow + deep ι-redex arms.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `listCons` cong arm. -/
theorem RawStep.par.cd_lemma_listCons {scope : Nat}
    {headRawSource headRawTarget
     tailRawSource tailRawTarget : RawTerm scope}
    (headIH : RawStep.par headRawTarget (RawTerm.cd headRawSource))
    (tailIH : RawStep.par tailRawTarget (RawTerm.cd tailRawSource)) :
    RawStep.par (RawTerm.listCons headRawTarget tailRawTarget)
      (RawTerm.cd (RawTerm.listCons headRawSource tailRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.listCons headIH tailIH

/-- `listElim` cong arm with nil/cons split. -/
theorem RawStep.par.cd_lemma_listElim {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     nilRawSource nilRawTarget
     consRawSource consRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (nilIH : RawStep.par nilRawTarget (RawTerm.cd nilRawSource))
    (consIH : RawStep.par consRawTarget (RawTerm.cd consRawSource)) :
    RawStep.par
      (RawTerm.listElim scrutineeRawTarget nilRawTarget consRawTarget)
      (RawTerm.cd
        (RawTerm.listElim scrutineeRawSource nilRawSource consRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdListElimCase]
  split
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaListElimNilDeep _
        (cdScrutineeEq ▸ scrutineeIH) nilIH
  case _ head tail cdScrutineeEq =>
      exact RawStep.par.iotaListElimConsDeep _
        (cdScrutineeEq ▸ scrutineeIH) consIH
  all_goals exact RawStep.par.listElim scrutineeIH nilIH consIH

/-- `optionSome` cong arm. -/
theorem RawStep.par.cd_lemma_optionSome {scope : Nat}
    {valueRawSource valueRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource)) :
    RawStep.par (RawTerm.optionSome valueRawTarget)
      (RawTerm.cd (RawTerm.optionSome valueRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.optionSome valueIH

/-- `optionMatch` cong arm with none/some split. -/
theorem RawStep.par.cd_lemma_optionMatch {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     noneRawSource noneRawTarget
     someRawSource someRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (noneIH : RawStep.par noneRawTarget (RawTerm.cd noneRawSource))
    (someIH : RawStep.par someRawTarget (RawTerm.cd someRawSource)) :
    RawStep.par
      (RawTerm.optionMatch scrutineeRawTarget
        noneRawTarget someRawTarget)
      (RawTerm.cd
        (RawTerm.optionMatch scrutineeRawSource
          noneRawSource someRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdOptionMatchCase]
  split
  case _ cdScrutineeEq =>
      exact RawStep.par.iotaOptionMatchNoneDeep _
        (cdScrutineeEq ▸ scrutineeIH) noneIH
  case _ value cdScrutineeEq =>
      exact RawStep.par.iotaOptionMatchSomeDeep _
        (cdScrutineeEq ▸ scrutineeIH) someIH
  all_goals exact RawStep.par.optionMatch scrutineeIH noneIH someIH

/-- `eitherInl` cong arm. -/
theorem RawStep.par.cd_lemma_eitherInl {scope : Nat}
    {valueRawSource valueRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource)) :
    RawStep.par (RawTerm.eitherInl valueRawTarget)
      (RawTerm.cd (RawTerm.eitherInl valueRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.eitherInl valueIH

/-- `eitherInr` cong arm. -/
theorem RawStep.par.cd_lemma_eitherInr {scope : Nat}
    {valueRawSource valueRawTarget : RawTerm scope}
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource)) :
    RawStep.par (RawTerm.eitherInr valueRawTarget)
      (RawTerm.cd (RawTerm.eitherInr valueRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.eitherInr valueIH

/-- `eitherMatch` cong arm with inl/inr split. -/
theorem RawStep.par.cd_lemma_eitherMatch {scope : Nat}
    {scrutineeRawSource scrutineeRawTarget
     leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (scrutineeIH :
      RawStep.par scrutineeRawTarget (RawTerm.cd scrutineeRawSource))
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par
      (RawTerm.eitherMatch scrutineeRawTarget
        leftRawTarget rightRawTarget)
      (RawTerm.cd
        (RawTerm.eitherMatch scrutineeRawSource
          leftRawSource rightRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdEitherMatchCase]
  split
  case _ value cdScrutineeEq =>
      exact RawStep.par.iotaEitherMatchInlDeep _
        (cdScrutineeEq ▸ scrutineeIH) leftIH
  case _ value cdScrutineeEq =>
      exact RawStep.par.iotaEitherMatchInrDeep _
        (cdScrutineeEq ▸ scrutineeIH) rightIH
  all_goals exact RawStep.par.eitherMatch scrutineeIH leftIH rightIH

/-- Shallow ι: list-elim on `listNil`. -/
theorem RawStep.par.cd_lemma_iotaListElimNil {scope : Nat}
    {nilRawSource nilRawTarget : RawTerm scope}
    (consBranch : RawTerm scope)
    (nilIH : RawStep.par nilRawTarget (RawTerm.cd nilRawSource)) :
    RawStep.par nilRawTarget
      (RawTerm.cd (RawTerm.listElim RawTerm.listNil
        nilRawSource consBranch)) := by
  simp only [RawTerm.cd]
  exact nilIH

/-- Shallow ι: list-elim on `listCons`. -/
theorem RawStep.par.cd_lemma_iotaListElimCons {scope : Nat}
    {headRawSource headRawTarget
     tailRawSource tailRawTarget
     consRawSource consRawTarget : RawTerm scope}
    (nilBranch : RawTerm scope)
    (headIH : RawStep.par headRawTarget (RawTerm.cd headRawSource))
    (tailIH : RawStep.par tailRawTarget (RawTerm.cd tailRawSource))
    (consIH : RawStep.par consRawTarget (RawTerm.cd consRawSource)) :
    RawStep.par
      (RawTerm.app (RawTerm.app consRawTarget headRawTarget) tailRawTarget)
      (RawTerm.cd (RawTerm.listElim
        (RawTerm.listCons headRawSource tailRawSource)
        nilBranch consRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app
    (RawStep.par.app consIH headIH) tailIH

/-- Shallow ι: option-match on `optionNone`. -/
theorem RawStep.par.cd_lemma_iotaOptionMatchNone {scope : Nat}
    {noneRawSource noneRawTarget : RawTerm scope}
    (someBranch : RawTerm scope)
    (noneIH : RawStep.par noneRawTarget (RawTerm.cd noneRawSource)) :
    RawStep.par noneRawTarget
      (RawTerm.cd (RawTerm.optionMatch RawTerm.optionNone
        noneRawSource someBranch)) := by
  simp only [RawTerm.cd]
  exact noneIH

/-- Shallow ι: option-match on `optionSome`. -/
theorem RawStep.par.cd_lemma_iotaOptionMatchSome {scope : Nat}
    {valueRawSource valueRawTarget
     someRawSource someRawTarget : RawTerm scope}
    (noneBranch : RawTerm scope)
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (someIH : RawStep.par someRawTarget (RawTerm.cd someRawSource)) :
    RawStep.par (RawTerm.app someRawTarget valueRawTarget)
      (RawTerm.cd (RawTerm.optionMatch
        (RawTerm.optionSome valueRawSource)
        noneBranch someRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app someIH valueIH

/-- Shallow ι: either-match on `eitherInl`. -/
theorem RawStep.par.cd_lemma_iotaEitherMatchInl {scope : Nat}
    {valueRawSource valueRawTarget
     leftRawSource leftRawTarget : RawTerm scope}
    (rightBranch : RawTerm scope)
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource)) :
    RawStep.par (RawTerm.app leftRawTarget valueRawTarget)
      (RawTerm.cd (RawTerm.eitherMatch
        (RawTerm.eitherInl valueRawSource)
        leftRawSource rightBranch)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app leftIH valueIH

/-- Shallow ι: either-match on `eitherInr`. -/
theorem RawStep.par.cd_lemma_iotaEitherMatchInr {scope : Nat}
    {valueRawSource valueRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftBranch : RawTerm scope)
    (valueIH : RawStep.par valueRawTarget (RawTerm.cd valueRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.app rightRawTarget valueRawTarget)
      (RawTerm.cd (RawTerm.eitherMatch
        (RawTerm.eitherInr valueRawSource)
        leftBranch rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.app rightIH valueIH

/-- Deep ι: list-elim scrutinee develops to `listNil`. -/
theorem RawStep.par.cd_lemma_iotaListElimNilDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {nilRawSource nilRawTarget : RawTerm scope}
    (consBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.listNil (RawTerm.cd scrutineeRawSource))
    (nilIH : RawStep.par nilRawTarget (RawTerm.cd nilRawSource)) :
    RawStep.par nilRawTarget
      (RawTerm.cd (RawTerm.listElim scrutineeRawSource
        nilRawSource consBranch)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.listNil_inv scrutineeIH
  rw [cdScrutinee]
  exact nilIH

/-- Deep ι: list-elim scrutinee develops to `listCons`. -/
theorem RawStep.par.cd_lemma_iotaListElimConsDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {headAfter tailAfter : RawTerm scope}
    {consRawSource consRawTarget : RawTerm scope}
    (nilBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par (RawTerm.listCons headAfter tailAfter)
        (RawTerm.cd scrutineeRawSource))
    (consIH : RawStep.par consRawTarget (RawTerm.cd consRawSource)) :
    RawStep.par
      (RawTerm.app (RawTerm.app consRawTarget headAfter) tailAfter)
      (RawTerm.cd (RawTerm.listElim scrutineeRawSource
        nilBranch consRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨headAfter', tailAfter', cdScrutineeEq, headParStep, tailParStep⟩ :=
    RawStep.par.listCons_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app
    (RawStep.par.app consIH headParStep) tailParStep

/-- Deep ι: option-match scrutinee develops to `optionNone`. -/
theorem RawStep.par.cd_lemma_iotaOptionMatchNoneDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {noneRawSource noneRawTarget : RawTerm scope}
    (someBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par RawTerm.optionNone (RawTerm.cd scrutineeRawSource))
    (noneIH : RawStep.par noneRawTarget (RawTerm.cd noneRawSource)) :
    RawStep.par noneRawTarget
      (RawTerm.cd (RawTerm.optionMatch scrutineeRawSource
        noneRawSource someBranch)) := by
  simp only [RawTerm.cd]
  have cdScrutinee := RawStep.par.optionNone_inv scrutineeIH
  rw [cdScrutinee]
  exact noneIH

/-- Deep ι: option-match scrutinee develops to `optionSome`. -/
theorem RawStep.par.cd_lemma_iotaOptionMatchSomeDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {valueAfter : RawTerm scope}
    {someRawSource someRawTarget : RawTerm scope}
    (noneBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par (RawTerm.optionSome valueAfter)
        (RawTerm.cd scrutineeRawSource))
    (someIH : RawStep.par someRawTarget (RawTerm.cd someRawSource)) :
    RawStep.par (RawTerm.app someRawTarget valueAfter)
      (RawTerm.cd (RawTerm.optionMatch scrutineeRawSource
        noneBranch someRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨valueAfter', cdScrutineeEq, valueParStep⟩ :=
    RawStep.par.optionSome_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app someIH valueParStep

/-- Deep ι: either-match scrutinee develops to `eitherInl`. -/
theorem RawStep.par.cd_lemma_iotaEitherMatchInlDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {valueAfter : RawTerm scope}
    {leftRawSource leftRawTarget : RawTerm scope}
    (rightBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par (RawTerm.eitherInl valueAfter)
        (RawTerm.cd scrutineeRawSource))
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource)) :
    RawStep.par (RawTerm.app leftRawTarget valueAfter)
      (RawTerm.cd (RawTerm.eitherMatch scrutineeRawSource
        leftRawSource rightBranch)) := by
  simp only [RawTerm.cd]
  obtain ⟨valueAfter', cdScrutineeEq, valueParStep⟩ :=
    RawStep.par.eitherInl_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app leftIH valueParStep

/-- Deep ι: either-match scrutinee develops to `eitherInr`. -/
theorem RawStep.par.cd_lemma_iotaEitherMatchInrDeep {scope : Nat}
    {scrutineeRawSource : RawTerm scope}
    {valueAfter : RawTerm scope}
    {rightRawSource rightRawTarget : RawTerm scope}
    (leftBranch : RawTerm scope)
    (scrutineeIH :
      RawStep.par (RawTerm.eitherInr valueAfter)
        (RawTerm.cd scrutineeRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.app rightRawTarget valueAfter)
      (RawTerm.cd (RawTerm.eitherMatch scrutineeRawSource
        leftBranch rightRawSource)) := by
  simp only [RawTerm.cd]
  obtain ⟨valueAfter', cdScrutineeEq, valueParStep⟩ :=
    RawStep.par.eitherInr_inv scrutineeIH
  rw [cdScrutineeEq]
  exact RawStep.par.app rightIH valueParStep

end LeanFX2

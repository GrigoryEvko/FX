import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.RecordAndCodata

Per-arm helpers for record / codata / session / effect arms inside
`RawStep.par.cd_lemma`: `recordIntroCong`, `betaRecordProjIntro`,
`betaRecordProjIntroDeep`, `recordProjCong`, `codataUnfoldCong`,
`codataDestCong`, `betaCodataDestUnfold`,
`betaCodataDestUnfoldDeep`, `sessionSendCong`, `sessionRecvCong`,
`effectPerformCong`.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `recordIntroCong` arm. -/
theorem RawStep.par.cd_lemma_recordIntroCong {scope : Nat}
    {firstRawSource firstRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource)) :
    RawStep.par (RawTerm.recordIntro firstRawTarget)
      (RawTerm.cd (RawTerm.recordIntro firstRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.recordIntroCong firstIH

/-- Shallow β: `recordProj (recordIntro first)` contracts to first. -/
theorem RawStep.par.cd_lemma_betaRecordProjIntro {scope : Nat}
    {firstRawSource firstRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource)) :
    RawStep.par firstRawTarget
      (RawTerm.cd (RawTerm.recordProj
        (RawTerm.recordIntro firstRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
  exact firstIH

/-- Deep β: record term develops to `recordIntro`. -/
theorem RawStep.par.cd_lemma_betaRecordProjIntroDeep {scope : Nat}
    {recordRawSource : RawTerm scope}
    {firstAfter : RawTerm scope}
    (recordIH :
      RawStep.par (RawTerm.recordIntro firstAfter)
        (RawTerm.cd recordRawSource)) :
    RawStep.par firstAfter
      (RawTerm.cd (RawTerm.recordProj recordRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
  obtain ⟨firstAfter', cdRecordEq, firstParStep⟩ :=
    RawStep.par.recordIntro_inv recordIH
  rw [cdRecordEq]
  exact firstParStep

/-- `recordProjCong` arm with redex split. -/
theorem RawStep.par.cd_lemma_recordProjCong {scope : Nat}
    {recordRawSource recordRawTarget : RawTerm scope}
    (recordIH :
      RawStep.par recordRawTarget (RawTerm.cd recordRawSource)) :
    RawStep.par (RawTerm.recordProj recordRawTarget)
      (RawTerm.cd (RawTerm.recordProj recordRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdRecordProjCase]
  split
  case _ firstRawTarget recordEqn =>
      exact RawStep.par.betaRecordProjIntroDeep
        (recordEqn ▸ recordIH)
  all_goals exact RawStep.par.recordProjCong recordIH

/-- `codataUnfoldCong` arm. -/
theorem RawStep.par.cd_lemma_codataUnfoldCong {scope : Nat}
    {stateRawSource stateRawTarget
     transitionRawSource transitionRawTarget : RawTerm scope}
    (stateIH : RawStep.par stateRawTarget (RawTerm.cd stateRawSource))
    (transitionIH :
      RawStep.par transitionRawTarget (RawTerm.cd transitionRawSource)) :
    RawStep.par (RawTerm.codataUnfold stateRawTarget transitionRawTarget)
      (RawTerm.cd (RawTerm.codataUnfold stateRawSource
        transitionRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.codataUnfoldCong stateIH transitionIH

/-- `codataDestCong` arm with redex split. -/
theorem RawStep.par.cd_lemma_codataDestCong {scope : Nat}
    {codataRawSource codataRawTarget : RawTerm scope}
    (codataIH :
      RawStep.par codataRawTarget (RawTerm.cd codataRawSource)) :
    RawStep.par (RawTerm.codataDest codataRawTarget)
      (RawTerm.cd (RawTerm.codataDest codataRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
  split
  case _ stateTarget transitionTarget codataEqn =>
      exact RawStep.par.betaCodataDestUnfoldDeep
        (codataEqn ▸ codataIH)
  all_goals exact RawStep.par.codataDestCong codataIH

/-- Shallow β: `codataDest (codataUnfold state transition)`. -/
theorem RawStep.par.cd_lemma_betaCodataDestUnfold {scope : Nat}
    {stateRawSource stateRawTarget
     transitionRawSource transitionRawTarget : RawTerm scope}
    (stateIH : RawStep.par stateRawTarget (RawTerm.cd stateRawSource))
    (transitionIH :
      RawStep.par transitionRawTarget (RawTerm.cd transitionRawSource)) :
    RawStep.par (RawTerm.app transitionRawTarget stateRawTarget)
      (RawTerm.cd (RawTerm.codataDest
        (RawTerm.codataUnfold stateRawSource transitionRawSource))) := by
  simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
  exact RawStep.par.app transitionIH stateIH

/-- Deep β: codata term develops to `codataUnfold`. -/
theorem RawStep.par.cd_lemma_betaCodataDestUnfoldDeep {scope : Nat}
    {codataRawSource : RawTerm scope}
    {stateAfter transitionAfter : RawTerm scope}
    (codataIH :
      RawStep.par (RawTerm.codataUnfold stateAfter transitionAfter)
        (RawTerm.cd codataRawSource)) :
    RawStep.par (RawTerm.app transitionAfter stateAfter)
      (RawTerm.cd (RawTerm.codataDest codataRawSource)) := by
  simp only [RawTerm.cd, RawTerm.cdCodataDestCase]
  obtain ⟨stateAfter', transitionAfter', cdCodataEq, stateParStep,
    transitionParStep⟩ := RawStep.par.codataUnfold_inv codataIH
  rw [cdCodataEq]
  exact RawStep.par.app transitionParStep stateParStep

/-- `sessionSendCong` arm. -/
theorem RawStep.par.cd_lemma_sessionSendCong {scope : Nat}
    {channelRawSource channelRawTarget
     payloadRawSource payloadRawTarget : RawTerm scope}
    (channelIH :
      RawStep.par channelRawTarget (RawTerm.cd channelRawSource))
    (payloadIH :
      RawStep.par payloadRawTarget (RawTerm.cd payloadRawSource)) :
    RawStep.par (RawTerm.sessionSend channelRawTarget payloadRawTarget)
      (RawTerm.cd (RawTerm.sessionSend channelRawSource
        payloadRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.sessionSendCong channelIH payloadIH

/-- `sessionRecvCong` arm. -/
theorem RawStep.par.cd_lemma_sessionRecvCong {scope : Nat}
    {channelRawSource channelRawTarget : RawTerm scope}
    (channelIH :
      RawStep.par channelRawTarget (RawTerm.cd channelRawSource)) :
    RawStep.par (RawTerm.sessionRecv channelRawTarget)
      (RawTerm.cd (RawTerm.sessionRecv channelRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.sessionRecvCong channelIH

/-- `effectPerformCong` arm. -/
theorem RawStep.par.cd_lemma_effectPerformCong {scope : Nat}
    {tagRawSource tagRawTarget
     argumentsRawSource argumentsRawTarget : RawTerm scope}
    (tagIH : RawStep.par tagRawTarget (RawTerm.cd tagRawSource))
    (argumentsIH :
      RawStep.par argumentsRawTarget (RawTerm.cd argumentsRawSource)) :
    RawStep.par (RawTerm.effectPerform tagRawTarget argumentsRawTarget)
      (RawTerm.cd (RawTerm.effectPerform tagRawSource
        argumentsRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.effectPerformCong tagIH argumentsIH

end LeanFX2

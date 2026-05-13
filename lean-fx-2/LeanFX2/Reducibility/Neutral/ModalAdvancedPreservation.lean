import LeanFX2.Reducibility.Neutral.EliminatorPreservation
import LeanFX2.Reducibility.Neutral.CubicalIdentityPreservation

/-! # LeanFX2.Reducibility.Neutral.ModalAdvancedPreservation

Preservation of `RawTerm.IsNeutral` under one raw parallel step
for the modal + refine / record / codata / session / effect
family: `modElim`, `subsume`, `refineElim`, `recordProj`,
`codataDest`, `sessionSend`, `sessionRecv`, `effectPerform`.
Includes the master `par_preserves` dispatcher that delegates
into every per-ctor closure atom.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `Neutral`; the master
dispatcher lives here because it depends on every sibling slice. -/

namespace LeanFX2


/-- Neutrality is preserved by one raw parallel step from `modElim`
with a neutral modal value. -/
theorem RawTerm.IsNeutral.modElim_par_preserves {scope : Nat}
    {modalRaw targetRaw : RawTerm scope}
    (modalParPreserves :
      ∀ {modalTarget : RawTerm scope},
        RawStep.par modalRaw modalTarget →
        RawTerm.IsNeutral modalTarget)
    (parallelStep : RawStep.par (RawTerm.modElim modalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.modElim_inv parallelStep with
    ⟨modalTarget, targetEq, modalStep⟩
    | ⟨payloadTarget, _targetEq, modalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.modElim (modalParPreserves modalStep)
  · exact (RawTerm.IsNeutral.not_modIntro
      (modalParPreserves modalStep)
      (valueRaw := payloadTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `subsume`
with a neutral inner term. -/
theorem RawTerm.IsNeutral.subsume_par_preserves {scope : Nat}
    {innerRaw targetRaw : RawTerm scope}
    (innerParPreserves :
      ∀ {innerTarget : RawTerm scope},
        RawStep.par innerRaw innerTarget →
        RawTerm.IsNeutral innerTarget)
    (parallelStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨innerTarget, targetEq, innerStep⟩ :=
    RawStep.par.subsume_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.subsume (innerParPreserves innerStep)

/-- Neutrality is preserved by one raw parallel step from `refineElim`
with a neutral refined value. -/
theorem RawTerm.IsNeutral.refineElim_par_preserves {scope : Nat}
    {refinedRaw targetRaw : RawTerm scope}
    (refinedParPreserves :
      ∀ {refinedTarget : RawTerm scope},
        RawStep.par refinedRaw refinedTarget →
        RawTerm.IsNeutral refinedTarget)
    (parallelStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.refineElim_inv parallelStep with
    ⟨refinedTarget, targetEq, refinedStep⟩
    | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.refineElim
      (refinedParPreserves refinedStep)
  · exact (RawTerm.IsNeutral.not_refineIntro
      (refinedParPreserves refinedStep)
      (valueRaw := valueTarget) (proofRaw := proofTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `recordProj`
with a neutral record value. -/
theorem RawTerm.IsNeutral.recordProj_par_preserves {scope : Nat}
    {recordRaw targetRaw : RawTerm scope}
    (recordParPreserves :
      ∀ {recordTarget : RawTerm scope},
        RawStep.par recordRaw recordTarget →
        RawTerm.IsNeutral recordTarget)
    (parallelStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.recordProj_inv parallelStep with
    ⟨recordTarget, targetEq, recordStep⟩
    | ⟨fieldTarget, _targetEq, recordStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.recordProj
      (recordParPreserves recordStep)
  · exact (RawTerm.IsNeutral.not_recordIntro
      (recordParPreserves recordStep)
      (fieldRaw := fieldTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `codataDest`
with a neutral codata value. -/
theorem RawTerm.IsNeutral.codataDest_par_preserves {scope : Nat}
    {codataRaw targetRaw : RawTerm scope}
    (codataParPreserves :
      ∀ {codataTarget : RawTerm scope},
        RawStep.par codataRaw codataTarget →
        RawTerm.IsNeutral codataTarget)
    (parallelStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.codataDest_inv parallelStep with
    ⟨codataTarget, targetEq, codataStep⟩
    | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.codataDest
      (codataParPreserves codataStep)
  · exact (RawTerm.IsNeutral.not_codataUnfold
      (codataParPreserves codataStep)
      (initialRaw := stateTarget) (transitionRaw := transitionTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `sessionSend`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionSend_par_preserves {scope : Nat}
    {channelRaw payloadRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep :
      RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, payloadTarget, targetEq,
      channelStep, _payloadStep⟩ :=
    RawStep.par.sessionSend_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionSend
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `sessionRecv`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionRecv_par_preserves {scope : Nat}
    {channelRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, targetEq, channelStep⟩ :=
    RawStep.par.sessionRecv_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionRecv
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `effectPerform`
with a neutral operation tag. -/
theorem RawTerm.IsNeutral.effectPerform_par_preserves {scope : Nat}
    {operationRaw argumentsRaw targetRaw : RawTerm scope}
    (operationParPreserves :
      ∀ {operationTarget : RawTerm scope},
        RawStep.par operationRaw operationTarget →
        RawTerm.IsNeutral operationTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨operationTarget, argumentsTarget, targetEq,
      operationStep, _argumentsStep⟩ :=
    RawStep.par.effectPerform_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.effectPerform
    (operationParPreserves operationStep)

/-- One raw parallel step preserves neutral shape.

This is the global dispatcher over the `RawTerm.IsNeutral` syntax class.
Each eliminator case delegates to its local preservation atom, and the
recursive hypothesis supplies preservation for the principal neutral
subterm. -/
theorem RawTerm.IsNeutral.par_preserves {scope : Nat}
    {sourceRaw targetRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (parallelStep : RawStep.par sourceRaw targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  induction sourceIsNeutral generalizing targetRaw with
  | var position =>
      exact RawTerm.IsNeutral.var_par_preserves parallelStep
  | app functionIsNeutral functionParPreserves =>
      exact RawTerm.IsNeutral.app_par_preserves
        (fun functionStep => functionParPreserves functionStep)
        parallelStep
  | fst pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.fst_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | snd pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.snd_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | boolElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.boolElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natRec scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natRec_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | listElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.listElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | optionMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.optionMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | eitherMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.eitherMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | pathApp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.pathApp_par_preserves
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | glueElim gluedValueIsNeutral gluedParPreserves =>
      exact RawTerm.IsNeutral.glueElim_par_preserves
        (fun gluedStep => gluedParPreserves gluedStep)
        parallelStep
  | transp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.transp_par_preserves
        pathIsNeutral
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | hcomp sidesIsNeutral sidesParPreserves =>
      exact RawTerm.IsNeutral.hcomp_par_preserves
        (fun sidesStep => sidesParPreserves sidesStep)
        parallelStep
  | idJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | oeqJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.oeqJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | idStrictRec witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idStrictRec_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | equivApp equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApp_par_preserves
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | equivApply equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApply_par_preserves
        equivIsNeutral
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | modElim rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.modElim_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | subsume rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.subsume_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | refineElim refinedValueIsNeutral refinedParPreserves =>
      exact RawTerm.IsNeutral.refineElim_par_preserves
        (fun refinedStep => refinedParPreserves refinedStep)
        parallelStep
  | recordProj recordValueIsNeutral recordParPreserves =>
      exact RawTerm.IsNeutral.recordProj_par_preserves
        (fun recordStep => recordParPreserves recordStep)
        parallelStep
  | codataDest codataValueIsNeutral codataParPreserves =>
      exact RawTerm.IsNeutral.codataDest_par_preserves
        (fun codataStep => codataParPreserves codataStep)
        parallelStep
  | sessionSend channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionSend_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | sessionRecv channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionRecv_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | effectPerform operationIsNeutral operationParPreserves =>
      exact RawTerm.IsNeutral.effectPerform_par_preserves
        (fun operationStep => operationParPreserves operationStep)
        parallelStep

end LeanFX2

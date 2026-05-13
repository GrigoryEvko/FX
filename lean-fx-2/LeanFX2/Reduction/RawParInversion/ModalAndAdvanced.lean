import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename

/-! # LeanFX2.Reduction.RawParInversion.ModalAndAdvanced

Inversion lemmas for `RawStep.par` on modal, refinement, record,
codata, session, and effect ctors:

* `modIntro` / `modElim` / `subsume` / `cumulUpMarker`
* `refineIntro` / `refineElim`
* `recordIntro` / `recordProj`
* `codataUnfold` / `codataDest`
* `sessionSend` / `sessionRecv`
* `effectPerform`

`modElim`, `refineElim`, `recordProj`, `codataDest` each admit a β
disjunct in addition to the structural cong.

## Root status

Layer 2 raw parallel-step inversion helper.  Zero axioms. -/

namespace LeanFX2

/-- `RawStep.par (modIntro inner) target → target = modIntro inner' ∧ par`. -/
theorem RawStep.par.modIntro_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modIntro innerTerm) target) :
    ∃ innerTarget, target = RawTerm.modIntro innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modIntro innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (modElim inner) target` either stays a congruent
`modElim`, or fires modal β after the inner value develops to a
`modIntro`. -/
theorem RawStep.par.modElim_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modElim innerTerm) target) :
    (∃ innerTarget, target = RawTerm.modElim innerTarget ∧
      RawStep.par innerTerm innerTarget) ∨
    (∃ payloadTarget, target = payloadTarget ∧
      RawStep.par innerTerm (RawTerm.modIntro payloadTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modElim innerStep => exact Or.inl ⟨_, rfl, innerStep⟩
  | betaModElimIntro innerStep =>
      exact Or.inr ⟨_, rfl, RawStep.par.modIntro innerStep⟩
  | betaModElimIntroDeep innerStep =>
      exact Or.inr ⟨_, rfl, innerStep⟩

/-- `RawStep.par (subsume inner) target → target = subsume inner' ∧ par`. -/
theorem RawStep.par.subsume_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.subsume innerTerm) target) :
    ∃ innerTarget, target = RawTerm.subsume innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | subsume innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (cumulUpMarker inner) target → target = cumulUpMarker inner' ∧ par`.
    CUMUL-2.6 `cumulUpMarkerCong` is the only non-`refl` rule with this source;
    inversion mirrors `subsume_inv` / `modIntro_inv` (single subterm cong).
    Originally lived in `LeanFX2.Term.PreservesTerm`; promoted to the canonical
    inversion file (K12.20.BB) so it's importable from `LeanFX2.Reducibility`. -/
theorem RawStep.par.cumulUpMarker_inv {scope : Nat}
    {innerCodeRaw : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.cumulUpMarker innerCodeRaw) target) :
    ∃ innerTarget, target = RawTerm.cumulUpMarker innerTarget ∧
      RawStep.par innerCodeRaw innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerCodeRaw, rfl, RawStep.par.refl _⟩
  | cumulUpMarkerCong innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (refineIntro v p) target → target = refineIntro v' p' ∧ pars`. -/
theorem RawStep.par.refineIntro_inv {scope : Nat}
    {rawValue predicateProof : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.refineIntro rawValue predicateProof) target) :
    ∃ valueTarget proofTarget,
      target = RawTerm.refineIntro valueTarget proofTarget ∧
        RawStep.par rawValue valueTarget ∧
        RawStep.par predicateProof proofTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨rawValue, predicateProof, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | refineIntroCong valueStep proofStep =>
      exact ⟨_, _, rfl, valueStep, proofStep⟩

/-- `RawStep.par (refineElim r) target` either stays a congruent
`refineElim`, or fires refinement β after the refined value develops
to a `refineIntro`. -/
theorem RawStep.par.refineElim_inv {scope : Nat}
    {refinedValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.refineElim refinedValue) target) :
    (∃ refinedTarget, target = RawTerm.refineElim refinedTarget ∧
      RawStep.par refinedValue refinedTarget) ∨
    (∃ valueTarget proofTarget,
      target = valueTarget ∧
        RawStep.par refinedValue
          (RawTerm.refineIntro valueTarget proofTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨refinedValue, rfl, RawStep.par.refl _⟩
  | betaRefineElimIntro valueStep proofStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.refineIntroCong valueStep proofStep⟩
  | betaRefineElimIntroDeep refinedStep =>
      exact Or.inr ⟨_, _, rfl, refinedStep⟩
  | refineElimCong refinedStep => exact Or.inl ⟨_, rfl, refinedStep⟩

/-- `RawStep.par (recordIntro f) target → target = recordIntro f' ∧ par`. -/
theorem RawStep.par.recordIntro_inv {scope : Nat}
    {firstField : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.recordIntro firstField) target) :
    ∃ firstTarget, target = RawTerm.recordIntro firstTarget ∧
      RawStep.par firstField firstTarget := by
  cases parallelStep with
  | refl _ => exact ⟨firstField, rfl, RawStep.par.refl _⟩
  | recordIntroCong firstStep => exact ⟨_, rfl, firstStep⟩

/-- `RawStep.par (recordProj r) target` either stays a congruent
`recordProj`, or fires record β after the record develops to a
`recordIntro`. -/
theorem RawStep.par.recordProj_inv {scope : Nat}
    {recordValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.recordProj recordValue) target) :
    (∃ recordTarget, target = RawTerm.recordProj recordTarget ∧
      RawStep.par recordValue recordTarget) ∨
    (∃ firstTarget, target = firstTarget ∧
      RawStep.par recordValue (RawTerm.recordIntro firstTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨recordValue, rfl, RawStep.par.refl _⟩
  | betaRecordProjIntro firstStep =>
      exact Or.inr ⟨_, rfl, RawStep.par.recordIntroCong firstStep⟩
  | betaRecordProjIntroDeep recordStep =>
      exact Or.inr ⟨_, rfl, recordStep⟩
  | recordProjCong recordStep => exact Or.inl ⟨_, rfl, recordStep⟩

/-- `RawStep.par (codataUnfold s t) target → target = codataUnfold s' t' ∧ pars`. -/
theorem RawStep.par.codataUnfold_inv {scope : Nat}
    {initialState transition : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.codataUnfold initialState transition) target) :
    ∃ stateTarget transitionTarget,
      target = RawTerm.codataUnfold stateTarget transitionTarget ∧
        RawStep.par initialState stateTarget ∧
        RawStep.par transition transitionTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨initialState, transition, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | codataUnfoldCong stateStep transitionStep =>
      exact ⟨_, _, rfl, stateStep, transitionStep⟩

/-- `RawStep.par (codataDest c) target` either stays a congruent
`codataDest`, or fires codata β after the codata value develops to an
unfold. -/
theorem RawStep.par.codataDest_inv {scope : Nat}
    {codataValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.codataDest codataValue) target) :
    (∃ codataTarget, target = RawTerm.codataDest codataTarget ∧
      RawStep.par codataValue codataTarget) ∨
    (∃ stateTarget transitionTarget,
      target = RawTerm.app transitionTarget stateTarget ∧
        RawStep.par codataValue
          (RawTerm.codataUnfold stateTarget transitionTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨codataValue, rfl, RawStep.par.refl _⟩
  | betaCodataDestUnfold stateStep transitionStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.codataUnfoldCong stateStep transitionStep⟩
  | betaCodataDestUnfoldDeep codataStep =>
      exact Or.inr ⟨_, _, rfl, codataStep⟩
  | codataDestCong codataStep => exact Or.inl ⟨_, rfl, codataStep⟩

/-- `RawStep.par (sessionSend c p) target → target = sessionSend c' p' ∧ pars`. -/
theorem RawStep.par.sessionSend_inv {scope : Nat}
    {channel payload : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.sessionSend channel payload) target) :
    ∃ channelTarget payloadTarget,
      target = RawTerm.sessionSend channelTarget payloadTarget ∧
        RawStep.par channel channelTarget ∧
        RawStep.par payload payloadTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨channel, payload, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | sessionSendCong channelStep payloadStep =>
      exact ⟨_, _, rfl, channelStep, payloadStep⟩

/-- `RawStep.par (sessionRecv c) target → target = sessionRecv c' ∧ par`. -/
theorem RawStep.par.sessionRecv_inv {scope : Nat}
    {channel : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.sessionRecv channel) target) :
    ∃ channelTarget, target = RawTerm.sessionRecv channelTarget ∧
      RawStep.par channel channelTarget := by
  cases parallelStep with
  | refl _ => exact ⟨channel, rfl, RawStep.par.refl _⟩
  | sessionRecvCong channelStep => exact ⟨_, rfl, channelStep⟩

/-- `RawStep.par (effectPerform o a) target → target = effectPerform o' a' ∧ pars`. -/
theorem RawStep.par.effectPerform_inv {scope : Nat}
    {operationTag arguments : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.effectPerform operationTag arguments) target) :
    ∃ operationTarget argumentsTarget,
      target = RawTerm.effectPerform operationTarget argumentsTarget ∧
        RawStep.par operationTag operationTarget ∧
        RawStep.par arguments argumentsTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨operationTag, arguments, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | effectPerformCong operationStep argumentsStep =>
      exact ⟨_, _, rfl, operationStep, argumentsStep⟩

end LeanFX2

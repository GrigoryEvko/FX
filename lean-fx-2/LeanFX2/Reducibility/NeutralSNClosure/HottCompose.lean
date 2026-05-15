import LeanFX2.Reducibility.NeutralSNClosure.RecordRefineCodata

/-! # LeanFX2.Reducibility.NeutralSNClosure.HottCompose

Layer-1 session / effect raw SN witnesses: `sessionRecv`,
`sessionSend`, `effectPerform`.

## Root status

Layer 3 metatheory leaf.  Surviving raw SN witnesses feed the
Term-level direct-case SN cascade (`Term/SN/DirectCases.lean`);
legacy Tait-era groupoid-composition siblings excised after the
Kripke step-indexed reducibility refactor. -/

namespace LeanFX2


/-- Session-type receive operation — pure unary cong over the
channel witness. -/
theorem RawTerm.sessionRecv_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    RawTerm.isStronglyNormalizing (RawTerm.sessionRecv channel) := by
  induction channelIsSN with
  | intro currentChannel _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.sessionRecv currentChannel) ?_
    intro target progressStep
    obtain ⟨channelTarget, targetEq, channelStep⟩ :=
      RawStep.par.sessionRecv_inv progressStep.1
    subst targetEq
    have channelDistinct :
        currentChannel ≠ channelTarget := fun channelEq =>
      progressStep.2 (congrArg RawTerm.sessionRecv channelEq)
    exact inductiveHypothesis channelTarget
      ⟨channelStep, channelDistinct⟩

/-- Session-type send operation bundles a channel with a payload.
Pure binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.sessionSend_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    ∀ {payload : RawTerm scope},
      RawTerm.isStronglyNormalizing payload →
      RawTerm.isStronglyNormalizing
        (RawTerm.sessionSend channel payload) := by
  induction channelIsSN with
  | intro currentChannel _ channelIH =>
    intro payload payloadIsSN
    induction payloadIsSN with
    | intro currentPayload payloadClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sessionSend currentChannel currentPayload) ?_
      intro target progressStep
      obtain ⟨channelTarget, payloadTarget, targetEq,
              channelStep, payloadStep⟩ :=
        RawStep.par.sessionSend_inv progressStep.1
      subst targetEq
      by_cases channelEq : currentChannel = channelTarget
      · subst channelEq
        have payloadDistinct :
            currentPayload ≠ payloadTarget := fun payloadEq =>
          progressStep.2
            (congrArg (RawTerm.sessionSend currentChannel) payloadEq)
        exact innerIH payloadTarget ⟨payloadStep, payloadDistinct⟩
      · have channelProgress :
            RawStep.parProgress currentChannel channelTarget :=
          ⟨channelStep, channelEq⟩
        by_cases payloadEq : currentPayload = payloadTarget
        · subst payloadEq
          exact channelIH channelTarget channelProgress
            (RawTerm.isStronglyNormalizing.intro currentPayload
              payloadClosure)
        · exact channelIH channelTarget channelProgress
            (payloadClosure payloadTarget
              ⟨payloadStep, payloadEq⟩)

/-- Algebraic effect operation invocation bundles an operation tag
with its arguments.  Pure binary cong; pair-style
universal-in-conclusion. -/
theorem RawTerm.effectPerform_isStronglyNormalizing {scope : Nat}
    {operationTag : RawTerm scope}
    (operationIsSN : RawTerm.isStronglyNormalizing operationTag) :
    ∀ {arguments : RawTerm scope},
      RawTerm.isStronglyNormalizing arguments →
      RawTerm.isStronglyNormalizing
        (RawTerm.effectPerform operationTag arguments) := by
  induction operationIsSN with
  | intro currentOperation _ operationIH =>
    intro arguments argumentsIsSN
    induction argumentsIsSN with
    | intro currentArguments argumentsClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.effectPerform currentOperation currentArguments) ?_
      intro target progressStep
      obtain ⟨operationTarget, argumentsTarget, targetEq,
              operationStep, argumentsStep⟩ :=
        RawStep.par.effectPerform_inv progressStep.1
      subst targetEq
      by_cases operationEq : currentOperation = operationTarget
      · subst operationEq
        have argumentsDistinct :
            currentArguments ≠ argumentsTarget := fun argumentsEq =>
          progressStep.2
            (congrArg (RawTerm.effectPerform currentOperation)
              argumentsEq)
        exact innerIH argumentsTarget
          ⟨argumentsStep, argumentsDistinct⟩
      · have operationProgress :
            RawStep.parProgress currentOperation operationTarget :=
          ⟨operationStep, operationEq⟩
        by_cases argumentsEq : currentArguments = argumentsTarget
        · subst argumentsEq
          exact operationIH operationTarget operationProgress
            (RawTerm.isStronglyNormalizing.intro currentArguments
              argumentsClosure)
        · exact operationIH operationTarget operationProgress
            (argumentsClosure argumentsTarget
              ⟨argumentsStep, argumentsEq⟩)


end LeanFX2

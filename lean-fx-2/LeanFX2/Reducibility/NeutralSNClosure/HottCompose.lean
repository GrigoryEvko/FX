import LeanFX2.Reducibility.NeutralSNClosure.RecordRefineCodata

/-! # LeanFX2.Reducibility.NeutralSNClosure.HottCompose

K12.20.AK groupoid-style composition SN preservation:
`pathCompose`, `oeqTrans`, `equivCompose`, plus the Layer-1
session / effect raw SN witnesses: `sessionRecv`, `sessionSend`,
`effectPerform`.

## Root status

Layer 3 metatheory leaf.  Fourth slice of NeutralSNClosure. -/

namespace LeanFX2


/-- **K12.20.AK.1 pathCompose SN preservation** — cubical path
composition.  Pure binary cong over two path witnesses;
pair-style universal-in-conclusion. -/
theorem RawTerm.pathCompose_isStronglyNormalizing {scope : Nat}
    {leftPath : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftPath) :
    ∀ {rightPath : RawTerm scope},
      RawTerm.isStronglyNormalizing rightPath →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathCompose leftPath rightPath) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightPath rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathCompose currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.pathCompose_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct :
            currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2
            (congrArg (RawTerm.pathCompose currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight
              rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AK.2 oeqTrans SN preservation** — observational
equality transitivity.  Pure binary cong over two proof
witnesses. -/
theorem RawTerm.oeqTrans_isStronglyNormalizing {scope : Nat}
    {firstProof : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstProof) :
    ∀ {secondProof : RawTerm scope},
      RawTerm.isStronglyNormalizing secondProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqTrans firstProof secondProof) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondProof secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqTrans currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.oeqTrans_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.oeqTrans currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AK.3 equivCompose SN preservation** — equivalence
composition.  Pure binary cong over two equivalence witnesses. -/
theorem RawTerm.equivCompose_isStronglyNormalizing {scope : Nat}
    {firstEquiv : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstEquiv) :
    ∀ {secondEquiv : RawTerm scope},
      RawTerm.isStronglyNormalizing secondEquiv →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivCompose firstEquiv secondEquiv) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondEquiv secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivCompose currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.equivCompose_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.equivCompose currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AL.1 sessionRecv SN preservation** — session-type
receive operation.  Pure unary cong over the channel witness. -/
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

/-- **K12.20.AL.2 sessionSend SN preservation** — session-type
send operation bundles a channel with a payload.  Pure binary
cong; pair-style universal-in-conclusion. -/
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

/-- **K12.20.AL.3 effectPerform SN preservation** — algebraic
effect operation invocation bundles an operation tag with its
arguments.  Pure binary cong; pair-style universal-in-conclusion. -/
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

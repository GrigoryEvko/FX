import LeanFX2.Term.StrengtheningImage.TotalOnWeakenAtomicUnary

/-! # Term/StrengtheningImage/TotalOnWeakenRecursive

Total-on-weaken wrappers for list, interval, application, codata, session, equivalence, and identity-recursive constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Wave C: 2-IH and 3-IH non-binder totality. -/

/-- 2-IH non-binder totality: `Term.listCons`.  Pure 2-IH ctor — no
extra Ty/RawTerm payloads. -/
theorem isTotalOnWeaken_listCons {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    (headIH : IsTotalOnWeaken headTerm)
    (tailIH : IsTotalOnWeaken tailTerm) :
    IsTotalOnWeaken (Term.listCons headTerm tailTerm) := by
  intro newType
  show (strengthenTyped? (Term.listCons (Term.weaken newType headTerm)
      (Term.weaken newType tailTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next headRecurse =>
      exfalso
      have totHyp := headIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType headTerm))) = true :=
        headRecurse ▸ totHyp
      cases this
  · split
    · next tailRecurse =>
        exfalso
        have totHyp := tailIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType tailTerm))) = true :=
          tailRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalMeet`.  Pure 2-IH cubical
interval meet operator. -/
theorem isTotalOnWeaken_intervalMeet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalMeet leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalMeet
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalJoin`.  Pure 2-IH cubical
interval join operator. -/
theorem isTotalOnWeaken_intervalJoin {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalJoin leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalJoin
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.app`.  Carries two Ty payloads
(domainType, codomainType) + two Term IH (function, argument). -/
theorem isTotalOnWeaken_app {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType)
      functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.app functionTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.app (Term.weaken newType functionTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.codataUnfold`.  One Ty (outputType)
+ two Term IH (initialState, transition).  Note: the dispatcher
strengthens only outputType (stateType is inferred from the IH). -/
theorem isTotalOnWeaken_codataUnfold {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition : Term context (Ty.arrow stateType outputType)
      transitionRaw}
    (stateIH : IsTotalOnWeaken initialState)
    (transitionIH : IsTotalOnWeaken transition) :
    IsTotalOnWeaken (Term.codataUnfold initialState transition) := by
  intro newType
  show (strengthenTyped? (Term.codataUnfold
      (Term.weaken newType initialState)
      (Term.weaken newType transition))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next outputFails =>
      exfalso
      have outputSuccess :
          outputType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some outputType :=
        Ty.strengthen?_weaken outputType
      rw [outputSuccess] at outputFails
      cases outputFails
  · split
    · next stateRecurse =>
        exfalso
        have totHyp := stateIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType initialState))) = true :=
          stateRecurse ▸ totHyp
        cases this
    · split
      · next transitionRecurse =>
          exfalso
          have totHyp := transitionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType transition))) = true :=
            transitionRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.sessionSend`.  One RawTerm
(protocolStep) + one Ty (payloadType) + two Term IH. -/
theorem isTotalOnWeaken_sessionSend {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term context (Ty.session protocolStep) channelRaw}
    {payload : Term context payloadType payloadRaw}
    (channelIH : IsTotalOnWeaken channel)
    (payloadIH : IsTotalOnWeaken payload) :
    IsTotalOnWeaken (Term.sessionSend protocolStep channel payload) := by
  intro newType
  show (strengthenTyped? (Term.sessionSend protocolStep.weaken
      (Term.weaken newType channel)
      (Term.weaken newType payload))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next protocolFails =>
      exfalso
      have protocolSuccess :
          protocolStep.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some protocolStep :=
        RawTerm.strengthen?_weaken protocolStep
      rw [protocolSuccess] at protocolFails
      cases protocolFails
  · split
    · next channelRecurse =>
        exfalso
        have totHyp := channelIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType channel))) = true :=
          channelRecurse ▸ totHyp
        cases this
    · split
      · next payloadRecurse =>
          exfalso
          have totHyp := payloadIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType payload))) = true :=
            payloadRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.equivApp`.  Two Ty payloads
(carrierA, carrierB) + two Term IH (equiv, argument). -/
theorem isTotalOnWeaken_equivApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApp equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApp
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.equivApply`.  Same shape as
`equivApp` — two Ty payloads + two Term IH. -/
theorem isTotalOnWeaken_equivApply {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApply equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApply
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.idJ`.  One Ty (carrier) + two
RawTerm (leftEndpoint, rightEndpoint) + two Term IH (baseCase,
witness). -/
theorem isTotalOnWeaken_idJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.oeqJ`.  Same shape as `idJ`. -/
theorem isTotalOnWeaken_oeqJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.oeqJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.oeqJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.idStrictRec`.  Same shape as `idJ`
plus a `modeIsStrict` value-level parameter. -/
theorem isTotalOnWeaken_idStrictRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idStrictRec modeIsStrict baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idStrictRec modeIsStrict
      (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

end Term

end LeanFX2

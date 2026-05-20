import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeHoTT

/-! # Term/StrengtheningImage/AggregatorTotalBridgeAdvanced

Bridge totality wrappers for heterogeneous equivalence intro, session send, and boolean eliminator.
-/

namespace LeanFX2

namespace Term

/-- Bridge totality wrapper for `Term.equivIntroHet`.  Source type
`Ty.equiv carrierA carrierB` encodes the carriers via mapTwo.  Source
raw `RawTerm.equivIntro forwardRaw backwardRaw` encodes those raws
but NOT leftInvRaw / rightInvRaw.  Take the missing raws as extra
hypotheses. -/
theorem isAggregatorTotal_equivIntroHet_with_inv_raws {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardTotal : IsAggregatorTotal forward)
    (backwardTotal : IsAggregatorTotal backward)
    (leftInvTotal : IsAggregatorTotal leftInv)
    (rightInvTotal : IsAggregatorTotal rightInv)
    (invRawsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierA targetCarrierB : Ty level targetScope}
        {targetForwardRaw targetBackwardRaw : RawTerm targetScope},
        carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA →
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        forwardRaw.partialStrengthen? strengthening.back =
            some targetForwardRaw →
        backwardRaw.partialStrengthen? strengthening.back =
            some targetBackwardRaw →
        ∃ targetLeftInvRaw targetRightInvRaw,
          leftInvRaw.partialStrengthen? strengthening.back =
              some targetLeftInvRaw ∧
          rightInvRaw.partialStrengthen? strengthening.back =
              some targetRightInvRaw) :
    IsAggregatorTotal
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (carrierA.partialStrengthen? strengthening.back)
      (carrierB.partialStrengthen? strengthening.back)
      Ty.equiv = some _ at typeStrengthens
  obtain ⟨targetCarrierA, targetCarrierB, carrierASuccess, carrierBSuccess,
    _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (forwardRaw.partialStrengthen? strengthening.back)
      (backwardRaw.partialStrengthen? strengthening.back)
      RawTerm.equivIntro = some _ at rawStrengthens
  obtain ⟨targetForwardRaw, targetBackwardRaw, forwardRawSuccess,
    backwardRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetLeftInvRaw, targetRightInvRaw, leftInvRawSuccess,
    rightInvRawSuccess⟩ :=
    invRawsTotal strengthening carrierASuccess carrierBSuccess
      forwardRawSuccess backwardRawSuccess
  -- Forward IH: type Ty.arrow carrierA carrierB
  have forwardArrowStrengthens :
      (Ty.arrow carrierA carrierB).partialStrengthen? strengthening.back =
        some (Ty.arrow targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  have backwardArrowStrengthens :
      (Ty.arrow carrierB carrierA).partialStrengthen? strengthening.back =
        some (Ty.arrow targetCarrierB targetCarrierA) := by
    show Option.mapTwo
        (carrierB.partialStrengthen? strengthening.back)
        (carrierA.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  have forwardTotalCall :=
    forwardTotal strengthening forwardArrowStrengthens forwardRawSuccess
  have backwardTotalCall :=
    backwardTotal strengthening backwardArrowStrengthens backwardRawSuccess
  -- Aux weakens for inverse-law type strengthening
  have carrierAWeakenStrengthens :
      carrierA.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierA.weaken := by
    rw [Ty.partialStrengthen?_weaken_lift carrierA strengthening.back,
      carrierASuccess]
    rfl
  have carrierBWeakenStrengthens :
      carrierB.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierB.weaken := by
    rw [Ty.partialStrengthen?_weaken_lift carrierB strengthening.back,
      carrierBSuccess]
    rfl
  have forwardRawWeakenStrengthens :
      forwardRaw.weaken.partialStrengthen? strengthening.back.lift =
        some targetForwardRaw.weaken := by
    rw [RawTerm.partialStrengthen?_weaken_lift forwardRaw
      strengthening.back, forwardRawSuccess]
    rfl
  have backwardRawWeakenStrengthens :
      backwardRaw.weaken.partialStrengthen? strengthening.back.lift =
        some targetBackwardRaw.weaken := by
    rw [RawTerm.partialStrengthen?_weaken_lift backwardRaw
      strengthening.back, backwardRawSuccess]
    rfl
  -- LeftInv codomain reconstruction
  have leftAppForwardStrengthens :
      (RawTerm.app forwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetForwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
    change Option.mapTwo
        (forwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
        RawTerm.app = _
    rw [forwardRawWeakenStrengthens]
    rfl
  have leftAppBackForwardStrengthens :
      (RawTerm.app backwardRaw.weaken
          (RawTerm.app forwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetBackwardRaw.weaken
          (RawTerm.app targetForwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))) := by
    change Option.mapTwo
        (backwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app forwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift)
        RawTerm.app = _
    rw [backwardRawWeakenStrengthens, leftAppForwardStrengthens]
    rfl
  have leftInvCodomainStrengthens :
      (equivIntroHetLeftInverseCodomain carrierA forwardRaw
        backwardRaw).partialStrengthen? strengthening.back.lift =
        some (equivIntroHetLeftInverseCodomain targetCarrierA
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapThree
        (carrierA.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app backwardRaw.weaken
          (RawTerm.app forwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift)
        ((RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩
          ).partialStrengthen? strengthening.back.lift)
        Ty.id = _
    rw [carrierAWeakenStrengthens, leftAppBackForwardStrengthens]
    rfl
  have leftInvTypeStrengthens :
      (equivIntroHetLeftInverseType carrierA forwardRaw
        backwardRaw).partialStrengthen? strengthening.back =
        some (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw) := by
    change Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        ((equivIntroHetLeftInverseCodomain carrierA forwardRaw
          backwardRaw).partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [carrierASuccess, leftInvCodomainStrengthens]
    rfl
  -- RightInv similarly
  have rightAppBackwardStrengthens :
      (RawTerm.app backwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetBackwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
    change Option.mapTwo
        (backwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
        RawTerm.app = _
    rw [backwardRawWeakenStrengthens]
    rfl
  have rightAppForwardBackwardStrengthens :
      (RawTerm.app forwardRaw.weaken
          (RawTerm.app backwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetForwardRaw.weaken
          (RawTerm.app targetBackwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))) := by
    change Option.mapTwo
        (forwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app backwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift)
        RawTerm.app = _
    rw [forwardRawWeakenStrengthens, rightAppBackwardStrengthens]
    rfl
  have rightInvCodomainStrengthens :
      (equivIntroHetRightInverseCodomain carrierB forwardRaw
        backwardRaw).partialStrengthen? strengthening.back.lift =
        some (equivIntroHetRightInverseCodomain targetCarrierB
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapThree
        (carrierB.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app forwardRaw.weaken
          (RawTerm.app backwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift)
        ((RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩
          ).partialStrengthen? strengthening.back.lift)
        Ty.id = _
    rw [carrierBWeakenStrengthens, rightAppForwardBackwardStrengthens]
    rfl
  have rightInvTypeStrengthens :
      (equivIntroHetRightInverseType carrierB forwardRaw
        backwardRaw).partialStrengthen? strengthening.back =
        some (equivIntroHetRightInverseType targetCarrierB
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapTwo
        (carrierB.partialStrengthen? strengthening.back)
        ((equivIntroHetRightInverseCodomain carrierB forwardRaw
          backwardRaw).partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [carrierBSuccess, rightInvCodomainStrengthens]
    rfl
  have leftInvTotalCall :=
    leftInvTotal strengthening leftInvTypeStrengthens leftInvRawSuccess
  have rightInvTotalCall :=
    rightInvTotal strengthening rightInvTypeStrengthens rightInvRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [carrierBSuccess] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next forwardFails =>
              rw [forwardFails] at forwardTotalCall
              cases forwardTotalCall
          · next _ _ =>
              split
              · next backwardFails =>
                  rw [backwardFails] at backwardTotalCall
                  cases backwardTotalCall
              · next _ _ =>
                  split
                  · next leftInvFails =>
                      rw [leftInvFails] at leftInvTotalCall
                      cases leftInvTotalCall
                  · next _ _ =>
                      split
                      · next rightInvFails =>
                          rw [rightInvFails] at rightInvTotalCall
                          cases rightInvTotalCall
                      · rfl

/-- Bridge totality wrapper for `Term.sessionSend`.  Source type is
`Ty.session protocolStep`; dispatcher needs protocolStep.back + channel
IH (Ty.session protocolStep) + payload IH (payloadType).  Take
payloadType.back as extra hypothesis (payloadType is NOT in source). -/
theorem isAggregatorTotal_sessionSend_with_payload {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelTotal : IsAggregatorTotal channel)
    (payloadTotal : IsAggregatorTotal payload)
    (payloadTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetProtocolStep : RawTerm targetScope},
        protocolStep.partialStrengthen? strengthening.back =
            some targetProtocolStep →
        ∃ targetPayloadType,
          payloadType.partialStrengthen? strengthening.back =
            some targetPayloadType) :
    IsAggregatorTotal
      (Term.sessionSend protocolStep channel payload) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens : (Ty.session protocolStep).back = some _
  -- Decompose by changing to the match form
  change (match protocolStep.partialStrengthen? strengthening.back with
          | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
          | none => none) = some _ at typeStrengthens
  split at typeStrengthens
  rotate_left
  · cases typeStrengthens
  next targetProtocolStep protocolSuccess =>
    -- rawStrengthens : (RawTerm.sessionSend channelRaw payloadRaw).back
    change Option.mapTwo
        (channelRaw.partialStrengthen? strengthening.back)
        (payloadRaw.partialStrengthen? strengthening.back)
        RawTerm.sessionSend = some _ at rawStrengthens
    obtain ⟨_, _, channelRawSuccess, payloadRawSuccess, _⟩ :=
      Option.mapTwo_eq_some rawStrengthens
    obtain ⟨targetPayloadType, payloadTypeSuccess⟩ :=
      payloadTypeTotal strengthening protocolSuccess
    -- channel's type strengthens
    have sessionTypeStrengthens :
        (Ty.session (level := level) protocolStep).partialStrengthen?
            strengthening.back =
          some (Ty.session (level := level) targetProtocolStep) := by
      show (match protocolStep.partialStrengthen? strengthening.back with
          | some strengthenedProtocol =>
              some (Ty.session (level := level) strengthenedProtocol)
          | none => none) = _
      rw [protocolSuccess]
    have channelTotalCall :=
      channelTotal strengthening sessionTypeStrengthens channelRawSuccess
    have payloadTotalCall :=
      payloadTotal strengthening payloadTypeSuccess payloadRawSuccess
    unfold partialStrengthenTyped?
    split
    · next protocolFails =>
        rw [protocolSuccess] at protocolFails
        cases protocolFails
    · next _ _ =>
        split
        · next channelFails =>
            rw [channelFails] at channelTotalCall
            cases channelTotalCall
        · next _ _ =>
            split
            · next payloadFails =>
                rw [payloadFails] at payloadTotalCall
                cases payloadTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.boolElim`.  Source type is
`motiveType.subst0 Ty.bool scrutineeRaw`; dispatcher needs
motiveType.back.lift + scrutinee IH (Ty.bool) + thenBranch IH +
elseBranch IH.  Take motiveType.back.lift as extra hypothesis.
thenBranch / elseBranch type strengthenings constructed via
`Ty.partialStrengthen?_subst0_of_success`. -/
theorem isAggregatorTotal_boolElim_with_motive {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (thenTotal : IsAggregatorTotal thenBranch)
    (elseTotal : IsAggregatorTotal elseBranch)
    (motiveTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (motiveType.subst0 Ty.bool scrutineeRaw).partialStrengthen?
            strengthening.back =
            some targetSourceType →
        ∃ targetMotiveType,
          motiveType.partialStrengthen? strengthening.back.lift =
            some targetMotiveType) :
    IsAggregatorTotal
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (thenRaw.partialStrengthen? strengthening.back)
      (elseRaw.partialStrengthen? strengthening.back)
      RawTerm.boolElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, thenRawSuccess, elseRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetMotiveType, motiveSuccess⟩ :=
    motiveTotal strengthening typeStrengthens
  -- scrutinee's type Ty.bool is closed-atomic
  have boolStrengthens :
      (Ty.bool : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.bool := rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening boolStrengthens scrutineeRawSuccess
  -- thenBranch's type: motiveType.subst0 Ty.bool RawTerm.boolTrue
  have boolTrueStrengthens :
      (RawTerm.boolTrue : RawTerm sourceScope).partialStrengthen?
          strengthening.back =
        some RawTerm.boolTrue := rfl
  have boolFalseStrengthens :
      (RawTerm.boolFalse : RawTerm sourceScope).partialStrengthen?
          strengthening.back =
        some RawTerm.boolFalse := rfl
  have thenTypeStrengthens :
      (motiveType.subst0 Ty.bool RawTerm.boolTrue).partialStrengthen?
          strengthening.back =
        some (targetMotiveType.subst0 Ty.bool RawTerm.boolTrue) :=
    Ty.partialStrengthen?_subst0_of_success motiveType targetMotiveType
      Ty.bool Ty.bool RawTerm.boolTrue RawTerm.boolTrue
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward motiveSuccess boolStrengthens
      boolTrueStrengthens
  have elseTypeStrengthens :
      (motiveType.subst0 Ty.bool RawTerm.boolFalse).partialStrengthen?
          strengthening.back =
        some (targetMotiveType.subst0 Ty.bool RawTerm.boolFalse) :=
    Ty.partialStrengthen?_subst0_of_success motiveType targetMotiveType
      Ty.bool Ty.bool RawTerm.boolFalse RawTerm.boolFalse
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward motiveSuccess boolStrengthens
      boolFalseStrengthens
  have thenTotalCall :=
    thenTotal strengthening thenTypeStrengthens thenRawSuccess
  have elseTotalCall :=
    elseTotal strengthening elseTypeStrengthens elseRawSuccess
  unfold partialStrengthenTyped?
  split
  · next motiveFails =>
      rw [motiveSuccess] at motiveFails
      cases motiveFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next thenFails =>
              rw [thenFails] at thenTotalCall
              cases thenTotalCall
          · next _ _ =>
              split
              · next elseFails =>
                  rw [elseFails] at elseTotalCall
                  cases elseTotalCall
              · rfl

end Term

end LeanFX2

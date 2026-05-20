import LeanFX2.Term.PartialStrengthen.Constructors.Effects

/-! # Term/PartialStrengthen/Constructors/HeterogeneousEquivalence

Typed partial-strengthening producers for heterogeneous equivalence
introduction terms.
-/

namespace LeanFX2

namespace Term

/-- Pre-witnessed heterogeneous equivalence introduction
strengthening.  Replaces the wrapper's deep `Option.casesOn` cascade
over `Ty.arrow`'s two pivots plus the four nested
`equivIntroHet*InverseType` derivations with explicit strengthening
witnesses for both carriers and both raw operand terms.  The four
typed children (forward / backward / leftInv / rightInv) and their
target counterparts are passed directly; `targetLeftInvRaw` /
`targetRightInvRaw` are implicit since `RawTerm.equivIntro`'s
schematic raw form only references `forwardRaw` / `backwardRaw`. -/
def partialStrengthenTypedEquivIntroHetOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {targetForwardRaw targetBackwardRaw : RawTerm targetScope}
    {targetLeftInvRaw targetRightInvRaw : RawTerm targetScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (targetForward :
      Term targetCtx (Ty.arrow targetCarrierA targetCarrierB)
        targetForwardRaw)
    (targetBackward :
      Term targetCtx (Ty.arrow targetCarrierB targetCarrierA)
        targetBackwardRaw)
    (targetLeftInv :
      Term targetCtx
        (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw)
        targetLeftInvRaw)
    (targetRightInv :
      Term targetCtx
        (equivIntroHetRightInverseType targetCarrierB targetForwardRaw
          targetBackwardRaw)
        targetRightInvRaw)
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back =
        some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back =
        some targetCarrierB)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    (forwardRawRenames :
      forwardRaw = targetForwardRaw.rename strengthening.forward)
    (backwardRawRenames :
      backwardRaw = targetBackwardRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv) where
  targetType := Ty.equiv targetCarrierA targetCarrierB
  targetRaw := RawTerm.equivIntro targetForwardRaw targetBackwardRaw
  targetTerm :=
    Term.equivIntroHet targetForward targetBackward targetLeftInv
      targetRightInv
  typeStrengthens := by
    change
      Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv =
          some (Ty.equiv targetCarrierA targetCarrierB)
    rw [carrierASuccess, carrierBSuccess]
    rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (forwardRaw.partialStrengthen? strengthening.back)
        (backwardRaw.partialStrengthen? strengthening.back)
        RawTerm.equivIntro =
          some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw)
    rw [forwardRawStrengthens, backwardRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename (Ty.equiv carrierA carrierB)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.equiv targetCarrierA targetCarrierB)
      (by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv =
              some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl)
  rawRenames := by
    cases forwardRawRenames
    cases backwardRawRenames
    rfl

/-- Heterogeneous equivalence introduction strengthens the forward and
backward functions plus their inverse-law proof functions.  The proof
children are aligned by structurally strengthening the named inverse-law
types from `TermHelpers`. -/
def partialStrengthenTypedEquivIntroHet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (forwardResult : StrengtheningResult strengthening forward)
    (backwardResult : StrengtheningResult strengthening backward)
    (leftInvResult : StrengtheningResult strengthening leftInv)
    (rightInvResult : StrengtheningResult strengthening rightInv) :
    StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  cases forwardResult with
  | mk targetForwardType targetForwardRaw targetForward
      forwardTypeStrengthens forwardRawStrengthens forwardTypeRenames
      forwardRawRenames =>
      have expectedForwardTypeStrengthens :
          (Ty.arrow carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.arrow targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.arrow = some (Ty.arrow targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedForwardTypeStrengthens] at forwardTypeStrengthens
      cases forwardTypeStrengthens
      cases backwardResult with
              | mk targetBackwardType targetBackwardRaw targetBackward
                  backwardTypeStrengthens backwardRawStrengthens
                  backwardTypeRenames backwardRawRenames =>
                  have expectedBackwardTypeStrengthens :
                      (Ty.arrow carrierB carrierA).partialStrengthen?
                          strengthening.back =
                        some (Ty.arrow targetCarrierB targetCarrierA) := by
                    change
                      Option.mapTwo
                        (carrierB.partialStrengthen? strengthening.back)
                        (carrierA.partialStrengthen? strengthening.back)
                        Ty.arrow =
                          some (Ty.arrow targetCarrierB targetCarrierA)
                    rw [carrierBSuccess, carrierASuccess]
                    rfl
                  rw [expectedBackwardTypeStrengthens] at backwardTypeStrengthens
                  cases backwardTypeStrengthens
                  have forwardWeakenStrengthens :
                      forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetForwardRaw.weaken := by
                    rw [RawTerm.partialStrengthen?_weaken_lift forwardRaw
                      strengthening.back, forwardRawStrengthens]
                    rfl
                  have backwardWeakenStrengthens :
                      backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetBackwardRaw.weaken := by
                    rw [RawTerm.partialStrengthen?_weaken_lift backwardRaw
                      strengthening.back, backwardRawStrengthens]
                    rfl
                  have carrierAWeakenStrengthens :
                      carrierA.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetCarrierA.weaken := by
                    rw [Ty.partialStrengthen?_weaken_lift carrierA
                      strengthening.back, carrierASuccess]
                    rfl
                  have carrierBWeakenStrengthens :
                      carrierB.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetCarrierB.weaken := by
                    rw [Ty.partialStrengthen?_weaken_lift carrierB
                      strengthening.back, carrierBSuccess]
                    rfl
                  have forwardVarAppStrengthens :
                      (RawTerm.app forwardRaw.weaken
                        (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                        ).partialStrengthen? strengthening.back.lift =
                        some (RawTerm.app targetForwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
                    change
                      Option.mapTwo
                        (forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        (some (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩))
                        RawTerm.app =
                          some (RawTerm.app targetForwardRaw.weaken
                            (RawTerm.var
                              ⟨0, Nat.zero_lt_succ targetScope⟩))
                    rw [forwardWeakenStrengthens]
                    rfl
                  have backwardVarAppStrengthens :
                      (RawTerm.app backwardRaw.weaken
                        (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                        ).partialStrengthen? strengthening.back.lift =
                        some (RawTerm.app targetBackwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
                    change
                      Option.mapTwo
                        (backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        (some (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩))
                        RawTerm.app =
                          some (RawTerm.app targetBackwardRaw.weaken
                            (RawTerm.var
                              ⟨0, Nat.zero_lt_succ targetScope⟩))
                    rw [backwardWeakenStrengthens]
                    rfl
                  have leftNestedAppStrengthens :
                      (RawTerm.app backwardRaw.weaken
                        (RawTerm.app forwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                        ).partialStrengthen? strengthening.back.lift =
                        some
                          (RawTerm.app targetBackwardRaw.weaken
                            (RawTerm.app targetForwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
                    change
                      Option.mapTwo
                        (backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        ((RawTerm.app forwardRaw.weaken
                          (RawTerm.var
                            ⟨0, Nat.zero_lt_succ sourceScope⟩)
                          ).partialStrengthen? strengthening.back.lift)
                        RawTerm.app =
                          some
                            (RawTerm.app targetBackwardRaw.weaken
                              (RawTerm.app targetForwardRaw.weaken
                                (RawTerm.var
                                  ⟨0, Nat.zero_lt_succ targetScope⟩)))
                    rw [backwardWeakenStrengthens, forwardVarAppStrengthens]
                    rfl
                  have rightNestedAppStrengthens :
                      (RawTerm.app forwardRaw.weaken
                        (RawTerm.app backwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                        ).partialStrengthen? strengthening.back.lift =
                        some
                          (RawTerm.app targetForwardRaw.weaken
                            (RawTerm.app targetBackwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
                    change
                      Option.mapTwo
                        (forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        ((RawTerm.app backwardRaw.weaken
                          (RawTerm.var
                            ⟨0, Nat.zero_lt_succ sourceScope⟩)
                          ).partialStrengthen? strengthening.back.lift)
                        RawTerm.app =
                          some
                            (RawTerm.app targetForwardRaw.weaken
                              (RawTerm.app targetBackwardRaw.weaken
                                (RawTerm.var
                                  ⟨0, Nat.zero_lt_succ targetScope⟩)))
                    rw [forwardWeakenStrengthens, backwardVarAppStrengthens]
                    rfl
                  have leftInverseTypeStrengthens :
                      (equivIntroHetLeftInverseType carrierA forwardRaw
                          backwardRaw).partialStrengthen?
                          strengthening.back =
                        some (equivIntroHetLeftInverseType targetCarrierA
                          targetForwardRaw targetBackwardRaw) := by
                    have leftCodomainStrengthens :
                        (equivIntroHetLeftInverseCodomain carrierA
                            forwardRaw backwardRaw).partialStrengthen?
                            strengthening.back.lift =
                          some
                            (equivIntroHetLeftInverseCodomain targetCarrierA
                              targetForwardRaw targetBackwardRaw) := by
                      change
                        Option.mapThree
                          (carrierA.weaken.partialStrengthen?
                            strengthening.back.lift)
                          ((RawTerm.app backwardRaw.weaken
                            (RawTerm.app forwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ sourceScope⟩))
                            ).partialStrengthen? strengthening.back.lift)
                          (some (RawTerm.var
                            ⟨0, Nat.zero_lt_succ targetScope⟩))
                          Ty.id =
                            some
                              (equivIntroHetLeftInverseCodomain
                                targetCarrierA targetForwardRaw
                                targetBackwardRaw)
                      rw [carrierAWeakenStrengthens,
                        leftNestedAppStrengthens]
                      rfl
                    change
                      Option.mapTwo
                        (carrierA.partialStrengthen? strengthening.back)
                        ((equivIntroHetLeftInverseCodomain carrierA
                          forwardRaw backwardRaw).partialStrengthen?
                          strengthening.back.lift)
                        Ty.piTy =
                          some (equivIntroHetLeftInverseType targetCarrierA
                            targetForwardRaw targetBackwardRaw)
                    rw [carrierASuccess, leftCodomainStrengthens]
                    rfl
                  have rightInverseTypeStrengthens :
                      (equivIntroHetRightInverseType carrierB forwardRaw
                          backwardRaw).partialStrengthen?
                          strengthening.back =
                        some (equivIntroHetRightInverseType targetCarrierB
                          targetForwardRaw targetBackwardRaw) := by
                    have rightCodomainStrengthens :
                        (equivIntroHetRightInverseCodomain carrierB
                            forwardRaw backwardRaw).partialStrengthen?
                            strengthening.back.lift =
                          some
                            (equivIntroHetRightInverseCodomain targetCarrierB
                              targetForwardRaw targetBackwardRaw) := by
                      change
                        Option.mapThree
                          (carrierB.weaken.partialStrengthen?
                            strengthening.back.lift)
                          ((RawTerm.app forwardRaw.weaken
                            (RawTerm.app backwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ sourceScope⟩))
                            ).partialStrengthen? strengthening.back.lift)
                          (some (RawTerm.var
                            ⟨0, Nat.zero_lt_succ targetScope⟩))
                          Ty.id =
                            some
                              (equivIntroHetRightInverseCodomain
                                targetCarrierB targetForwardRaw
                                targetBackwardRaw)
                      rw [carrierBWeakenStrengthens,
                        rightNestedAppStrengthens]
                      rfl
                    change
                      Option.mapTwo
                        (carrierB.partialStrengthen? strengthening.back)
                        ((equivIntroHetRightInverseCodomain carrierB
                          forwardRaw backwardRaw).partialStrengthen?
                          strengthening.back.lift)
                        Ty.piTy =
                          some (equivIntroHetRightInverseType targetCarrierB
                            targetForwardRaw targetBackwardRaw)
                    rw [carrierBSuccess, rightCodomainStrengthens]
                    rfl
                  cases leftInvResult with
                  | mk targetLeftInvType targetLeftInvRaw targetLeftInv
                      leftInvTypeStrengthens leftInvRawStrengthens
                      leftInvTypeRenames leftInvRawRenames =>
                      rw [leftInverseTypeStrengthens] at leftInvTypeStrengthens
                      cases leftInvTypeStrengthens
                      cases rightInvResult with
                      | mk targetRightInvType targetRightInvRaw
                          targetRightInv rightInvTypeStrengthens
                          rightInvRawStrengthens rightInvTypeRenames
                          rightInvRawRenames =>
                          rw [rightInverseTypeStrengthens] at rightInvTypeStrengthens
                          cases rightInvTypeStrengthens
                          exact partialStrengthenTypedEquivIntroHetOfSuccess
                            targetForward targetBackward targetLeftInv
                            targetRightInv carrierASuccess carrierBSuccess
                            forwardRawStrengthens backwardRawStrengthens
                            forwardRawRenames backwardRawRenames

end Term

end LeanFX2

import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.HoTTElimSuccess
import LeanFX2.Term.StrengtheningImage.EquivIntroAndEffects

/-! # Term/StrengtheningImage/HoTTAppWrappers

Soundness lemmas for app-pattern wrappers around HoTT and equivalence eliminators.
-/

namespace LeanFX2

namespace Term

/-- Soundness of the App-pattern `partialStrengthenTypedIdJ` wrapper.
Triple-pivot cascade (`carrierSuccess`/`leftSuccess`/`rightSuccess`)
threads through `Ty.id` decomposition on the witness child. -/
theorem partialStrengthenTypedIdJ_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIdJ carrierSuccess leftSuccess rightSuccess
        baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.id targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.id =
                  some (Ty.id targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdJOfSuccess_sound
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedOeqJ` wrapper.
Mirrors `partialStrengthenTypedIdJ_sound` with `Ty.oeq` decomposition. -/
theorem partialStrengthenTypedOeqJ_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqJ carrierSuccess leftSuccess rightSuccess
        baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.oeq targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.oeq =
                  some (Ty.oeq targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedOeqJOfSuccess_sound
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedIdStrictRec`
wrapper.  Same shape as `partialStrengthenTypedIdJ_sound` but with the
strict-identity carrier `Ty.idStrict` plus the `modeIsStrict`
evidence threaded through. -/
theorem partialStrengthenTypedIdStrictRec_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRec modeIsStrict carrierSuccess
        leftSuccess rightSuccess baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.idStrict carrier leftEndpoint
                  rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.idStrict targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.idStrict =
                  some (Ty.idStrict targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdStrictRecOfSuccess_sound
            modeIsStrict
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivApp`
wrapper.  Dual-pivot cascade (`carrierASuccess`/`carrierBSuccess`)
threads through `Ty.equiv` decomposition on the equiv-term child;
the argument child's type aligns via `rw [carrierASuccess]`. -/
theorem partialStrengthenTypedEquivApp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    {equivResult : StrengtheningResult strengthening equivTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (equivSound : StrengtheningSoundness equivResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApp carrierASuccess carrierBSuccess
        equivResult argumentResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivAppOfSuccess_sound
            (equivTerm := equivTerm) (argumentTerm := argumentTerm)
            (carrierASuccess := carrierASuccess)
            (carrierBSuccess := carrierBSuccess)
            (equivRawStrengthens := equivRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (equivRawRenames := equivRawRenames)
            (argumentRawRenames := argumentRawRenames)
            equivSound.termRenames argumentSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivApply`
wrapper.  Same shape as `partialStrengthenTypedEquivApp_sound` — only
the raw constructor differs (univalence-beta vs the regular equiv
application). -/
theorem partialStrengthenTypedEquivApply_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    {equivResult : StrengtheningResult strengthening equivTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (equivSound : StrengtheningSoundness equivResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApply carrierASuccess carrierBSuccess
        equivResult argumentResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivApplyOfSuccess_sound
            (equivTerm := equivTerm) (argumentTerm := argumentTerm)
            (carrierASuccess := carrierASuccess)
            (carrierBSuccess := carrierBSuccess)
            (equivRawStrengthens := equivRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (equivRawRenames := equivRawRenames)
            (argumentRawRenames := argumentRawRenames)
            equivSound.termRenames argumentSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivIntroHet`
wrapper.  Closes the heterogeneous-equivalence introduction soundness
chain: dual carrier pivot, four child results (forward + backward
function carriers, plus heterogeneous inverse-law proof functions
whose codomain types are computed by `equivIntroHet*InverseType`).
Mirrors the wrapper's case-cascade and delegates to
`_OfSuccess_sound`. -/
theorem partialStrengthenTypedEquivIntroHet_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {forwardResult : StrengtheningResult strengthening forward}
    {backwardResult : StrengtheningResult strengthening backward}
    {leftInvResult : StrengtheningResult strengthening leftInv}
    {rightInvResult : StrengtheningResult strengthening rightInv}
    (forwardSound : StrengtheningSoundness forwardResult)
    (backwardSound : StrengtheningSoundness backwardResult)
    (leftInvSound : StrengtheningSoundness leftInvResult)
    (rightInvSound : StrengtheningSoundness rightInvResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivIntroHet carrierASuccess carrierBSuccess
        forwardResult backwardResult leftInvResult rightInvResult) := by
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
                Ty.arrow = some (Ty.arrow targetCarrierB targetCarrierA)
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
                  exact partialStrengthenTypedEquivIntroHetOfSuccess_sound
                    (forward := forward) (backward := backward)
                    (leftInv := leftInv) (rightInv := rightInv)
                    (carrierASuccess := carrierASuccess)
                    (carrierBSuccess := carrierBSuccess)
                    (forwardRawStrengthens := forwardRawStrengthens)
                    (backwardRawStrengthens := backwardRawStrengthens)
                    (forwardRawRenames := forwardRawRenames)
                    (backwardRawRenames := backwardRawRenames)
                    (leftInvRawRenames := leftInvRawRenames)
                    (rightInvRawRenames := rightInvRawRenames)
                    forwardSound.termRenames backwardSound.termRenames
                    leftInvSound.termRenames rightInvSound.termRenames

end Term

end LeanFX2

import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.HoTTIntro
import LeanFX2.Term.StrengtheningImage.HoTTElimSuccess
import LeanFX2.Term.StrengtheningImage.EquivIntroAndEffects
import LeanFX2.Term.StrengtheningImage.HoTTAppWrappers

/-! # Term/StrengtheningImage/DispatcherAdvancedEquiv

Dispatcher-arm soundness for equivalence and heterogeneous HoTT constructors.
-/

namespace LeanFX2

namespace Term

/-- Dispatcher soundness at the `Term.equivApp` arm.  Heterogeneous-carrier
equivalence application: both carrier types strengthen flat (no binder
shift) and the two value children supply IHs via the standard pattern. -/
theorem partialStrengthenTyped?_atEquivApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivTerm strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.equivApp equivTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i equivResult equivRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedEquivApp_sound
            carrierASuccess carrierBSuccess
            (equivIH equivResult equivRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.equivApply` arm.  Univalence-flavoured
equivalence application: same shape as the `equivApp` arm — both carrier
types strengthen flat, two value children supply IHs.  Only the raw
constructor differs (`RawTerm.equivApply` vs `RawTerm.equivApp`). -/
theorem partialStrengthenTyped?_atEquivApply_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivTerm strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.equivApply equivTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i equivResult equivRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedEquivApply_sound
            carrierASuccess carrierBSuccess
            (equivIH equivResult equivRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.uaToEquiv` arm.  Univalence-β extractor:
two flat type witnesses (`leftTy`/`rightTy`), two flat raw witnesses
(`leftTyRaw`/`rightTyRaw`), and one value IH on the universe-path proof.
Universe-level positional forwarding (`innerLevel`/`innerLevelLt`) rides
through the wrapper. -/
theorem partialStrengthenTyped?_atUaToEquiv_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (proofIH : ∀ proofResult,
        partialStrengthenTyped? proof strengthening =
            some proofResult →
          StrengtheningSoundness proofResult)
    (result : StrengtheningResult strengthening
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof))
    (success : partialStrengthenTyped?
        (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
          leftTy rightTy leftTyRaw rightTyRaw proof) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftTy leftTyStrengthens
    split at success
    · cases success
    · rename_i targetRightTy rightTyStrengthens
      split at success
      · cases success
      · rename_i targetLeftTyRaw leftRawStrengthens
        split at success
        · cases success
        · rename_i targetRightTyRaw rightRawStrengthens
          split at success
          · cases success
          · rename_i proofResult proofRecurse
            cases success
            exact partialStrengthenTypedUaToEquiv_sound innerLevel
              innerLevelLt leftTy rightTy targetLeftTy targetRightTy
              leftTyRaw rightTyRaw targetLeftTyRaw targetRightTyRaw
              leftTyStrengthens rightTyStrengthens leftRawStrengthens
              rightRawStrengthens (proofIH proofResult proofRecurse)

/-- Dispatcher soundness at the `Term.equivIntroHet` arm.
Heterogeneous-carrier equivalence introduction: two carrier types plus
four function-shaped IHs (forward, backward, left-inverse, right-inverse).
Six sequential splits feed the wrapper soundness with all four IH
witnesses. -/
theorem partialStrengthenTyped?_atEquivIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
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
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (forwardIH : ∀ forwardResult,
        partialStrengthenTyped? forward strengthening =
            some forwardResult →
          StrengtheningSoundness forwardResult)
    (backwardIH : ∀ backwardResult,
        partialStrengthenTyped? backward strengthening =
            some backwardResult →
          StrengtheningSoundness backwardResult)
    (leftInvIH : ∀ leftInvResult,
        partialStrengthenTyped? leftInv strengthening =
            some leftInvResult →
          StrengtheningSoundness leftInvResult)
    (rightInvIH : ∀ rightInvResult,
        partialStrengthenTyped? rightInv strengthening =
            some rightInvResult →
          StrengtheningSoundness rightInvResult)
    (result : StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv))
    (success : partialStrengthenTyped?
        (Term.equivIntroHet forward backward leftInv rightInv)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i forwardResult forwardRecurse
        split at success
        · cases success
        · rename_i backwardResult backwardRecurse
          split at success
          · cases success
          · rename_i leftInvResult leftInvRecurse
            split at success
            · cases success
            · rename_i rightInvResult rightInvRecurse
              cases success
              exact partialStrengthenTypedEquivIntroHet_sound
                carrierASuccess carrierBSuccess
                (forwardIH forwardResult forwardRecurse)
                (backwardIH backwardResult backwardRecurse)
                (leftInvIH leftInvResult leftInvRecurse)
                (rightInvIH rightInvResult rightInvRecurse)

/-- Dispatcher soundness at the `Term.uaIntroHet` arm.  Heterogeneous
univalence introduction: positional `innerLevel`/`innerLevelLt`, two
carrier-type witnesses, four raw witnesses (`carrierARaw`, `carrierBRaw`,
`forwardRaw`, `backwardRaw`), and a single equivalence-witness value
IH. -/
theorem partialStrengthenTyped?_atUaIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivWitness strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (result : StrengtheningResult strengthening
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness))
    (success : partialStrengthenTyped?
        (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
          carrierARaw carrierBRaw equivWitness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierAStrengthens
    split at success
    · cases success
    · rename_i targetCarrierB carrierBStrengthens
      split at success
      · cases success
      · rename_i targetCarrierARaw carrierARawStrengthens
        split at success
        · cases success
        · rename_i targetCarrierBRaw carrierBRawStrengthens
          split at success
          · cases success
          · rename_i targetForwardRaw forwardRawStrengthens
            split at success
            · cases success
            · rename_i targetBackwardRaw backwardRawStrengthens
              split at success
              · cases success
              · rename_i equivResult equivRecurse
                cases success
                exact partialStrengthenTypedUaIntroHet_sound innerLevel
                  innerLevelLt targetCarrierA targetCarrierB
                  carrierARaw carrierBRaw targetCarrierARaw targetCarrierBRaw
                  targetForwardRaw targetBackwardRaw
                  carrierAStrengthens carrierBStrengthens
                  carrierARawStrengthens carrierBRawStrengthens
                  forwardRawStrengthens backwardRawStrengthens
                  (equivIH equivResult equivRecurse)

/-- Dispatcher soundness at the `Term.funextIntroHet` arm.
Heterogeneous-carrier funext introduction.  Closed leaf: two type
witnesses (`domainType`/`codomainType`) and two lifted raw witnesses
(`applyARaw`/`applyBRaw` under the binder via `strengthening.back.lift`).
No value IH — the wrapper consumes the raw witnesses directly. -/
theorem partialStrengthenTyped?_atFunextIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextIntroHet (context := sourceCtx) domainType codomainType
        applyARaw applyBRaw))
    (success : partialStrengthenTyped?
        (Term.funextIntroHet (context := sourceCtx) domainType codomainType
          applyARaw applyBRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainStrengthens
    split at success
    · cases success
    · rename_i targetCodomainType codomainStrengthens
      split at success
      · cases success
      · rename_i targetApplyARaw applyAStrengthens
        split at success
        · cases success
        · rename_i targetApplyBRaw applyBStrengthens
          cases success
          exact partialStrengthenTypedFunextIntroHet_sound domainType
            codomainType targetDomainType targetCodomainType applyARaw
            applyBRaw targetApplyARaw targetApplyBRaw
            domainStrengthens codomainStrengthens
            applyAStrengthens applyBStrengthens

end Term

end LeanFX2

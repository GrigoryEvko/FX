import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/HoTTIntro

Soundness lemmas for univalence and heterogeneous HoTT introduction producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for univalence-β extraction.  The producer is direct: all
four type/raw pivots (`leftTy`, `rightTy`, `leftTyRaw`, `rightTyRaw`) are
pre-witnessed by hypotheses, and the proof's typeStrengthens is unified
via a synthesized `expectedProofTypeStrengthens` rewrite to discharge
the `Ty.id (Ty.universe ...)` shape.  Mirrors the producer's case chain
so the HEq congruence applies directly. -/
theorem partialStrengthenTypedUaToEquiv_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (targetLeftTy targetRightTy : Ty level targetScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    (targetLeftTyRaw targetRightTyRaw : RawTerm targetScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (leftTyStrengthens :
      leftTy.partialStrengthen? strengthening.back = some targetLeftTy)
    (rightTyStrengthens :
      rightTy.partialStrengthen? strengthening.back = some targetRightTy)
    (leftRawStrengthens :
      leftTyRaw.partialStrengthen? strengthening.back = some targetLeftTyRaw)
    (rightRawStrengthens :
      rightTyRaw.partialStrengthen? strengthening.back = some targetRightTyRaw)
    {proofResult : StrengtheningResult strengthening proof}
    (proofSound : StrengtheningSoundness proofResult) :
    StrengtheningSoundness
      (partialStrengthenTypedUaToEquiv innerLevel innerLevelLt leftTy
        rightTy targetLeftTy targetRightTy leftTyRaw rightTyRaw
        targetLeftTyRaw targetRightTyRaw leftTyStrengthens rightTyStrengthens
        leftRawStrengthens rightRawStrengthens proofResult) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm
      proofTypeStrengthens proofRawStrengthens proofTypeRenames
      proofRawRenames =>
      have expectedProofTypeStrengthens :
          (Ty.id (Ty.universe innerLevel innerLevelLt)
              leftTyRaw rightTyRaw).partialStrengthen? strengthening.back =
            some (Ty.id (Ty.universe innerLevel innerLevelLt)
              targetLeftTyRaw targetRightTyRaw) := by
        change
          Option.mapThree
            ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
              strengthening.back)
            (leftTyRaw.partialStrengthen? strengthening.back)
            (rightTyRaw.partialStrengthen? strengthening.back)
            Ty.id =
              some (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetLeftTyRaw targetRightTyRaw)
        rw [leftRawStrengthens, rightRawStrengthens]
        rfl
      rw [expectedProofTypeStrengthens] at proofTypeStrengthens
      cases proofTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedUaToEquiv,
          StrengtheningResult.renamedTarget] at proofSound ⊢
      have leftTyRenames :
          leftTy = targetLeftTy.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename leftTy
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftTy leftTyStrengthens
      have rightTyRenames :
          rightTy = targetRightTy.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename rightTy
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightTy rightTyStrengthens
      have leftRawRenames :
          leftTyRaw = targetLeftTyRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename leftTyRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftTyRaw leftRawStrengthens
      have rightRawRenames :
          rightTyRaw = targetRightTyRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename rightTyRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightTyRaw rightRawStrengthens
      exact Term.uaToEquiv_HEq_congr leftTyRenames rightTyRenames
        leftRawRenames rightRawRenames proofRawRenames
        proofSound.termRenames

/-- Soundness for heterogeneous funext introduction.  The producer has
no Term children — the strengthened result is built purely from
strengthening witnesses on the four type/raw pivots.  Soundness derives
all four renames via `partialStrengthen?_imp_rename` and applies the HEq
congruence directly. -/
theorem partialStrengthenTypedFunextIntroHet_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1))
    (targetApplyARaw targetApplyBRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyAStrengthens :
      applyARaw.partialStrengthen? strengthening.back.lift =
        some targetApplyARaw)
    (applyBStrengthens :
      applyBRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyBRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextIntroHet domainType codomainType
        targetDomainType targetCodomainType applyARaw applyBRaw
        targetApplyARaw targetApplyBRaw domainStrengthens codomainStrengthens
        applyAStrengthens applyBStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextIntroHet,
      StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainType codomainStrengthens
  have applyARenames :
      applyARaw = targetApplyARaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyARaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyARaw applyAStrengthens
  have applyBRenames :
      applyBRaw = targetApplyBRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyBRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyBRaw applyBStrengthens
  exact Term.funextIntroHet_HEq_congr domainRenames codomainRenames
    applyARenames applyBRenames

/-- Soundness for heterogeneous univalence introduction.  Mirrors the
producer's case chain: cases equivResult, build the expected
`Ty.equiv` and `RawTerm.equivIntro` strengthenings via the six pre-
witnesses, rw + cases to unify the equiv type and raw, then apply
`uaIntroHet_HEq_congr` with the derived renames. -/
theorem partialStrengthenTypedUaIntroHet_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (targetCarrierA targetCarrierB : Ty level targetScope)
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    (targetCarrierARaw targetCarrierBRaw : RawTerm targetScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (targetForwardRaw targetBackwardRaw : RawTerm targetScope)
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (carrierAStrengthens :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBStrengthens :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (carrierARawStrengthens :
      carrierARaw.partialStrengthen? strengthening.back =
        some targetCarrierARaw)
    (carrierBRawStrengthens :
      carrierBRaw.partialStrengthen? strengthening.back =
        some targetCarrierBRaw)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    {equivResult : StrengtheningResult strengthening equivWitness}
    (equivSound : StrengtheningSoundness equivResult) :
    StrengtheningSoundness
      (partialStrengthenTypedUaIntroHet innerLevel innerLevelLt
        targetCarrierA targetCarrierB carrierARaw carrierBRaw
        targetCarrierARaw targetCarrierBRaw targetForwardRaw targetBackwardRaw
        carrierAStrengthens carrierBStrengthens carrierARawStrengthens
        carrierBRawStrengthens forwardRawStrengthens backwardRawStrengthens
        equivResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivWitness
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
            Ty.equiv =
              some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierAStrengthens, carrierBStrengthens]
        rfl
      have expectedEquivRawStrengthens :
          (RawTerm.equivIntro forwardRaw backwardRaw).partialStrengthen?
              strengthening.back =
            some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw) := by
        change
          Option.mapTwo
            (forwardRaw.partialStrengthen? strengthening.back)
            (backwardRaw.partialStrengthen? strengthening.back)
            RawTerm.equivIntro =
              some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw)
        rw [forwardRawStrengthens, backwardRawStrengthens]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      rw [expectedEquivRawStrengthens] at equivRawStrengthens
      cases equivTypeStrengthens
      cases equivRawStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedUaIntroHet,
          StrengtheningResult.renamedTarget] at equivSound ⊢
      have carrierARenames :
          carrierA = targetCarrierA.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrierA
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierA carrierAStrengthens
      have carrierBRenames :
          carrierB = targetCarrierB.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrierB
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierB carrierBStrengthens
      have carrierARawRenames :
          carrierARaw = targetCarrierARaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename carrierARaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierARaw carrierARawStrengthens
      have carrierBRawRenames :
          carrierBRaw = targetCarrierBRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename carrierBRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierBRaw carrierBRawStrengthens
      have forwardRawRenames :
          forwardRaw = targetForwardRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename forwardRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetForwardRaw forwardRawStrengthens
      have backwardRawRenames :
          backwardRaw = targetBackwardRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename backwardRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetBackwardRaw backwardRawStrengthens
      exact Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        carrierARenames carrierBRenames carrierARawRenames carrierBRawRenames
        forwardRawRenames backwardRawRenames equivSound.termRenames

end Term

end LeanFX2

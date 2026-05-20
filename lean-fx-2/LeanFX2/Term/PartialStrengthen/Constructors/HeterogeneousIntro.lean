import LeanFX2.Term.PartialStrengthen.Constructors.EquivalenceApplications

/-! # Term/PartialStrengthen/Constructors/HeterogeneousIntro

Typed partial-strengthening producers for heterogeneous funext and
univalence introduction terms.
-/

namespace LeanFX2

namespace Term

/-- Heterogeneous funext-introduction strengthens its flat arrow
identity type and the two binder-scoped apply payloads. -/
def partialStrengthenTypedFunextIntroHet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
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
    StrengtheningResult strengthening
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) where
  targetType :=
    Ty.id (Ty.arrow targetDomainType targetCodomainType)
      (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw)
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyARaw)
  targetTerm :=
    Term.funextIntroHet (context := targetCtx)
      targetDomainType targetCodomainType targetApplyARaw targetApplyBRaw
  typeStrengthens := by
    have arrowStrengthens :
        (Ty.arrow domainType codomainType).partialStrengthen?
            strengthening.back =
          some (Ty.arrow targetDomainType targetCodomainType) := by
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow =
            some (Ty.arrow targetDomainType targetCodomainType)
      rw [domainStrengthens, codomainStrengthens]
      rfl
    have leftLamStrengthens :
        (RawTerm.lam applyARaw).partialStrengthen? strengthening.back =
          some (RawTerm.lam targetApplyARaw) := by
      change RawTerm.partialRename? applyARaw strengthening.back.lift =
        some targetApplyARaw at applyAStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      rw [applyAStrengthens]
    have rightLamStrengthens :
        (RawTerm.lam applyBRaw).partialStrengthen? strengthening.back =
          some (RawTerm.lam targetApplyBRaw) := by
      change RawTerm.partialRename? applyBRaw strengthening.back.lift =
        some targetApplyBRaw at applyBStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      rw [applyBStrengthens]
    change
      Option.mapThree
        ((Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam applyARaw).partialStrengthen? strengthening.back)
        ((RawTerm.lam applyBRaw).partialStrengthen? strengthening.back)
        Ty.id =
          some
            (Ty.id (Ty.arrow targetDomainType targetCodomainType)
              (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw))
    rw [arrowStrengthens, leftLamStrengthens, rightLamStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyARaw strengthening.back.lift =
      some targetApplyARaw at applyAStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyAStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (Ty.id (Ty.arrow targetDomainType targetCodomainType)
          (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw))
        (by
          have arrowStrengthens :
              (Ty.arrow domainType codomainType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetDomainType targetCodomainType) := by
            change
              Option.mapTwo
                (domainType.partialStrengthen? strengthening.back)
                (codomainType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
            rw [domainStrengthens, codomainStrengthens]
            rfl
          have leftLamStrengthens :
              (RawTerm.lam applyARaw).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam targetApplyARaw) := by
            change RawTerm.partialRename? applyARaw
              strengthening.back.lift = some targetApplyARaw at applyAStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            rw [applyAStrengthens]
          have rightLamStrengthens :
              (RawTerm.lam applyBRaw).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam targetApplyBRaw) := by
            change RawTerm.partialRename? applyBRaw
              strengthening.back.lift = some targetApplyBRaw at applyBStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            rw [applyBStrengthens]
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam applyARaw).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam applyBRaw).partialStrengthen?
                strengthening.back)
              Ty.id =
                some
                  (Ty.id (Ty.arrow targetDomainType targetCodomainType)
                    (RawTerm.lam targetApplyARaw)
                    (RawTerm.lam targetApplyBRaw))
          rw [arrowStrengthens, leftLamStrengthens, rightLamStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyARaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyARaw))
        (by
          change RawTerm.partialRename? applyARaw strengthening.back.lift =
            some targetApplyARaw at applyAStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyAStrengthens])

/-- Heterogeneous univalence introduction strengthens by strengthening
the packaged equivalence witness and the schematic universe endpoints. -/
def partialStrengthenTypedUaIntroHet {mode : Mode} {level : Nat}
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
    (equivResult : StrengtheningResult strengthening equivWitness) :
    StrengtheningResult strengthening
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
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
      exact {
        targetType :=
          Ty.id (Ty.universe innerLevel innerLevelLt)
            targetCarrierARaw targetCarrierBRaw
        targetRaw := RawTerm.equivIntro targetForwardRaw targetBackwardRaw
        targetTerm :=
          Term.uaIntroHet (context := targetCtx) innerLevel innerLevelLt
            targetCarrierARaw targetCarrierBRaw targetEquivWitness
        typeStrengthens := by
          change
            Option.mapThree
              ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
                strengthening.back)
              (carrierARaw.partialStrengthen? strengthening.back)
              (carrierBRaw.partialStrengthen? strengthening.back)
              Ty.id =
                some (Ty.id (Ty.universe innerLevel innerLevelLt)
                  targetCarrierARaw targetCarrierBRaw)
          rw [carrierARawStrengthens, carrierBRawStrengthens]
          rfl
        rawStrengthens := expectedEquivRawStrengthens
        typeRenames := by
          exact
            Ty.partialStrengthen?_imp_rename
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                carrierARaw carrierBRaw)
              strengthening.forward strengthening.back
              strengthening.injectsBack
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetCarrierARaw targetCarrierBRaw)
              (by
                change
                  Option.mapThree
                    ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
                      strengthening.back)
                    (carrierARaw.partialStrengthen? strengthening.back)
                    (carrierBRaw.partialStrengthen? strengthening.back)
                    Ty.id =
                      some (Ty.id (Ty.universe innerLevel innerLevelLt)
                        targetCarrierARaw targetCarrierBRaw)
                rw [carrierARawStrengthens, carrierBRawStrengthens]
                rfl)
        rawRenames := by
          cases equivRawRenames
          rfl
      }

end Term

end LeanFX2

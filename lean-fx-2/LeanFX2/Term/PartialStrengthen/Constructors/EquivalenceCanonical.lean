import LeanFX2.Term.PartialStrengthen.Constructors.CumulAndTypeCodes

/-! # Term/PartialStrengthen/Constructors/EquivalenceCanonical

Typed partial-strengthening producers for canonical identity equivalences
and funext reflexivity witnesses.
-/

namespace LeanFX2

namespace Term

/-- Canonical identity-equivalence terms strengthen by strengthening
their carrier type.  The raw identity functions are binder-local, so
they survive every context strengthening unchanged except for scope. -/
def partialStrengthenTypedEquivReflId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier) :
    StrengtheningResult strengthening
      (Term.equivReflId (context := sourceCtx) carrier) where
  targetType := Ty.equiv targetCarrier targetCarrier
  targetRaw :=
    RawTerm.equivIntro
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
  targetTerm := Term.equivReflId (context := targetCtx) targetCarrier
  typeStrengthens := by
    change
      Option.mapTwo
        (carrier.partialStrengthen? strengthening.back)
        (carrier.partialStrengthen? strengthening.back)
        Ty.equiv =
          some (Ty.equiv targetCarrier targetCarrier)
    rw [carrierStrengthens]
    rfl
  rawStrengthens := rfl
  typeRenames := by
    rw [Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierStrengthens]
    rfl
  rawRenames := rfl

/-- Canonical universe-identity equivalence witnesses strengthen by
strengthening the represented carrier type and raw universe endpoint.
The proof raw itself is the same binder-local identity equivalence as
`partialStrengthenTypedEquivReflId`. -/
def partialStrengthenTypedEquivReflIdAtId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierRaw : RawTerm sourceScope)
    (targetCarrierRaw : RawTerm targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (carrierRawStrengthens :
      carrierRaw.partialStrengthen? strengthening.back =
        some targetCarrierRaw) :
    StrengtheningResult strengthening
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
        carrier carrierRaw) where
  targetType :=
    Ty.id (Ty.universe innerLevel innerLevelLt)
      targetCarrierRaw targetCarrierRaw
  targetRaw :=
    RawTerm.equivIntro
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
  targetTerm :=
    by
      have carrierRenames :
          carrier = targetCarrier.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrier
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrier carrierStrengthens
      exact Term.equivReflIdAtId (context := targetCtx) innerLevel innerLevelLt
        targetCarrier targetCarrierRaw
  typeStrengthens := by
    change
      Option.mapThree
        ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
          strengthening.back)
        (carrierRaw.partialStrengthen? strengthening.back)
        (carrierRaw.partialStrengthen? strengthening.back)
        Ty.id =
          some (Ty.id (Ty.universe innerLevel innerLevelLt)
            targetCarrierRaw targetCarrierRaw)
    rw [carrierRawStrengthens]
    rfl
  rawStrengthens := rfl
  typeRenames := by
    rw [RawTerm.partialStrengthen?_imp_rename carrierRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierRaw carrierRawStrengthens]
    rfl
  rawRenames := rfl

/-- Canonical funext reflexivity terms strengthen by strengthening the
domain, codomain, and the binder-scoped apply payload. -/
def partialStrengthenTypedFunextRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningResult strengthening
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) where
  targetType :=
    funextReflType targetDomainType targetCodomainType targetApplyRaw
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyRaw)
  targetTerm :=
    Term.funextRefl (context := targetCtx)
      targetDomainType targetCodomainType targetApplyRaw
  typeStrengthens := by
    have codomainWeakenStrengthens :
        codomainType.weaken.partialStrengthen? strengthening.back.lift =
          some targetCodomainType.weaken := by
      rw [Ty.partialStrengthen?_weaken_lift codomainType
        strengthening.back, codomainStrengthens]
      rfl
    have bodyStrengthens :
        (Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
            strengthening.back.lift =
          some (Ty.id targetCodomainType.weaken targetApplyRaw
            targetApplyRaw) := by
      change
        Option.mapThree
          (codomainType.weaken.partialStrengthen? strengthening.back.lift)
          (applyRaw.partialStrengthen? strengthening.back.lift)
          (applyRaw.partialStrengthen? strengthening.back.lift)
          Ty.id =
            some (Ty.id targetCodomainType.weaken targetApplyRaw
              targetApplyRaw)
      rw [codomainWeakenStrengthens, applyStrengthens]
      rfl
    change
      Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
          strengthening.back.lift)
        Ty.piTy =
          some
            (funextReflType targetDomainType targetCodomainType
              targetApplyRaw)
    rw [domainStrengthens, bodyStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyRaw strengthening.back.lift =
      some targetApplyRaw at applyStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (funextReflType domainType codomainType applyRaw)
        strengthening.forward strengthening.back strengthening.injectsBack
        (funextReflType targetDomainType targetCodomainType targetApplyRaw)
        (by
          have codomainWeakenStrengthens :
              codomainType.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetCodomainType.weaken := by
            rw [Ty.partialStrengthen?_weaken_lift codomainType
              strengthening.back, codomainStrengthens]
            rfl
          have bodyStrengthens :
              (Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
                  strengthening.back.lift =
                some (Ty.id targetCodomainType.weaken targetApplyRaw
                  targetApplyRaw) := by
            change
              Option.mapThree
                (codomainType.weaken.partialStrengthen?
                  strengthening.back.lift)
                (applyRaw.partialStrengthen? strengthening.back.lift)
                (applyRaw.partialStrengthen? strengthening.back.lift)
                Ty.id =
                  some (Ty.id targetCodomainType.weaken targetApplyRaw
                    targetApplyRaw)
            rw [codomainWeakenStrengthens, applyStrengthens]
            rfl
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
                strengthening.back.lift)
              Ty.piTy =
                some
                  (funextReflType targetDomainType targetCodomainType
                    targetApplyRaw)
          rw [domainStrengthens, bodyStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyRaw))
        (by
          change RawTerm.partialRename? applyRaw strengthening.back.lift =
            some targetApplyRaw at applyStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyStrengthens])

/-- Id-typed funext reflexivity witnesses use the same strengthened raw
payload as `partialStrengthenTypedFunextRefl`, with a flat arrow
identity carrier. -/
def partialStrengthenTypedFunextReflAtId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningResult strengthening
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) where
  targetType :=
    Ty.id (Ty.arrow targetDomainType targetCodomainType)
      (RawTerm.lam (RawTerm.refl targetApplyRaw))
      (RawTerm.lam (RawTerm.refl targetApplyRaw))
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyRaw)
  targetTerm :=
    Term.funextReflAtId (context := targetCtx)
      targetDomainType targetCodomainType targetApplyRaw
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
    have rawLamStrengthens :
        (RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
            strengthening.back =
          some (RawTerm.lam (RawTerm.refl targetApplyRaw)) := by
      change RawTerm.partialRename? applyRaw strengthening.back.lift =
        some targetApplyRaw at applyStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      simp only [RawTerm.partialRename?]
      rw [applyStrengthens]
    change
      Option.mapThree
        ((Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
          strengthening.back)
        Ty.id =
          some
            (Ty.id (Ty.arrow targetDomainType targetCodomainType)
              (RawTerm.lam (RawTerm.refl targetApplyRaw))
              (RawTerm.lam (RawTerm.refl targetApplyRaw)))
    rw [arrowStrengthens, rawLamStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyRaw strengthening.back.lift =
      some targetApplyRaw at applyStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam (RawTerm.refl applyRaw))
          (RawTerm.lam (RawTerm.refl applyRaw)))
        strengthening.forward strengthening.back strengthening.injectsBack
        (Ty.id (Ty.arrow targetDomainType targetCodomainType)
          (RawTerm.lam (RawTerm.refl targetApplyRaw))
          (RawTerm.lam (RawTerm.refl targetApplyRaw)))
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
          have rawLamStrengthens :
              (RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam (RawTerm.refl targetApplyRaw)) := by
            change RawTerm.partialRename? applyRaw strengthening.back.lift =
              some targetApplyRaw at applyStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            simp only [RawTerm.partialRename?]
            rw [applyStrengthens]
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                strengthening.back)
              Ty.id =
                some
                  (Ty.id (Ty.arrow targetDomainType targetCodomainType)
                    (RawTerm.lam (RawTerm.refl targetApplyRaw))
                    (RawTerm.lam (RawTerm.refl targetApplyRaw)))
          rw [arrowStrengthens, rawLamStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyRaw))
        (by
          change RawTerm.partialRename? applyRaw strengthening.back.lift =
            some targetApplyRaw at applyStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyStrengthens])

end Term

end LeanFX2

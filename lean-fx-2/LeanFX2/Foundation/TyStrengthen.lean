import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawPartialRename.Strengthen
import LeanFX2.Foundation.RawPartialRename.Inversion.OptionPatterns

/-! # Type partial strengthening.

`Ty.partialStrengthen?` is the type-index counterpart to
`RawTerm.partialStrengthen?`.  It is the propagation layer that keeps
typed strengthening from degenerating into a brute-force cross-product:
future `Term.partialStrengthen?` can align the type index via this
single structural recursion and the raw index via `RawTerm.partialStrengthen?`.
-/

namespace LeanFX2

/-- Apply a partial strengthening to every scope-indexed component of a
type.  Raw endpoints use `RawTerm.partialStrengthen?`; binder payloads
use `PartialRawRenaming.lift`, matching `Ty.rename`'s binder behavior. -/
def Ty.partialStrengthen? {level : Nat} : ∀ {sourceScope targetScope : Nat},
    Ty level sourceScope →
    PartialRawRenaming sourceScope targetScope →
    Option (Ty level targetScope)
  | _, _, .unit, _ => some .unit
  | _, _, .bool, _ => some .bool
  | _, _, .nat, _ => some .nat
  | _, _, .arrow domainType codomainType, back =>
      Option.mapTwo
        (domainType.partialStrengthen? back)
        (codomainType.partialStrengthen? back)
        Ty.arrow
  | _, _, .piTy domainType codomainType, back =>
      Option.mapTwo
        (domainType.partialStrengthen? back)
        (codomainType.partialStrengthen? back.lift)
        Ty.piTy
  | _, _, .sigmaTy firstType secondType, back =>
      Option.mapTwo
        (firstType.partialStrengthen? back)
        (secondType.partialStrengthen? back.lift)
        Ty.sigmaTy
  | _, _, .tyVar position, back =>
      match back position with
      | some targetPosition => some (Ty.tyVar targetPosition)
      | none => none
  | _, _, .id carrier leftEndpoint rightEndpoint, back =>
      Option.mapThree
        (carrier.partialStrengthen? back)
        (leftEndpoint.partialStrengthen? back)
        (rightEndpoint.partialStrengthen? back)
        Ty.id
  | _, _, .listType elementType, back =>
      match elementType.partialStrengthen? back with
      | some strengthenedElement => some (Ty.listType strengthenedElement)
      | none => none
  | _, _, .optionType elementType, back =>
      match elementType.partialStrengthen? back with
      | some strengthenedElement => some (Ty.optionType strengthenedElement)
      | none => none
  | _, _, .eitherType leftType rightType, back =>
      Option.mapTwo
        (leftType.partialStrengthen? back)
        (rightType.partialStrengthen? back)
        Ty.eitherType
  | _, _, .universe universeLevel levelLe, _ =>
      some (Ty.universe universeLevel levelLe)
  | _, _, .empty, _ => some .empty
  | _, _, .interval, _ => some .interval
  | _, _, .path carrier leftEndpoint rightEndpoint, back =>
      Option.mapThree
        (carrier.partialStrengthen? back)
        (leftEndpoint.partialStrengthen? back)
        (rightEndpoint.partialStrengthen? back)
        Ty.path
  | _, _, .glue baseType boundaryWitness, back =>
      Option.mapTwo
        (baseType.partialStrengthen? back)
        (boundaryWitness.partialStrengthen? back)
        Ty.glue
  | _, _, .oeq carrier leftEndpoint rightEndpoint, back =>
      Option.mapThree
        (carrier.partialStrengthen? back)
        (leftEndpoint.partialStrengthen? back)
        (rightEndpoint.partialStrengthen? back)
        Ty.oeq
  | _, _, .idStrict carrier leftEndpoint rightEndpoint, back =>
      Option.mapThree
        (carrier.partialStrengthen? back)
        (leftEndpoint.partialStrengthen? back)
        (rightEndpoint.partialStrengthen? back)
        Ty.idStrict
  | _, _, .equiv domainType codomainType, back =>
      Option.mapTwo
        (domainType.partialStrengthen? back)
        (codomainType.partialStrengthen? back)
        Ty.equiv
  | _, _, .refine baseType predicate, back =>
      Option.mapTwo
        (baseType.partialStrengthen? back)
        (predicate.partialStrengthen? back.lift)
        Ty.refine
  | _, _, .record singleFieldType, back =>
      match singleFieldType.partialStrengthen? back with
      | some strengthenedField => some (Ty.record strengthenedField)
      | none => none
  | _, _, .codata stateType outputType, back =>
      Option.mapTwo
        (stateType.partialStrengthen? back)
        (outputType.partialStrengthen? back)
        Ty.codata
  | _, _, .session protocolStep, back =>
      match protocolStep.partialStrengthen? back with
      | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
      | none => none
  | _, _, .effect carrierType effectTag, back =>
      Option.mapTwo
        (carrierType.partialStrengthen? back)
        (effectTag.partialStrengthen? back)
        Ty.effect
  | _, _, .modal modalityTag carrierType, back =>
      match carrierType.partialStrengthen? back with
      | some strengthenedCarrier => some (Ty.modal modalityTag strengthenedCarrier)
      | none => none

/-- Single-newest-slot type strengthening. -/
@[reducible] def Ty.strengthen? {level scope : Nat}
    (someType : Ty level (scope + 1)) : Option (Ty level scope) :=
  someType.partialStrengthen? PartialRawRenaming.dropNewest

/-- Semantic newest-slot use predicate for types. -/
def Ty.usesNewestSlot? {level scope : Nat}
    (someType : Ty level (scope + 1)) : Bool :=
  (someType.strengthen?).isNone

set_option linter.unusedVariables false in
/-- Successful type partial strengthening reconstructs the original type
by renaming the strengthened type forward. -/
theorem Ty.partialStrengthen?_imp_rename {level : Nat} :
    ∀ {sourceScope targetScope : Nat}
      (someType : Ty level sourceScope)
      (forwardRenaming : RawRenaming targetScope sourceScope)
      (back : PartialRawRenaming sourceScope targetScope)
      (renamingInjectsBack :
        ∀ (intermediatePos : Fin sourceScope)
          (sourcePos : Fin targetScope),
          back intermediatePos = some sourcePos →
          intermediatePos = forwardRenaming sourcePos)
      (extracted : Ty level targetScope),
      someType.partialStrengthen? back = some extracted →
      someType = extracted.rename forwardRenaming := by
  intro sourceScope targetScope someType
  induction someType generalizing targetScope with
  | unit =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | bool =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | nat =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨domainExtracted, codomainExtracted,
        domainSuccess, codomainSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [domainIH forwardRenaming back renamingInjectsBack
            domainExtracted domainSuccess,
          codomainIH forwardRenaming back renamingInjectsBack
            codomainExtracted codomainSuccess]
  | piTy domainType codomainType domainIH codomainIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨domainExtracted, codomainExtracted,
        domainSuccess, codomainSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [domainIH forwardRenaming back renamingInjectsBack
            domainExtracted domainSuccess,
          codomainIH forwardRenaming.lift back.lift
            (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
            codomainExtracted codomainSuccess]
  | sigmaTy firstType secondType firstIH secondIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨firstExtracted, secondExtracted,
        firstSuccess, secondSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [firstIH forwardRenaming back renamingInjectsBack
            firstExtracted firstSuccess,
          secondIH forwardRenaming.lift back.lift
            (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
            secondExtracted secondSuccess]
  | tyVar position =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match back position with
        | some targetPosition => some (Ty.tyVar targetPosition)
        | none => none) = some extracted at success
      cases hBack : back position with
      | none =>
          rw [show (match back position with
              | some targetPosition => some (Ty.tyVar targetPosition)
              | none => none) = none by rw [hBack]] at success
          cases success
      | some targetPosition =>
          rw [show (match back position with
              | some targetPosition => some (Ty.tyVar targetPosition)
              | none => none) = some (Ty.tyVar targetPosition) by rw [hBack]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          exact congrArg Ty.tyVar (renamingInjectsBack position targetPosition hBack)
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨carrierExtracted, leftExtracted, rightExtracted,
        carrierSuccess, leftSuccess, rightSuccess, extractedEq⟩ :=
        Option.mapThree_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted carrierSuccess,
          RawTerm.partialStrengthen?_imp_rename leftEndpoint forwardRenaming back
            renamingInjectsBack leftExtracted leftSuccess,
          RawTerm.partialStrengthen?_imp_rename rightEndpoint forwardRenaming back
            renamingInjectsBack rightExtracted rightSuccess]
  | listType elementType elementIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match elementType.partialStrengthen? back with
        | some strengthenedElement => some (Ty.listType strengthenedElement)
        | none => none) = some extracted at success
      cases hElement : elementType.partialStrengthen? back with
      | none =>
          rw [show (match elementType.partialStrengthen? back with
              | some strengthenedElement => some (Ty.listType strengthenedElement)
              | none => none) = none by rw [hElement]] at success
          cases success
      | some elementExtracted =>
          rw [show (match elementType.partialStrengthen? back with
              | some strengthenedElement => some (Ty.listType strengthenedElement)
              | none => none) = some (Ty.listType elementExtracted) by rw [hElement]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          rw [elementIH forwardRenaming back renamingInjectsBack
            elementExtracted hElement]
  | optionType elementType elementIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match elementType.partialStrengthen? back with
        | some strengthenedElement => some (Ty.optionType strengthenedElement)
        | none => none) = some extracted at success
      cases hElement : elementType.partialStrengthen? back with
      | none =>
          rw [show (match elementType.partialStrengthen? back with
              | some strengthenedElement => some (Ty.optionType strengthenedElement)
              | none => none) = none by rw [hElement]] at success
          cases success
      | some elementExtracted =>
          rw [show (match elementType.partialStrengthen? back with
              | some strengthenedElement => some (Ty.optionType strengthenedElement)
              | none => none) = some (Ty.optionType elementExtracted) by rw [hElement]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          rw [elementIH forwardRenaming back renamingInjectsBack
            elementExtracted hElement]
  | eitherType leftType rightType leftIH rightIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨leftExtracted, rightExtracted,
        leftSuccess, rightSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [leftIH forwardRenaming back renamingInjectsBack
            leftExtracted leftSuccess,
          rightIH forwardRenaming back renamingInjectsBack
            rightExtracted rightSuccess]
  | «universe» universeLevel levelLe =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | empty =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | interval =>
      intro forwardRenaming back renamingInjectsBack extracted success
      injection success with extractedEq
      rw [← extractedEq]
      rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨carrierExtracted, leftExtracted, rightExtracted,
        carrierSuccess, leftSuccess, rightSuccess, extractedEq⟩ :=
        Option.mapThree_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted carrierSuccess,
          RawTerm.partialStrengthen?_imp_rename leftEndpoint forwardRenaming back
            renamingInjectsBack leftExtracted leftSuccess,
          RawTerm.partialStrengthen?_imp_rename rightEndpoint forwardRenaming back
            renamingInjectsBack rightExtracted rightSuccess]
  | glue baseType boundaryWitness baseIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨baseExtracted, boundaryExtracted,
        baseSuccess, boundarySuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [baseIH forwardRenaming back renamingInjectsBack
            baseExtracted baseSuccess,
          RawTerm.partialStrengthen?_imp_rename boundaryWitness forwardRenaming back
            renamingInjectsBack boundaryExtracted boundarySuccess]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨carrierExtracted, leftExtracted, rightExtracted,
        carrierSuccess, leftSuccess, rightSuccess, extractedEq⟩ :=
        Option.mapThree_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted carrierSuccess,
          RawTerm.partialStrengthen?_imp_rename leftEndpoint forwardRenaming back
            renamingInjectsBack leftExtracted leftSuccess,
          RawTerm.partialStrengthen?_imp_rename rightEndpoint forwardRenaming back
            renamingInjectsBack rightExtracted rightSuccess]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨carrierExtracted, leftExtracted, rightExtracted,
        carrierSuccess, leftSuccess, rightSuccess, extractedEq⟩ :=
        Option.mapThree_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted carrierSuccess,
          RawTerm.partialStrengthen?_imp_rename leftEndpoint forwardRenaming back
            renamingInjectsBack leftExtracted leftSuccess,
          RawTerm.partialStrengthen?_imp_rename rightEndpoint forwardRenaming back
            renamingInjectsBack rightExtracted rightSuccess]
  | equiv domainType codomainType domainIH codomainIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨domainExtracted, codomainExtracted,
        domainSuccess, codomainSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [domainIH forwardRenaming back renamingInjectsBack
            domainExtracted domainSuccess,
          codomainIH forwardRenaming back renamingInjectsBack
            codomainExtracted codomainSuccess]
  | refine baseType predicate baseIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨baseExtracted, predicateExtracted,
        baseSuccess, predicateSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [baseIH forwardRenaming back renamingInjectsBack
            baseExtracted baseSuccess,
          RawTerm.partialStrengthen?_imp_rename predicate forwardRenaming.lift
            back.lift
            (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
            predicateExtracted predicateSuccess]
  | record singleFieldType singleFieldIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match singleFieldType.partialStrengthen? back with
        | some strengthenedField => some (Ty.record strengthenedField)
        | none => none) = some extracted at success
      cases hField : singleFieldType.partialStrengthen? back with
      | none =>
          rw [show (match singleFieldType.partialStrengthen? back with
              | some strengthenedField => some (Ty.record strengthenedField)
              | none => none) = none by rw [hField]] at success
          cases success
      | some fieldExtracted =>
          rw [show (match singleFieldType.partialStrengthen? back with
              | some strengthenedField => some (Ty.record strengthenedField)
              | none => none) = some (Ty.record fieldExtracted) by rw [hField]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          rw [singleFieldIH forwardRenaming back renamingInjectsBack
            fieldExtracted hField]
  | codata stateType outputType stateIH outputIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨stateExtracted, outputExtracted,
        stateSuccess, outputSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [stateIH forwardRenaming back renamingInjectsBack
            stateExtracted stateSuccess,
          outputIH forwardRenaming back renamingInjectsBack
            outputExtracted outputSuccess]
  | session protocolStep =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match protocolStep.partialStrengthen? back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some extracted at success
      cases hProtocol : protocolStep.partialStrengthen? back with
      | none =>
          rw [show (match protocolStep.partialStrengthen? back with
              | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
              | none => none) = none by rw [hProtocol]] at success
          cases success
      | some protocolExtracted =>
          rw [show (match protocolStep.partialStrengthen? back with
              | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
              | none => none) = some (Ty.session protocolExtracted) by rw [hProtocol]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          rw [RawTerm.partialStrengthen?_imp_rename protocolStep
            forwardRenaming back renamingInjectsBack protocolExtracted hProtocol]
  | effect carrierType effectTag carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      obtain ⟨carrierExtracted, effectExtracted,
        carrierSuccess, effectSuccess, extractedEq⟩ :=
        Option.mapTwo_eq_some success
      rw [extractedEq]
      simp only [Ty.rename]
      rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted carrierSuccess,
          RawTerm.partialStrengthen?_imp_rename effectTag forwardRenaming back
            renamingInjectsBack effectExtracted effectSuccess]
  | modal modalityTag carrierType carrierIH =>
      intro forwardRenaming back renamingInjectsBack extracted success
      change (match carrierType.partialStrengthen? back with
        | some strengthenedCarrier => some (Ty.modal modalityTag strengthenedCarrier)
        | none => none) = some extracted at success
      cases hCarrier : carrierType.partialStrengthen? back with
      | none =>
          rw [show (match carrierType.partialStrengthen? back with
              | some strengthenedCarrier => some (Ty.modal modalityTag strengthenedCarrier)
              | none => none) = none by rw [hCarrier]] at success
          cases success
      | some carrierExtracted =>
          rw [show (match carrierType.partialStrengthen? back with
              | some strengthenedCarrier => some (Ty.modal modalityTag strengthenedCarrier)
              | none => none) = some (Ty.modal modalityTag carrierExtracted) by rw [hCarrier]] at success
          injection success with extractedEq
          rw [← extractedEq]
          simp only [Ty.rename]
          rw [carrierIH forwardRenaming back renamingInjectsBack
            carrierExtracted hCarrier]

/-- Successful single-slot type strengthening gives the canonical
weakening equation. -/
theorem Ty.strengthen?_imp_weaken {level scope : Nat}
    (someType : Ty level (scope + 1)) (extracted : Ty level scope)
    (success : someType.strengthen? = some extracted) :
    someType = extracted.weaken :=
  Ty.partialStrengthen?_imp_rename someType RawRenaming.weaken
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_renamingInjectsBack
    extracted success

/-- A type that semantically avoids the newest slot is syntactically a
weakening of a type in the previous scope. -/
theorem Ty.not_usesNewestSlot?_imp_weaken {level scope : Nat}
    (someType : Ty level (scope + 1))
    (slotIsUnused : someType.usesNewestSlot? = false) :
    ∃ extracted : Ty level scope, someType = extracted.weaken := by
  unfold Ty.usesNewestSlot? at slotIsUnused
  unfold Ty.strengthen? at slotIsUnused
  cases success : Ty.partialStrengthen? someType PartialRawRenaming.dropNewest with
  | none =>
      rw [success] at slotIsUnused
      cases slotIsUnused
  | some extracted =>
      exact ⟨extracted, Ty.strengthen?_imp_weaken someType extracted success⟩

end LeanFX2

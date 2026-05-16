import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.RawPartialRename.Strengthen
import LeanFX2.Foundation.RawPartialRenameCommute
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

/-- Renaming a type along a total renaming and then partially
strengthening along a partial inverse recovers the original type.

This is the type-level companion to
`RawTerm.partialStrengthen?_rename_some` and is the forward direction used
by context strengthening. -/
theorem Ty.partialStrengthen?_rename_some {level : Nat} :
    ∀ {sourceScope middleScope targetScope : Nat}
      (someType : Ty level sourceScope)
      (sourceRenaming : RawRenaming sourceScope middleScope)
      (targetRenaming : RawRenaming sourceScope targetScope)
      (back : PartialRawRenaming middleScope targetScope),
      (∀ position, back (sourceRenaming position) =
        some (targetRenaming position)) →
      (someType.rename sourceRenaming).partialStrengthen? back =
        some (someType.rename targetRenaming) := by
  intro sourceScope middleScope targetScope someType
  induction someType generalizing middleScope targetScope with
  | unit =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | bool =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | nat =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming back renamingSurvives,
        codomainIH sourceRenaming targetRenaming back renamingSurvives]
  | piTy domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming back renamingSurvives,
        codomainIH sourceRenaming.lift targetRenaming.lift back.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | sigmaTy firstType secondType firstIH secondIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming back renamingSurvives,
        secondIH sourceRenaming.lift targetRenaming.lift back.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | tyVar position =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [renamingSurvives position]
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some leftEndpoint sourceRenaming
          targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some rightEndpoint sourceRenaming
          targetRenaming back
          renamingSurvives]
  | listType elementType elementIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [elementIH sourceRenaming targetRenaming back renamingSurvives]
  | optionType elementType elementIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [elementIH sourceRenaming targetRenaming back renamingSurvives]
  | eitherType leftType rightType leftIH rightIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming back renamingSurvives,
        rightIH sourceRenaming targetRenaming back renamingSurvives]
  | «universe» universeLevel levelLe =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | empty =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | interval =>
      intro sourceRenaming targetRenaming back renamingSurvives
      rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some leftEndpoint sourceRenaming
          targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some rightEndpoint sourceRenaming
          targetRenaming back
          renamingSurvives]
  | glue baseType boundaryWitness baseIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some boundaryWitness sourceRenaming
          targetRenaming back
          renamingSurvives]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some leftEndpoint sourceRenaming
          targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some rightEndpoint sourceRenaming
          targetRenaming back
          renamingSurvives]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some leftEndpoint sourceRenaming
          targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some rightEndpoint sourceRenaming
          targetRenaming back
          renamingSurvives]
  | equiv domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming back renamingSurvives,
        codomainIH sourceRenaming targetRenaming back renamingSurvives]
  | refine baseType predicate baseIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some predicate sourceRenaming.lift
          targetRenaming.lift back.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | record singleFieldType singleFieldIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [singleFieldIH sourceRenaming targetRenaming back renamingSurvives]
  | codata stateType outputType stateIH outputIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [stateIH sourceRenaming targetRenaming back renamingSurvives,
        outputIH sourceRenaming targetRenaming back renamingSurvives]
  | session protocolStep =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [RawTerm.partialStrengthen?_rename_some protocolStep sourceRenaming
        targetRenaming back
        renamingSurvives]
  | effect carrierType effectTag carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives,
        RawTerm.partialStrengthen?_rename_some effectTag sourceRenaming
          targetRenaming back
          renamingSurvives]
  | modal modalityTag carrierType carrierIH =>
      intro sourceRenaming targetRenaming back renamingSurvives
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [carrierIH sourceRenaming targetRenaming back renamingSurvives]

set_option linter.unusedVariables false in
/-- Type partial strengthening commutes with a compatible total
renaming.  This is the type-index analogue of
`RawTerm.partialRename?_rename_compat`. -/
theorem Ty.partialStrengthen?_rename_compat {level : Nat} :
    ∀ {sourceScope sourceTarget targetScope targetTarget : Nat}
      (someType : Ty level sourceScope)
      (sourceRenaming : RawRenaming sourceScope sourceTarget)
      (targetRenaming : RawRenaming targetScope targetTarget)
      (partialSource : PartialRawRenaming sourceScope targetScope)
      (partialTarget : PartialRawRenaming sourceTarget targetTarget),
      (∀ position, partialTarget (sourceRenaming position) =
        (partialSource position).map targetRenaming) →
      (someType.rename sourceRenaming).partialStrengthen? partialTarget =
        (someType.partialStrengthen? partialSource).map
          (fun targetType => targetType.rename targetRenaming) := by
  intro sourceScope sourceTarget targetScope targetTarget someType
  induction someType generalizing sourceTarget targetScope targetTarget with
  | unit => intros; rfl
  | bool => intros; rfl
  | nat => intros; rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialSource partialTarget compat,
        codomainIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases domainType.partialStrengthen? partialSource <;>
        cases codomainType.partialStrengthen? partialSource <;> rfl
  | piTy domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialSource partialTarget compat,
        codomainIH sourceRenaming.lift targetRenaming.lift
          partialSource.lift partialTarget.lift
          (PartialRawRenaming.lift_compat sourceRenaming targetRenaming
            partialSource partialTarget compat)]
      cases domainType.partialStrengthen? partialSource <;>
        cases codomainType.partialStrengthen? partialSource.lift <;> rfl
  | sigmaTy firstType secondType firstIH secondIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialSource partialTarget compat,
        secondIH sourceRenaming.lift targetRenaming.lift
          partialSource.lift partialTarget.lift
          (PartialRawRenaming.lift_compat sourceRenaming targetRenaming
            partialSource partialTarget compat)]
      cases firstType.partialStrengthen? partialSource <;>
        cases secondType.partialStrengthen? partialSource.lift <;> rfl
  | tyVar position =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [compat position]
      cases partialSource position <;> rfl
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      unfold RawTerm.partialStrengthen?
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat leftEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat rightEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases carrier.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? leftEndpoint partialSource <;>
        cases RawTerm.partialRename? rightEndpoint partialSource <;> rfl
  | listType elementType elementIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [elementIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases elementType.partialStrengthen? partialSource <;> rfl
  | optionType elementType elementIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [elementIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases elementType.partialStrengthen? partialSource <;> rfl
  | eitherType leftType rightType leftIH rightIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialSource partialTarget compat,
        rightIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases leftType.partialStrengthen? partialSource <;>
        cases rightType.partialStrengthen? partialSource <;> rfl
  | «universe» universeLevel levelLe => intros; rfl
  | empty => intros; rfl
  | interval => intros; rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      unfold RawTerm.partialStrengthen?
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat leftEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat rightEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases carrier.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? leftEndpoint partialSource <;>
        cases RawTerm.partialRename? rightEndpoint partialSource <;> rfl
  | glue baseType boundaryWitness baseIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      unfold RawTerm.partialStrengthen?
      rw [baseIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat boundaryWitness sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases baseType.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? boundaryWitness partialSource <;> rfl
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      unfold RawTerm.partialStrengthen?
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat leftEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat rightEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases carrier.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? leftEndpoint partialSource <;>
        cases RawTerm.partialRename? rightEndpoint partialSource <;> rfl
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapThree]
      unfold RawTerm.partialStrengthen?
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat leftEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat rightEndpoint sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases carrier.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? leftEndpoint partialSource <;>
        cases RawTerm.partialRename? rightEndpoint partialSource <;> rfl
  | equiv domainType codomainType domainIH codomainIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialSource partialTarget compat,
        codomainIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases domainType.partialStrengthen? partialSource <;>
        cases codomainType.partialStrengthen? partialSource <;> rfl
  | refine baseType predicate baseIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      unfold RawTerm.partialStrengthen?
      rw [baseIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat predicate sourceRenaming.lift
          targetRenaming.lift partialSource.lift partialTarget.lift
          (PartialRawRenaming.lift_compat sourceRenaming targetRenaming
            partialSource partialTarget compat)]
      cases baseType.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? predicate partialSource.lift <;> rfl
  | record singleFieldType singleFieldIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [singleFieldIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases singleFieldType.partialStrengthen? partialSource <;> rfl
  | codata stateType outputType stateIH outputIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      rw [stateIH sourceRenaming targetRenaming partialSource partialTarget compat,
        outputIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases stateType.partialStrengthen? partialSource <;>
        cases outputType.partialStrengthen? partialSource <;> rfl
  | session protocolStep =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      unfold RawTerm.partialStrengthen?
      rw [RawTerm.partialRename?_rename_compat protocolStep sourceRenaming
        targetRenaming partialSource partialTarget compat]
      cases RawTerm.partialRename? protocolStep partialSource <;> rfl
  | effect carrierType effectTag carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?, Option.mapTwo]
      unfold RawTerm.partialStrengthen?
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat,
        RawTerm.partialRename?_rename_compat effectTag sourceRenaming
          targetRenaming partialSource partialTarget compat]
      cases carrierType.partialStrengthen? partialSource <;>
        cases RawTerm.partialRename? effectTag partialSource <;> rfl
  | modal modalityTag carrierType carrierIH =>
      intro sourceRenaming targetRenaming partialSource partialTarget compat
      simp only [Ty.rename, Ty.partialStrengthen?]
      rw [carrierIH sourceRenaming targetRenaming partialSource partialTarget compat]
      cases carrierType.partialStrengthen? partialSource <;> rfl

/-- Type partial strengthening commutes with one outer weakening when
the partial strengthening is lifted under the new binder. -/
theorem Ty.partialStrengthen?_weaken_lift {level : Nat}
    {sourceScope targetScope : Nat}
    (someType : Ty level sourceScope)
    (back : PartialRawRenaming sourceScope targetScope) :
    someType.weaken.partialStrengthen? back.lift =
      (someType.partialStrengthen? back).map Ty.weaken := by
  unfold Ty.weaken
  exact Ty.partialStrengthen?_rename_compat someType
    RawRenaming.weaken RawRenaming.weaken back back.lift
    (PartialRawRenaming.lift_weaken_map back)

/-- Strengthening after weakening recovers the original type. -/
theorem Ty.strengthen?_weaken {level scope : Nat}
    (someType : Ty level scope) :
    someType.weaken.strengthen? = some someType := by
  unfold Ty.strengthen?
  unfold Ty.weaken
  rw [Ty.partialStrengthen?_rename_some someType RawRenaming.weaken
      RawRenaming.identity PartialRawRenaming.dropNewest
      PartialRawRenaming.dropNewest_weaken,
    Ty.rename_identity]

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

/-- Partial strengthening commutes with single-binder type substitution
when each substituted component strengthens through the same partial
renaming.

This is the Σ/Π reconstruction bridge used by typed strengthening:
dependent component types such as `secondType.subst0 firstType firstRaw`
can be strengthened by strengthening the binder body under `back.lift`
and the substituted argument/type under `back`. -/
theorem Ty.partialStrengthen?_subst0_of_success {level : Nat}
    {sourceScope targetScope : Nat}
    (codomainType : Ty level (sourceScope + 1))
    (targetCodomainType : Ty level (targetScope + 1))
    (argType : Ty level sourceScope)
    (targetArgType : Ty level targetScope)
    (argRaw : RawTerm sourceScope)
    (targetArgRaw : RawTerm targetScope)
    (forwardRenaming : RawRenaming targetScope sourceScope)
    (back : PartialRawRenaming sourceScope targetScope)
    (renamingInjectsBack :
      ∀ (sourcePosition : Fin sourceScope)
        (targetPosition : Fin targetScope),
        back sourcePosition = some targetPosition →
        sourcePosition = forwardRenaming targetPosition)
    (backForward :
      ∀ targetPosition, back (forwardRenaming targetPosition) =
        some targetPosition)
    (codomainStrengthens :
      codomainType.partialStrengthen? back.lift =
        some targetCodomainType)
    (argTypeStrengthens :
      argType.partialStrengthen? back = some targetArgType)
    (argRawStrengthens :
      argRaw.partialStrengthen? back = some targetArgRaw) :
    (codomainType.subst0 argType argRaw).partialStrengthen? back =
      some (targetCodomainType.subst0 targetArgType targetArgRaw) := by
  have codomainRenames :
      codomainType = targetCodomainType.rename forwardRenaming.lift :=
    Ty.partialStrengthen?_imp_rename codomainType forwardRenaming.lift
      back.lift (PartialRawRenaming.lift_renamingInjectsBack
        renamingInjectsBack) targetCodomainType codomainStrengthens
  have argTypeRenames :
      argType = targetArgType.rename forwardRenaming :=
    Ty.partialStrengthen?_imp_rename argType forwardRenaming back
      renamingInjectsBack targetArgType argTypeStrengthens
  have argRawRenames :
      argRaw = targetArgRaw.rename forwardRenaming :=
    RawTerm.partialStrengthen?_imp_rename argRaw forwardRenaming back
      renamingInjectsBack targetArgRaw argRawStrengthens
  rw [codomainRenames, argTypeRenames, argRawRenames]
  rw [← Ty.subst0_rename_commute targetCodomainType targetArgType
    targetArgRaw forwardRenaming]
  rw [Ty.partialStrengthen?_rename_some
    (targetCodomainType.subst0 targetArgType targetArgRaw)
    forwardRenaming RawRenaming.identity back backForward,
    Ty.rename_identity]

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

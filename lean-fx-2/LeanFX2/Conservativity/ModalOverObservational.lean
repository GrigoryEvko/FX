import LeanFX2.Modal.Foundation
import LeanFX2.Foundation.Ty

/-! # Conservativity/ModalOverObservational

Type-level modal-over-observational conservativity boundary.

## Deliverable

The full sprint deliverable is term-level preservation for programs that do
not use modal introduction or elimination.  This file ships the type-level
fragment that can be checked today:

* `isModalFreeTy` recognizes types with no `Ty.modal` constructor;
* `modalToObservationalTy` erases modal wrappers;
* `modalToObservationalTy_preserves_isModalFreeTy` proves the translation is
  identity on modal-free types.
-/

namespace LeanFX2
namespace Conservativity

/-- Recognize types that do not mention modal wrappers. -/
def isModalFreeTy {level : Nat} : ∀ {scope : Nat}, Ty level scope → Prop
  | _, .unit => True
  | _, .bool => True
  | _, .nat => True
  | _, .arrow domainType codomainType =>
      isModalFreeTy domainType ∧ isModalFreeTy codomainType
  | _, .piTy domainType codomainType =>
      isModalFreeTy domainType ∧ isModalFreeTy codomainType
  | _, .sigmaTy firstType secondType =>
      isModalFreeTy firstType ∧ isModalFreeTy secondType
  | _, .tyVar _position => True
  | _, .id carrier _leftEndpoint _rightEndpoint =>
      isModalFreeTy carrier
  | _, .listType elementType =>
      isModalFreeTy elementType
  | _, .optionType elementType =>
      isModalFreeTy elementType
  | _, .eitherType leftType rightType =>
      isModalFreeTy leftType ∧ isModalFreeTy rightType
  | _, .universe _universeLevel _levelLe => True
  | _, .empty => True
  | _, .interval => True
  | _, .path carrier _leftEndpoint _rightEndpoint =>
      isModalFreeTy carrier
  | _, .glue baseType _boundaryWitness =>
      isModalFreeTy baseType
  | _, .oeq carrier _leftEndpoint _rightEndpoint =>
      isModalFreeTy carrier
  | _, .idStrict carrier _leftEndpoint _rightEndpoint =>
      isModalFreeTy carrier
  | _, .equiv domainType codomainType =>
      isModalFreeTy domainType ∧ isModalFreeTy codomainType
  | _, .refine baseType _predicate =>
      isModalFreeTy baseType
  | _, .record singleFieldType =>
      isModalFreeTy singleFieldType
  | _, .codata stateType outputType =>
      isModalFreeTy stateType ∧ isModalFreeTy outputType
  | _, .session _protocolStep => True
  | _, .effect carrierType _effectTag =>
      isModalFreeTy carrierType
  | _, .modal _modalityTag _carrierType => False

/-- Erase modal wrappers from types, preserving all non-modal structure. -/
def modalToObservationalTy {level : Nat} :
    ∀ {scope : Nat}, Ty level scope → Ty level scope
  | _, .unit => .unit
  | _, .bool => .bool
  | _, .nat => .nat
  | _, .arrow domainType codomainType =>
      .arrow (modalToObservationalTy domainType)
        (modalToObservationalTy codomainType)
  | _, .piTy domainType codomainType =>
      .piTy (modalToObservationalTy domainType)
        (modalToObservationalTy codomainType)
  | _, .sigmaTy firstType secondType =>
      .sigmaTy (modalToObservationalTy firstType)
        (modalToObservationalTy secondType)
  | _, .tyVar position => .tyVar position
  | _, .id carrier leftEndpoint rightEndpoint =>
      .id (modalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .listType elementType =>
      .listType (modalToObservationalTy elementType)
  | _, .optionType elementType =>
      .optionType (modalToObservationalTy elementType)
  | _, .eitherType leftType rightType =>
      .eitherType (modalToObservationalTy leftType)
        (modalToObservationalTy rightType)
  | _, .universe universeLevel levelLe => .universe universeLevel levelLe
  | _, .empty => .empty
  | _, .interval => .interval
  | _, .path carrier leftEndpoint rightEndpoint =>
      .path (modalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .glue baseType boundaryWitness =>
      .glue (modalToObservationalTy baseType) boundaryWitness
  | _, .oeq carrier leftEndpoint rightEndpoint =>
      .oeq (modalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .idStrict carrier leftEndpoint rightEndpoint =>
      .idStrict (modalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .equiv domainType codomainType =>
      .equiv (modalToObservationalTy domainType)
        (modalToObservationalTy codomainType)
  | _, .refine baseType predicate =>
      .refine (modalToObservationalTy baseType) predicate
  | _, .record singleFieldType =>
      .record (modalToObservationalTy singleFieldType)
  | _, .codata stateType outputType =>
      .codata (modalToObservationalTy stateType)
        (modalToObservationalTy outputType)
  | _, .session protocolStep => .session protocolStep
  | _, .effect carrierType effectTag =>
      .effect (modalToObservationalTy carrierType) effectTag
  | _, .modal _modalityTag carrierType =>
      modalToObservationalTy carrierType

/-- Modal erasure is identity on modal-free types. -/
theorem modalToObservationalTy_preserves_isModalFreeTy {level : Nat} :
    ∀ {scope : Nat} (someType : Ty level scope),
      isModalFreeTy someType → modalToObservationalTy someType = someType
  | _, .unit, _modalFreeProof => rfl
  | _, .bool, _modalFreeProof => rfl
  | _, .nat, _modalFreeProof => rfl
  | _, .arrow domainType codomainType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        domainType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        codomainType modalFreeProof.right]
  | _, .piTy domainType codomainType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        domainType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        codomainType modalFreeProof.right]
  | _, .sigmaTy firstType secondType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        firstType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        secondType modalFreeProof.right]
  | _, .tyVar _position, _modalFreeProof => rfl
  | _, .id carrier leftEndpoint rightEndpoint, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        carrier modalFreeProof]
  | _, .listType elementType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        elementType modalFreeProof]
  | _, .optionType elementType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        elementType modalFreeProof]
  | _, .eitherType leftType rightType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        leftType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        rightType modalFreeProof.right]
  | _, .universe _universeLevel _levelLe, _modalFreeProof => rfl
  | _, .empty, _modalFreeProof => rfl
  | _, .interval, _modalFreeProof => rfl
  | _, .path carrier leftEndpoint rightEndpoint, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        carrier modalFreeProof]
  | _, .glue baseType boundaryWitness, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        baseType modalFreeProof]
  | _, .oeq carrier leftEndpoint rightEndpoint, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        carrier modalFreeProof]
  | _, .idStrict carrier leftEndpoint rightEndpoint, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        carrier modalFreeProof]
  | _, .equiv domainType codomainType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        domainType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        codomainType modalFreeProof.right]
  | _, .refine baseType predicate, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        baseType modalFreeProof]
  | _, .record singleFieldType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        singleFieldType modalFreeProof]
  | _, .codata stateType outputType, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        stateType modalFreeProof.left]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        outputType modalFreeProof.right]
  | _, .session _protocolStep, _modalFreeProof => rfl
  | _, .effect carrierType effectTag, modalFreeProof => by
      simp only [modalToObservationalTy]
      rw [modalToObservationalTy_preserves_isModalFreeTy
        carrierType modalFreeProof]
  | _, .modal _modalityTag _carrierType, modalFreeProof =>
      False.elim modalFreeProof

end Conservativity
end LeanFX2

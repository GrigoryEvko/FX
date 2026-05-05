import LeanFX2.Conservativity.HOTTOverMLTT
import LeanFX2.Translation.CubicalToObservational

/-! # Conservativity/CubicalOverHOTT

Type-level cubical-over-HOTT conservativity boundary.

## Deliverable

The full sprint deliverable is term-level preservation for cubical terms after
observationalization.  The current kernel can honestly ship the type-level
boundary:

* `isCubicalFreeTy` recognizes types with no interval, path, or Glue type
  formers;
* `cubicalToObservationalTy` is the explicit type-level translation;
* `cubicalToObservationalTy_preserves_isCubicalFreeTy` proves that translation
  is identity on cubical-free types.
-/

namespace LeanFX2
namespace Conservativity

/-- Recognize types that do not mention cubical interval, Path, or Glue
constructors. -/
def isCubicalFreeTy {level : Nat} : ∀ {scope : Nat}, Ty level scope → Prop
  | _, .unit => True
  | _, .bool => True
  | _, .nat => True
  | _, .arrow domainType codomainType =>
      isCubicalFreeTy domainType ∧ isCubicalFreeTy codomainType
  | _, .piTy domainType codomainType =>
      isCubicalFreeTy domainType ∧ isCubicalFreeTy codomainType
  | _, .sigmaTy firstType secondType =>
      isCubicalFreeTy firstType ∧ isCubicalFreeTy secondType
  | _, .tyVar _position => True
  | _, .id carrier _leftEndpoint _rightEndpoint =>
      isCubicalFreeTy carrier
  | _, .listType elementType =>
      isCubicalFreeTy elementType
  | _, .optionType elementType =>
      isCubicalFreeTy elementType
  | _, .eitherType leftType rightType =>
      isCubicalFreeTy leftType ∧ isCubicalFreeTy rightType
  | _, .universe _universeLevel _levelLe => True
  | _, .empty => True
  | _, .interval => False
  | _, .path _carrier _leftEndpoint _rightEndpoint => False
  | _, .glue _baseType _boundaryWitness => False
  | _, .oeq carrier _leftEndpoint _rightEndpoint =>
      isCubicalFreeTy carrier
  | _, .idStrict carrier _leftEndpoint _rightEndpoint =>
      isCubicalFreeTy carrier
  | _, .equiv domainType codomainType =>
      isCubicalFreeTy domainType ∧ isCubicalFreeTy codomainType
  | _, .refine baseType _predicate =>
      isCubicalFreeTy baseType
  | _, .record singleFieldType =>
      isCubicalFreeTy singleFieldType
  | _, .codata stateType outputType =>
      isCubicalFreeTy stateType ∧ isCubicalFreeTy outputType
  | _, .session _protocolStep => True
  | _, .effect carrierType _effectTag =>
      isCubicalFreeTy carrierType
  | _, .modal _modalityTag carrierType =>
      isCubicalFreeTy carrierType

/-- Cubical-to-observational translation is identity on cubical-free types. -/
theorem cubicalToObservationalTy_preserves_isCubicalFreeTy {level : Nat} :
    ∀ {scope : Nat} (someType : Ty level scope),
      isCubicalFreeTy someType →
        Translation.cubicalToObservationalTy someType = someType
  | _, .unit, _cubicalFreeProof => rfl
  | _, .bool, _cubicalFreeProof => rfl
  | _, .nat, _cubicalFreeProof => rfl
  | _, .arrow domainType codomainType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        domainType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        codomainType cubicalFreeProof.right]
  | _, .piTy domainType codomainType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        domainType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        codomainType cubicalFreeProof.right]
  | _, .sigmaTy firstType secondType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        firstType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        secondType cubicalFreeProof.right]
  | _, .tyVar _position, _cubicalFreeProof => rfl
  | _, .id carrier leftEndpoint rightEndpoint, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        carrier cubicalFreeProof]
  | _, .listType elementType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        elementType cubicalFreeProof]
  | _, .optionType elementType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        elementType cubicalFreeProof]
  | _, .eitherType leftType rightType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        leftType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        rightType cubicalFreeProof.right]
  | _, .universe _universeLevel _levelLe, _cubicalFreeProof => rfl
  | _, .empty, _cubicalFreeProof => rfl
  | _, .interval, cubicalFreeProof => False.elim cubicalFreeProof
  | _, .path _carrier _leftEndpoint _rightEndpoint, cubicalFreeProof =>
      False.elim cubicalFreeProof
  | _, .glue _baseType _boundaryWitness, cubicalFreeProof =>
      False.elim cubicalFreeProof
  | _, .oeq carrier leftEndpoint rightEndpoint, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        carrier cubicalFreeProof]
  | _, .idStrict carrier leftEndpoint rightEndpoint, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        carrier cubicalFreeProof]
  | _, .equiv domainType codomainType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        domainType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        codomainType cubicalFreeProof.right]
  | _, .refine baseType predicate, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        baseType cubicalFreeProof]
  | _, .record singleFieldType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        singleFieldType cubicalFreeProof]
  | _, .codata stateType outputType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        stateType cubicalFreeProof.left]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        outputType cubicalFreeProof.right]
  | _, .session _protocolStep, _cubicalFreeProof => rfl
  | _, .effect carrierType effectTag, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        carrierType cubicalFreeProof]
  | _, .modal modalityTag carrierType, cubicalFreeProof => by
      simp only [Translation.cubicalToObservationalTy]
      rw [cubicalToObservationalTy_preserves_isCubicalFreeTy
        carrierType cubicalFreeProof]

end Conservativity
end LeanFX2

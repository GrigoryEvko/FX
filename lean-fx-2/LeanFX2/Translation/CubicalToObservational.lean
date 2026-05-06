import LeanFX2.Foundation.Ty

/-! # Translation/CubicalToObservational

Cubical-to-observational translation.

## Deliverable

This module defines the type-level part of the cubical-to-observational
translation functor.

The current slice is intentionally syntactic:

* cubical `Path` types translate to observational `Id` types;
* the interval type translates to `Unit`;
* Glue types translate to their translated base type;
* non-cubical structure is preserved recursively.

Term translation and typing preservation require the later explicit typing
judgment from the conservativity tasks.  This file does not claim those
theorems.
-/

namespace LeanFX2
namespace Translation

/-- Translate a cubical type into the observational fragment.

The recursive cases preserve every non-cubical type former.  Cubical-specific
type formers are collapsed as follows:

* `Ty.interval` becomes `Ty.unit`;
* `Ty.path carrier left right` becomes `Ty.id translatedCarrier left right`;
* `Ty.glue base boundary` becomes the translated base type.

Raw endpoints and boundary witnesses are left unchanged because this is only
the type-level translation; raw-term translation is a later functor slice. -/
def cubicalToObservationalTy {level : Nat} :
    ∀ {scope : Nat}, Ty level scope → Ty level scope
  | _, .unit => .unit
  | _, .bool => .bool
  | _, .nat => .nat
  | _, .arrow domainType codomainType =>
      .arrow (cubicalToObservationalTy domainType)
        (cubicalToObservationalTy codomainType)
  | _, .piTy domainType codomainType =>
      .piTy (cubicalToObservationalTy domainType)
        (cubicalToObservationalTy codomainType)
  | _, .sigmaTy firstType secondType =>
      .sigmaTy (cubicalToObservationalTy firstType)
        (cubicalToObservationalTy secondType)
  | _, .tyVar position => .tyVar position
  | _, .id carrier leftEndpoint rightEndpoint =>
      .id (cubicalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .listType elementType =>
      .listType (cubicalToObservationalTy elementType)
  | _, .optionType elementType =>
      .optionType (cubicalToObservationalTy elementType)
  | _, .eitherType leftType rightType =>
      .eitherType (cubicalToObservationalTy leftType)
        (cubicalToObservationalTy rightType)
  | _, .universe universeLevel levelLe => .universe universeLevel levelLe
  | _, .empty => .empty
  | _, .interval => .unit
  | _, .path carrier leftEndpoint rightEndpoint =>
      .id (cubicalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .glue baseType _boundaryWitness =>
      cubicalToObservationalTy baseType
  | _, .oeq carrier leftEndpoint rightEndpoint =>
      .oeq (cubicalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .idStrict carrier leftEndpoint rightEndpoint =>
      .idStrict (cubicalToObservationalTy carrier) leftEndpoint rightEndpoint
  | _, .equiv domainType codomainType =>
      .equiv (cubicalToObservationalTy domainType)
        (cubicalToObservationalTy codomainType)
  | _, .refine baseType predicate =>
      .refine (cubicalToObservationalTy baseType) predicate
  | _, .record singleFieldType =>
      .record (cubicalToObservationalTy singleFieldType)
  | _, .codata stateType outputType =>
      .codata (cubicalToObservationalTy stateType)
        (cubicalToObservationalTy outputType)
  | _, .session protocolStep => .session protocolStep
  | _, .effect carrierType effectTag =>
      .effect (cubicalToObservationalTy carrierType) effectTag
  | _, .modal modalityTag carrierType =>
      .modal modalityTag (cubicalToObservationalTy carrierType)

/-- The interval type is erased to `Unit` by the type-level translation. -/
theorem cubicalToObservationalTy_interval {level scope : Nat} :
    cubicalToObservationalTy (level := level) (scope := scope) Ty.interval =
      Ty.unit := rfl

/-- Cubical paths become observational identity types. -/
theorem cubicalToObservationalTy_path {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    cubicalToObservationalTy
      (Ty.path carrier leftEndpoint rightEndpoint) =
      Ty.id (cubicalToObservationalTy carrier)
        leftEndpoint rightEndpoint := rfl

/-- Glue types collapse to their translated base type in this type-level
translation. -/
theorem cubicalToObservationalTy_glue {level scope : Nat}
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope) :
    cubicalToObservationalTy (Ty.glue baseType boundaryWitness) =
      cubicalToObservationalTy baseType := rfl

/-- Non-cubical identity types are preserved structurally, recursively
translating only their carrier. -/
theorem cubicalToObservationalTy_id {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    cubicalToObservationalTy (Ty.id carrier leftEndpoint rightEndpoint) =
      Ty.id (cubicalToObservationalTy carrier)
        leftEndpoint rightEndpoint := rfl

end Translation
end LeanFX2

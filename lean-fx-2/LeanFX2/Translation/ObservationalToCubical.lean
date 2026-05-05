import LeanFX2.Cubical.Bridge
import LeanFX2.Foundation.Ty

/-! # Translation/ObservationalToCubical

Observational-to-cubical translation.

## Deliverable

This module defines the type-level part of the observational-to-cubical
translation functor.

The current slice is intentionally syntactic:

* observational `Id`, `OEq`, and strict identity types translate to cubical
  `Path` types;
* non-observational structure is preserved recursively;
* existing cubical structure is preserved recursively.

Term translation and typing preservation require the later explicit typing
judgment from the conservativity tasks.  This file does not claim those
theorems.
-/

namespace LeanFX2
namespace Translation

/-- Translate an observational type into the cubical fragment.

The recursive cases preserve every non-observational type former.
Observational equality type formers are represented by cubical paths over the
translated carrier.  Raw endpoints and predicates are left unchanged because
this is only the type-level translation; raw-term translation is a later
functor slice. -/
def observationalToCubicalTy {level : Nat} :
    ∀ {scope : Nat}, Ty level scope → Ty level scope
  | _, .unit => .unit
  | _, .bool => .bool
  | _, .nat => .nat
  | _, .arrow domainType codomainType =>
      .arrow (observationalToCubicalTy domainType)
        (observationalToCubicalTy codomainType)
  | _, .piTy domainType codomainType =>
      .piTy (observationalToCubicalTy domainType)
        (observationalToCubicalTy codomainType)
  | _, .sigmaTy firstType secondType =>
      .sigmaTy (observationalToCubicalTy firstType)
        (observationalToCubicalTy secondType)
  | _, .tyVar position => .tyVar position
  | _, .id carrier leftEndpoint rightEndpoint =>
      .path (observationalToCubicalTy carrier) leftEndpoint rightEndpoint
  | _, .listType elementType =>
      .listType (observationalToCubicalTy elementType)
  | _, .optionType elementType =>
      .optionType (observationalToCubicalTy elementType)
  | _, .eitherType leftType rightType =>
      .eitherType (observationalToCubicalTy leftType)
        (observationalToCubicalTy rightType)
  | _, .universe universeLevel levelLe => .universe universeLevel levelLe
  | _, .empty => .empty
  | _, .interval => .interval
  | _, .path carrier leftEndpoint rightEndpoint =>
      .path (observationalToCubicalTy carrier) leftEndpoint rightEndpoint
  | _, .glue baseType boundaryWitness =>
      .glue (observationalToCubicalTy baseType) boundaryWitness
  | _, .oeq carrier leftEndpoint rightEndpoint =>
      .path (observationalToCubicalTy carrier) leftEndpoint rightEndpoint
  | _, .idStrict carrier leftEndpoint rightEndpoint =>
      .path (observationalToCubicalTy carrier) leftEndpoint rightEndpoint
  | _, .equiv domainType codomainType =>
      .equiv (observationalToCubicalTy domainType)
        (observationalToCubicalTy codomainType)
  | _, .refine baseType predicate =>
      .refine (observationalToCubicalTy baseType) predicate
  | _, .record singleFieldType =>
      .record (observationalToCubicalTy singleFieldType)
  | _, .codata stateType outputType =>
      .codata (observationalToCubicalTy stateType)
        (observationalToCubicalTy outputType)
  | _, .session protocolStep => .session protocolStep
  | _, .effect carrierType effectTag =>
      .effect (observationalToCubicalTy carrierType) effectTag
  | _, .modal modalityTag carrierType =>
      .modal modalityTag (observationalToCubicalTy carrierType)

/-- Observational identity types become cubical paths. -/
theorem observationalToCubicalTy_id {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    observationalToCubicalTy
      (Ty.id carrier leftEndpoint rightEndpoint) =
      Ty.path (observationalToCubicalTy carrier)
        leftEndpoint rightEndpoint := rfl

/-- Observational equality types become cubical paths. -/
theorem observationalToCubicalTy_oeq {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    observationalToCubicalTy
      (Ty.oeq carrier leftEndpoint rightEndpoint) =
      Ty.path (observationalToCubicalTy carrier)
        leftEndpoint rightEndpoint := rfl

/-- Strict identity types become cubical paths in this type-level
translation. -/
theorem observationalToCubicalTy_idStrict {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    observationalToCubicalTy
      (Ty.idStrict carrier leftEndpoint rightEndpoint) =
      Ty.path (observationalToCubicalTy carrier)
        leftEndpoint rightEndpoint := rfl

/-- Existing cubical path types are preserved structurally, recursively
translating only their carrier. -/
theorem observationalToCubicalTy_path {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    observationalToCubicalTy
      (Ty.path carrier leftEndpoint rightEndpoint) =
      Ty.path (observationalToCubicalTy carrier)
        leftEndpoint rightEndpoint := rfl

end Translation
end LeanFX2

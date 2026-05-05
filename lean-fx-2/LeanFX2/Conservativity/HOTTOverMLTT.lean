import LeanFX2.Foundation.Ty

/-! # Conservativity/HOTTOverMLTT

Type-level HOTT-over-MLTT conservativity boundary.

## Deliverable

The full sprint deliverable is term-level typing preservation for the MLTT-only
fragment.  The current kernel does not yet expose a general `HasType` judgment,
so this module ships the type-level part that can be stated honestly:

* `isMLTTOnlyTy` recognizes the strict MLTT type fragment;
* `hottToMLTTTy` erases HOTT/cubical/modal extensions to MLTT-shaped types;
* `hottToMLTTTy_preserves_isMLTTOnlyTy` proves the translation is identity on
  recognized MLTT-only types.
-/

namespace LeanFX2
namespace Conservativity

/-- Recognize the strict MLTT type fragment.

The fragment includes the base type formers, dependent products/sums, variables,
identity, common structural containers, universes, and the empty type.  It
excludes cubical, observational, modal, refinement, session, effect, codata,
record, and equivalence extensions. -/
def isMLTTOnlyTy {level : Nat} : ∀ {scope : Nat}, Ty level scope → Prop
  | _, .unit => True
  | _, .bool => True
  | _, .nat => True
  | _, .arrow domainType codomainType =>
      isMLTTOnlyTy domainType ∧ isMLTTOnlyTy codomainType
  | _, .piTy domainType codomainType =>
      isMLTTOnlyTy domainType ∧ isMLTTOnlyTy codomainType
  | _, .sigmaTy firstType secondType =>
      isMLTTOnlyTy firstType ∧ isMLTTOnlyTy secondType
  | _, .tyVar _position => True
  | _, .id carrier _leftEndpoint _rightEndpoint =>
      isMLTTOnlyTy carrier
  | _, .listType elementType =>
      isMLTTOnlyTy elementType
  | _, .optionType elementType =>
      isMLTTOnlyTy elementType
  | _, .eitherType leftType rightType =>
      isMLTTOnlyTy leftType ∧ isMLTTOnlyTy rightType
  | _, .universe _universeLevel _levelLe => True
  | _, .empty => True
  | _, .interval => False
  | _, .path _carrier _leftEndpoint _rightEndpoint => False
  | _, .glue _baseType _boundaryWitness => False
  | _, .oeq _carrier _leftEndpoint _rightEndpoint => False
  | _, .idStrict _carrier _leftEndpoint _rightEndpoint => False
  | _, .equiv _domainType _codomainType => False
  | _, .refine _baseType _predicate => False
  | _, .record _singleFieldType => False
  | _, .codata _stateType _outputType => False
  | _, .session _protocolStep => False
  | _, .effect _carrierType _effectTag => False
  | _, .modal _modalityTag _carrierType => False

/-- Erase extended HOTT/cubical/modal type formers to MLTT-shaped types.

This translation is intentionally lossy outside the `isMLTTOnlyTy` fragment.
The preservation theorem below is the load-bearing statement: on MLTT-only
types, the translation is judgmentally the identity. -/
def hottToMLTTTy {level : Nat} :
    ∀ {scope : Nat}, Ty level scope → Ty level scope
  | _, .unit => .unit
  | _, .bool => .bool
  | _, .nat => .nat
  | _, .arrow domainType codomainType =>
      .arrow (hottToMLTTTy domainType) (hottToMLTTTy codomainType)
  | _, .piTy domainType codomainType =>
      .piTy (hottToMLTTTy domainType) (hottToMLTTTy codomainType)
  | _, .sigmaTy firstType secondType =>
      .sigmaTy (hottToMLTTTy firstType) (hottToMLTTTy secondType)
  | _, .tyVar position => .tyVar position
  | _, .id carrier leftEndpoint rightEndpoint =>
      .id (hottToMLTTTy carrier) leftEndpoint rightEndpoint
  | _, .listType elementType =>
      .listType (hottToMLTTTy elementType)
  | _, .optionType elementType =>
      .optionType (hottToMLTTTy elementType)
  | _, .eitherType leftType rightType =>
      .eitherType (hottToMLTTTy leftType) (hottToMLTTTy rightType)
  | _, .universe universeLevel levelLe => .universe universeLevel levelLe
  | _, .empty => .empty
  | _, .interval => .unit
  | _, .path carrier leftEndpoint rightEndpoint =>
      .id (hottToMLTTTy carrier) leftEndpoint rightEndpoint
  | _, .glue baseType _boundaryWitness =>
      hottToMLTTTy baseType
  | _, .oeq carrier leftEndpoint rightEndpoint =>
      .id (hottToMLTTTy carrier) leftEndpoint rightEndpoint
  | _, .idStrict carrier leftEndpoint rightEndpoint =>
      .id (hottToMLTTTy carrier) leftEndpoint rightEndpoint
  | _, .equiv _domainType _codomainType => .unit
  | _, .refine baseType _predicate =>
      hottToMLTTTy baseType
  | _, .record singleFieldType =>
      hottToMLTTTy singleFieldType
  | _, .codata _stateType outputType =>
      hottToMLTTTy outputType
  | _, .session _protocolStep => .unit
  | _, .effect carrierType _effectTag =>
      hottToMLTTTy carrierType
  | _, .modal _modalityTag carrierType =>
      hottToMLTTTy carrierType

/-- The HOTT-to-MLTT type translation is identity on MLTT-only types. -/
theorem hottToMLTTTy_preserves_isMLTTOnlyTy {level : Nat} :
    ∀ {scope : Nat} (someType : Ty level scope),
      isMLTTOnlyTy someType → hottToMLTTTy someType = someType
  | _, .unit, _mlttProof => rfl
  | _, .bool, _mlttProof => rfl
  | _, .nat, _mlttProof => rfl
  | _, .arrow domainType codomainType, mlttProof => by
      simp only [hottToMLTTTy]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy domainType mlttProof.left]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy codomainType mlttProof.right]
  | _, .piTy domainType codomainType, mlttProof => by
      simp only [hottToMLTTTy]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy domainType mlttProof.left]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy codomainType mlttProof.right]
  | _, .sigmaTy firstType secondType, mlttProof => by
      simp only [hottToMLTTTy]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy firstType mlttProof.left]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy secondType mlttProof.right]
  | _, .tyVar _position, _mlttProof => rfl
  | _, .id carrier leftEndpoint rightEndpoint, mlttProof => by
      simp only [hottToMLTTTy]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy carrier mlttProof]
  | _, .listType elementType, mlttProof => by
      exact congrArg Ty.listType
        (hottToMLTTTy_preserves_isMLTTOnlyTy elementType mlttProof)
  | _, .optionType elementType, mlttProof => by
      exact congrArg Ty.optionType
        (hottToMLTTTy_preserves_isMLTTOnlyTy elementType mlttProof)
  | _, .eitherType leftType rightType, mlttProof => by
      simp only [hottToMLTTTy]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy leftType mlttProof.left]
      rw [hottToMLTTTy_preserves_isMLTTOnlyTy rightType mlttProof.right]
  | _, .universe _universeLevel _levelLe, _mlttProof => rfl
  | _, .empty, _mlttProof => rfl
  | _, .interval, mlttProof => False.elim mlttProof
  | _, .path _carrier _leftEndpoint _rightEndpoint, mlttProof =>
      False.elim mlttProof
  | _, .glue _baseType _boundaryWitness, mlttProof => False.elim mlttProof
  | _, .oeq _carrier _leftEndpoint _rightEndpoint, mlttProof =>
      False.elim mlttProof
  | _, .idStrict _carrier _leftEndpoint _rightEndpoint, mlttProof =>
      False.elim mlttProof
  | _, .equiv _domainType _codomainType, mlttProof => False.elim mlttProof
  | _, .refine _baseType _predicate, mlttProof => False.elim mlttProof
  | _, .record _singleFieldType, mlttProof => False.elim mlttProof
  | _, .codata _stateType _outputType, mlttProof => False.elim mlttProof
  | _, .session _protocolStep, mlttProof => False.elim mlttProof
  | _, .effect _carrierType _effectTag, mlttProof => False.elim mlttProof
  | _, .modal _modalityTag _carrierType, mlttProof => False.elim mlttProof

end Conservativity
end LeanFX2

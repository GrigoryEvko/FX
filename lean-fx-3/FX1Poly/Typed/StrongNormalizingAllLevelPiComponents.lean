import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Core.StrongNormalizationSubterm

/-! # FX1Poly/Typed/StrongNormalizingAllLevelPiComponents
    — component projections for strongly-normalizing all-level reducible Π type codes

The positive-member-extension bridge ultimately needs structural access to type values.  For a dependent
Π type code, strong normalization of the whole code gives strong normalization of its syntactic children,
while all-level reducibility of the whole code gives all-level reducibility of the domain and positive-level
reducibility of each instantiated codomain under an all-positive argument.  This file packages those
projections without claiming global fuel irrelevance.

## Zero-axiom verification

The proofs are direct products of the already-gated subterm-SN inversions and the all-level Π reducibility
projections.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar

/-- **Domain data of a strongly-normalizing all-level reducible Π type code.**  The domain is strongly
normalizing as a syntactic child and reducible as a type at every semantic fuel. -/
theorem IsReducibleTypeAtAllLevels.domainDataOfStronglyNormalizingPiType {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (piTypeNormalizing : IsStronglyNormalizing (piTyCodeCell domainCode codomainCode))
    (piTypeReducibleAtAllLevels :
      IsReducibleTypeAtAllLevels (piTyCodeCell domainCode codomainCode)) :
    IsStronglyNormalizing domainCode ∧ IsReducibleTypeAtAllLevels domainCode :=
  ⟨StepStar.domain_isStronglyNormalizing_of_piTyCode piTypeNormalizing,
    IsReducibleTypeAtAllLevels.domainOfPiType piTypeReducibleAtAllLevels⟩

/-- **Codomain data of a strongly-normalizing all-level reducible Π type code at an all-positive argument.**
The open codomain child is strongly normalizing, and the instantiated codomain is reducible at every
positive semantic fuel for every all-positive domain argument. -/
theorem IsReducibleTypeAtAllLevels.codomainDataOfStronglyNormalizingPiTypeAtAllPositiveArgument
    {scope : Nat} {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {argument : RawTerm scope}
    (piTypeNormalizing : IsStronglyNormalizing (piTyCodeCell domainCode codomainCode))
    (piTypeReducibleAtAllLevels :
      IsReducibleTypeAtAllLevels (piTyCodeCell domainCode codomainCode))
    (argumentMemberAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels domainCode argument) :
    IsStronglyNormalizing codomainCode ∧
      IsReducibleTypeAtAllPositiveLevels (RawTerm.subst0 codomainCode argument) :=
  ⟨StepStar.codomain_isStronglyNormalizing_of_piTyCode piTypeNormalizing,
    IsReducibleTypeAtAllLevels.codomainOfPiTypeAtAllPositiveArgument
      piTypeReducibleAtAllLevels argumentMemberAtAllPositiveLevels⟩

end FX1Poly.Typed

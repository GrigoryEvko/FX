import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

-- Combined dependent-Pi arm: package the shipped type leg (piTypeOfDomainMemberExtension) + member leg
-- (piTypeMemberExtension) into the single piType-arm combinator the eventual mutual induction calls.
-- Dependent codomain; universe-domain-free closed (the open case is a UNIVERSE domain).
theorem dependentPiArm_probe {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ (argument : RawTerm scope) {memberLevel : Nat},
        IsReducibleMemberAt memberLevel domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument))
    (codomainMemberExtension : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          ∀ applicationTerm : RawTerm scope, ∀ {memberLevel : Nat},
            IsReducibleMemberAt memberLevel (RawTerm.subst0 codomainCode argument) applicationTerm →
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument) applicationTerm) :
    IsReducibleTypeAtAllLevels
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) ∧
      (∀ (functionTerm : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
            functionTerm →
          IsReducibleMemberAtAllPositiveLevels
            (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
            functionTerm) :=
  ⟨IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension
      domainAllLevels domainMemberExtension codomainAllLevels,
    fun functionTerm {_predLevel} member =>
      IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension
        domainAllLevels domainMemberExtension codomainAllLevels codomainMemberExtension member⟩

end FX1Poly.Typed

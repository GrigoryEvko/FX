import FX1Poly.Typed.PiTypeSaturationReassembly
import FX1Poly.Typed.NeutralFuelStability
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- TYPE side: dependent Pi over a neutral domain is all-positive reducible, conditional only on codomain.
theorem IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain_probe {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllPositive : ∀ {arg : RawTerm scope},
        IsReducibleMemberAtAllPositiveLevels dom arg →
        IsReducibleTypeAtAllPositiveLevels (RawTerm.subst0 cod arg)) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) := by
  have domainAllLevels : IsReducibleTypeAtAllLevels dom :=
    IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse
  exact IsReducibleTypeAtAllPositiveLevels.ofPiType
    domainAllLevels.atAllPositiveLevels
    (fun {_arg _predLevel} member =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        domainWeakHeadNormal domainNotPiType domainNotUniverse domainAllLevels member)
    codomainAllPositive

-- MEMBER side: member-extension for a dependent Pi over a neutral domain, conditional only on codomain.
theorem IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain_probe
    {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 cod argument))
    (codomainMemberExtension : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
          ∀ applicationTerm : RawTerm scope, ∀ {memberPredLevel : Nat},
            IsReducibleMemberAt (memberPredLevel + 1) (RawTerm.subst0 cod argument) applicationTerm →
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 cod argument) applicationTerm)
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm := by
  have domainAllLevels : IsReducibleTypeAtAllLevels dom :=
    IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse
  exact IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtensionPositive
    domainAllLevels
    (fun _argument {_memberPredLevel} argMember =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        domainWeakHeadNormal domainNotPiType domainNotUniverse domainAllLevels argMember)
    codomainAllLevels
    codomainMemberExtension
    member

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain_probe
#print axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain_probe

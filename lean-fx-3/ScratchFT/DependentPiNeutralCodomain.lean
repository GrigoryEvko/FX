import FX1Poly.Typed.DependentPiOverNeutralDomain

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- TYPE side: dependent Pi over a neutral domain whose codomain-instantiations are ALL neutral is
-- UNCONDITIONALLY all-positive reducible (codomain leg discharged via the neutral leaf).
theorem IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain_probe
    {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainWeakHeadNormal : ∀ arg : RawTerm scope,
        ∀ reduct : RawTerm scope, ¬ WeakHeadStep (RawTerm.subst0 cod arg) reduct)
    (codomainNotPiType : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_piTyCode)
    (codomainNotUniverse : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) :=
  IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain
    domainWeakHeadNormal domainNotPiType domainNotUniverse
    (fun {arg} _member =>
      (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (codomainWeakHeadNormal arg) (codomainNotPiType arg)
        (codomainNotUniverse arg)).atAllPositiveLevels)

-- MEMBER side: member-extension for the same fully-neutral dependent Pi is UNCONDITIONAL.
theorem IsReducibleMemberAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain_probe
    {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainWeakHeadNormal : ∀ arg : RawTerm scope,
        ∀ reduct : RawTerm scope, ¬ WeakHeadStep (RawTerm.subst0 cod arg) reduct)
    (codomainNotPiType : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_piTyCode)
    (codomainNotUniverse : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_universeCode)
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm :=
  IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain
    domainWeakHeadNormal domainNotPiType domainNotUniverse
    (fun argument _argMember =>
      IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument))
    (fun argument _argMember applicationTerm {_memberPredLevel} applicationMember =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument)
        (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument))
        applicationMember)
    member

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain_probe
#print axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain_probe

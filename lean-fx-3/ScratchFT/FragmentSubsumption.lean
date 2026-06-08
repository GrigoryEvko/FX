import FX1Poly.Typed.DependentlyTypedNeutralDomainFragment
import FX1Poly.Typed.FirstOrderSimplyTypedReducibility

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Subsumption: the dependent-neutral fragment strictly contains the first-order simply-typed fragment.
-- A non-dependent arrow dom -> weaken codBase is a dependentPi whose codomain instantiation is constantly codBase.
theorem IsFirstOrderSimplyTyped.toNeutralDomainDependentlyTyped_probe {scope : Nat}
    {typeCode : RawTerm scope}
    (firstOrder : IsFirstOrderSimplyTyped typeCode) :
    IsNeutralDomainDependentlyTyped typeCode := by
  induction firstOrder with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact IsNeutralDomainDependentlyTyped.leaf weakHeadNormal notPiType notUniverse
  | arrow domainWeakHeadNormal domainNotPiType domainNotUniverse _codomainFirstOrder codomainFragment =>
      exact IsNeutralDomainDependentlyTyped.dependentPi
        domainWeakHeadNormal domainNotPiType domainNotUniverse
        (fun arg => by
          show IsNeutralDomainDependentlyTyped
            (RawTerm.subst (RawTermSubst.singleton arg) (RawTerm.weaken _))
          rw [RawTerm.weaken_subst_singleton]
          exact codomainFragment)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.toNeutralDomainDependentlyTyped_probe

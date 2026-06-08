import FX1Poly.Typed.DependentPiNeutralCodomain
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- ALL-LEVELS type-side dependent Pi over a neutral domain (companion to the positive-only arm shipped earlier).
theorem IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain_probe {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
        IsReducibleTypeAtAllLevels (RawTerm.subst0 cod argument)) :
    IsReducibleTypeAtAllLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) :=
  IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension
    (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse)
    (fun _argument {_memberLevel} member =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
        domainWeakHeadNormal domainNotPiType domainNotUniverse member)
    codomainAllLevels

-- The inductive fragment: neutral/data leaves + dependent Pi over neutral domains whose codomain
-- INSTANTIATIONS are recursively in the fragment.
inductive IsNeutralDomainDependentlyTyped_probe : {scope : Nat} → RawTerm scope → Prop
  | leaf {scope : Nat} {classifier : RawTerm scope}
      (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
      (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
      (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
      IsNeutralDomainDependentlyTyped_probe classifier
  | dependentPi {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
      (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
      (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
      (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
      (codomainFragment : ∀ argument : RawTerm scope,
          IsNeutralDomainDependentlyTyped_probe (RawTerm.subst0 cod argument)) :
      IsNeutralDomainDependentlyTyped_probe
        (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))

-- Fundamental theorem: every fragment type is reducible at all levels AND admits member-extension.
theorem IsNeutralDomainDependentlyTyped_probe.reducibleAndMemberExtension
    {scope : Nat} {typeCode : RawTerm scope}
    (fragment : IsNeutralDomainDependentlyTyped_probe typeCode) :
    IsReducibleTypeAtAllLevels typeCode ∧
      (∀ (functionTerm : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) typeCode functionTerm →
          IsReducibleMemberAtAllPositiveLevels typeCode functionTerm) := by
  induction fragment with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact ⟨IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          weakHeadNormal notPiType notUniverse,
        fun functionTerm {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
            weakHeadNormal notPiType notUniverse member⟩
  | dependentPi domainWeakHeadNormal domainNotPiType domainNotUniverse _codomainFragment codomainIH =>
      refine ⟨IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain_probe
          domainWeakHeadNormal domainNotPiType domainNotUniverse
          (fun argument _argMember => (codomainIH argument).1),
        fun functionTerm {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain
            domainWeakHeadNormal domainNotPiType domainNotUniverse
            (fun argument _argMember => (codomainIH argument).1)
            (fun argument _argMember applicationTerm {_memberPredLevel} applicationMember =>
              (codomainIH argument).2 applicationTerm applicationMember)
            member⟩

-- Convenience leaf: every neutral term is in the fragment.
theorem IsNeutralDomainDependentlyTyped_probe.ofNeutral {scope : Nat} {classifier : RawTerm scope}
    (neutral : IsNeutral classifier) : IsNeutralDomainDependentlyTyped_probe classifier :=
  IsNeutralDomainDependentlyTyped_probe.leaf
    neutral.noWeakHeadStep neutral.rootGenerator_ne_piTyCode neutral.rootGenerator_ne_universeCode

-- Concrete genuinely-dependent fragment member: Pi (x : A). P x.
theorem concreteDependentPi_isFragment_probe {scope : Nat} (domVar familyVar : Fin scope) :
    IsNeutralDomainDependentlyTyped_probe
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_var domVar .childNil)
          (.childCons
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            .childNil))) :=
  IsNeutralDomainDependentlyTyped_probe.dependentPi
    (fun _reduct => (IsNeutral.var domVar).noWeakHeadStep _)
    (IsNeutral.var domVar).rootGenerator_ne_piTyCode
    (IsNeutral.var domVar).rootGenerator_ne_universeCode
    (fun arg => by
      rw [show RawTerm.subst0
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            arg
          = (.mkGen .gen_app ()
              (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil)))
          from by
            rw [RawTerm.subst0_app_reduces,
                show RawTerm.subst0 (RawTerm.weaken (.mkGen .gen_var familyVar .childNil)) arg
                  = (.mkGen .gen_var familyVar .childNil : RawTerm scope)
                  from RawTerm.weaken_subst_singleton _ _,
                RawTerm.subst0_var_zero]]
      exact IsNeutralDomainDependentlyTyped_probe.ofNeutral (IsNeutral.app (IsNeutral.var familyVar)))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain_probe
#print axioms FX1Poly.Typed.IsNeutralDomainDependentlyTyped_probe.reducibleAndMemberExtension
#print axioms FX1Poly.Typed.concreteDependentPi_isFragment_probe

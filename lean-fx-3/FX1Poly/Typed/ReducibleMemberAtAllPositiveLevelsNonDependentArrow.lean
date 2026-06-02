import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsNonDependentArrow
    — member-extension for a NON-DEPENDENT arrow: the codomain hypotheses collapse to constant

The non-dependent (simple-arrow) specialization of `IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension`.
For a dependent Π the codomain hypotheses are quantified over the bound argument: the instantiated codomain
`RawTerm.subst0 codomainCode argument` and its all-levels reducibility / member-extension are argument-indexed.
For a simple arrow `domainCode → codomainBase` — i.e. `piTyCodeCell domainCode (RawTerm.weaken codomainBase)`
— the weakening cancels the substitution (`RawTerm.weaken_subst_singleton`: `subst0 (weaken B) arg = B`), so
those argument-indexed hypotheses collapse to the CONSTANT facts about the base codomain `codomainBase`: its
all-levels reducibility and its own member-extension, with no dependence on the argument.

This is the member-side twin of `formerChildrenReducibleNonDependentAtAll` (the formation-side non-dependent
arm): it is the recursion step for the operational member-extension principle
(`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`) over the SIMPLY-TYPED fragment — types built
from neutral / data formers and non-dependent arrows, where the Π codomain never grows under instantiation, so
the principle recurses structurally on the (strictly smaller) domain and base codomain.  Dependent Π domains
and universe domains remain the open type-polymorphism residual (the codomain-substitution measure and the
universe impredicativity); this lemma is exactly the fragment where that obstruction is absent.

## Zero-axiom verification

`refine` through `piTypeMemberExtension` with the two argument-indexed codomain goals discharged by rewriting
`RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase` (`RawTerm.weaken_subst_singleton`, with
`subst0` defeq `subst (singleton _)`) and supplying the constant base-codomain hypotheses.  No induction.
Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-extension for a non-dependent arrow.**  A positive-level member of the simple arrow
`domainCode → codomainBase` extends to all positive levels given: the domain is reducible at all levels and
admits member-extension, and the BASE codomain is reducible at all levels and admits member-extension.  The
dependent `piTypeMemberExtension`'s argument-indexed codomain hypotheses collapse here because the weakened
codomain cancels the binder substitution (`subst0 (weaken codomainBase) argument = codomainBase`).  The
member-side analog of `formerChildrenReducibleNonDependentAtAll`. -/
theorem IsReducibleMemberAtAllPositiveLevels.nonDependentArrow {scope : Nat}
    {domainCode codomainBase : RawTerm scope}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ argument : RawTerm scope, ∀ {memberLevel : Nat},
        IsReducibleMemberAt memberLevel domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevels : IsReducibleTypeAtAllLevels codomainBase)
    (codomainMemberExtension : ∀ applicationTerm : RawTerm scope, ∀ {memberLevel : Nat},
        IsReducibleMemberAt memberLevel codomainBase applicationTerm →
          IsReducibleMemberAtAllPositiveLevels codomainBase applicationTerm)
    (member : IsReducibleMemberAt (predLevel + 1)
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) functionTerm := by
  refine IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension domainAllLevels
    domainMemberExtension ?_ ?_ member
  · intro argument _argumentInDomain
    rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
      RawTerm.weaken_subst_singleton codomainBase argument]
    exact codomainAllLevels
  · intro argument _argumentInDomain applicationTerm memberLevel applicationMember
    rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
      RawTerm.weaken_subst_singleton codomainBase argument] at applicationMember ⊢
    exact codomainMemberExtension applicationTerm applicationMember

end FX1Poly.Typed

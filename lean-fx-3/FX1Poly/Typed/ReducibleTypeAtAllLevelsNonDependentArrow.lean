import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsNonDependentArrow
    — all-levels type reducibility for a NON-DEPENDENT arrow

The type-side twin of `IsReducibleMemberAtAllPositiveLevels.nonDependentArrow`.  The dependent
`IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension` asks for the codomain to be reducible at all levels
for every all-positive domain argument — an argument-indexed premise.  For a simple arrow
`domainCode → codomainBase` — i.e. `piTyCodeCell domainCode (RawTerm.weaken codomainBase)` — the weakening
cancels the binder substitution (`RawTerm.weaken_subst_singleton`: `subst0 (weaken B) arg = B`), so that
premise collapses to the CONSTANT fact `IsReducibleTypeAtAllLevels codomainBase`, with no dependence on the
argument.  The domain still needs member-extension (the Π type arm threads the domain candidate through it),
exactly as in the dependent case.

Together with `IsReducibleMemberAtAllPositiveLevels.nonDependentArrow` this is the full non-dependent-arrow
reducibility pair (type + member): a simple arrow over an all-levels, member-extending domain and an all-levels
base codomain is itself all-levels reducible and member-extending.  It is the simply-typed reducibility step
where the dependent-Π codomain-substitution measure obstruction is structurally absent — the codomain never
grows under instantiation.

## Zero-axiom verification

`refine` through `piTypeOfDomainMemberExtension` with the single argument-indexed codomain goal discharged by
rewriting `RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase`
(`RawTerm.weaken_subst_singleton`, with `subst0` defeq `subst (singleton _)`) and supplying the constant base
codomain hypothesis.  No induction.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **All-levels type reducibility for a non-dependent arrow.**  The simple arrow
`domainCode → codomainBase` is reducible at all levels given the domain is reducible at all levels and admits
member-extension, and the base codomain is reducible at all levels.  The dependent
`piTypeOfDomainMemberExtension`'s argument-indexed codomain premise collapses here via weaken-cancellation
(`subst0 (weaken codomainBase) argument = codomainBase`).  The type-side twin of
`IsReducibleMemberAtAllPositiveLevels.nonDependentArrow`. -/
theorem IsReducibleTypeAtAllLevels.nonDependentArrow {scope : Nat}
    {domainCode codomainBase : RawTerm scope}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ (argument : RawTerm scope) {memberLevel : Nat},
        IsReducibleMemberAt memberLevel domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevels : IsReducibleTypeAtAllLevels codomainBase) :
    IsReducibleTypeAtAllLevels (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  refine IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension domainAllLevels
    domainMemberExtension ?_
  intro argument _argumentInDomain
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainAllLevels

end FX1Poly.Typed

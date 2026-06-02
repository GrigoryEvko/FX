import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsNonDependentArrow
    — all-levels type reducibility for a NON-DEPENDENT arrow

The type-side twin of `IsReducibleMemberAtAllPositiveLevels.nonDependentArrow`.  The dependent
`IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension` asks for the codomain to be reducible at all levels
for every all-positive domain argument — an argument-indexed premise.  For a simple arrow
`domainCode → codomainBase` — i.e. `piTyCodeCell domainCode (RawTerm.weaken codomainBase)` — the weakening
cancels the binder substitution (`RawTerm.weaken_subst_singleton`: `subst0 (weaken B) arg = B`), so that
premise collapses to the CONSTANT fact `IsReducibleTypeAtAllLevels codomainBase`, with no dependence on the
argument.  `nonDependentArrow` still threads domain member-extension (it routes through
`piTypeOfDomainMemberExtension`); `nonDependentArrowOfAllLevelsDomain` below DROPS it — for a non-dependent
codomain the domain candidate need not be the canonical member-predicate, so the argument membership is never
consumed and member-extension is unnecessary.  That member-extension-free form reaches a non-dependent arrow
over a UNIVERSE domain (`universeDomainNonDependentArrow`), the type-side crack past the universe-domain wall.

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

/-- **All-levels type reducibility for a non-dependent arrow WITHOUT domain member-extension.**  Strictly
generalizes `nonDependentArrow`: a simple arrow `domainCode → codomainBase` is reducible at all levels from
the domain and codomain being reducible at all levels ALONE — the domain need NOT admit member-extension.

The mechanism: for a non-dependent codomain `RawTerm.weaken codomainBase`, the `piType` constructor's
per-argument codomain candidate is CONSTANT in the argument (the weakening cancels the binder substitution,
`subst0 (weaken codomainBase) argument = codomainBase`), so the argument's domain membership is never
consumed — unlike `piTypeOfDomainMemberExtension`, which routes the codomain through the all-positive domain
membership and therefore needs member-extension.  Each level is built directly: the domain candidate from
`domainAllLevels`, a constant codomain candidate from `codomainAllLevels`, and the argument-membership
discarded.

This is the precise type-side CRACK past the universe-domain wall: a non-dependent arrow over a UNIVERSE
domain (`Type@e → codomainBase`, see `universeDomainNonDependentArrow`) is all-levels reducible even though
a universe domain has NO member-extension (the open type-polymorphic core).  Only the MEMBER leg of a
universe-domain arrow stays blocked — applying the function consumes domain-member level-irrelevance, which
for a universe domain is exactly the open universe member-extension; the TYPE leg here is unconditional. -/
theorem IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain {scope : Nat}
    {domainCode codomainBase : RawTerm scope}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (codomainAllLevels : IsReducibleTypeAtAllLevels codomainBase) :
    IsReducibleTypeAtAllLevels (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  intro level
  have codomainSubstEquation : ∀ argument : RawTerm scope,
      RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase :=
    fun argument => RawTerm.weaken_subst_singleton codomainBase argument
  cases level with
  | zero =>
      obtain ⟨_domainCandidate, domainReducible⟩ := domainAllLevels 0
      obtain ⟨codomainCandidate, codomainReducible⟩ := codomainAllLevels 0
      refine ⟨_, ReducibleTypeStep.piType (fun _argument => codomainCandidate) domainReducible
        (fun argument _argumentInDomain => ?_)⟩
      rw [codomainSubstEquation argument]
      exact codomainReducible
  | succ predLevel =>
      obtain ⟨_domainCandidate, domainReducible⟩ := domainAllLevels (predLevel + 1)
      obtain ⟨codomainCandidate, codomainReducible⟩ := codomainAllLevels (predLevel + 1)
      refine ⟨_, ReducibleTypeStep.piType (fun _argument => codomainCandidate) domainReducible
        (fun argument _argumentInDomain => ?_)⟩
      rw [codomainSubstEquation argument]
      exact codomainReducible

/-- **A non-dependent arrow over a UNIVERSE domain is reducible at all levels.**  `Type@levelExpr+flag →
codomainBase` is all-levels reducible whenever the codomain is — the concrete witness that
`nonDependentArrowOfAllLevelsDomain` reaches past the universe-domain wall.  The universe domain is
all-levels reducible unconditionally (`ofUniverseCode`); the member-extension-requiring `nonDependentArrow`
could not produce this (a universe domain has no member-extension).  Only the dependent and member legs of a
universe domain remain open. -/
theorem IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {codomainBase : RawTerm scope}
    (codomainAllLevels : IsReducibleTypeAtAllLevels codomainBase) :
    IsReducibleTypeAtAllLevels
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) :=
  IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain
    IsReducibleTypeAtAllLevels.ofUniverseCode codomainAllLevels

end FX1Poly.Typed

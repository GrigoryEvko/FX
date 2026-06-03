import FX1Poly.Typed.DependentlyTypedNeutralDomainFragment
import FX1Poly.Typed.FirstOrderSimplyTypedReducibility

/-! # FX1Poly/Typed/FirstOrderSimplyTypedSubsumption
    — the dependent-neutral fragment STRICTLY CONTAINS the first-order simply-typed fragment

`IsFirstOrderSimplyTyped` (neutral / data leaves + NON-dependent arrows whose domains are neutral / data) and
`IsNeutralDomainDependentlyTyped` (the same leaves + DEPENDENT Π over neutral domains) each carry their own
fundamental theorem.  This file proves the containment `IsFirstOrderSimplyTyped ⊆ IsNeutralDomainDependentlyTyped`:
a non-dependent arrow `dom → RawTerm.weaken codomainBase` is a degenerate dependent Π whose codomain
instantiation `RawTerm.subst0 (RawTerm.weaken codomainBase) arg = codomainBase` is CONSTANT in the argument
(the weakening cancels the substitution, `RawTerm.weaken_subst_singleton`), so the `dependentPi` constructor's
universally-quantified codomain-fragment premise is discharged by the (constant) codomain's first-order
witness.  The dependent fragment is therefore a strict generalization — its codomains may genuinely depend on
the bound variable, while the simply-typed arrows are exactly the constant-codomain special case.

The corollary `reducibleAndMemberExtensionViaDependentFragment` is the payoff: the dependent fragment's single
fundamental theorem (`IsNeutralDomainDependentlyTyped.reducibleAndMemberExtension`) re-derives the first-order
simply-typed reducibility-and-member-extension result through the subsumption — one fundamental theorem now
covers both fragments.  (Higher-order simply-typed `IsSimplyTyped`, whose arrow DOMAINS may themselves be
arrows, is NOT subsumed: the dependent fragment requires neutral / data domains.  Subsuming higher-order
domains needs the domain's member-extension at fuel `0`, the degenerate-fuel-`0` boundary, which is deferred
together with the universe-domain crux of #672.)

## Zero-axiom verification

A 2-arm induction over `IsFirstOrderSimplyTyped` (the `leaf` arm maps to the fragment leaf; the `arrow` arm
applies `dependentPi`, discharging its codomain premise by `RawTerm.weaken_subst_singleton` and the codomain
inductive hypothesis), plus a one-step composition for the corollary.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The dependent-neutral fragment contains the first-order simply-typed fragment.**  Every
`IsFirstOrderSimplyTyped` type is `IsNeutralDomainDependentlyTyped`: leaves map across directly, and a
non-dependent arrow is the degenerate dependent Π whose codomain instantiation is the constant base codomain
(`RawTerm.weaken_subst_singleton` cancels the substitution), discharged by the codomain's first-order witness
under the `dependentPi` constructor's per-argument premise. -/
theorem IsFirstOrderSimplyTyped.toNeutralDomainDependentlyTyped {scope : Nat}
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

/-- **The dependent fragment's fundamental theorem re-derives first-order simply-typed reducibility.**  Via
the subsumption, every first-order simply-typed type is reducible at all levels and admits member-extension —
proved through `IsNeutralDomainDependentlyTyped.reducibleAndMemberExtension` rather than the bespoke
`IsFirstOrderSimplyTyped.reducibleAndMemberExtension`.  One fundamental theorem now covers both fragments. -/
theorem IsFirstOrderSimplyTyped.reducibleAndMemberExtensionViaDependentFragment {scope : Nat}
    {typeCode : RawTerm scope}
    (firstOrder : IsFirstOrderSimplyTyped typeCode) :
    IsReducibleTypeAtAllLevels typeCode ∧
      (∀ (functionTerm : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) typeCode functionTerm →
          IsReducibleMemberAtAllPositiveLevels typeCode functionTerm) :=
  firstOrder.toNeutralDomainDependentlyTyped.reducibleAndMemberExtension

end FX1Poly.Typed

import FX1Poly.Typed.FundamentalAtAllTelescopePositiveArguments
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsHeadExpand

/-! # FX1Poly/Typed/FundamentalTelescopeConsWhnfDomain
    — the formation-FT telescope-cons arm CLOSES for a weak-head-reducible domain

Sibling of `FundamentalTelescopeConsNeutralDomain`.  Where the neutral lemma discharges the cons companion's
`headMemberExtendsToAllPositive` premise OUTRIGHT (membership in a neutral / data-former classifier is
`IsStronglyNormalizing`, level-independent), this file discharges it for a domain whose substituted form
weak-head-STEPS: a member of the redex classifier peels across the weak-head step to the contractum (shared
candidate), the contractum's own member-extension strengthens it to all-positive, and the value-level head-
expansion lifts it back — exactly `IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand`.

So the telescope-cons arm closes for any former whose substituted domain weak-head-reduces to a member-
extending contractum, given the contractum's member-extension.  Chaining with the neutral leaf (contractum
neutral / data) this covers every domain whose weak-head normal form is neutral or a data former.  Like the
positive-argument wiring it composes (see the `FundamentalAtAllTelescopePositiveArguments` docstring), this
is non-recursive telescope plumbing: it consumes a supplied contractum-member-extension rather than
manufacturing one, so it does not touch the open universe-domain Tarski case.

## Zero-axiom verification

A direct composition of `fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises` with
`IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand`; no new proof.  Verified `#print axioms` clean: no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The formation-FT telescope-cons arm, closed for a weak-head-reducible domain.**  When the substituted
domain `RawTerm.subst substitution head` weak-head-steps to `substitutedHeadReduct` and that contractum admits
member-extension, the cons companion's head-member premise is discharged by
`IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand`, so the telescope-cons relation holds given only
the tail recursion.  The weak-head-reducible companion of `fundamentalTelescopeConsAtAllNeutralDomain`. -/
theorem fundamentalTelescopeConsAtAllWhnfDomain {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    {substitutedHeadReduct : RawTerm (targetScope + 1)}
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution)
    (headFundamental : FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (substitutedHeadStep : WeakHeadStep (RawTerm.subst substitution head) substitutedHeadReduct)
    (reductMemberExtension : ∀ {memberLevel : Nat} (term : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel substitutedHeadReduct term →
          IsReducibleMemberAtAllPositiveLevels substitutedHeadReduct term)
    (tailReducibleAtAllPositiveArgument :
      ∀ (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises reducibleEnv headFundamental
    (fun {_memberLevel} argument argumentMember =>
      IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand substitutedHeadStep
        reductMemberExtension argument argumentMember)
    tailReducibleAtAllPositiveArgument

end FX1Poly.Typed

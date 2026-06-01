import FX1Poly.Typed.FundamentalAtAllLeafArms

/-! # FX1Poly/Typed/FundamentalAtAllFormerChildren
    — package the two-child Π/Σ-formation semantic companion over the all-level environment

The generic `genFormation` / `genFormationPi` arm for the two dependent type formers needs the
`FormerChildrenReducible` bundle consumed by `fundamentalPiFormationAtAll` and
`fundamentalSigmaFormationAtAll`: the domain child at two adjacent levels, and the codomain child under a
single argument substituted into the binder.

This file factors that packaging step.  It deliberately does not manufacture the codomain-under-argument
premise; that premise is the recursive binder/telescope obligation.  The theorem here is the stable
non-recursive bridge from:

* a domain `FundamentalConclusionAtAll`, plus
* the recursive codomain-under-argument semantic premise,

to the exact `FormerChildrenReducible` record used by the former-membership dispatch.

## Zero-axiom verification

The proof is tuple construction plus two `subst_universeCodeCell` rewrites on the domain fundamental
theorem.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Former-child reducibility from the factored all-level child premises.**  The domain child is read from
its `FundamentalConclusionAtAll` result at `predLevel` and `predLevel + 1`, yielding the two adjacent
universe memberships the Π/Σ former dispatch needs.  The codomain child is supplied by the recursive
telescope/binder companion under `RawTermSubst.cons argument substitution`, at the single conclusion level
`predLevel + 1`. -/
theorem formerChildrenReducibleAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainMemberUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducible predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel := by
  intro _targetScope substitution env predLevel
  refine ⟨?domainAtLevel, ?domainAboveAndCodomain⟩
  · have domainMember := domainFundamental substitution env predLevel
    rwa [subst_universeCodeCell] at domainMember
  · refine ⟨?domainAtNextLevel, ?codomainUnderArgument⟩
    · have domainMemberAbove := domainFundamental substitution env (predLevel + 1)
      rwa [subst_universeCodeCell] at domainMemberAbove
    · intro memberLevel argument argumentMember
      exact codomainMemberUnderArgument substitution env predLevel argument argumentMember

end FX1Poly.Typed

import FX1Poly.Typed.FundamentalAtAllLeafArms

/-! # FX1Poly/Typed/FundamentalAtAllPiIntro
    — package the recursive binder premises for all-level dependent Π introduction

`fundamentalPiIntroAtAll` is the semantic dispatch for λ-introduction once two binder-recursive companions
are available:

* the instantiated codomain is a reducible type for every reducible domain argument; and
* the instantiated body is a reducible member of that codomain.

The recursor naturally produces those companions as MEMBERSHIP statements under the `cons`-extended
substitution: the codomain premise is a member of its universe, and the body premise is a member of the
codomain.  This file performs the non-recursive translation from those `cons`-substitution memberships into
the `subst0 (subst (lift substitution) ...) argument` shape consumed by `fundamentalPiIntroAtAll`.

## Zero-axiom verification

The proof composes `fundamentalPiIntroAtAll`, `tarskiDecode`, `subst_universeCodeCell`, and
`RawTerm.subst_cons_eq_subst0_lift`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Dependent Π-introduction from recursive member premises.**  The domain premise remains an all-level
fundamental-theorem result.  The codomain/body premises are stated exactly as the recursor produces them
under `RawTermSubst.cons argument substitution`; this theorem decodes the codomain universe membership and
rewrites both `cons` substitutions into the instantiated `subst0` form required by
`fundamentalPiIntroAtAll`. -/
theorem fundamentalPiIntroAtAllFromMemberPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainMemberUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAt (predLevel + 2)
            (RawTerm.subst (RawTermSubst.cons argument substitution)
              (universeCodeCell codomainLevel flag))
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (bodyMemberUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAt (predLevel + 1)
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)
            (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    FundamentalConclusionAtAll context (lamCell domainCode body)
      (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroAtAll domainFundamental
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain => by
      have codomainMember :=
        codomainMemberUnderArgument substitution env predLevel
          (domainCandidate := domainCandidate) domainReducible argument argumentInDomain
      rw [subst_universeCodeCell] at codomainMember
      have codomainReducibleType := codomainMember.tarskiDecode
      rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainReducibleType)
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain => by
      rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
        ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
      exact bodyMemberUnderArgument substitution env predLevel
        (domainCandidate := domainCandidate) domainReducible argument argumentInDomain)

end FX1Poly.Typed

import FX1Poly.Typed.FundamentalAtAllLeafArms

/-! # FX1Poly/Typed/FundamentalAtAllNonDependentBinders
    — non-dependent binder arms over the all-level reducible environment

The fully dependent binder arms require a codomain premise that may mention the freshly-bound value.  In the
stratified Tarski relation this is exactly where universe-level bookkeeping is hard: if the codomain uses the
fresh value as a type, the recursive premise may need the head variable at a higher reducibility level than
the binder rule supplied.

This file records the precise non-dependent binder case, where the codomain is `RawTerm.weaken codomainCode`.
Then substituting an argument for the fresh variable cancels the weakening, so the codomain proof is read from
the original all-level environment with no dependency on the argument's level.  These lemmas are not a roadmap
label; they are the exact theorem names for the simple-arrow binder/formation cases.

## Zero-axiom verification

Each proof delegates to the already-gated semantic rules:
`IsReducibleMemberAt.abstractionNonDependentUnderSubst` for lambda introduction and
`FormerChildrenReducible.toPiMember` / `.toSigmaMember` for the two formers.  The only rewrites are the
substitution cancellation for weakened codomains and `subst_universeCodeCell`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Non-dependent former-child reducibility over the all-level environment.**  If the domain and the
base codomain are fundamental members of their universe classifiers, then the former child bundle for
`piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)` is available.  The codomain component is
argument-independent because substituting through `weaken` cancels against `RawTermSubst.cons`. -/
theorem formerChildrenReducibleNonDependentAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducible predLevel flag substitution domainCode
        (RawTerm.weaken codomainCodeBase) domainLevel codomainLevel := by
  intro _targetScope substitution env predLevel
  refine ⟨?domainAtLevel, ?domainAtNextLevel, ?codomainUnderArgument⟩
  · exact domainFundamental substitution env predLevel
  · exact domainFundamental substitution env (predLevel + 1)
  · intro _memberLevel argument _argumentMember
    have codomainMember := codomainFundamental substitution env predLevel
    rw [subst_universeCodeCell] at codomainMember
    change IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
      (RawTerm.subst (RawTermSubst.cons argument substitution)
        (RawTerm.rename RawRenaming.weaken codomainCodeBase))
    rw [RawTerm.weaken_subst_cons]
    exact codomainMember

/-- **Non-dependent Π-formation over the all-level environment.**  The simple-arrow former
`piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)` inhabits its universe once the domain and base
codomain are fundamental members of their universe classifiers. -/
theorem fundamentalPiFormationNonDependentAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase))
      (universeCodeCell formerLevel flag) :=
  fundamentalPiFormationAtAll
    (formerChildrenReducibleNonDependentAtAll domainFundamental codomainFundamental)

/-- **Non-dependent Σ-formation over the all-level environment.**  The simple dependent-pair former with a
weakened codomain inhabits its universe under the same child hypotheses as
`fundamentalPiFormationNonDependentAtAll`. -/
theorem fundamentalSigmaFormationNonDependentAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context
      (.mkGen .gen_sigmaTyCode ()
        (.childCons domainCode (.childCons (RawTerm.weaken codomainCodeBase) .childNil)))
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationAtAll
    (formerChildrenReducibleNonDependentAtAll domainFundamental codomainFundamental)

/-- **Non-dependent Π-introduction over the all-level environment.**  For a lambda whose classifier is the
simple arrow `piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)`, the domain and base codomain are
decoded from universe membership one level up.  The body premise is stated exactly at the base codomain's
chosen candidate; any recursive proof can obtain that by reducing its own membership witness with
`ReducibleTypeAt.deterministic`. -/
theorem fundamentalPiIntroNonDependentAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag))
    (bodyReducibleUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate codomainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution codomainCodeBase)
          codomainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          codomainCandidate
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    FundamentalConclusionAtAll context (lamCell body)
      (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)) := by
  intro _targetScope substitution env predLevel
  have domainMember := domainFundamental substitution env (predLevel + 1)
  rw [subst_universeCodeCell] at domainMember
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  have codomainMember := codomainFundamental substitution env (predLevel + 1)
  rw [subst_universeCodeCell] at codomainMember
  obtain ⟨codomainCandidate, codomainReducible⟩ := codomainMember.tarskiDecode
  exact IsReducibleMemberAt.abstractionNonDependentUnderSubst substitution domainReducible
    (fun _argument argumentInDomain =>
      domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
    codomainReducible
    (fun argument argumentInDomain =>
      bodyReducibleUnderArgument substitution env predLevel domainReducible codomainReducible
        argument argumentInDomain)

end FX1Poly.Typed

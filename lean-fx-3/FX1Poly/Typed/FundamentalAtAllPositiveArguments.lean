import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro

/-! # FX1Poly/Typed/FundamentalAtAllPositiveArguments
    — dependent binder bridges from all-positive semantic arguments

The grown dependent fundamental theorem is blocked at the exact point where a binder rule supplies a fresh
argument at one semantic level, while a dependent codomain may need that same argument at another positive
level.  This file factors the non-recursive bridge that WOULD make the all-level recursor close:

* if every argument in the decoded domain candidate can be strengthened to membership at every positive
  level of the domain, then the ordinary all-level codomain/body recursive hypotheses can be used under the
  cons-extended environment; and
* the same all-positive argument bridge packages the two Pi/Sigma-formation child premises consumed by the
  dispatch-level former membership lemmas.

No theorem here asserts that existing `ReducibleTypeAt` domain candidates have this strengthening.  That is
the remaining semantic obligation for a proof-relevant/Kripke argument relation.  These bridges pin the
required shape without weakening the final statement or hiding a level-irrelevance assumption.

## Zero-axiom verification

The proofs compose already-gated all-level binder/former packages with `ReducibleEnvAtAllLevels.cons`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **All-positive semantic membership.**  A term is a reducible member of a type at every positive
stratification level.  This is the argument strength an all-level dependent binder needs in order to run
ordinary all-level recursive hypotheses under `context.cons domainCode`. -/
def IsReducibleMemberAtAllPositiveLevels {scope : Nat}
    (typeCode term : RawTerm scope) : Prop :=
  ∀ level : Nat, IsReducibleMemberAt (level + 1) typeCode term

/-- Read an all-positive member at one concrete positive level. -/
theorem IsReducibleMemberAtAllPositiveLevels.atLevel {scope : Nat}
    {typeCode term : RawTerm scope}
    (memberAtAllPositiveLevels : IsReducibleMemberAtAllPositiveLevels typeCode term)
    (level : Nat) :
    IsReducibleMemberAt (level + 1) typeCode term :=
  memberAtAllPositiveLevels level

/-- **Dependent Pi-introduction from all-positive arguments.**  If every argument accepted by the decoded
domain candidate can be strengthened to all positive domain-membership levels, then the codomain and body
all-level recursive hypotheses can be run under the cons-extended all-level environment.  This is the exact
non-recursive binder bridge needed by a proof-relevant/Kripke argument relation. -/
theorem fundamentalPiIntroAtAllFromAllPositiveArgumentPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainMemberExtendsToAllPositive :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtAll context (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroAtAllFromMemberPremises domainFundamental
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain => by
      have argumentAtAllPositiveLevels :=
        domainMemberExtendsToAllPositive substitution env predLevel
          (domainCandidate := domainCandidate) domainReducible argument argumentInDomain
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels) (predLevel + 1))
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain => by
      have argumentAtAllPositiveLevels :=
        domainMemberExtendsToAllPositive substitution env predLevel
          (domainCandidate := domainCandidate) domainReducible argument argumentInDomain
      exact bodyFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels) predLevel)

/-- **Dispatch-level Pi/Sigma former children from all-positive arguments.**  If any semantic domain member
needed by the former dispatch can be strengthened to all positive domain-membership levels, then the
codomain child's all-level recursive hypothesis supplies both codomain-under-argument premises consumed by
`FormerChildrenReducibleAtDispatchLevels`. -/
theorem formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainMemberExtendsToAllPositive :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (_predLevel : Nat)
        {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel (RawTerm.subst substitution domainCode) argument →
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsFromAtAllPremises domainFundamental
    (fun substitution env predLevel argument argumentMember => by
      have argumentAtAllPositiveLevels :=
        domainMemberExtendsToAllPositive substitution env predLevel argument argumentMember
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels) predLevel)
    (fun substitution env predLevel argument argumentMember => by
      have argumentAtAllPositiveLevels :=
        domainMemberExtendsToAllPositive substitution env predLevel argument argumentMember
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels) predLevel)

end FX1Poly.Typed

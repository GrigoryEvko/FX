import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro

/-! # FX1Poly/Typed/FundamentalAtAllVectorPremises
    — bridge vector recursive premises into the all-level binder/former companions

The outer dependent fundamental theorem is stated over `ReducibleEnvAtAllLevels`, so the `var` and `conv`
arms can read the environment at whatever positive level the conclusion demands.  Binder-recursive premises
are different: after extending a context with a fresh argument, the fresh variable is known at ONE semantic
level, not at every level.

This file introduces the vector-environment conclusion shape consumed by binder recursive premises and ships
the two non-recursive bridges from those vector premises back to the all-level arm packages:

* `fundamentalPiIntroAtAllFromVectorPremises`, for lambda introduction; and
* `formerChildrenReducibleAtAllFromVectorPremise`, for the two-child Pi/Sigma former telescope.

The bridges are intentionally factored away from the recursor.  The recursor only has to supply vector
premises for the binder-extended context; these lemmas perform the environment construction with
`ReducibleEnvVec.cons`.

## Zero-axiom verification

Both proofs are direct applications of the already-gated all-level packages.  The only environment work is
`env.toVecPositive` for the tail variables plus `ReducibleEnvVec.cons` for the fresh head.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The vector-environment fundamental-theorem conclusion.**  Under any closing substitution and any
per-variable reducible environment, the subject is a reducible member of its classifier at the requested
positive conclusion level.  This is the shape recursive binder premises consume after a single fresh
argument is consed into the environment. -/
def IsFundamentalConclusionAtVector {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    {envLevels : Fin scope → Nat} (predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **Pi-introduction over the all-level environment, from vector recursive premises.**  The domain remains
an all-level premise.  The codomain/body recursive premises are vector-shaped, because the fresh argument is
available at exactly the domain-member level.  For each argument, the tail variables are read from the
all-level environment at the conclusion level, then `ReducibleEnvVec.cons` installs the fresh head. -/
theorem fundamentalPiIntroAtAllFromVectorPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      IsFundamentalConclusionAtVector (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      IsFundamentalConclusionAtVector (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtAll context (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroAtAllFromMemberPremises domainFundamental
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain =>
      codomainFundamental (RawTermSubst.cons argument substitution) (predLevel + 1)
        (ReducibleEnvVec.cons (env.toVecPositive (fun _index => predLevel))
          ⟨domainCandidate, domainReducible, argumentInDomain⟩))
    (fun _targetScope substitution env predLevel {domainCandidate} domainReducible argument
        argumentInDomain =>
      bodyFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons (env.toVecPositive (fun _index => predLevel))
          ⟨domainCandidate, domainReducible, argumentInDomain⟩))

/-- **Former-child reducibility over the all-level environment, from a vector codomain premise.**  The domain
child is read from its all-level premise at the two adjacent levels required by `FormerChildrenReducible`.
The codomain child is produced by the vector recursive premise under a `cons`-extended environment; the
fresh head is installed at the arbitrary `memberLevel` supplied by the telescope relation. -/
theorem formerChildrenReducibleAtAllFromVectorPremise {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      IsFundamentalConclusionAtVector (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducible predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel :=
  formerChildrenReducibleAtAll domainFundamental
    (fun _targetScope substitution env predLevel {_memberLevel} argument argumentMember =>
      codomainFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons (env.toVecPositive (fun _index => predLevel)) argumentMember))

end FX1Poly.Typed

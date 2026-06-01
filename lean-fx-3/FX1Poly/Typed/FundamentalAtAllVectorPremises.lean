import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro
import FX1Poly.Typed.FundamentalAtAllNonDependentBinders

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

The bridges are intentionally factored away from the recursor.  They are useful exactly at a binder, where a
fresh head has one semantic member level while the tail variables still come from the all-level environment.
They are NOT a standalone replacement for the full fundamental theorem: an arbitrary-vector conclusion is too
strong for a judgment with `var`, because the `var` arm can only return the level stored for that variable.
Use these bridges only for recursive premises whose level vector has been built by the binder rule itself.

## Zero-axiom verification

Both proofs are direct applications of the already-gated all-level packages.  The only environment work is
`env.toVecPositive` for the tail variables plus `ReducibleEnvVec.cons` for the fresh head.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The vector-environment binder-premise conclusion.**  Under a closing substitution and a per-variable
reducible environment, the subject is a reducible member of its classifier at the requested positive
conclusion level.  This is deliberately stronger than the all-level conclusion and is generally unprovable
for judgments with an unrestricted `var` arm.  Its intended use is local: binder-recursive premises consume
it after the caller has constructed a level vector whose fresh head matches the semantic level demanded by
the binder rule. -/
def IsFundamentalConclusionAtVector {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    {envLevels : Fin scope → Nat} (predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **Variable lookup in a vector environment at the matching level.**  The vector premise shape is not
unconditionally valid for `var`: lookup returns the level stored for the variable, while a fundamental-theorem
conclusion asks for the caller's `predLevel + 1`.  This is the exact valid bridge: if the stored level for the
looked-up variable is the requested positive conclusion level, the variable arm closes by `lookupReducible`.
Binder-local recursors can arrange this equality for freshly installed heads; a global formation theorem cannot
assume it for arbitrary variables. -/
theorem fundamentalVarAtVectorMatchingLevel {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope)
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    {envLevels : Fin scope → Nat} (predLevel : Nat)
    (env : ReducibleEnvVec envLevels context substitution)
    (levelMatches : envLevels index = predLevel + 1) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (context.lookup index))
      (RawTerm.subst substitution (variableCell index)) := by
  rw [← levelMatches]
  exact ReducibleEnvVec.lookupReducible env index

/-- **Read a vector-environment fundamental result as an all-level result.**  The all-level environment
supplies the positive vector whose every tail entry is the conclusion level.  This is the final export
bridge for a recursor proved in vector form. -/
theorem fundamentalConclusionAtAllOfVector {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental : IsFundamentalConclusionAtVector context subject classifier) :
    FundamentalConclusionAtAll context subject classifier := by
  intro _targetScope substitution env predLevel
  exact subjectFundamental substitution predLevel (env.toVecPositive (fun _index => predLevel))

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

/-- **Non-dependent Pi-introduction over the all-level environment, from a vector body premise.**  The
domain and base codomain remain all-level premises.  The lambda body is a binder-local vector premise:
under each reducible argument, the fresh head is available at exactly the simple-arrow domain level, while
tail variables come from the all-level environment at the conclusion level.  Determinism transports the
body membership from its witnessing candidate to the fixed base-codomain candidate decoded by
`fundamentalPiIntroNonDependentAtAll`. -/
theorem fundamentalPiIntroNonDependentAtAllFromVectorPremise {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      IsFundamentalConclusionAtVector (context.cons domainCode) body
        (RawTerm.weaken codomainCodeBase)) :
    FundamentalConclusionAtAll context (lamCell body)
      (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)) :=
  fundamentalPiIntroNonDependentAtAll domainFundamental codomainFundamental
    (fun _targetScope substitution env predLevel {domainCandidate codomainCandidate}
        domainReducible codomainReducible argument argumentInDomain => by
      have bodyMember := bodyFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons (env.toVecPositive (fun _index => predLevel))
          ⟨domainCandidate, domainReducible, argumentInDomain⟩)
      rw [RawTerm.weaken_eq_rename] at bodyMember
      rw [RawTerm.weaken_subst_cons] at bodyMember
      rw [RawTerm.subst_cons_eq_subst0_lift _ argument substitution] at bodyMember
      obtain ⟨witnessCandidate, witnessReducible, witnessMember⟩ := bodyMember
      exact (ReducibleTypeAt.deterministic witnessReducible codomainReducible _).mp witnessMember)

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

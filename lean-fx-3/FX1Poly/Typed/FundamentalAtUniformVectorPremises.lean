import FX1Poly.Typed.FundamentalAtAllNonDependentBinders

/-! # FX1Poly/Typed/FundamentalAtUniformVectorPremises
    — level-matching vector premises for simple-arrow binder bodies

`IsFundamentalConclusionAtVector` is intentionally strong: it asks a term to be reducible at the caller's
conclusion level under an ARBITRARY per-variable level vector.  That is useful as an explicit hypothesis,
but it cannot be the global fundamental-theorem motive because the `var` arm only returns the level stored
for the looked-up variable.

This file records the level-matching vector shape that DOES close the `var` arm: every variable in the
environment is stored at the same positive level as the conclusion, `predLevel + 1`.  This is not enough for
the fully dependent formation telescope (which sometimes asks for a codomain under a domain argument one
level lower), but it is exactly the binder-local shape consumed by the non-dependent/simple-arrow
lambda-introduction rule.

## Zero-axiom verification

The variable proof is direct lookup; the all-level export instantiates the all-level environment to the
uniform vector; the simple-arrow pi-introduction bridge delegates to
`fundamentalPiIntroNonDependentAtAll`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The canonical uniform level vector: every variable position is assigned `level`, with the recursive
definition chosen so `positiveUniformLevels (scope+1) level` is definitionally
`levelCons level (positiveUniformLevels scope level)`.  That exact shape is what binder-local
`ReducibleEnvVec.cons` produces. -/
def positiveUniformLevels : (scope : Nat) → Nat → Fin scope → Nat
  | 0, _level, index => index.elim0
  | scope + 1, level, index => levelCons level (positiveUniformLevels scope level) index

/-- The canonical uniform level vector really is pointwise constant. -/
theorem positiveUniformLevels_eq {scope : Nat} (level : Nat) (index : Fin scope) :
    positiveUniformLevels scope level index = level := by
  induction scope with
  | zero => exact index.elim0
  | succ priorScope inductiveHypothesis =>
      match index with
      | ⟨0, _isLt⟩ => rfl
      | ⟨position + 1, isLtSucc⟩ =>
          exact inductiveHypothesis ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- **Level-matching vector fundamental-theorem conclusion.**  Under a closing substitution and a vector
environment whose every variable is available at the conclusion level `predLevel + 1`, the subject is a
reducible member of its classifier at that same positive level.  This is the strongest vector shape the
plain `var` arm can validate without an extra level-equality hypothesis. -/
def IsFundamentalConclusionAtUniformVector {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (predLevel : Nat)
    (_env : ReducibleEnvVec (positiveUniformLevels scope (predLevel + 1)) context substitution),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **The matching-vector variable arm.**  Since the vector stores every variable exactly at the conclusion
level, lookup is already in the goal's level. -/
theorem fundamentalVarAtUniformVector {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    IsFundamentalConclusionAtUniformVector context (variableCell index) (context.lookup index) := by
  intro _targetScope substitution predLevel env
  rw [← positiveUniformLevels_eq (predLevel + 1) index]
  exact ReducibleEnvVec.lookupReducible env index

/-- **Export a matching-vector theorem to the all-level environment.**  An all-level environment supplies the
uniform positive vector by reading every tail variable at `predLevel + 1`. -/
theorem fundamentalConclusionAtAllOfUniformVector {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental : IsFundamentalConclusionAtUniformVector context subject classifier) :
    FundamentalConclusionAtAll context subject classifier := by
  intro _targetScope substitution env predLevel
  exact subjectFundamental substitution predLevel (fun index => by
    rw [positiveUniformLevels_eq (predLevel + 1) index]
    exact env predLevel index)

/-- **Non-dependent pi-introduction over the all-level environment, from a matching-vector body premise.**
The body is checked under the binder-local vector whose fresh head and every tail variable are at the
conclusion level `predLevel + 1`.  This is the precise simple-arrow case: the codomain is
`RawTerm.weaken codomainCodeBase`, so the fixed base-codomain candidate is recovered by weakening
cancellation and determinism in `fundamentalPiIntroNonDependentAtAll`. -/
theorem fundamentalPiIntroNonDependentAtAllFromUniformVectorPremise {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode codomainCodeBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtAll context codomainCodeBase (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      IsFundamentalConclusionAtUniformVector (context.cons domainCode) body
        (RawTerm.weaken codomainCodeBase)) :
    FundamentalConclusionAtAll context (lamCell body)
      (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)) :=
  fundamentalPiIntroNonDependentAtAll domainFundamental codomainFundamental
    (fun _targetScope substitution env predLevel {domainCandidate codomainCandidate}
        domainReducible codomainReducible argument argumentInDomain => by
      let tailEnv : ReducibleEnvVec (positiveUniformLevels scope (predLevel + 1))
          context substitution := fun index => by
        rw [positiveUniformLevels_eq (predLevel + 1) index]
        exact env predLevel index
      have bodyMember := bodyFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons tailEnv
          ⟨domainCandidate, domainReducible, argumentInDomain⟩)
      rw [RawTerm.weaken_eq_rename] at bodyMember
      rw [RawTerm.weaken_subst_cons] at bodyMember
      rw [RawTerm.subst_cons_eq_subst0_lift _ argument substitution] at bodyMember
      obtain ⟨witnessCandidate, witnessReducible, witnessMember⟩ := bodyMember
      exact (ReducibleTypeAt.deterministic witnessReducible codomainReducible _).mp witnessMember)

end FX1Poly.Typed

import FX1Poly.Typed.FundamentalAtAllLeafArms

/-! # FX1Poly/Typed/FundamentalAtAllCanonicalCandidate
    — canonical per-level candidates extracted from the all-level dependent fundamental conclusion

The all-positive argument layer is intentionally strong: it asks a type to denote
`IsReducibleMemberAtAllPositiveLevels` as its candidate.  That is not available for arbitrary universe
members in the current stratified model.  What IS always available from a type fundamental theorem result
`T : Type@u` is the canonical candidate at each concrete fuel level:

  `IsReducibleMemberAt level T`.

This file packages that weaker, unconditional candidate companion.  It is the level-indexed/vector-side
fact a proof-relevant inner recursion can consume without assuming global level-irrelevance or an
all-positive universe candidate.

## Zero-axiom verification

The proof runs the all-level member conclusion one universe rung up, decodes it with `tarskiDecode`, and
transports the resulting reducible type to its canonical member predicate via
`ReducibleTypeAt.reducibleMemberCandidate`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Canonical per-level candidate under all-level substitutions.**  After any closing substitution whose
context variables are reducible at every positive fuel level, `typeCode` denotes its own concrete-level member
predicate at every fuel level. -/
def HasCanonicalReducibleCandidateUnderAllLevelSubstitution {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevels context substitution) (level : Nat),
    ReducibleTypeAt level (RawTerm.subst substitution typeCode)
      (IsReducibleMemberAt level (RawTerm.subst substitution typeCode))

/-- **Positive-fuel canonical candidate under all-level substitutions.**  The same companion restricted to
positive levels, matching the shape most binder rules consume after `tarskiDecode`. -/
def HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
    ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeCode)
      (IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution typeCode))

/-- Full per-level canonical candidates imply the positive-fuel companion. -/
theorem HasCanonicalReducibleCandidateUnderAllLevelSubstitution.atPositiveLevels
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope}
    (hasCanonicalCandidate :
      HasCanonicalReducibleCandidateUnderAllLevelSubstitution context typeCode) :
    HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution context typeCode := by
  intro _targetScope substitution env predLevel
  exact hasCanonicalCandidate substitution env (predLevel + 1)

/-- **Type-in-universe fundamental conclusions yield canonical candidates.**  If the all-level fundamental
conclusion proves `typeCode : Type@levelExpr`, then at every substituted fuel level the substituted type code
denotes the concrete member predicate `IsReducibleMemberAt level`. -/
theorem FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateUnderSubstitution
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeFundamental :
      FundamentalConclusionAtAll context typeCode (universeCodeCell levelExpr flag)) :
    HasCanonicalReducibleCandidateUnderAllLevelSubstitution context typeCode := by
  intro _targetScope substitution env level
  have typeMember := typeFundamental substitution env level
  rw [subst_universeCodeCell] at typeMember
  obtain ⟨_candidate, typeReducible⟩ := typeMember.tarskiDecode
  exact ReducibleTypeAt.reducibleMemberCandidate typeReducible

/-- Positive-fuel form of
`FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateUnderSubstitution`. -/
theorem FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateAtPositiveLevels
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeFundamental :
      FundamentalConclusionAtAll context typeCode (universeCodeCell levelExpr flag)) :
    HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution context typeCode :=
  HasCanonicalReducibleCandidateUnderAllLevelSubstitution.atPositiveLevels
    (typeFundamental.typeInUniverse_hasCanonicalReducibleCandidateUnderSubstitution)

end FX1Poly.Typed

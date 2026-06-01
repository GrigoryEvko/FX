import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates

/-! # FX1Poly/Typed/FundamentalWithPositiveTypeCandidates
    -- fundamental-theorem arm bodies over the proof-relevant positive-candidate environment

The ordinary all-level conclusion `FundamentalConclusionAtAll` is the external semantic statement used by
the dependent fundamental theorem.  Binder recursion needs a stronger environment while proving that
statement: besides ordinary all-level reducibility for context variables, the environment must carry the
positive-fuel all-positive candidate companion for each looked-up binding type.  That companion is what lets
a one-level domain argument become an all-positive argument before extending the environment under a binder.

This file introduces the corresponding proof-relevant conclusion shape and validates the core arm bodies
over it.  The non-binder arms are the same semantic rules as the ordinary all-level development, read through
the environment projection.  The lambda arm is the important bridge: it uses the domain's positive-candidate
companion to construct the strengthened cons environment consumed by the codomain and body recursive
premises.

No theorem here claims final unconditional normalization by itself.  It is a motive/arm layer for the
dependent fundamental theorem assembly.

## Zero-axiom verification

The proofs compose already-gated arm bodies, `tarskiDecode`, `subst_universeCodeCell`,
`RawTerm.subst_cons_eq_subst0_lift`, and
`ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.consFromPositiveTypeCandidate`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The dependent fundamental theorem's conclusion over the strengthened environment.**  A subject is a
reducible member of its substituted classifier at every positive semantic fuel, but only for substitutions
whose environment also carries positive-fuel candidate companions for looked-up binding types. -/
def FundamentalConclusionWithPositiveTypeCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- Read an ordinary all-level fundamental result through the strengthened environment projection. -/
theorem FundamentalConclusionAtAll.toPositiveTypeCandidateEnv
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental : FundamentalConclusionAtAll context subject classifier) :
    FundamentalConclusionWithPositiveTypeCandidates context subject classifier := by
  intro _targetScope substitution envWithCandidates predLevel
  exact subjectFundamental substitution envWithCandidates.toAllLevels predLevel

/-- **The `var` arm over the strengthened environment.** -/
theorem fundamentalVarWithPositiveTypeCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionWithPositiveTypeCandidates context (variableCell index) (context.lookup index) :=
  FundamentalConclusionAtAll.toPositiveTypeCandidateEnv (fundamentalVarAtAll context index)

/-- **The `universeFormation` arm over the strengthened environment.** -/
theorem fundamentalUniverseFormationWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    FundamentalConclusionWithPositiveTypeCandidates context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) :=
  FundamentalConclusionAtAll.toPositiveTypeCandidateEnv
    (fundamentalUniverseFormationAtAll context levelExpr flag)

/-- **The `conv` arm over the strengthened environment.**  The reclassifier premise is run one fuel level
up, decoded to a reducible target type at the conclusion fuel, and the subject member is transported across
the substituted conversion. -/
theorem fundamentalConvWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context reclassifier
        (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalConclusionWithPositiveTypeCandidates context subject reclassifier := by
  intro _targetScope substitution envWithCandidates predLevel
  have reclassifierMember := reclassifierFundamental substitution envWithCandidates (predLevel + 1)
  rw [subst_universeCodeCell] at reclassifierMember
  obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
  exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
    (subjectFundamental substitution envWithCandidates predLevel) reclassifierReducible converts

/-- **The `piElim`/application arm over the strengthened environment.** -/
theorem fundamentalPiElimWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (functionFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context argument domainCode) :
    FundamentalConclusionWithPositiveTypeCandidates context
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope substitution envWithCandidates predLevel
  exact IsReducibleMemberAt.applicationUnderSubst substitution
    (functionFundamental substitution envWithCandidates predLevel)
    (argumentFundamental substitution envWithCandidates predLevel)

/-- **Dependent lambda introduction over the strengthened environment.**  The domain premise supplies the
ordinary decoded domain candidate at the conclusion fuel.  The domain's positive-fuel candidate companion
then upgrades every argument accepted by that decoded candidate into all-positive membership, allowing the
strengthened environment to extend under the binder.  The codomain and body recursive premises are consumed
under that strengthened cons environment. -/
theorem fundamentalPiIntroWithPositiveTypeCandidatesFromPositiveDomainCandidate
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionWithPositiveTypeCandidates (context.cons domainCode) body codomainCode) :
    FundamentalConclusionWithPositiveTypeCandidates context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envWithCandidates predLevel
  have domainMember := domainFundamental substitution envWithCandidates (predLevel + 1)
  rw [subst_universeCodeCell] at domainMember
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible
    (fun _argument argumentInDomain =>
      domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
    ?codomainExists ?bodyReducible
  · intro argument argumentInDomain
    have argumentAtAllPositiveLevels :
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution domainCode) argument :=
      HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
        (domainHasPositiveCandidateUnderSubstitution substitution
          envWithCandidates.toAllLevels predLevel)
        domainReducible argumentInDomain
    have extendedEnvWithCandidates :
        ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons domainCode)
          (RawTermSubst.cons argument substitution) :=
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.consFromPositiveTypeCandidate
        envWithCandidates argumentAtAllPositiveLevels domainHasPositiveCandidateUnderSubstitution
    have codomainMember :=
      codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithCandidates (predLevel + 1)
    rw [subst_universeCodeCell] at codomainMember
    have codomainReducibleType := codomainMember.tarskiDecode
    rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainReducibleType
  · intro argument argumentInDomain
    have argumentAtAllPositiveLevels :
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution domainCode) argument :=
      HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
        (domainHasPositiveCandidateUnderSubstitution substitution
          envWithCandidates.toAllLevels predLevel)
        domainReducible argumentInDomain
    have extendedEnvWithCandidates :
        ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons domainCode)
          (RawTermSubst.cons argument substitution) :=
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.consFromPositiveTypeCandidate
        envWithCandidates argumentAtAllPositiveLevels domainHasPositiveCandidateUnderSubstitution
    rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
      ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
    exact bodyFundamental (RawTermSubst.cons argument substitution)
      extendedEnvWithCandidates predLevel

end FX1Poly.Typed

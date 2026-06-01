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
open StepStar

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

/-- **The positive-candidate type half over the strengthened environment.**  A type code has, under every
strengthened closing substitution and every positive semantic fuel, the all-positive member predicate as a
reducible candidate.  This is the proof-relevant companion the lambda and former binder arms consume for
domain types. -/
def PositiveCandidateConclusionWithPositiveTypeCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat),
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution typeCode)

/-- **A positive-candidate conclusion strengthens membership in any decoded candidate to all-positive
membership.**  This is the binder-local projection consumed when a decoded domain candidate accepts an
argument: the positive-candidate type half identifies that level's candidate with
`IsReducibleMemberAtAllPositiveLevels`, and determinism transports the argument into the all-positive
predicate. -/
theorem PositiveCandidateConclusionWithPositiveTypeCandidates.memberExtendsToAllPositive
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context typeCode)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
    (typeReducible :
      ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeCode) candidate)
    {argument : RawTerm (targetScope + 1)} (argumentInCandidate : candidate argument) :
    IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution typeCode) argument :=
  HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
    (typeHasPositiveCandidate substitution envWithCandidates predLevel)
    typeReducible argumentInCandidate

/-- **Extend a strengthened environment from a positive-candidate conclusion and one decoded argument.**
The caller supplies an argument in the decoded candidate for the binder domain at the current positive fuel;
`memberExtendsToAllPositive` upgrades it to all-positive membership, and the same positive-candidate
conclusion supplies variable zero's type-candidate companion after consing. -/
theorem PositiveCandidateConclusionWithPositiveTypeCandidates.consEnv
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context typeCode)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
    (typeReducible :
      ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeCode) candidate)
    {argument : RawTerm (targetScope + 1)} (argumentInCandidate : candidate argument) :
    ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons typeCode)
      (RawTermSubst.cons argument substitution) :=
  ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons envWithCandidates
    (typeHasPositiveCandidate.memberExtendsToAllPositive substitution envWithCandidates
      predLevel typeReducible argumentInCandidate)
    (fun headPredLevel =>
      typeHasPositiveCandidate substitution envWithCandidates headPredLevel)

/-- **A strengthened fundamental result for `typeCode : Type@levelExpr` yields the type half at every fuel.**
Running the strengthened member conclusion at every positive universe-membership fuel and decoding Tarski
membership gives both strong normalization and reducibility of the substituted type code at every semantic
fuel.  This is the strengthened-environment counterpart of
`FundamentalConclusionAtAll.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility`. -/
theorem FundamentalConclusionWithPositiveTypeCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context typeCode
        (universeCodeCell levelExpr flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution),
      IsStronglyNormalizing (RawTerm.subst substitution typeCode) ∧
        IsReducibleTypeAtAllLevels (RawTerm.subst substitution typeCode) := by
  intro _targetScope substitution envWithCandidates
  have typeMemberAtAllPositive :
      IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag)
        (RawTerm.subst substitution typeCode) := by
    intro level
    have typeMember := typeFundamental substitution envWithCandidates level
    rwa [subst_universeCodeCell] at typeMember
  exact (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := levelExpr) (flag := flag)).mp typeMemberAtAllPositive

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

/-- **The positive-candidate universe-code type half over the strengthened environment, conditional on
the exact lower-type extension obligation.**  Universe codes are the only place where the positive-candidate
type half cannot be discharged structurally: at fuel `predLevel + 1`, the universe candidate is the lower
reducibility relation at `predLevel`, so turning it into the all-positive member predicate requires that
lower reducible types extend to all positive levels.  This theorem packages that obligation in the
strengthened-environment shape consumed by the dependent fundamental theorem assembly. -/
theorem positiveCandidateUniverseCodeWithPositiveTypeCandidatesOfLowerTypeExtendsToAllLevels
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
        (predLevel : Nat) (typeCode : RawTerm (targetScope + 1)),
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    PositiveCandidateConclusionWithPositiveTypeCandidates context (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_universeCodeCell]
  exact HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels
    levelExpr flag
    (fun typeCode typeCodeNormalizing typeCodeReducibleAtLowerLevel =>
      lowerTypeExtendsToAllLevels substitution envWithCandidates predLevel typeCode
        typeCodeNormalizing typeCodeReducibleAtLowerLevel)

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

/-- **The positive-candidate `var` type half over the strengthened environment.**  The environment carries
exactly the companion required for each looked-up binding type. -/
theorem positiveCandidateVarWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    PositiveCandidateConclusionWithPositiveTypeCandidates context (context.lookup index) := by
  intro _targetScope substitution envWithCandidates predLevel
  exact envWithCandidates.lookupPositiveCandidate index predLevel

/-- **The positive-candidate Sigma type half over the strengthened environment.**  Sigma codes are neutral
non-Pi type codes in this stratified reducibility semantics, so they denote the all-positive candidate at
every positive fuel without recursive child candidate premises. -/
theorem positiveCandidateSigmaTypeWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    PositiveCandidateConclusionWithPositiveTypeCandidates context
      (sigmaTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution _envWithCandidates predLevel
  exact HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst
    (level := predLevel + 1) substitution domainCode codomainCode

/-- **The positive-candidate dependent Pi type half over the strengthened environment.**  The domain
candidate companion upgrades any accepted argument to all-positive membership; the strengthened environment
then extends through the binder, allowing the codomain candidate companion to run under the cons
substitution. -/
theorem positiveCandidatePiTypeWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context domainCode)
    (codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates (context.cons domainCode) codomainCode) :
    PositiveCandidateConclusionWithPositiveTypeCandidates context
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_piTyCodeCell]
  exact HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel
    (fun candidatePredLevel =>
      domainHasPositiveCandidate substitution envWithCandidates candidatePredLevel)
    (fun candidatePredLevel argument argumentAtAllPositiveLevels => by
      have extendedEnvWithCandidates :
          ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons domainCode)
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons envWithCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithCandidates headPredLevel)
      have codomainCandidate :=
        codomainHasPositiveCandidate (RawTermSubst.cons argument substitution)
          extendedEnvWithCandidates candidatePredLevel
      rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainCandidate)

/-- **Dispatch-level former children over the strengthened environment.**  The domain child is read from
the strengthened member half at the two adjacent levels consumed by Pi/Sigma formation.  For the codomain
child at the one-higher domain level, the positive-candidate type half upgrades the argument to all-positive
domain membership, extends the strengthened environment through the binder, and runs the codomain recursive
premise.  The base-level codomain child remains explicit, because fuel `0` domain membership cannot in
general be promoted to all-positive membership. -/
theorem formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
      (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel := by
  intro _targetScope substitution envWithCandidates predLevel
  refine ⟨?domainAtLevel, ?domainAboveAndCodomain⟩
  · have domainMember := domainFundamental substitution envWithCandidates predLevel
    rwa [subst_universeCodeCell] at domainMember
  · refine ⟨?domainAtNextLevel, ?codomainAtDomainLevel, ?codomainAtNextDomainLevel⟩
    · have domainMemberAbove := domainFundamental substitution envWithCandidates (predLevel + 1)
      rwa [subst_universeCodeCell] at domainMemberAbove
    · intro argument argumentMember
      exact codomainMemberAtDomainLevel substitution envWithCandidates predLevel
        argument argumentMember
    · intro argument argumentMember
      obtain ⟨domainCandidate, domainReducible, argumentInDomain⟩ := argumentMember
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidate substitution envWithCandidates predLevel)
          domainReducible argumentInDomain
      have extendedEnvWithCandidates :
          ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons domainCode)
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons envWithCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithCandidates headPredLevel)
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithCandidates predLevel

/-- **Pi-formation over the strengthened environment from the factored dispatch-level child premises.** -/
theorem fundamentalPiFormationWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithPositiveTypeCandidates context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
    domainFundamental domainHasPositiveCandidate codomainMemberAtDomainLevel codomainFundamental
    substitution envWithCandidates predLevel).toPiMember

/-- **Sigma-formation over the strengthened environment from the factored dispatch-level child premises.** -/
theorem fundamentalSigmaFormationWithPositiveTypeCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithPositiveTypeCandidates context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
    domainFundamental domainHasPositiveCandidate codomainMemberAtDomainLevel codomainFundamental
    substitution envWithCandidates predLevel).toSigmaMember

/-- **The base-level codomain premise for a universe-code domain over the strengthened environment.**
Fuel zero is impossible for universe-domain membership.  At successor fuel, the universe-domain positive
candidate companion upgrades the argument to all-positive membership, extends the strengthened environment,
and runs the codomain recursive premise at the required successor level. -/
theorem codomainMemberAtDomainLevelWithPositiveTypeCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
      (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt predLevel
        (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode) := by
  intro _targetScope substitution envWithCandidates predLevel argument argumentMember
  cases predLevel with
  | zero =>
      rw [subst_universeCodeCell] at argumentMember
      exact False.elim
        (IsReducibleMemberAt.universeCodeHasNoMemberAtZero domainLevel flag argument
          argumentMember)
  | succ memberPredLevel =>
      obtain ⟨domainCandidate, domainReducible, argumentInDomain⟩ := argumentMember
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidate substitution envWithCandidates memberPredLevel)
          domainReducible argumentInDomain
      have extendedEnvWithCandidates :
          ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
            (context.cons (universeCodeCell domainLevel flag))
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons envWithCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithCandidates headPredLevel)
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithCandidates (memberPredLevel + 1)

/-- **Dispatch-level former children for a universe-code domain over the strengthened environment.**  This
specializes `formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates` by deriving the explicit
base-level codomain premise from the empty fuel-zero universe semantics and the positive-fuel domain
candidate companion. -/
theorem formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
      (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution
        (universeCodeCell domainLevel flag) codomainCode domainLevel.lsucc codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
    domainFundamental domainHasPositiveCandidate
    (codomainMemberAtDomainLevelWithPositiveTypeCandidatesFromUniverseDomain
      domainHasPositiveCandidate codomainFundamental)
    codomainFundamental

/-- **Pi-formation for a universe-code domain over the strengthened environment.** -/
theorem fundamentalPiFormationWithPositiveTypeCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithPositiveTypeCandidates context
      (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate codomainFundamental
    substitution envWithCandidates predLevel).toPiMember

/-- **Sigma-formation for a universe-code domain over the strengthened environment.** -/
theorem fundamentalSigmaFormationWithPositiveTypeCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithPositiveTypeCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithPositiveTypeCandidates context
      (sigmaTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate codomainFundamental
    substitution envWithCandidates predLevel).toSigmaMember

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

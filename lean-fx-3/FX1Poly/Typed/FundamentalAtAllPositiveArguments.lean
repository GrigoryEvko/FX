import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro
import FX1Poly.Core.StratifiedReducibleMemberNeutral
import FX1Poly.Core.StratifiedReducibleUniverseDecode

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
open StepStar

/-- **All-positive semantic membership.**  A term is a reducible member of a type at every positive
stratification level.  This is the argument strength an all-level dependent binder needs in order to run
ordinary all-level recursive hypotheses under `context.cons domainCode`. -/
def IsReducibleMemberAtAllPositiveLevels {scope : Nat}
    (typeCode term : RawTerm scope) : Prop :=
  ∀ level : Nat, IsReducibleMemberAt (level + 1) typeCode term

/-- A type code is reducible at every stratification fuel level.  This is the type-level counterpart of
`IsReducibleMemberAtAllPositiveLevels`, used to state exactly what all-positive membership in a universe
means. -/
def IsReducibleTypeAtAllLevels {scope : Nat} (typeCode : RawTerm scope) : Prop :=
  ∀ level : Nat, IsReducibleTypeAt level typeCode

/-- Read an all-positive member at one concrete positive level. -/
theorem IsReducibleMemberAtAllPositiveLevels.atLevel {scope : Nat}
    {typeCode term : RawTerm scope}
    (memberAtAllPositiveLevels : IsReducibleMemberAtAllPositiveLevels typeCode term)
    (level : Nat) :
    IsReducibleMemberAt (level + 1) typeCode term :=
  memberAtAllPositiveLevels level

/-- **All-positive membership in a universe.**  A term is an all-positive member of a universe code exactly
when it is strongly normalizing and reducible as a type at every fuel level.  This theorem states the hard
dependent-Type obligation precisely: ordinary Tarski membership at one positive level decodes to one lower
type-reducibility level, while all-positive universe membership requires those decodings uniformly at every
level. -/
theorem IsReducibleMemberAtAllPositiveLevels.universeCode_iff {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope} :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode ↔
      IsStronglyNormalizing typeCode ∧ IsReducibleTypeAtAllLevels typeCode := by
  constructor
  · intro memberAtAllPositiveLevels
    have memberAtFirstLevel :
        IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt 0 typeCode :=
      (IsReducibleMemberAt.universeMembership_iff (predLevel := 0)
        (levelExpr := levelExpr) (flag := flag)).mp (memberAtAllPositiveLevels 0)
    exact ⟨memberAtFirstLevel.1, fun level =>
      ((IsReducibleMemberAt.universeMembership_iff (predLevel := level)
        (levelExpr := levelExpr) (flag := flag)).mp (memberAtAllPositiveLevels level)).2⟩
  · intro normalizingAndReducibleAtAllLevels
    intro level
    exact (IsReducibleMemberAt.universeMembership_iff (predLevel := level)
      (levelExpr := levelExpr) (flag := flag)).mpr
      ⟨normalizingAndReducibleAtAllLevels.1, normalizingAndReducibleAtAllLevels.2 level⟩

/-- **A fundamental theorem result for `typeCode : Type@levelExpr` yields the type half at every fuel.**
This is the reusable extraction from the all-level member theorem: running the fundamental result at every
positive membership level and decoding universe membership gives strong normalization of the substituted
type code plus `IsReducibleTypeAtAllLevels`.  It is deliberately only the type-half fact, not the stronger
all-positive candidate witness needed by dependent binders. -/
theorem FundamentalConclusionAtAll.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeFundamental :
      FundamentalConclusionAtAll context typeCode (universeCodeCell levelExpr flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution),
      IsStronglyNormalizing (RawTerm.subst substitution typeCode) ∧
        IsReducibleTypeAtAllLevels (RawTerm.subst substitution typeCode) := by
  intro _targetScope substitution env
  have typeMemberAtAllPositive :
      IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag)
        (RawTerm.subst substitution typeCode) := by
    intro level
    have typeMember := typeFundamental substitution env level
    rwa [subst_universeCodeCell] at typeMember
  exact (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := levelExpr) (flag := flag)).mp typeMemberAtAllPositive

/-- **A type whose level candidate is the all-positive member predicate.**  This is the candidate-level
semantic hook the dependent binder needs: determinism then turns membership in any decoded candidate for the
same type/level into all-positive membership. -/
def HasAllPositiveReducibleCandidateAt {scope : Nat} (level : Nat) (typeCode : RawTerm scope) : Prop :=
  ReducibleTypeAt level typeCode (IsReducibleMemberAtAllPositiveLevels typeCode)

/-- **All-positive candidate under every all-level reducible substitution.**  This is the type-companion
shape needed by the dependent fundamental theorem: after any closing substitution whose context variables
are reducible at all positive levels, the substituted type code denotes the all-positive member predicate at
every fuel level. -/
def HasAllPositiveReducibleCandidateUnderAllLevelSubstitution {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevels context substitution) (level : Nat),
    HasAllPositiveReducibleCandidateAt level (RawTerm.subst substitution typeCode)

/-- **All-positive candidate at every positive fuel under every all-level reducible substitution.**  This
is the universe-compatible type-companion shape: universe codes cannot denote the all-positive candidate at
fuel `0` (the lower relation is empty there), but binder and formation dispatch premises consume positive
fuel levels. -/
def HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
    HasAllPositiveReducibleCandidateAt (predLevel + 1) (RawTerm.subst substitution typeCode)

/-- If a type denotes the all-positive member predicate at a level, any other candidate for that same
type/level contains only all-positive members. -/
theorem HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive {scope : Nat}
    {level : Nat} {typeCode term : RawTerm scope} {candidate : RawTerm scope → Prop}
    (hasAllPositiveCandidate : HasAllPositiveReducibleCandidateAt level typeCode)
    (candidateReducible : ReducibleTypeAt level typeCode candidate)
    (candidateMember : candidate term) :
    IsReducibleMemberAtAllPositiveLevels typeCode term :=
  (ReducibleTypeAt.deterministic candidateReducible hasAllPositiveCandidate term).mp candidateMember

/-- **Neutral classifiers have the all-positive member predicate as a reducible candidate.**  For a
weak-head-normal classifier that is neither Π-rooted nor universe-rooted, stratified membership is exactly
strong normalization at every level.  Therefore the candidate `IsStronglyNormalizing` is pointwise equivalent
to `IsReducibleMemberAtAllPositiveLevels classifier`, and the `ofPointwiseIff` congruence arm turns the
neutral reducible-type witness into the all-positive candidate witness.

This is the first concrete discharge of `HasAllPositiveReducibleCandidateAt`: it covers neutral object-level
domains (variables, stuck eliminators, and future neutral data classifiers).  It deliberately does not cover
universe domains; those are the hard dependent-type case because a universe member at one fuel level only
contains a type reducible one level down. -/
theorem HasAllPositiveReducibleCandidateAt.ofNeutralClassifier {scope : Nat}
    {level : Nat} {typeCode : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    HasAllPositiveReducibleCandidateAt level typeCode := by
  have pointwise :
      PointwiseIff IsStronglyNormalizing (IsReducibleMemberAtAllPositiveLevels typeCode) := by
    intro term
    constructor
    · intro termNormalizing positiveLevel
      exact (IsReducibleMemberAt.atNeutralClassifier (level := positiveLevel + 1)
        weakHeadNormal notPiType notUniverse).mpr termNormalizing
    · intro termMemberAtAllPositiveLevels
      exact (IsReducibleMemberAt.atNeutralClassifier (level := 1)
        weakHeadNormal notPiType notUniverse).mp (termMemberAtAllPositiveLevels 0)
  cases level with
  | zero =>
      exact ReducibleTypeStep.ofPointwiseIff
        (ReducibleTypeStep.neutral weakHeadNormal notPiType notUniverse) pointwise
  | succ predLevel =>
      exact ReducibleTypeStep.ofPointwiseIff
        (ReducibleTypeStep.neutral weakHeadNormal notPiType notUniverse) pointwise

/-- **Neutral-classifier members extend to all positive levels.**  The membership-level form of
`HasAllPositiveReducibleCandidateAt.ofNeutralClassifier`: at a neutral non-Π non-universe classifier,
membership at any level is equivalent to strong normalization, and strong normalization re-injects as
membership at every positive level. -/
theorem IsReducibleMemberAt.extendsToAllPositiveAtNeutralClassifier {scope : Nat}
    {memberLevel : Nat} {typeCode term : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (member : IsReducibleMemberAt memberLevel typeCode term) :
    IsReducibleMemberAtAllPositiveLevels typeCode term := by
  have termNormalizing :
      IsStronglyNormalizing term :=
    (IsReducibleMemberAt.atNeutralClassifier (level := memberLevel)
      weakHeadNormal notPiType notUniverse).mp member
  intro positiveLevel
  exact (IsReducibleMemberAt.atNeutralClassifier (level := positiveLevel + 1)
    weakHeadNormal notPiType notUniverse).mpr termNormalizing

/-- **Π types preserve the all-positive candidate discipline.**  If the domain has the all-positive
member-predicate as a reducible candidate at every level, and every instantiated codomain has the same
property for every all-positive argument, then the dependent Π-code also has the all-positive
member-predicate as a reducible candidate.

This is the positive recursive clause for the proof-relevant/Kripke argument relation: a function is an
all-positive member of `Π domainCode. codomainCode` exactly when it maps all-positive domain arguments to
all-positive codomain members.  The forward direction constructs the Π candidate at each positive level; the
reverse direction inverts the Π candidate at that level and uses determinism to align the per-level domain
and codomain candidates with their all-positive canonical candidates. -/
theorem HasAllPositiveReducibleCandidateAt.piType {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasAllPositiveCandidate :
      ∀ level : Nat, HasAllPositiveReducibleCandidateAt level domainCode)
    (codomainHasAllPositiveCandidate :
      ∀ (level : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          HasAllPositiveReducibleCandidateAt level (RawTerm.subst0 codomainCode argument)) :
    HasAllPositiveReducibleCandidateAt level (piTyCodeCell domainCode codomainCode) := by
  let allPositiveArrowCandidate : RawTerm scope → Prop :=
    fun functionTerm =>
      ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument)
            (appCell functionTerm argument)
  have piReducibleAtLevel :
      ReducibleTypeAt level (piTyCodeCell domainCode codomainCode) allPositiveArrowCandidate := by
    cases level with
    | zero =>
        exact ReducibleTypeStep.piType
          (codomainCandidate :=
            fun argument =>
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument))
          (domainHasAllPositiveCandidate 0)
          (fun argument argumentAtAllPositiveLevels =>
            codomainHasAllPositiveCandidate 0 argument argumentAtAllPositiveLevels)
    | succ predLevel =>
        exact ReducibleTypeStep.piType
          (codomainCandidate :=
            fun argument =>
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument))
          (domainHasAllPositiveCandidate (predLevel + 1))
          (fun argument argumentAtAllPositiveLevels =>
            codomainHasAllPositiveCandidate (predLevel + 1) argument argumentAtAllPositiveLevels)
  have pointwise :
      PointwiseIff allPositiveArrowCandidate
        (IsReducibleMemberAtAllPositiveLevels (piTyCodeCell domainCode codomainCode)) := by
    intro functionTerm
    constructor
    · intro functionMapsAllPositive positiveLevel
      have piReducibleAtPositiveLevel :
          ReducibleTypeAt (positiveLevel + 1) (piTyCodeCell domainCode codomainCode)
            allPositiveArrowCandidate := by
        exact ReducibleTypeStep.piType
          (codomainCandidate :=
            fun argument =>
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument))
          (domainHasAllPositiveCandidate (positiveLevel + 1))
          (fun argument argumentAtAllPositiveLevels =>
            codomainHasAllPositiveCandidate (positiveLevel + 1) argument argumentAtAllPositiveLevels)
      exact ⟨allPositiveArrowCandidate, piReducibleAtPositiveLevel, functionMapsAllPositive⟩
    · intro functionMemberAtAllPositiveLevels argument argumentAtAllPositiveLevels positiveLevel
      obtain ⟨piCandidate, piReducible, functionInPiCandidate⟩ :=
        functionMemberAtAllPositiveLevels positiveLevel
      obtain ⟨domainCandidateAtLevel, codomainCandidateAtLevel, domainReducibleAtLevel,
        codomainReducibleAtLevel, piCandidateEquivalence⟩ := piReducible.piTypeInversion
      have argumentInDomainCandidate : domainCandidateAtLevel argument :=
        (ReducibleTypeAt.deterministic
          (domainHasAllPositiveCandidate (positiveLevel + 1)) domainReducibleAtLevel argument).mp
          argumentAtAllPositiveLevels
      have functionMapsDomainCandidate :=
        (piCandidateEquivalence functionTerm).mp functionInPiCandidate
      have applicationInCodomainCandidate :
          codomainCandidateAtLevel argument (appCell functionTerm argument) :=
        functionMapsDomainCandidate argument argumentInDomainCandidate
      have applicationAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument)
            (appCell functionTerm argument) :=
        (ReducibleTypeAt.deterministic
          (codomainReducibleAtLevel argument argumentInDomainCandidate)
          (codomainHasAllPositiveCandidate (positiveLevel + 1) argument argumentAtAllPositiveLevels)
          (appCell functionTerm argument)).mp applicationInCodomainCandidate
      exact applicationAtAllPositiveLevels positiveLevel
  cases level with
  | zero => exact ReducibleTypeStep.ofPointwiseIff piReducibleAtLevel pointwise
  | succ predLevel => exact ReducibleTypeStep.ofPointwiseIff piReducibleAtLevel pointwise

/-- **Π types preserve the all-positive candidate discipline at positive fuel levels.**  This avoids the
universe-code level-0 obstruction: to build the Π candidate at `predLevel+1`, and to interpret its
all-positive member predicate, only positive-level domain/codomain all-positive candidate witnesses are
needed. -/
theorem HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel {scope : Nat} {predLevel : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasAllPositiveCandidate :
      ∀ predLevel : Nat, HasAllPositiveReducibleCandidateAt (predLevel + 1) domainCode)
    (codomainHasAllPositiveCandidate :
      ∀ (predLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          HasAllPositiveReducibleCandidateAt (predLevel + 1)
            (RawTerm.subst0 codomainCode argument)) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1) (piTyCodeCell domainCode codomainCode) := by
  let allPositiveArrowCandidate : RawTerm scope → Prop :=
    fun functionTerm =>
      ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument)
            (appCell functionTerm argument)
  have piReducibleAtLevel :
      ReducibleTypeAt (predLevel + 1) (piTyCodeCell domainCode codomainCode)
        allPositiveArrowCandidate :=
    ReducibleTypeStep.piType
      (codomainCandidate :=
        fun argument =>
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument))
      (domainHasAllPositiveCandidate predLevel)
      (fun argument argumentAtAllPositiveLevels =>
        codomainHasAllPositiveCandidate predLevel argument argumentAtAllPositiveLevels)
  have pointwise :
      PointwiseIff allPositiveArrowCandidate
        (IsReducibleMemberAtAllPositiveLevels (piTyCodeCell domainCode codomainCode)) := by
    intro functionTerm
    constructor
    · intro functionMapsAllPositive positiveLevel
      have piReducibleAtPositiveLevel :
          ReducibleTypeAt (positiveLevel + 1) (piTyCodeCell domainCode codomainCode)
            allPositiveArrowCandidate :=
        ReducibleTypeStep.piType
          (codomainCandidate :=
            fun argument =>
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument))
          (domainHasAllPositiveCandidate positiveLevel)
          (fun argument argumentAtAllPositiveLevels =>
            codomainHasAllPositiveCandidate positiveLevel argument argumentAtAllPositiveLevels)
      exact ⟨allPositiveArrowCandidate, piReducibleAtPositiveLevel, functionMapsAllPositive⟩
    · intro functionMemberAtAllPositiveLevels argument argumentAtAllPositiveLevels positiveLevel
      obtain ⟨piCandidate, piReducible, functionInPiCandidate⟩ :=
        functionMemberAtAllPositiveLevels positiveLevel
      obtain ⟨domainCandidateAtLevel, codomainCandidateAtLevel, domainReducibleAtLevel,
        codomainReducibleAtLevel, piCandidateEquivalence⟩ := piReducible.piTypeInversion
      have argumentInDomainCandidate : domainCandidateAtLevel argument :=
        (ReducibleTypeAt.deterministic
          (domainHasAllPositiveCandidate positiveLevel) domainReducibleAtLevel argument).mp
          argumentAtAllPositiveLevels
      have functionMapsDomainCandidate :=
        (piCandidateEquivalence functionTerm).mp functionInPiCandidate
      have applicationInCodomainCandidate :
          codomainCandidateAtLevel argument (appCell functionTerm argument) :=
        functionMapsDomainCandidate argument argumentInDomainCandidate
      have applicationAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument)
            (appCell functionTerm argument) :=
        (ReducibleTypeAt.deterministic
          (codomainReducibleAtLevel argument argumentInDomainCandidate)
          (codomainHasAllPositiveCandidate positiveLevel argument argumentAtAllPositiveLevels)
          (appCell functionTerm argument)).mp applicationInCodomainCandidate
      exact applicationAtAllPositiveLevels positiveLevel
  exact ReducibleTypeStep.ofPointwiseIff piReducibleAtLevel pointwise

/-- **Substituted Π types preserve the all-positive candidate discipline.**  This is the
under-substitution form consumed by a type companion for the fundamental theorem: after distributing the
closing substitution over the Π cell, `HasAllPositiveReducibleCandidateAt.piType` applies to the substituted
domain and lifted substituted codomain. -/
theorem HasAllPositiveReducibleCandidateAt.piTypeUnderSubst {sourceScope targetScope : Nat}
    {level : Nat} {domainCode : RawTerm sourceScope} {codomainCode : RawTerm (sourceScope + 1)}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainHasAllPositiveCandidate :
      ∀ level : Nat,
        HasAllPositiveReducibleCandidateAt level (RawTerm.subst substitution domainCode))
    (codomainHasAllPositiveCandidate :
      ∀ (level : Nat) (argument : RawTerm targetScope),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          HasAllPositiveReducibleCandidateAt level
            (RawTerm.subst0 (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) argument)) :
    HasAllPositiveReducibleCandidateAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) := by
  rw [subst_piTyCodeCell]
  exact HasAllPositiveReducibleCandidateAt.piType
    domainHasAllPositiveCandidate codomainHasAllPositiveCandidate

/-- **Substituted Π types preserve the all-positive candidate discipline at positive fuel levels.** -/
theorem HasAllPositiveReducibleCandidateAt.piTypeUnderSubstAtPositiveLevel
    {sourceScope targetScope : Nat} {predLevel : Nat}
    {domainCode : RawTerm sourceScope} {codomainCode : RawTerm (sourceScope + 1)}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainHasAllPositiveCandidate :
      ∀ predLevel : Nat,
        HasAllPositiveReducibleCandidateAt (predLevel + 1)
          (RawTerm.subst substitution domainCode))
    (codomainHasAllPositiveCandidate :
      ∀ (predLevel : Nat) (argument : RawTerm targetScope),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          HasAllPositiveReducibleCandidateAt (predLevel + 1)
            (RawTerm.subst0 (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) argument)) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) := by
  rw [subst_piTyCodeCell]
  exact HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel
    domainHasAllPositiveCandidate codomainHasAllPositiveCandidate

/-- **Σ type codes have the all-positive member predicate as their reducible candidate.**  In the current
stratified reducibility relation, only Π codes receive a dependent-arrow candidate; Σ codes are
weak-head-normal non-Π non-universe classifiers, hence they use the neutral strong-normalization candidate at
every level.  Therefore the neutral all-positive bridge applies directly. -/
theorem HasAllPositiveReducibleCandidateAt.sigmaType {scope : Nat} {level : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    HasAllPositiveReducibleCandidateAt level (sigmaTyCodeCell domainCode codomainCode) :=
  HasAllPositiveReducibleCandidateAt.ofNeutralClassifier
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **Substituted Σ type codes have the all-positive member predicate as their reducible candidate.**  The
substitution distributes over the Σ cell, and the resulting Σ code is still a neutral non-Π non-universe
classifier in the stratified reducibility relation. -/
theorem HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst {sourceScope targetScope : Nat}
    {level : Nat} (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    HasAllPositiveReducibleCandidateAt level
      (RawTerm.subst substitution (sigmaTyCodeCell domainCode codomainCode)) := by
  rw [subst_sigmaTyCodeCell]
  exact HasAllPositiveReducibleCandidateAt.sigmaType
    (RawTerm.subst substitution domainCode)
    (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode)

/-- **Π type codes preserve all-positive candidates under all-level substitutions.**  The domain companion
supplies all-positive candidates for the substituted domain at every fuel level; the codomain companion is
run under the cons-extended all-level environment built from an all-positive domain argument.  This packages
the binder-recursive type-companion step without choosing candidates. -/
theorem HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.piType
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context domainCode)
    (codomainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution
        (context.cons domainCode) codomainCode) :
    HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env level
  exact HasAllPositiveReducibleCandidateAt.piTypeUnderSubst substitution
    (fun candidateLevel =>
      domainHasAllPositiveCandidateUnderSubstitution substitution env candidateLevel)
    (fun candidateLevel argument argumentAtAllPositiveLevels => by
      have codomainHasCandidate :=
        codomainHasAllPositiveCandidateUnderSubstitution
          (RawTermSubst.cons argument substitution)
          (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels)
          candidateLevel
      rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainHasCandidate)

/-- **Σ type codes have all-positive candidates under all-level substitutions.**  In the stratified
candidate relation, Σ codes are neutral non-Π non-universe classifiers, so no recursive candidate
assumption is needed for the candidate itself; child reducibility is enforced separately by the former
membership theorem. -/
theorem HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.sigmaType
    {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context
      (sigmaTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution _env level
  exact HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst
    (level := level) substitution domainCode codomainCode

/-- **Π type codes preserve positive-fuel all-positive candidates under all-level substitutions.** -/
theorem HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.piType
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution
        (context.cons domainCode) codomainCode) :
    HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env predLevel
  exact HasAllPositiveReducibleCandidateAt.piTypeUnderSubstAtPositiveLevel substitution
    (fun candidatePredLevel =>
      domainHasAllPositiveCandidateUnderSubstitution substitution env candidatePredLevel)
    (fun candidatePredLevel argument argumentAtAllPositiveLevels => by
      have codomainHasCandidate :=
        codomainHasAllPositiveCandidateUnderSubstitution
          (RawTermSubst.cons argument substitution)
          (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels)
          candidatePredLevel
      rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainHasCandidate)

/-- **Σ type codes have positive-fuel all-positive candidates under all-level substitutions.** -/
theorem HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.sigmaType
    {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context
      (sigmaTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution _env predLevel
  exact HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst
    (level := predLevel + 1) substitution domainCode codomainCode

/-- **Conditional universe all-positive candidate.**  A universe code at positive fuel
`predLevel + 1` has the all-positive member predicate as its reducible candidate if every strongly
normalizing type reducible at the lower fuel `predLevel` is reducible at every fuel level.  This is the exact
remaining semantic obligation for dependent domains ranging over types: Tarski membership in a universe
decodes one level down, while an all-level binder needs the decoded type at every positive universe-member
level. -/
theorem HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels {scope : Nat}
    {predLevel : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ typeCode : RawTerm scope,
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (universeCodeCell levelExpr flag : RawTerm scope) := by
  have pointwise :
      PointwiseIff (universeReducibilityPredicate (ReducibleTypeAt predLevel))
        (IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag : RawTerm scope)) := by
    intro typeCode
    constructor
    · intro universeMemberAtLowerLevel
      exact (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
        (levelExpr := levelExpr) (flag := flag)).mpr
        ⟨universeMemberAtLowerLevel.1,
          lowerTypeExtendsToAllLevels typeCode
            universeMemberAtLowerLevel.1 universeMemberAtLowerLevel.2⟩
    · intro universeMemberAtAllPositiveLevels
      have normalizingAndReducibleAtAllLevels :=
        (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
          (levelExpr := levelExpr) (flag := flag)).mp universeMemberAtAllPositiveLevels
      exact ⟨normalizingAndReducibleAtAllLevels.1,
        normalizingAndReducibleAtAllLevels.2 predLevel⟩
  exact ReducibleTypeStep.ofPointwiseIff (ReducibleTypeStep.universeCode levelExpr flag) pointwise

/-- **Fuel-zero universe membership is empty.**  At reducibility fuel `0`, a universe code's candidate is
`universeReducibilityPredicate` over the empty lower relation, so no term can be a member of any universe
code at that fuel.  This is the ordinary-membership counterpart of
`HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero`: the obstruction is not only that successor
universes cannot denote the all-positive candidate at fuel `0`; even the raw universe-member predicate is
empty at fuel `0`.  Dependent formation proofs therefore must split the base level from positive levels
rather than attempting to strengthen fuel-`0` universe membership. -/
theorem IsReducibleMemberAt.universeCodeHasNoMemberAtZero {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) (memberCode : RawTerm scope) :
    ¬ IsReducibleMemberAt 0 (universeCodeCell levelExpr flag : RawTerm scope) memberCode := by
  intro memberAtZero
  obtain ⟨candidate, universeReducible, memberInCandidate⟩ := memberAtZero
  have candidateIsEmpty :
      PointwiseIff candidate
        (universeReducibilityPredicate
          (fun _typeCode _candidate => False : RawTerm scope → (RawTerm scope → Prop) → Prop)) :=
    ReducibleTypeStep.universeCodeInversion universeReducible
  have memberInEmptyUniversePredicate := (candidateIsEmpty memberCode).mp memberInCandidate
  obtain ⟨_stronglyNormalizing, lowerReducibleWitness⟩ := memberInEmptyUniversePredicate
  obtain ⟨_lowerCandidate, impossibleLowerReducible⟩ := lowerReducibleWitness
  exact impossibleLowerReducible

/-- **Successor universe codes do not have the all-positive candidate at fuel zero.**  This is the
formal obstruction behind the dependent binder impasse: at fuel `0`, the universe candidate is
`universeReducibilityPredicate` over the empty lower relation, so it contains no type witnesses.  But a
successor universe `Type@(succ levelExpr)` does have its predecessor `Type@levelExpr` as an all-positive
member — by `universeFormation` at every positive fuel.  If the successor universe denoted the all-positive
member predicate already at fuel `0`, `universeCodeInversion` would identify that predecessor membership
with the empty lower universe predicate, contradiction.  Thus the missing binder bridge cannot be obtained
by pretending the all-positive universe candidate exists uniformly at every fuel; positive-fuel premises are
essential. -/
theorem HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasAllPositiveReducibleCandidateAt 0
      (universeCodeCell levelExpr.lsucc flag : RawTerm scope) := by
  intro hasAllPositiveCandidateAtZero
  have allPositiveCandidateIsEmpty :
      PointwiseIff
        (IsReducibleMemberAtAllPositiveLevels
          (universeCodeCell levelExpr.lsucc flag : RawTerm scope))
        (universeReducibilityPredicate
          (fun _typeCode _candidate => False : RawTerm scope → (RawTerm scope → Prop) → Prop)) :=
    ReducibleTypeStep.universeCodeInversion hasAllPositiveCandidateAtZero
  have predecessorIsAllPositiveMember :
      IsReducibleMemberAtAllPositiveLevels
        (universeCodeCell levelExpr.lsucc flag : RawTerm scope)
        (universeCodeCell levelExpr flag) := by
    intro predLevel
    exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag
  have predecessorIsInEmptyUniversePredicate :=
    (allPositiveCandidateIsEmpty (universeCodeCell levelExpr flag)).mp predecessorIsAllPositiveMember
  obtain ⟨_witnessCandidate, impossibleLowerWitness⟩ :=
    predecessorIsInEmptyUniversePredicate.2
  exact impossibleLowerWitness

/-- **All-level candidate companions cannot classify successor universes under a realized reducible
substitution.**  This is the substitution-facing version of
`HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero`: if a context actually admits an all-level
reducible closing substitution, then claiming that `Type@(succ levelExpr)` denotes the all-positive member
predicate at EVERY fuel immediately instantiates the impossible fuel-`0` candidate.  This prevents the
formation/binder assembly from accidentally using the full-fuel companion on universe domains; only the
positive-fuel companion can be sound there. -/
theorem HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.notSuccUniverseCode
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (hasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context
        (universeCodeCell levelExpr.lsucc flag))
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution) :
    False := by
  have candidateAtZero := hasAllPositiveCandidateUnderSubstitution substitution env 0
  rw [subst_universeCodeCell] at candidateAtZero
  exact HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero levelExpr flag candidateAtZero

/-- **Universe codes have positive-fuel all-positive candidates under all-level substitutions, conditional
on the exact lower-type extension obligation.**  This packages the universe case for the positive-fuel
type-companion predicate without hiding the remaining semantic assumption. -/
theorem HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.universeCodeOfLowerTypeExtendsToAllLevels
    {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        (typeCode : RawTerm (targetScope + 1)),
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context
      (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution env predLevel
  rw [subst_universeCodeCell]
  exact HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels
    levelExpr flag
    (fun typeCode typeCodeNormalizing typeCodeReducibleAtLowerLevel =>
      lowerTypeExtendsToAllLevels substitution env predLevel typeCode
        typeCodeNormalizing typeCodeReducibleAtLowerLevel)

/-- **Positive-fuel candidate companions strengthen ordinary members to all-positive members.**  This is
the recursor-facing projection from the positive-fuel type companion: once the substituted domain denotes
`IsReducibleMemberAtAllPositiveLevels` at the exact positive level consumed by a binder, determinism turns
membership in any decoded domain candidate at that same level into all-positive membership. -/
theorem HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.memberExtendsToAllPositive
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope}
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
      {domainCandidate : RawTerm (targetScope + 1) → Prop},
      ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument := by
  intro _targetScope substitution env predLevel domainCandidate domainReducible argument argumentMember
  exact HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
    (domainHasPositiveCandidateUnderSubstitution substitution env predLevel)
    domainReducible argumentMember

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

/-- **Dependent Π-introduction from an all-positive domain candidate.**  This is the recursor-facing form of
`fundamentalPiIntroAtAllFromAllPositiveArgumentPremises`: instead of assuming directly that every member of
the decoded domain candidate extends to all positive levels, it asks for the semantic candidate witness that
the substituted domain denotes `IsReducibleMemberAtAllPositiveLevels` at the exact decoded level.  Candidate
determinism then turns ordinary domain-candidate membership into all-positive domain membership. -/
theorem fundamentalPiIntroAtAllFromAllPositiveDomainCandidate {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasAllPositiveCandidate :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
        HasAllPositiveReducibleCandidateAt (predLevel + 1)
          (RawTerm.subst substitution domainCode))
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtAll context (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroAtAllFromAllPositiveArgumentPremises domainFundamental
    (fun _targetScope substitution env predLevel {_domainCandidate} domainReducible _argument
        argumentInDomain =>
      HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
        (domainHasAllPositiveCandidate substitution env predLevel)
        domainReducible argumentInDomain)
    codomainFundamental bodyFundamental

/-- **Dependent Π-introduction from the positive-fuel domain-candidate companion.**  This packages the
previous bridge in the exact positive-fuel companion form expected from the type half of the dependent
fundamental theorem.  The domain companion supplies the all-positive candidate at `predLevel + 1`, which is
precisely the decoded domain level consumed by the abstraction rule. -/
theorem fundamentalPiIntroAtAllFromPositiveDomainCandidateCompanion
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtAll context (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroAtAllFromAllPositiveDomainCandidate domainFundamental
    (fun substitution env predLevel =>
      domainHasPositiveCandidateUnderSubstitution substitution env predLevel)
    codomainFundamental bodyFundamental

/-- **All-level candidate companions strengthen ordinary members at any level to all-positive members.**
This is the former-dispatch projection from the full all-level type companion.  Unlike the positive-fuel
companion, this one is strong enough for dispatch premises that may inspect the domain at fuel `0`. -/
theorem HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.memberExtendsToAllPositive
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope}
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context domainCode) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (memberLevel : Nat)
      {domainCandidate : RawTerm (targetScope + 1) → Prop},
      ReducibleTypeAt memberLevel (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument := by
  intro _targetScope substitution env memberLevel domainCandidate domainReducible argument argumentMember
  exact HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
    (domainHasAllPositiveCandidateUnderSubstitution substitution env memberLevel)
    domainReducible argumentMember

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

/-- **Dispatch-level Π/Σ former children from all-positive domain candidates.**  This is the
recursor-facing sibling of `formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises`.  The
former dispatch may receive the domain argument at either of its consumed member levels, so the premise
provides the all-positive domain candidate at the concrete `memberLevel` being consumed; determinism then
strengthens that member into all-positive membership before running the codomain recursive hypothesis under
the cons-extended all-level environment. -/
theorem formerChildrenReducibleAtDispatchLevelsFromAllPositiveDomainCandidate {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasAllPositiveCandidate :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (_predLevel : Nat)
        (memberLevel : Nat),
        HasAllPositiveReducibleCandidateAt memberLevel
          (RawTerm.subst substitution domainCode))
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises domainFundamental
    (fun _targetScope substitution env predLevel {memberLevel} _argument argumentMember =>
      let memberWitness := argumentMember
      let candidateWitness := domainHasAllPositiveCandidate substitution env predLevel memberLevel
      let ⟨_domainCandidate, domainReducible, argumentInDomain⟩ := memberWitness
      HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
        candidateWitness domainReducible argumentInDomain)
    codomainFundamental

/-- **Dispatch-level Π/Σ former children from the all-level domain-candidate companion.**  This packages the
former-facing bridge in the exact full-fuel companion form needed when the dispatch may consume a domain
member at fuel `0`.  It is therefore appropriate for neutral and Σ-domain companions; universe domains still
need the separate positive-fuel analysis because the universe candidate is not all-positive at level `0`. -/
theorem formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context domainCode)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsFromAllPositiveDomainCandidate domainFundamental
    (fun substitution env _predLevel memberLevel =>
      domainHasAllPositiveCandidateUnderSubstitution substitution env memberLevel)
    codomainFundamental

/-- **Dispatch-level Π/Σ former children from a positive-fuel domain companion plus the base-level
codomain premise.**  This is the precise bridge for domains such as universe codes: the positive-fuel
companion can strengthen the `predLevel + 1` domain argument used by the former dispatch, but it deliberately
does NOT claim anything at fuel `0`.  Therefore the codomain premise at the domain-candidate level
`predLevel` is kept explicit, while the one-higher codomain premise is discharged by strengthening that
argument to all-positive membership and running the all-level codomain fundamental theorem under the
cons-extended environment. -/
theorem formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsFromAtAllPremises domainFundamental
    codomainMemberAtDomainLevel
    (fun substitution env predLevel argument argumentMember => by
      obtain ⟨_domainCandidate, domainReducible, argumentInDomain⟩ := argumentMember
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidateUnderSubstitution substitution env predLevel)
          domainReducible argumentInDomain
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtAllLevels.cons env argumentAtAllPositiveLevels) predLevel)

/-- **Π-formation from the all-level domain-candidate companion.**  This is the direct former-rule bridge
for domains whose substituted candidate is available at every fuel level: build the dispatch-level child
bundle from the companion, then run the Π-former semantic dispatch. -/
theorem fundamentalPiFormationAtAllFromAllLevelDomainCandidateCompanion
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context domainCode)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalPiFormationAtDispatchLevelsAtAll
    (formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
      domainFundamental domainHasAllPositiveCandidateUnderSubstitution codomainFundamental)

/-- **Π-formation from a positive-fuel domain companion plus the base-level codomain premise.**  This is
the universe-safe former-rule bridge: positive-fuel domain candidates discharge the one-higher dispatch
premise, while the base-level premise remains explicit because successor universes cannot have an
all-positive candidate at fuel `0`. -/
theorem fundamentalPiFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalPiFormationAtDispatchLevelsAtAll
    (formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
      domainFundamental domainHasPositiveCandidateUnderSubstitution codomainMemberAtDomainLevel
      codomainFundamental)

/-- **Σ-formation from the all-level domain-candidate companion.**  The data-former twin of
`fundamentalPiFormationAtAllFromAllLevelDomainCandidateCompanion`.  It uses the same dispatch-level child
bundle and then runs the Σ-former semantic dispatch. -/
theorem fundamentalSigmaFormationAtAllFromAllLevelDomainCandidateCompanion
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasAllPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context domainCode)
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationAtDispatchLevelsAtAll
    (formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
      domainFundamental domainHasAllPositiveCandidateUnderSubstitution codomainFundamental)

/-- **Σ-formation from a positive-fuel domain companion plus the base-level codomain premise.**  The
data-former twin of `fundamentalPiFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise`. -/
theorem fundamentalSigmaFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidateUnderSubstitution :
      HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution context domainCode)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionAtAll (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtAll context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationAtDispatchLevelsAtAll
    (formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
      domainFundamental domainHasPositiveCandidateUnderSubstitution codomainMemberAtDomainLevel
      codomainFundamental)

end FX1Poly.Typed

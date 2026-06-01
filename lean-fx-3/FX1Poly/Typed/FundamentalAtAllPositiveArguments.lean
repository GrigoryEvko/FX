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

end FX1Poly.Typed

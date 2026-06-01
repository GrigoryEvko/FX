import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro
import FX1Poly.Core.StratifiedReducibleMemberNeutral

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

/-- Read an all-positive member at one concrete positive level. -/
theorem IsReducibleMemberAtAllPositiveLevels.atLevel {scope : Nat}
    {typeCode term : RawTerm scope}
    (memberAtAllPositiveLevels : IsReducibleMemberAtAllPositiveLevels typeCode term)
    (level : Nat) :
    IsReducibleMemberAt (level + 1) typeCode term :=
  memberAtAllPositiveLevels level

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

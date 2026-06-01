import FX1Poly.Typed.FundamentalWithPositiveTypeCandidates
import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates

/-! # FX1Poly/Typed/FundamentalWithTypeValueCandidates
    -- fundamental-theorem motives over the type-value candidate environment

`FundamentalWithPositiveTypeCandidates` records the positive-fuel candidate companion for every looked-up
binding TYPE.  The dependent fundamental theorem's type-variable arm needs one more boundary datum: when a
variable's substituted classifier is a universe code, the substituted VARIABLE VALUE itself must carry the
positive-fuel all-positive candidate companion.  `ReducibleEnvAtAllLevelsWithTypeValueCandidates` packages
that data.

This file introduces the corresponding conclusion shapes:

* ordinary member reducibility over the stronger environment;
* positive-candidate reducibility for type codes over the stronger environment; and
* the conditional type-value candidate conclusion: if the substituted classifier is a universe code, then
  the substituted subject is a positive-candidate type value.

The last shape is the local Lean analogue of the bundled validity records in `logrel-coq`: the fundamental
theorem should carry the boundary/type-value payload that later arms consume, instead of trying to recover it
from a bare membership result by level irrelevance.

## Zero-axiom verification

All proofs are projections from the previously gated positive-candidate layer or from the
type-value-candidate environment.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **The member half over the type-value candidate environment.**  This is the ordinary semantic
fundamental-theorem conclusion, but quantified over the stronger proof-relevant environment that also
contains type-variable value candidates. -/
def FundamentalConclusionWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **The type-code half over the type-value candidate environment.**  A type code exposes
`IsReducibleMemberAtAllPositiveLevels` as its candidate at every positive fuel, under every strengthened
closing substitution. -/
def PositiveCandidateConclusionWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (typeCode : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat),
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution typeCode)

/-- **The conditional type-value half over the type-value candidate environment.**  If a subject's
substituted classifier is a universe code, then the substituted subject itself is a type value with the
positive-fuel all-positive candidate.  This is the proof-relevant payload the type-variable arm needs. -/
def TypeValueCandidateConclusionWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    {levelExpr : LevelExpr} {flag : UniverseFlag},
    RawTerm.subst substitution classifier = universeCodeCell levelExpr flag →
      ∀ predLevel : Nat,
        HasAllPositiveReducibleCandidateAt (predLevel + 1)
          (RawTerm.subst substitution subject)

/-- **Bundled semantic validity over the type-value candidate environment.**  This package is intentionally
stronger than a bare member conclusion: it carries both ordinary membership and the conditional type-value
candidate payload needed when the classifier is a universe code.  The shape mirrors the "valid term bundles
its boundaries" discipline used by logical-relation developments, while remaining specific to the FX1Poly
stratified fuel semantics. -/
def FundamentalValidityWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  FundamentalConclusionWithTypeValueCandidates context subject classifier ∧
    TypeValueCandidateConclusionWithTypeValueCandidates context subject classifier

/-- Project the ordinary member conclusion from a bundled validity result. -/
theorem FundamentalValidityWithTypeValueCandidates.memberConclusion
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectValidity :
      FundamentalValidityWithTypeValueCandidates context subject classifier) :
    FundamentalConclusionWithTypeValueCandidates context subject classifier :=
  subjectValidity.1

/-- Project the conditional type-value candidate conclusion from a bundled validity result. -/
theorem FundamentalValidityWithTypeValueCandidates.typeValueCandidateConclusion
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectValidity :
      FundamentalValidityWithTypeValueCandidates context subject classifier) :
    TypeValueCandidateConclusionWithTypeValueCandidates context subject classifier :=
  subjectValidity.2

/-- Read a positive-candidate-environment member theorem through the stronger type-value environment. -/
theorem FundamentalConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental :
      FundamentalConclusionWithPositiveTypeCandidates context subject classifier) :
    FundamentalConclusionWithTypeValueCandidates context subject classifier := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact subjectFundamental substitution
    envWithTypeValueCandidates.toPositiveTypeCandidates predLevel

/-- Read a positive-candidate-environment type theorem through the stronger type-value environment. -/
theorem PositiveCandidateConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithPositiveTypeCandidates context typeCode) :
    PositiveCandidateConclusionWithTypeValueCandidates context typeCode := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact typeHasPositiveCandidate substitution
    envWithTypeValueCandidates.toPositiveTypeCandidates predLevel

/-- A type-code positive-candidate theorem also supplies the conditional type-value theorem, for any
classifier.  The classifier-universe equality is unused because the subject is already known to be a type
value under all strengthened substitutions. -/
theorem PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode classifier : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context typeCode) :
    TypeValueCandidateConclusionWithTypeValueCandidates context typeCode classifier := by
  intro _targetScope substitution envWithTypeValueCandidates _levelExpr _flag
  intro _classifierSubstIsUniverse predLevel
  exact typeHasPositiveCandidate substitution envWithTypeValueCandidates predLevel

/-- **The variable member arm over the type-value environment.** -/
theorem fundamentalVarWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionWithTypeValueCandidates context (variableCell index) (context.lookup index) :=
  FundamentalConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
    (fundamentalVarWithPositiveTypeCandidates context index)

/-- **The looked-up binding-type positive-candidate arm over the type-value environment.** -/
theorem positiveCandidateVarLookupWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    PositiveCandidateConclusionWithTypeValueCandidates context (context.lookup index) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact envWithTypeValueCandidates.lookupPositiveCandidate index predLevel

/-- **The type-variable value arm over the type-value environment.**  If the substituted lookup classifier
of a variable is a universe code, the environment supplies the positive-fuel candidate companion for the
substituted variable value itself. -/
theorem typeValueCandidateVarWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (variableCell index) (context.lookup index) := by
  intro _targetScope substitution envWithTypeValueCandidates _levelExpr _flag
  intro lookupSubstIsUniverse predLevel
  exact envWithTypeValueCandidates.lookupTypeValuePositiveCandidate
    index lookupSubstIsUniverse predLevel

/-- **The bundled variable arm over the type-value environment.**  This is the load-bearing type-variable
case: variable membership comes from the all-level environment projection, while the conditional type-value
payload comes from the environment's substituted-lookup universe witness. -/
theorem fundamentalVarValidityWithTypeValueCandidates {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalValidityWithTypeValueCandidates context (variableCell index) (context.lookup index) :=
  ⟨fundamentalVarWithTypeValueCandidates context index,
    typeValueCandidateVarWithTypeValueCandidates context index⟩

/-- **Universe formation over the type-value environment.**  This theorem is polymorphic in the syntactic
universe expression and universe flag; it is not a one-universe result. -/
theorem fundamentalUniverseFormationWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    FundamentalConclusionWithTypeValueCandidates context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) :=
  FundamentalConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
    (fundamentalUniverseFormationWithPositiveTypeCandidates context levelExpr flag)

/-- **Universe-code positive-candidate type half over the type-value environment, conditional on the exact
lower-type extension obligation.**  The theorem is fully universe-parametric: `levelExpr` and `flag` remain
arbitrary.  The remaining hypothesis is not a one-universe artifact; it is the honest lower-reducibility
extension obligation imposed by the stratified fuel semantics for universe candidates. -/
theorem positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (typeCode : RawTerm (targetScope + 1)),
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    PositiveCandidateConclusionWithTypeValueCandidates context (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_universeCodeCell]
  exact HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels
    levelExpr flag
    (fun typeCode typeCodeNormalizing typeCodeReducibleAtLowerLevel =>
      lowerTypeExtendsToAllLevels substitution envWithTypeValueCandidates predLevel typeCode
        typeCodeNormalizing typeCodeReducibleAtLowerLevel)

/-- **Universe-code type-value half over the type-value environment, conditional on lower-type extension.**
Because a universe code is itself a type value, the positive-candidate universe theorem also supplies the
conditional type-value payload for any universe classifier. -/
theorem typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (subjectLevelExpr classifierLevelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (typeCode : RawTerm (targetScope + 1)),
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (universeCodeCell subjectLevelExpr flag) (universeCodeCell classifierLevelExpr flag) :=
  PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
    (classifier := universeCodeCell classifierLevelExpr flag)
    (positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
      context subjectLevelExpr flag lowerTypeExtendsToAllLevels)

/-- **Bundled universe validity over arbitrary universe levels and flags.**  The member half is pure
universe formation (`Type@levelExpr : Type@(lsucc levelExpr)`); the type-value half is exactly the
stratified lower-type extension obligation.  This theorem makes the "not one universe" status explicit in
the library: both the syntactic level expression and flag are parameters, not constants. -/
theorem fundamentalUniverseValidityWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (lowerTypeExtendsToAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (typeCode : RawTerm (targetScope + 1)),
        IsStronglyNormalizing typeCode →
          IsReducibleTypeAt predLevel typeCode → IsReducibleTypeAtAllLevels typeCode) :
    FundamentalValidityWithTypeValueCandidates context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  ⟨fundamentalUniverseFormationWithTypeValueCandidates context levelExpr flag,
    typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
      context levelExpr levelExpr.lsucc flag lowerTypeExtendsToAllLevels⟩

/-- **The `conv` member arm over the type-value environment.**  The reclassifier premise is run one fuel
level up, decoded from its universe membership to a reducible target type at the conclusion fuel, and the
subject member is transported along the substituted conversion.  This is only the member half: the
conditional type-value payload for arbitrary conversions is intentionally not asserted here, because a
conversion into a universe classifier does not by itself identify the original classifier as a universe
code. -/
theorem fundamentalConvWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionWithTypeValueCandidates context reclassifier
        (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalConclusionWithTypeValueCandidates context subject reclassifier := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  have reclassifierMember :=
    reclassifierFundamental substitution envWithTypeValueCandidates (predLevel + 1)
  rw [subst_universeCodeCell] at reclassifierMember
  obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
  exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
    (subjectFundamental substitution envWithTypeValueCandidates predLevel)
    reclassifierReducible converts

/-- **The `piElim`/application member arm over the type-value environment.**  Application does not need any
new type-value payload: the dependent application rule consumes the function and argument member premises at
the same conclusion fuel and performs the codomain substitution bookkeeping internally. -/
theorem fundamentalPiElimWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (functionFundamental :
      FundamentalConclusionWithTypeValueCandidates context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentFundamental :
      FundamentalConclusionWithTypeValueCandidates context argument domainCode) :
    FundamentalConclusionWithTypeValueCandidates context
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact IsReducibleMemberAt.applicationUnderSubst substitution
    (functionFundamental substitution envWithTypeValueCandidates predLevel)
    (argumentFundamental substitution envWithTypeValueCandidates predLevel)

/-- **The positive-candidate Sigma type half over the type-value environment.**  Sigma codes are neutral
non-Pi type codes in the stratified reducibility semantics, so the existing positive-candidate arm reads
through the stronger environment unchanged. -/
theorem positiveCandidateSigmaTypeWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    PositiveCandidateConclusionWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) :=
  PositiveCandidateConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
    (positiveCandidateSigmaTypeWithPositiveTypeCandidates context domainCode codomainCode)

/-- **The Sigma type-value half over the type-value environment.**  Since a Sigma code is already known to
carry the all-positive candidate at every positive fuel, it also satisfies the conditional type-value
payload for any universe classifier. -/
theorem typeValueCandidateSigmaTypeWithTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (classifier : RawTerm scope) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) classifier :=
  PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
    (positiveCandidateSigmaTypeWithTypeValueCandidates context domainCode codomainCode)

/-- A strengthened member result for `typeCode : Type@levelExpr` yields strong normalization and
all-level reducibility of the substituted type code. -/
theorem FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeFundamental :
      FundamentalConclusionWithTypeValueCandidates context typeCode
        (universeCodeCell levelExpr flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution),
      IsStronglyNormalizing (RawTerm.subst substitution typeCode) ∧
        IsReducibleTypeAtAllLevels (RawTerm.subst substitution typeCode) := by
  intro _targetScope substitution envWithTypeValueCandidates
  have typeMemberAtAllPositive :
      IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag)
        (RawTerm.subst substitution typeCode) := by
    intro level
    have typeMember := typeFundamental substitution envWithTypeValueCandidates level
    rwa [subst_universeCodeCell] at typeMember
  exact (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := levelExpr) (flag := flag)).mp typeMemberAtAllPositive

end FX1Poly.Typed

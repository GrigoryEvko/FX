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

/-- **Vacuous type-value payload for classifiers that can never substitute to a universe code.**  The
conditional type-value half asks for a positive-candidate witness only under a classifier-universe equality.
For syntactically non-universe classifiers whose root is preserved by every substitution (for example Pi
and future Sigma intro classifiers), that equality is impossible.  This reusable eliminator keeps such arms
honest: the type-value branch is closed by an explicit root-impossibility proof, not by semantic
level-irrelevance or a hidden reducibility cast. -/
theorem TypeValueCandidateConclusionWithTypeValueCandidates.ofSubstitutedClassifierNeUniverse
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (substitutedClassifierIsNeverUniverse :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        {levelExpr : LevelExpr} {flag : UniverseFlag},
        RawTerm.subst substitution classifier = universeCodeCell levelExpr flag → False) :
    TypeValueCandidateConclusionWithTypeValueCandidates context subject classifier := by
  intro _targetScope substitution _envWithTypeValueCandidates _levelExpr _flag
  intro classifierSubstIsUniverse _predLevel
  exact False.elim (substitutedClassifierIsNeverUniverse substitution classifierSubstIsUniverse)

/-- **A type-value-environment positive-candidate conclusion strengthens decoded membership.**  If a
decoded candidate for a type accepts an argument, the positive-candidate companion identifies that candidate
with all-positive membership and transports the argument into the all-positive predicate. -/
theorem PositiveCandidateConclusionWithTypeValueCandidates.memberExtendsToAllPositive
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context typeCode)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
    (typeReducible :
      ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeCode) candidate)
    {argument : RawTerm (targetScope + 1)} (argumentInCandidate : candidate argument) :
    IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution typeCode) argument :=
  HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
    (typeHasPositiveCandidate substitution envWithTypeValueCandidates predLevel)
    typeReducible argumentInCandidate

/-- **Extend the type-value environment through a binder from a decoded argument.**  The positive-candidate
type half upgrades the decoded argument to all-positive membership and supplies the binding TYPE's
positive-candidate companion.  The caller must still provide the value payload required specifically when
the substituted binding type is a universe code: in that case the bound VALUE itself is a type value and
must denote the all-positive member predicate.  Keeping that premise explicit is the sound boundary; it does
not assume level irrelevance or that every reducible type automatically carries the all-positive candidate. -/
theorem PositiveCandidateConclusionWithTypeValueCandidates.consEnvWithTypeValueCandidate
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (typeHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context typeCode)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
    (typeReducible :
      ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeCode) candidate)
    {argument : RawTerm (targetScope + 1)} (argumentInCandidate : candidate argument)
    (argumentValueHasPositiveCandidateWhenTypeIsUniverse :
      ∀ {levelExpr : LevelExpr} {flag : UniverseFlag},
        RawTerm.subst substitution typeCode = universeCodeCell levelExpr flag →
          ∀ candidatePredLevel : Nat,
            HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument) :
    ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons typeCode)
      (RawTermSubst.cons argument substitution) :=
  ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons envWithTypeValueCandidates
    (typeHasPositiveCandidate.memberExtendsToAllPositive substitution
      envWithTypeValueCandidates predLevel typeReducible argumentInCandidate)
    (fun headPredLevel =>
      typeHasPositiveCandidate substitution envWithTypeValueCandidates headPredLevel)
    argumentValueHasPositiveCandidateWhenTypeIsUniverse

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

/-- **Bundled conversion validity over the type-value environment, with the target type-value payload
explicit.**  The ordinary member half is the semantic conversion rule
`fundamentalConvWithTypeValueCandidates`.  The conditional type-value half is deliberately an input: if a
conversion changes the classifier into something syntactically universe-shaped after substitution, bare
membership in that universe gives only lower-level type reducibility, not the all-positive candidate payload
the strengthened FT motive requires.  This theorem therefore records the exact proof obligation a full
recursor assembly must discharge rather than hiding it behind a false level-irrelevance cast. -/
theorem fundamentalConvValidityWithTypeValueCandidatesFromTargetTypeValuePremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionWithTypeValueCandidates context reclassifier
        (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier)
    (targetTypeValueCandidate :
      TypeValueCandidateConclusionWithTypeValueCandidates context subject reclassifier) :
    FundamentalValidityWithTypeValueCandidates context subject reclassifier :=
  ⟨fundamentalConvWithTypeValueCandidates subjectFundamental reclassifierFundamental converts,
    targetTypeValueCandidate⟩

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

/-- **Bundled dependent application validity over the type-value environment, with the result type-value
payload explicit.**  The member half is `fundamentalPiElimWithTypeValueCandidates`.  The type-value half is
again a genuine extra obligation: when the instantiated codomain reduces to a universe-shaped classifier,
the application result must be known as a type value carrying the all-positive candidate.  Ordinary Π-member
reducibility alone proves the application is a member of the instantiated codomain; it does not expose the
stronger type-value payload for universe-valued codomains.  This factored arm is the precise recursor
interface for the eventual application case. -/
theorem fundamentalPiElimValidityWithTypeValueCandidatesFromResultTypeValuePremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (functionFundamental :
      FundamentalConclusionWithTypeValueCandidates context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentFundamental :
      FundamentalConclusionWithTypeValueCandidates context argument domainCode)
    (resultTypeValueCandidate :
      TypeValueCandidateConclusionWithTypeValueCandidates context
        (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument)) :
    FundamentalValidityWithTypeValueCandidates context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  ⟨fundamentalPiElimWithTypeValueCandidates functionFundamental argumentFundamental,
    resultTypeValueCandidate⟩

/-- **Dependent lambda introduction over the type-value environment, with the universe-domain value
payload explicit.**  The ordinary member proof is the same canonical-candidate argument as in the
positive-candidate layer: the domain is decoded one fuel level up, accepted arguments are strengthened to
all-positive membership, and the codomain/body recursive premises run under the cons-extended environment.

The additional premise is exactly the type-value payload required by
`ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons`: if the substituted domain itself is a universe, the
chosen argument is a type value and must carry the all-positive candidate at every positive fuel.  This is
the proof-relevant boundary needed for universe-valued binders; the theorem does not collapse it by false
level irrelevance. -/
theorem fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (_predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
        {argument : RawTerm (targetScope + 1)}, candidate argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) body codomainCode) :
    FundamentalConclusionWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  have domainMember := domainFundamental substitution envWithTypeValueCandidates (predLevel + 1)
  rw [subst_universeCodeCell] at domainMember
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible
    (fun _argument argumentInDomain =>
      domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
    ?codomainExists ?bodyReducible
  · intro argument argumentInDomain
    have extendedEnvWithTypeValueCandidates :
        ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons domainCode)
          (RawTermSubst.cons argument substitution) :=
      domainHasPositiveCandidate.consEnvWithTypeValueCandidate substitution
        envWithTypeValueCandidates predLevel domainReducible argumentInDomain
        (argumentValueHasPositiveCandidateWhenDomainIsUniverse substitution
          envWithTypeValueCandidates predLevel argumentInDomain)
    have codomainMember :=
      codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithTypeValueCandidates (predLevel + 1)
    rw [subst_universeCodeCell] at codomainMember
    have codomainReducibleType := codomainMember.tarskiDecode
    rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainReducibleType
  · intro argument argumentInDomain
    have extendedEnvWithTypeValueCandidates :
        ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons domainCode)
          (RawTermSubst.cons argument substitution) :=
      domainHasPositiveCandidate.consEnvWithTypeValueCandidate substitution
        envWithTypeValueCandidates predLevel domainReducible argumentInDomain
        (argumentValueHasPositiveCandidateWhenDomainIsUniverse substitution
          envWithTypeValueCandidates predLevel argumentInDomain)
    rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
      ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
    exact bodyFundamental (RawTermSubst.cons argument substitution)
      extendedEnvWithTypeValueCandidates predLevel

/-- **A substituted Pi-code classifier is never syntactically a universe code.**  Substitution distributes
over the Pi code and preserves its `gen_piTyCode` root, while a universe code has root
`gen_universeCode`.  This is the syntactic discharge for the conditional type-value payload of lambda
introduction: the classifier of a lambda is a Pi code, so the "if the classifier is a universe" branch is
unreachable by root injectivity, not by any semantic level-irrelevance assumption. -/
theorem substitutedPiTyCode_ne_universeCodeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1))
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.subst substitution (piTyCodeCell domainCode codomainCode) ≠
      universeCodeCell levelExpr flag := by
  rw [subst_piTyCodeCell]
  intro classifierEquation
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator classifierEquation :
      Generator.gen_piTyCode = Generator.gen_universeCode)

/-- **A substituted Sigma-code classifier is never syntactically a universe code.**  This is the Sigma
counterpart of `substitutedPiTyCode_ne_universeCodeCell`, staged for future Sigma introduction/elimination
validity arms: substitution preserves the `gen_sigmaTyCode` root, which is disjoint from
`gen_universeCode`. -/
theorem substitutedSigmaTyCode_ne_universeCodeCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1))
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.subst substitution (sigmaTyCodeCell domainCode codomainCode) ≠
      universeCodeCell levelExpr flag := by
  rw [subst_sigmaTyCodeCell]
  intro classifierEquation
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator classifierEquation :
      Generator.gen_sigmaTyCode = Generator.gen_universeCode)

/-- **Bundled dependent lambda-introduction validity over the type-value environment.**  The member half is
`fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise`.  The conditional type-value half
is discharged syntactically: after any closing substitution, the classifier remains a Pi code and therefore
cannot be a universe code.  This packages the `piIntro` recursor arm for the strengthened FT motive without
smuggling in level monotonicity or collapsing universe-valued binders. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (_predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
        {argument : RawTerm (targetScope + 1)}, candidate argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) body codomainCode) :
    FundamentalValidityWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell domainCode codomainCode) :=
  ⟨fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise
      domainFundamental domainHasPositiveCandidate
      argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainFundamental bodyFundamental,
    TypeValueCandidateConclusionWithTypeValueCandidates.ofSubstitutedClassifierNeUniverse
      (fun {_targetScope} substitution {levelExpr} {flag} classifierSubstIsUniverse =>
        substitutedPiTyCode_ne_universeCodeCell substitution domainCode codomainCode
          levelExpr flag classifierSubstIsUniverse)⟩

/-- **The positive-candidate dependent Pi type half over the type-value environment.**  The construction is
the strengthened-environment version of the reducibility candidate for Pi codes: the domain candidate
companion upgrades each accepted argument to all-positive membership, the type-value environment extends
under the binder, and the codomain candidate companion runs under the cons substitution.

As in the lambda arm, universe-valued domains require an explicit type-value payload for each chosen
argument.  This theorem therefore exposes the exact premise needed to make binder extension sound instead
of deriving it from ordinary universe membership. -/
theorem positiveCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode) :
    PositiveCandidateConclusionWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_piTyCodeCell]
  exact HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel
    (fun candidatePredLevel =>
      domainHasPositiveCandidate substitution envWithTypeValueCandidates candidatePredLevel)
    (fun candidatePredLevel argument argumentAtAllPositiveLevels => by
      have extendedEnvWithTypeValueCandidates :
          ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons domainCode)
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons envWithTypeValueCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithTypeValueCandidates headPredLevel)
          (argumentValueHasPositiveCandidateWhenDomainIsUniverse substitution
            envWithTypeValueCandidates argument argumentAtAllPositiveLevels)
      have codomainCandidate :=
        codomainHasPositiveCandidate (RawTermSubst.cons argument substitution)
          extendedEnvWithTypeValueCandidates candidatePredLevel
      rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainCandidate)

/-- **The dependent Pi type-value half over the type-value environment.**  A Pi code satisfying the explicit
universe-domain value premise is a type value, so its positive-candidate theorem supplies the conditional
type-value payload for any classifier. -/
theorem typeValueCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode)
    (classifier : RawTerm scope) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) classifier :=
  PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
    (positiveCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
      domainHasPositiveCandidate argumentValueHasPositiveCandidateWhenDomainIsUniverse
      codomainHasPositiveCandidate)

/-- **Dispatch-level former children over the type-value environment.**  This is the Π/Σ-formation child
bundle at the exact levels consumed by the semantic former rules.  The first two domain children are read
from the ordinary member half.  The base-level codomain child is kept as an explicit premise, because fuel
zero does not in general expose enough information to extend a type-value environment.  The one-higher
codomain child is the load-bearing branch: the domain positive-candidate half upgrades the decoded argument
to all-positive membership, the explicit type-value premise supplies the value-candidate payload when the
domain is a universe, and the codomain recursive premise runs under the cons-extended environment. -/
theorem formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
      (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
        domainLevel codomainLevel := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  refine ⟨?domainAtLevel, ?domainAboveAndCodomain⟩
  · have domainMember := domainFundamental substitution envWithTypeValueCandidates predLevel
    rwa [subst_universeCodeCell] at domainMember
  · refine ⟨?domainAtNextLevel, ?codomainAtDomainLevel, ?codomainAtNextDomainLevel⟩
    · have domainMemberAbove :=
        domainFundamental substitution envWithTypeValueCandidates (predLevel + 1)
      rwa [subst_universeCodeCell] at domainMemberAbove
    · intro argument argumentMember
      exact codomainMemberAtDomainLevel substitution envWithTypeValueCandidates predLevel
        argument argumentMember
    · intro argument argumentMember
      obtain ⟨domainCandidate, domainReducible, argumentInDomain⟩ := argumentMember
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidate substitution envWithTypeValueCandidates predLevel)
          domainReducible argumentInDomain
      have extendedEnvWithTypeValueCandidates :
          ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons domainCode)
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons envWithTypeValueCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithTypeValueCandidates headPredLevel)
          (argumentValueHasPositiveCandidateWhenDomainIsUniverse substitution
            envWithTypeValueCandidates argument argumentAtAllPositiveLevels)
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithTypeValueCandidates predLevel

/-- **Pi-formation over the type-value environment from the factored dispatch-level child premises.** -/
theorem fundamentalPiFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithTypeValueCandidates context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainMemberAtDomainLevel
    codomainFundamental substitution envWithTypeValueCandidates predLevel).toPiMember

/-- **Sigma-formation over the type-value environment from the factored dispatch-level child premises.** -/
theorem fundamentalSigmaFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithTypeValueCandidates context (sigmaTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainMemberAtDomainLevel
    codomainFundamental substitution envWithTypeValueCandidates predLevel).toSigmaMember

/-- **Bundled Pi-formation validity over the type-value environment.**  The member half uses the
dispatch-level former-children bundle; the type-value half uses the positive-candidate Pi-code theorem, so
the resulting formed Pi code can itself serve as a universe-classified type value in later binder arms. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode) :
    FundamentalValidityWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  ⟨fundamentalPiFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
      domainFundamental domainHasPositiveCandidate
      argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainMemberAtDomainLevel
      codomainFundamental,
    typeValueCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
      domainHasPositiveCandidate argumentValueHasPositiveCandidateWhenDomainIsUniverse
      codomainHasPositiveCandidate (universeCodeCell formerLevel flag)⟩

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

/-- **Bundled Sigma-formation validity over the type-value environment.**  Sigma formation still needs the
same member-side former-children premises as Pi formation, but its type-value half is neutral-data-former
positive-candidate reducibility and reads through the stronger environment unchanged. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution domainCode = universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  ⟨fundamentalSigmaFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
      domainFundamental domainHasPositiveCandidate
      argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainMemberAtDomainLevel
      codomainFundamental,
    typeValueCandidateSigmaTypeWithTypeValueCandidates context domainCode codomainCode
      (universeCodeCell formerLevel flag)⟩

/-- **The base-level codomain premise for a universe-code domain over the type-value environment.**  Fuel
zero is impossible for universe-domain membership.  At successor fuel, the domain positive-candidate
companion upgrades the argument to all-positive membership, the explicit type-value premise supplies the
value-candidate payload for the universe binding, and the codomain recursive premise runs under the
type-value cons environment. -/
theorem codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
      (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt predLevel
        (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel argument argumentMember
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
          (domainHasPositiveCandidate substitution envWithTypeValueCandidates memberPredLevel)
          domainReducible argumentInDomain
      have extendedEnvWithTypeValueCandidates :
          ReducibleEnvAtAllLevelsWithTypeValueCandidates
            (context.cons (universeCodeCell domainLevel flag))
            (RawTermSubst.cons argument substitution) :=
        ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons envWithTypeValueCandidates
          argumentAtAllPositiveLevels
          (fun headPredLevel =>
            domainHasPositiveCandidate substitution envWithTypeValueCandidates headPredLevel)
          (argumentValueHasPositiveCandidateWhenDomainIsUniverse substitution
            envWithTypeValueCandidates argument argumentAtAllPositiveLevels)
      exact codomainFundamental (RawTermSubst.cons argument substitution)
        extendedEnvWithTypeValueCandidates (memberPredLevel + 1)

/-- **Dispatch-level former children for a universe-code domain over the type-value environment.**  This
specializes the generic type-value child bundle by deriving the base-level codomain premise from the empty
fuel-zero universe semantics and the explicit universe-domain type-value argument payload. -/
theorem formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
      (predLevel : Nat),
      FormerChildrenReducibleAtDispatchLevels predLevel flag substitution
        (universeCodeCell domainLevel flag) codomainCode domainLevel.lsucc codomainLevel :=
  formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse
    (codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
      domainHasPositiveCandidate argumentValueHasPositiveCandidateWhenDomainIsUniverse
      codomainFundamental)
    codomainFundamental

/-- **Pi-formation for a universe-code domain over the type-value environment.** -/
theorem fundamentalPiFormationWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithTypeValueCandidates context
      (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainFundamental
    substitution envWithTypeValueCandidates predLevel).toPiMember

/-- **Sigma-formation for a universe-code domain over the type-value environment.** -/
theorem fundamentalSigmaFormationWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionWithTypeValueCandidates context
      (sigmaTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  rw [subst_universeCodeCell]
  exact (formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainFundamental
    substitution envWithTypeValueCandidates predLevel).toSigmaMember

/-- **Bundled Pi-formation validity for a universe-code domain over the type-value environment.**  This is
the bundled counterpart of `fundamentalPiFormationWithTypeValueCandidatesFromUniverseDomain`: the member
half uses the universe-domain former-children specialization, while the type-value half is the generic Pi
positive-candidate construction.  The theorem stays universe-polymorphic in both `LevelExpr` and
`UniverseFlag`; it does not collapse to a single universe or hide the universe-domain value payload. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag))
    (codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode) :
    FundamentalValidityWithTypeValueCandidates context
      (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalPiFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse
    (codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
      domainHasPositiveCandidate argumentValueHasPositiveCandidateWhenDomainIsUniverse
      codomainFundamental)
    codomainFundamental codomainHasPositiveCandidate

/-- **Bundled Sigma-formation validity for a universe-code domain over the type-value environment.**  The
member half uses the universe-domain dispatch-level child bundle; the type-value half is Sigma's neutral
positive-candidate payload.  This packages the universe-domain Sigma formation arm for the strengthened FT
motive without adding any level-irrelevance assumption. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (argumentValueHasPositiveCandidateWhenDomainIsUniverse :
      ∀ {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels
          (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument →
          ∀ {levelExpr : LevelExpr} {domainFlag : UniverseFlag},
            RawTerm.subst substitution (universeCodeCell domainLevel flag) =
              universeCodeCell levelExpr domainFlag →
              ∀ candidatePredLevel : Nat,
                HasAllPositiveReducibleCandidateAt (candidatePredLevel + 1) argument)
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainFundamental domainHasPositiveCandidate
    argumentValueHasPositiveCandidateWhenDomainIsUniverse
    (codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
      domainHasPositiveCandidate argumentValueHasPositiveCandidateWhenDomainIsUniverse
      codomainFundamental)
    codomainFundamental

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

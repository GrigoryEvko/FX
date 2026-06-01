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

/-- **Recover the positive-candidate type half from a universe-classified type-value payload.**  The
type-value conclusion is conditional on the substituted classifier being a universe code.  When the
classifier is syntactically `Type@levelExpr`, that condition is discharged by substitution preservation,
leaving exactly the positive-candidate theorem for the subject type code.  This is the recursor-facing
bridge that lets a bundled IH for `typeCode : Type@levelExpr` feed binder/former domain companions. -/
theorem TypeValueCandidateConclusionWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeValueCandidate :
      TypeValueCandidateConclusionWithTypeValueCandidates context typeCode
        (universeCodeCell levelExpr flag)) :
    PositiveCandidateConclusionWithTypeValueCandidates context typeCode := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact typeValueCandidate substitution envWithTypeValueCandidates
    (levelExpr := levelExpr) (flag := flag) (by rw [subst_universeCodeCell]) predLevel

/-- **Recover the positive-candidate type half from bundled validity at a universe classifier.**  This is
the bundled version of `TypeValueCandidateConclusionWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier`:
the ordinary member half is irrelevant, while the type-value half supplies the positive-candidate
companion demanded by dependent binder and former arms. -/
theorem FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typeValidity :
      FundamentalValidityWithTypeValueCandidates context typeCode
        (universeCodeCell levelExpr flag)) :
    PositiveCandidateConclusionWithTypeValueCandidates context typeCode :=
  TypeValueCandidateConclusionWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
    typeValidity.typeValueCandidateConclusion

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

/-- **Semantic universe members carry type-value candidates.**  This is the exact proof-relevant principle
needed by universe-valued binders: any all-positive member of any universe code, at any syntactic universe
level expression and flag, is itself a type value exposing the all-positive candidate at every positive fuel.

This is intentionally a named theorem interface, not an axiom.  Existing arms may assume it explicitly while
the final universe-value reducibility argument is built.  The statement is multi-universe by construction:
`levelExpr` and `flag` are arbitrary parameters. -/
def HasTypeValueCandidatesForAllPositiveUniverseMembers : Prop :=
  ∀ {scope : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope},
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag) typeCode →
      ∀ predLevel : Nat, HasAllPositiveReducibleCandidateAt (predLevel + 1) typeCode

/-- Read `HasTypeValueCandidatesForAllPositiveUniverseMembers` through a substituted domain that is known
syntactically to be a universe code.  This is the reusable discharge for
`ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons` at universe-valued binders: the binder already has an
all-positive argument in the substituted domain, and the equality identifies that domain with a concrete
universe code. -/
theorem HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers)
    {sourceScope targetScope : Nat} {domainCode : RawTerm sourceScope}
    (substitution : RawTermSubst sourceScope (targetScope + 1))
    {argument : RawTerm (targetScope + 1)}
    (argumentAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution domainCode) argument)
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (substitutedDomainIsUniverse :
      RawTerm.subst substitution domainCode = universeCodeCell levelExpr flag)
    (predLevel : Nat) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1) argument :=
  universeMembersHaveTypeValueCandidates
    (substitutedDomainIsUniverse ▸ argumentAtAllPositiveLevels) predLevel

/-- **Semantic completion for all reducible type values.**  This is the universe-member payload with the
universe wrapper peeled off: every strongly-normalizing type code that is reducible at every fuel level
denotes the all-positive member predicate at every positive fuel.

The statement is intentionally separated from `HasTypeValueCandidatesForAllPositiveUniverseMembers`.
`IsReducibleMemberAtAllPositiveLevels.universeCode_iff` proves they are equivalent, so the remaining
semantic work can target the sharper type-value completion principle directly instead of redoing a Tarski
universe decode at each binder arm. -/
def HasTypeValueCandidatesForAllReducibleTypesAtAllLevels : Prop :=
  ∀ {scope : Nat} {typeCode : RawTerm scope},
    IsStronglyNormalizing typeCode →
      IsReducibleTypeAtAllLevels typeCode →
        ∀ predLevel : Nat, HasAllPositiveReducibleCandidateAt (predLevel + 1) typeCode

/-- **Positive-member extension for strongly normalizing all-level types.**  This is the operational
binder-facing form of type-value completion: if a type code is strongly normalizing and reducible at every
fuel, then any member at one positive fuel is a member at every positive fuel.  The theorem below proves this
is equivalent to `HasTypeValueCandidatesForAllReducibleTypesAtAllLevels`, so the remaining semantic
completion target can be attacked either as a candidate theorem or as this direct member-extension theorem. -/
def HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes : Prop :=
  ∀ {scope : Nat} {typeCode term : RawTerm scope} {predLevel : Nat},
    IsStronglyNormalizing typeCode →
      IsReducibleTypeAtAllLevels typeCode →
        IsReducibleMemberAt (predLevel + 1) typeCode term →
          IsReducibleMemberAtAllPositiveLevels typeCode term

/-- The reducible-type completion principle implies the universe-member payload: all-positive membership in
a universe code is exactly strong normalization plus reducibility at every fuel level. -/
theorem HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    HasTypeValueCandidatesForAllPositiveUniverseMembers := by
  intro scope levelExpr flag typeCode memberAtAllPositiveLevels predLevel
  have typeValueData :=
    (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
      (scope := scope) (levelExpr := levelExpr) (flag := flag)
      (typeCode := typeCode)).mp memberAtAllPositiveLevels
  exact allReducibleTypesHaveTypeValueCandidates typeValueData.1 typeValueData.2 predLevel

/-- Conversely, the universe-member payload implies the reducible-type completion principle: package any
strongly-normalizing all-level reducible type as an all-positive member of a fixed standard universe, then
use the universe-member payload.  The chosen syntactic universe is arbitrary; the proof uses
`Type@0[standard]` only as a Tarski wrapper. -/
theorem HasTypeValueCandidatesForAllPositiveUniverseMembers.toAllReducibleTypesAtAllLevels
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers) :
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels := by
  intro scope typeCode typeCodeNormalizing typeCodeReducibleAtAllLevels predLevel
  have memberAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard : RawTerm scope) typeCode :=
    (IsReducibleMemberAtAllPositiveLevels.universeCode_iff
      (scope := scope) (levelExpr := LevelExpr.lzero) (flag := UniverseFlag.standard)
      (typeCode := typeCode)).mpr
      ⟨typeCodeNormalizing, typeCodeReducibleAtAllLevels⟩
  exact universeMembersHaveTypeValueCandidates memberAtAllPositiveLevels predLevel

/-- **Universe-member payload iff reducible-type completion.**  This pins the remaining type-value semantic
obligation exactly: proving it for universe members is the same as proving that every strongly-normalizing
type reducible at all fuel levels has the all-positive member predicate as a candidate at every positive
fuel. -/
theorem hasTypeValueCandidatesForAllPositiveUniverseMembers_iff_allReducibleTypesAtAllLevels :
    HasTypeValueCandidatesForAllPositiveUniverseMembers ↔
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels :=
  ⟨HasTypeValueCandidatesForAllPositiveUniverseMembers.toAllReducibleTypesAtAllLevels,
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers⟩

/-- **Type-value completion is equivalent to positive-member extension.**  The candidate formulation says
that every strongly normalizing all-level type denotes `IsReducibleMemberAtAllPositiveLevels` at every
positive fuel.  The member-extension formulation says that any concrete positive-fuel member of such a type
extends to all positive fuels.

Forward direction: use the all-positive candidate at the member's fuel and determinism to transport the
member into it.  Reverse direction: choose any candidate of the type at the requested positive fuel and
close it under `ofPointwiseIff`; one direction is the extension property, the other direction reads the
all-positive member at that same fuel and transports its witness candidate back by determinism. -/
theorem hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension :
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels ↔
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes := by
  constructor
  · intro allReducibleTypesHaveTypeValueCandidates
    intro _scope typeCode term predLevel typeCodeNormalizing typeCodeReducibleAtAllLevels member
    obtain ⟨candidate, typeCodeReducibleAtLevel, termInCandidate⟩ := member
    exact HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
      (allReducibleTypesHaveTypeValueCandidates typeCodeNormalizing
        typeCodeReducibleAtAllLevels predLevel)
      typeCodeReducibleAtLevel termInCandidate
  · intro positiveMemberExtension
    intro scope typeCode typeCodeNormalizing typeCodeReducibleAtAllLevels predLevel
    obtain ⟨candidate, typeCodeReducibleAtLevel⟩ :=
      typeCodeReducibleAtAllLevels (predLevel + 1)
    have pointwise :
        PointwiseIff candidate (IsReducibleMemberAtAllPositiveLevels typeCode) := by
      intro term
      constructor
      · intro termInCandidate
        exact positiveMemberExtension typeCodeNormalizing typeCodeReducibleAtAllLevels
          ⟨candidate, typeCodeReducibleAtLevel, termInCandidate⟩
      · intro termAtAllPositiveLevels
        obtain ⟨witnessCandidate, witnessReducible, termInWitness⟩ :=
          termAtAllPositiveLevels predLevel
        exact (ReducibleTypeAt.deterministic witnessReducible typeCodeReducibleAtLevel term).mp
          termInWitness
    cases predLevel with
    | zero =>
        exact ReducibleTypeStep.ofPointwiseIff typeCodeReducibleAtLevel pointwise
    | succ memberPredLevel =>
        exact ReducibleTypeStep.ofPointwiseIff typeCodeReducibleAtLevel pointwise

/-- **Type-value completion entails lower-fuel extension.**  If every strongly-normalizing all-level
reducible type exposes the all-positive member predicate, then any strongly-normalizing type reducible at
one fuel level is reducible at every fuel level.

Proof idea: view `typeCode` as a member of a fixed standard universe at fuel `predLevel + 1`.  The completion
principle gives that universe code the all-positive member predicate as its candidate at the same positive
fuel.  Candidate determinism then transports the one-fuel universe membership of `typeCode` into
all-positive universe membership, and `universeCode_iff` decodes that back to all-level type reducibility.
This pins the exact strength of the type-value completion principle: it is not weaker than the level
extension property consumed by universe-code formation. -/
theorem HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.reducibleTypeAtExtendsToAllLevels
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    {scope : Nat} {predLevel : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop}
    (typeCodeNormalizing : IsStronglyNormalizing typeCode)
    (typeCodeReducibleAtLevel : ReducibleTypeAt predLevel typeCode candidate) :
    IsReducibleTypeAtAllLevels typeCode := by
  let standardUniverse : RawTerm scope :=
    universeCodeCell LevelExpr.lzero UniverseFlag.standard
  have standardUniverseNormalizing : IsStronglyNormalizing standardUniverse :=
    universeCode_isStronglyNormalizing (LevelExpr.lzero, UniverseFlag.standard)
  have standardUniverseReducibleAtAllLevels :
      IsReducibleTypeAtAllLevels standardUniverse := by
    intro level
    cases level with
    | zero =>
        exact ⟨_, ReducibleTypeStep.universeCode LevelExpr.lzero UniverseFlag.standard⟩
    | succ predLevel =>
        exact ⟨_, ReducibleTypeStep.universeCode LevelExpr.lzero UniverseFlag.standard⟩
  have standardUniverseHasAllPositiveCandidate :
      HasAllPositiveReducibleCandidateAt (predLevel + 1) standardUniverse :=
    allReducibleTypesHaveTypeValueCandidates standardUniverseNormalizing
      standardUniverseReducibleAtAllLevels predLevel
  have typeCodeMemberInStandardUniverseAtLevel :
      universeReducibilityPredicate (ReducibleTypeAt predLevel) typeCode :=
    ⟨typeCodeNormalizing, ⟨candidate, typeCodeReducibleAtLevel⟩⟩
  have typeCodeMemberAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels standardUniverse typeCode :=
    HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
      standardUniverseHasAllPositiveCandidate
      (ReducibleTypeStep.universeCode LevelExpr.lzero UniverseFlag.standard)
      typeCodeMemberInStandardUniverseAtLevel
  exact ((IsReducibleMemberAtAllPositiveLevels.universeCode_iff
    (levelExpr := LevelExpr.lzero) (flag := UniverseFlag.standard)
    (typeCode := typeCode)).mp typeCodeMemberAtAllPositiveLevels).2

/-- **Positive-member extension supplies the candidate completion principle.**  This named projection keeps
the operational bridge (`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`) as the public
premise while reusing the already-proved equivalence to the candidate formulation. -/
theorem HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.toAllReducibleTypesHaveTypeValueCandidates
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels :=
  hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension.mpr
    positiveMemberExtension

/-- **Positive-member extension entails lower-fuel type extension.**  This is the universe-formation bridge
in its most operational form: if a strongly normalizing type code is reducible at one fuel, then the
positive-member-extension principle makes it reducible at every fuel.  It is the exact theorem consumed by
the universe-code/type-value arms after the semantic obligation is discharged. -/
theorem HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.reducibleTypeAtExtendsToAllLevels
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    {scope : Nat} {predLevel : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop}
    (typeCodeNormalizing : IsStronglyNormalizing typeCode)
    (typeCodeReducibleAtLevel : ReducibleTypeAt predLevel typeCode candidate) :
    IsReducibleTypeAtAllLevels typeCode :=
  HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.reducibleTypeAtExtendsToAllLevels
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    typeCodeNormalizing typeCodeReducibleAtLevel

/-- **A member conclusion yields the type-value payload from the universe-member principle.**  If a
substituted classifier is syntactically a universe code, the member half can be run at EVERY positive fuel,
so it exhibits the substituted subject as an all-positive member of that universe.  The global
universe-member/type-value principle then gives the required all-positive candidate for the subject itself.
This is the generic closure principle behind application and conversion type-value payloads: no per-arm
type-value premise is needed once the member half is already all-positive. -/
theorem FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers) :
    TypeValueCandidateConclusionWithTypeValueCandidates context subject classifier := by
  intro _targetScope substitution envWithTypeValueCandidates levelExpr flag
    classifierSubstIsUniverse predLevel
  have subjectMemberAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag)
        (RawTerm.subst substitution subject) := by
    intro level
    have subjectMember := subjectFundamental substitution envWithTypeValueCandidates level
    rwa [classifierSubstIsUniverse] at subjectMember
  exact universeMembersHaveTypeValueCandidates subjectMemberAtAllPositiveLevels predLevel

/-- **A member conclusion yields the type-value payload from type-value completion.**  This is the
completion-principle version of
`toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates`, using the already-proved
equivalence from all reducible types to all positive universe members. -/
theorem FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    TypeValueCandidateConclusionWithTypeValueCandidates context subject classifier :=
  subjectFundamental.toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates.toUniverseMembers

/-- **Bundle a member conclusion into validity from the universe-member principle.** -/
theorem FundamentalConclusionWithTypeValueCandidates.toValidityOfUniverseMembersHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers) :
    FundamentalValidityWithTypeValueCandidates context subject classifier :=
  ⟨subjectFundamental,
    subjectFundamental.toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates
      universeMembersHaveTypeValueCandidates⟩

/-- **Bundle a member conclusion into validity from type-value completion.** -/
theorem FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    FundamentalValidityWithTypeValueCandidates context subject classifier :=
  subjectFundamental.toValidityOfUniverseMembersHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates.toUniverseMembers

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

/-- **Universe-code positive candidate from type-value completion.**  The lower-type extension premise of
`positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels` is exactly supplied by
`HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.reducibleTypeAtExtendsToAllLevels`, so universe-code
formation can be read directly from the type-value completion principle.  The statement remains fully
multi-universe: `levelExpr` and `flag` are arbitrary. -/
theorem positiveCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    PositiveCandidateConclusionWithTypeValueCandidates context (universeCodeCell levelExpr flag) :=
  positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    context levelExpr flag
    (fun _substitution _envWithTypeValueCandidates _predLevel _typeCode typeCodeNormalizing
        typeCodeReducibleAtLevel =>
      let ⟨_candidate, candidateReducibleAtLevel⟩ := typeCodeReducibleAtLevel
      allReducibleTypesHaveTypeValueCandidates.reducibleTypeAtExtendsToAllLevels
        typeCodeNormalizing candidateReducibleAtLevel)

/-- **Universe-code type-value payload from type-value completion.**  This is the type-value half of a
universe code's validity with the lower-fuel bridge discharged by the global type-value completion
principle. -/
theorem typeValueCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (subjectLevelExpr classifierLevelExpr : LevelExpr) (flag : UniverseFlag)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (universeCodeCell subjectLevelExpr flag) (universeCodeCell classifierLevelExpr flag) :=
  typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    context subjectLevelExpr classifierLevelExpr flag
    (fun _substitution _envWithTypeValueCandidates _predLevel _typeCode typeCodeNormalizing
        typeCodeReducibleAtLevel =>
      let ⟨_candidate, candidateReducibleAtLevel⟩ := typeCodeReducibleAtLevel
      allReducibleTypesHaveTypeValueCandidates.reducibleTypeAtExtendsToAllLevels
        typeCodeNormalizing candidateReducibleAtLevel)

/-- **Bundled universe validity from type-value completion.**  This is the universe-formation validity arm
the dependent fundamental theorem can consume once it assumes the global type-value completion principle,
with no separate lower-fuel extension parameter. -/
theorem fundamentalUniverseValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    FundamentalValidityWithTypeValueCandidates context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  fundamentalUniverseValidityWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
    context levelExpr flag
    (fun _substitution _envWithTypeValueCandidates _predLevel _typeCode typeCodeNormalizing
        typeCodeReducibleAtLevel =>
      let ⟨_candidate, candidateReducibleAtLevel⟩ := typeCodeReducibleAtLevel
      allReducibleTypesHaveTypeValueCandidates.reducibleTypeAtExtendsToAllLevels
        typeCodeNormalizing candidateReducibleAtLevel)

/-- **Universe-code positive candidate from positive-member extension.**  The statement is fully
multi-universe: every syntactic level expression and universe flag is accepted.  The operational
positive-member-extension premise supplies the lower-fuel extension bridge required by the Tarski universe
candidate. -/
theorem positiveCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    PositiveCandidateConclusionWithTypeValueCandidates context (universeCodeCell levelExpr flag) :=
  positiveCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    context levelExpr flag
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates

/-- **Universe-code type-value payload from positive-member extension.**  This is the universe-parametric
type-value half for arbitrary `Type@levelExpr`/flag cells, stated against the operational member-extension
bridge. -/
theorem typeValueCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (subjectLevelExpr classifierLevelExpr : LevelExpr) (flag : UniverseFlag)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    TypeValueCandidateConclusionWithTypeValueCandidates context
      (universeCodeCell subjectLevelExpr flag) (universeCodeCell classifierLevelExpr flag) :=
  typeValueCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    context subjectLevelExpr classifierLevelExpr flag
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates

/-- **Bundled universe validity from positive-member extension.**  This is the direct multi-universe
universe-formation arm for the type-value FT interface: member reducibility is ordinary universe formation,
and the type-value half is discharged by positive-member extension. -/
theorem fundamentalUniverseValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    FundamentalValidityWithTypeValueCandidates context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  fundamentalUniverseValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    context levelExpr flag
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates

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

/-- **Bundled conversion validity from type-value completion.**  The member half is the semantic conversion
rule.  The type-value half is derived generically: if the substituted reclassifier is a universe code, the
converted subject member conclusion can be run at every positive fuel, and the completion principle turns
that all-positive universe membership into the required type-value payload. -/
theorem fundamentalConvValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionWithTypeValueCandidates context reclassifier
        (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalValidityWithTypeValueCandidates context subject reclassifier :=
  FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
    (fundamentalConvWithTypeValueCandidates subjectFundamental reclassifierFundamental converts)
    allReducibleTypesHaveTypeValueCandidates

/-- **Bundled conversion validity from positive-member extension.**  The conversion member rule is unchanged;
the type-value payload is supplied by the operational member-extension bridge. -/
theorem fundamentalConvValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (subjectFundamental :
      FundamentalConclusionWithTypeValueCandidates context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionWithTypeValueCandidates context reclassifier
        (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalValidityWithTypeValueCandidates context subject reclassifier :=
  fundamentalConvValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    subjectFundamental reclassifierFundamental converts

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

/-- **Dependent application validity from type-value completion.**  The member half is the usual semantic
application.  The type-value half no longer needs a bespoke result premise: if the instantiated codomain is
a universe code after substitution, the member half supplies all-positive universe membership of the
application result, and the global completion principle turns that membership into the required type-value
candidate payload. -/
theorem fundamentalPiElimValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (functionFundamental :
      FundamentalConclusionWithTypeValueCandidates context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentFundamental :
      FundamentalConclusionWithTypeValueCandidates context argument domainCode) :
    FundamentalValidityWithTypeValueCandidates context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
    (fundamentalPiElimWithTypeValueCandidates functionFundamental argumentFundamental)
    allReducibleTypesHaveTypeValueCandidates

/-- **Dependent application validity from positive-member extension.**  This exposes the application arm
against the operational type-value bridge directly. -/
theorem fundamentalPiElimValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (functionFundamental :
      FundamentalConclusionWithTypeValueCandidates context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentFundamental :
      FundamentalConclusionWithTypeValueCandidates context argument domainCode) :
    FundamentalValidityWithTypeValueCandidates context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  fundamentalPiElimValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    functionFundamental argumentFundamental

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

/-- **Dependent lambda introduction with the decoded domain candidate exposed to the type-value premise.**
This is the recursor-facing variant of `fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise`:
the extra universe-domain value premise receives the actual decoded domain reducibility witness, not just
membership in an abstract candidate.  That shape lets universe-domain wrappers derive the payload from the
domain positive-candidate companion plus `HasTypeValueCandidatesForAllPositiveUniverseMembers`. -/
theorem fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise
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
        (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
        {argument : RawTerm (targetScope + 1)},
          ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) candidate →
            candidate argument →
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
          envWithTypeValueCandidates predLevel domainReducible argumentInDomain)
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
          envWithTypeValueCandidates predLevel domainReducible argumentInDomain)
    rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
      ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
    exact bodyFundamental (RawTermSubst.cons argument substitution)
      extendedEnvWithTypeValueCandidates predLevel

/-- **Bundled lambda-introduction validity with the decoded domain candidate exposed.**  The member half uses
`fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise`; the type-value half is again syntactic,
because a substituted Pi classifier cannot be a universe code. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
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
        (predLevel : Nat) {candidate : RawTerm (targetScope + 1) → Prop}
        {argument : RawTerm (targetScope + 1)},
          ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) candidate →
            candidate argument →
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
  ⟨fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise
      domainFundamental domainHasPositiveCandidate
      argumentValueHasPositiveCandidateWhenDomainIsUniverse codomainFundamental bodyFundamental,
    TypeValueCandidateConclusionWithTypeValueCandidates.ofSubstitutedClassifierNeUniverse
      (fun {_targetScope} substitution {levelExpr} {flag} classifierSubstIsUniverse =>
        substitutedPiTyCode_ne_universeCodeCell substitution domainCode codomainCode
          levelExpr flag classifierSubstIsUniverse)⟩

/-- **Generic dependent lambda-introduction validity from type-value completion.**  This is the
recursor-facing binder arm for the bundled type-value FT: the domain recursive IH is a bundled validity
proof for `domainCode : Type@domainLevel`, so its type-value half recovers the positive-candidate companion
for the domain.  Any accepted argument is therefore promoted to all-positive membership in the substituted
domain; if that substituted domain is itself a universe code, the global completion principle supplies the
type-value payload needed to extend the proof-relevant environment under the binder.  No syntactic
restriction is placed on the domain code. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) body codomainCode) :
    FundamentalValidityWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  let domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier domainValidity
  let universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers :=
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
      allReducibleTypesHaveTypeValueCandidates
  exact fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
    domainValidity.memberConclusion
    domainHasPositiveCandidate
    (fun {_targetScope} substitution envWithTypeValueCandidates predLevel {_candidate} {argument}
        domainReducible argumentInDomain {_levelExpr} {_domainFlag}
        substitutedDomainIsUniverse candidatePredLevel =>
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument :=
        PositiveCandidateConclusionWithTypeValueCandidates.memberExtendsToAllPositive
          domainHasPositiveCandidate substitution envWithTypeValueCandidates predLevel
          domainReducible argumentInDomain
      HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
        universeMembersHaveTypeValueCandidates substitution argumentAtAllPositiveLevels
        substitutedDomainIsUniverse candidatePredLevel)
    codomainValidity.memberConclusion bodyValidity.memberConclusion

/-- **Generic dependent lambda-introduction validity from positive-member extension.**  This is the direct
operational-premise form of the bundled lambda arm: the domain type-value payload still comes from the
domain validity proof, while any universe-valued binder argument is completed by positive-member extension. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) body codomainCode) :
    FundamentalValidityWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell domainCode codomainCode) :=
  fundamentalPiIntroValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    domainValidity codomainValidity bodyValidity

/-- **Universe-domain lambda introduction from the global universe-member type-value principle.**  When the
domain is syntactically a universe code, any decoded domain argument can first be strengthened to all-positive
universe membership by the domain positive-candidate companion; the global multi-universe principle then
turns that semantic universe member into the type-value payload required by the cons environment. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode body : RawTerm (scope + 1)}
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) body codomainCode) :
    FundamentalValidityWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode) :=
  fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
    domainFundamental domainHasPositiveCandidate
    (fun {_targetScope} substitution envWithTypeValueCandidates predLevel {_candidate} {argument}
        domainReducible argumentInDomain {_levelExpr} {_domainFlag}
        substitutedDomainIsUniverse candidatePredLevel =>
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution (universeCodeCell domainLevel flag)) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidate substitution envWithTypeValueCandidates predLevel)
          domainReducible argumentInDomain
      universeMembersHaveTypeValueCandidates.ofSubstitutedUniverseDomainMember
        substitution argumentAtAllPositiveLevels substitutedDomainIsUniverse candidatePredLevel)
    codomainFundamental bodyFundamental

/-- **Universe-domain lambda introduction from type-value completion.**  This is the direct completion
principle version of `fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain`: the global
all-reducible-types payload is converted once to the all-positive-universe-member payload needed to extend
the binder environment. -/
theorem fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode body : RawTerm (scope + 1)}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) body codomainCode) :
    FundamentalValidityWithTypeValueCandidates context (lamCell body)
      (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode) :=
  fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain
    allReducibleTypesHaveTypeValueCandidates.toUniverseMembers
    domainFundamental domainHasPositiveCandidate codomainFundamental bodyFundamental

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

/-- **Generic Pi-formation validity from type-value completion.**  This is the recursor-facing Π-former
arm for arbitrary domains: bundled validity of `domainCode : Type@domainLevel` supplies the positive
domain-candidate companion; the global type-value completion principle supplies the binder value payload
whenever a substituted domain is syntactically a universe; bundled codomain validity supplies both the
member and positive-candidate halves for `codomainCode : Type@codomainLevel`.

The one premise left explicit is the base-level codomain member premise.  This is intentional and
soundness-critical: at fuel zero an arbitrary domain can have members, so no universe-domain
`no-member-at-zero` contradiction is available. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  let domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier domainValidity
  let codomainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier codomainValidity
  let universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers :=
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
      allReducibleTypesHaveTypeValueCandidates
  exact fundamentalPiFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainValidity.memberConclusion
    domainHasPositiveCandidate
    (fun {_targetScope} substitution envWithTypeValueCandidates argument argumentAtAllPositiveLevels
        {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
      HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
        universeMembersHaveTypeValueCandidates substitution argumentAtAllPositiveLevels
        substitutedDomainIsUniverse candidatePredLevel)
    codomainMemberAtDomainLevel codomainValidity.memberConclusion codomainHasPositiveCandidate

/-- **Generic Sigma-formation validity from type-value completion.**  The Sigma twin of
`fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates`.
Sigma's type-value half is neutral-data-former reducibility, so the codomain validity is consumed only for
the member half; the argument value payload is still supplied uniformly by the global type-value completion
principle.  The base-level codomain member premise remains explicit for the same fuel-zero reason as in the
Π theorem. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  let domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier domainValidity
  let universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers :=
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
      allReducibleTypesHaveTypeValueCandidates
  exact fundamentalSigmaFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
    domainValidity.memberConclusion
    domainHasPositiveCandidate
    (fun {_targetScope} substitution envWithTypeValueCandidates argument argumentAtAllPositiveLevels
        {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
      HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
        universeMembersHaveTypeValueCandidates substitution argumentAtAllPositiveLevels
        substitutedDomainIsUniverse candidatePredLevel)
    codomainMemberAtDomainLevel codomainValidity.memberConclusion

/-- **Generic Π-formation validity from positive-member extension.**  The base-level codomain premise
remains explicit for the same reason as in the completion-theorem version; positive-member extension
supplies the universe-valued argument payload. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    domainValidity codomainMemberAtDomainLevel codomainValidity

/-- **Generic Sigma-formation validity from positive-member extension.**  The Sigma type-value half remains
neutral-data-former reducibility; positive-member extension supplies the universe-valued argument payload
used while extending the proof-relevant environment. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (codomainMemberAtDomainLevel :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
        IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
          (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    domainValidity codomainMemberAtDomainLevel codomainValidity

/-- **Base-level codomain premise from a fuel-zero-empty domain.**  This is the reusable form of the
universe-domain trick: if the substituted domain has no members at fuel zero, then the base-level branch of
former-child reducibility is discharged by contradiction.  At successor fuel, the domain positive-candidate
companion upgrades the argument to all-positive membership, the caller's type-value payload extends the
environment, and the codomain recursive premise runs one level up. -/
theorem codomainMemberAtDomainLevelWithTypeValueCandidatesFromNoZeroDomain
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode)
    (domainHasNoMemberAtZero :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt 0 (RawTerm.subst substitution domainCode) argument → False)
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
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
      (predLevel : Nat) (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt predLevel (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode) := by
  intro _targetScope substitution envWithTypeValueCandidates predLevel argument argumentMember
  cases predLevel with
  | zero =>
      exact False.elim
        (domainHasNoMemberAtZero substitution envWithTypeValueCandidates argument argumentMember)
  | succ memberPredLevel =>
      obtain ⟨domainCandidate, domainReducible, argumentInDomain⟩ := argumentMember
      have argumentAtAllPositiveLevels :
          IsReducibleMemberAtAllPositiveLevels
            (RawTerm.subst substitution domainCode) argument :=
        HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
          (domainHasPositiveCandidate substitution envWithTypeValueCandidates memberPredLevel)
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
        extendedEnvWithTypeValueCandidates (memberPredLevel + 1)

/-- **Generic Pi-formation validity for fuel-zero-empty domains.**  This specializes the arbitrary-domain
type-value-completion former arm by deriving the base-level codomain premise from `domainHasNoMemberAtZero`.
It strictly generalizes the syntactic universe-domain wrapper without claiming all domains satisfy the
fuel-zero emptiness property. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesFromNoZeroDomainAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasNoMemberAtZero :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt 0 (RawTerm.subst substitution domainCode) argument → False)
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  let domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier domainValidity
  let universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers :=
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
      allReducibleTypesHaveTypeValueCandidates
  exact fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates domainValidity
    (codomainMemberAtDomainLevelWithTypeValueCandidatesFromNoZeroDomain
      domainHasPositiveCandidate domainHasNoMemberAtZero
      (fun {_targetScope} substitution envWithTypeValueCandidates argument argumentAtAllPositiveLevels
          {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
        HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
          universeMembersHaveTypeValueCandidates substitution argumentAtAllPositiveLevels
          substitutedDomainIsUniverse candidatePredLevel)
      codomainValidity.memberConclusion)
    codomainValidity

/-- **Generic Sigma-formation validity for fuel-zero-empty domains.**  Sigma's no-zero-domain wrapper,
parallel to `fundamentalPiFormationValidityWithTypeValueCandidatesFromNoZeroDomainAllReducibleTypesHaveTypeValueCandidates`. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesFromNoZeroDomainAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainValidity :
      FundamentalValidityWithTypeValueCandidates context domainCode
        (universeCodeCell domainLevel flag))
    (domainHasNoMemberAtZero :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
        (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt 0 (RawTerm.subst substitution domainCode) argument → False)
    (codomainValidity :
      FundamentalValidityWithTypeValueCandidates (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  let domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context domainCode :=
    FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier domainValidity
  let universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers :=
    HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
      allReducibleTypesHaveTypeValueCandidates
  exact fundamentalSigmaFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates domainValidity
    (codomainMemberAtDomainLevelWithTypeValueCandidatesFromNoZeroDomain
      domainHasPositiveCandidate domainHasNoMemberAtZero
      (fun {_targetScope} substitution envWithTypeValueCandidates argument argumentAtAllPositiveLevels
          {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
        HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
          universeMembersHaveTypeValueCandidates substitution argumentAtAllPositiveLevels
          substitutedDomainIsUniverse candidatePredLevel)
      codomainValidity.memberConclusion)
    codomainValidity

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

/-- **Bundled Pi-formation validity for a universe-code domain from the global universe-member type-value
principle.**  This removes the repeated explicit argument-payload premise from
`fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain`: all-positive members of the
universe domain are converted to type-value candidates by the named multi-universe principle. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
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
  fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate
    (fun {_targetScope} substitution _envWithTypeValueCandidates _argument argumentAtAllPositiveLevels
        {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
      universeMembersHaveTypeValueCandidates.ofSubstitutedUniverseDomainMember
        substitution argumentAtAllPositiveLevels substitutedDomainIsUniverse candidatePredLevel)
    codomainFundamental codomainHasPositiveCandidate

/-- **Bundled Sigma-formation validity for a universe-code domain from the global universe-member type-value
principle.**  The member half uses the same universe-domain child bundle as Pi formation; Sigma's type-value
half remains the neutral Sigma positive-candidate theorem. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (universeMembersHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllPositiveUniverseMembers)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomain
    domainFundamental domainHasPositiveCandidate
    (fun {_targetScope} substitution _envWithTypeValueCandidates _argument argumentAtAllPositiveLevels
        {_levelExpr} {_domainFlag} substitutedDomainIsUniverse candidatePredLevel =>
      universeMembersHaveTypeValueCandidates.ofSubstitutedUniverseDomainMember
        substitution argumentAtAllPositiveLevels substitutedDomainIsUniverse candidatePredLevel)
    codomainFundamental

/-- **Pi-formation validity for a universe-code domain from type-value completion.**  Direct wrapper around
`fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates`,
using the completion principle's universe-member projection. -/
theorem fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
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
  fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates.toUniverseMembers
    domainFundamental domainHasPositiveCandidate codomainFundamental codomainHasPositiveCandidate

/-- **Sigma-formation validity for a universe-code domain from type-value completion.**  Direct wrapper
around the universe-member-payload version, again making the completion principle the single global
semantic hypothesis. -/
theorem fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {codomainCode : RawTerm (scope + 1)}
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels)
    (domainFundamental :
      FundamentalConclusionWithTypeValueCandidates context (universeCodeCell domainLevel flag)
        (universeCodeCell domainLevel.lsucc flag))
    (domainHasPositiveCandidate :
      PositiveCandidateConclusionWithTypeValueCandidates context
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionWithTypeValueCandidates
        (context.cons (universeCodeCell domainLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    FundamentalValidityWithTypeValueCandidates context
      (sigmaTyCodeCell (universeCodeCell domainLevel flag) codomainCode)
      (universeCodeCell formerLevel flag) :=
  fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
    allReducibleTypesHaveTypeValueCandidates.toUniverseMembers
    domainFundamental domainHasPositiveCandidate codomainFundamental

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

import FX1Poly.Typed.FundamentalWithPositiveTypeCandidates
import FX1Poly.Typed.FundamentalWithTypeValueCandidates
import FX1Poly.Typed.HasTypeDescPiFundamentalVectorFromFormation
import FX1Poly.Typed.HasTypeDescPiValidity

/-! # FX1Poly/Typed/HasTypeDescPiStronglyNormalizingFromFundamental
    — dependent strong-normalization handoff from the exact all-level fundamental theorem

The grown description engine's strong-normalization target should depend on the real all-level fundamental
theorem shape:

`HasTypeDescPi ... subject classifier -> FundamentalConclusionAtAll context subject classifier`.

The older `...FromFormation` corollaries in `HasTypeDescPiFundamentalVectorFromFormation` route through an
explicit formation-engine VECTOR premise.  That theorem is useful as a conditional recursor assembly, but
the vector premise is deliberately too strong to be the final formation theorem.  This file exposes the
downstream strong-normalization handoff against the correct final interface: once a caller supplies the
all-level fundamental conclusion for a derivation, CR1 gives strong normalization immediately.  No roadmap
label is encoded in the declarations.

## Zero-axiom verification

The substituted theorem is one projection through `IsReducibleMemberAt.stronglyNormalizing`; the closed
theorem reuses the same empty-substitution/rename reflection already used by the conditional corollary.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Foundation

/-- **The exact all-level fundamental theorem interface for `HasTypeDescPi`.**  This is the theorem shape the
dependent strong-normalization handoff consumes: every grown typing derivation has an all-level reducibility
conclusion under every closing reducible substitution. -/
def HasTypeDescPiAllLevelFundamentalTheorem (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeDescPi profile context subject classifier →
      FundamentalConclusionAtAll context subject classifier

/-- **The strengthened positive-candidate fundamental theorem interface for `HasTypeDescPi`.**  This is the
proof-relevant theorem shape used by the binder-facing development: every grown typing derivation has the
strengthened reducibility conclusion under closing substitutions whose environments also carry positive
type-candidate companions for context bindings. -/
def HasTypeDescPiPositiveCandidateFundamentalTheorem (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeDescPi profile context subject classifier →
      FundamentalConclusionWithPositiveTypeCandidates context subject classifier

/-- **The bundled type-value-candidate fundamental theorem interface for `HasTypeDescPi`.**  This is the
stronger theorem shape used by the universe-polymorphic/type-variable development: every grown typing
derivation returns ordinary member reducibility together with the conditional type-value candidate payload.
Universe levels are not collapsed to one object here; `subject` and `classifier` range over arbitrary raw
codes, including `universeCodeCell levelExpr flag` for every syntactic `LevelExpr` and `UniverseFlag`. -/
def HasTypeDescPiTypeValueCandidateFundamentalTheorem (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeDescPi profile context subject classifier →
      FundamentalValidityWithTypeValueCandidates context subject classifier

/-- **Substituted strong-normalization theorem interface for `HasTypeDescPi`.**  A profile has substituted
strong normalization when every grown typing derivation in a well-formed context sends both its subject and
its classifier to strongly normalizing terms under every all-level reducible closing substitution. -/
def HasTypeDescPiSubstitutedStrongNormalizationTheorem (profile : PolyProfile) : Prop :=
  ∀ {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    WfContext context →
      HasTypeDescPi profile context subject classifier →
        ∀ (substitution : RawTermSubst scope (targetScope + 1)),
          ReducibleEnvAtAllLevels context substitution →
            ∀ _predLevel : Nat,
              IsStronglyNormalizing (RawTerm.subst substitution subject) ∧
                IsStronglyNormalizing (RawTerm.subst substitution classifier)

/-- **Substituted strong-normalization theorem interface for the strengthened positive-candidate
environment.**  This is the nonempty-context downstream shape of the proof-relevant FT: a caller supplies
the strengthened closing environment, and both the substituted subject and classifier strongly normalize. -/
def HasTypeDescPiPositiveCandidateSubstitutedStrongNormalizationTheorem
    (profile : PolyProfile) : Prop :=
  ∀ {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    WfContext context →
      HasTypeDescPi profile context subject classifier →
        ∀ (substitution : RawTermSubst scope (targetScope + 1)),
          ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution →
            ∀ _predLevel : Nat,
              IsStronglyNormalizing (RawTerm.subst substitution subject) ∧
                IsStronglyNormalizing (RawTerm.subst substitution classifier)

/-- **Substituted strong-normalization theorem interface for the bundled type-value-candidate environment.**
This is the downstream shape of the strongest current FT interface: a caller supplies the proof-relevant
environment carrying binding-type and type-variable value candidates, and both the substituted subject and
classifier strongly normalize. -/
def HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem
    (profile : PolyProfile) : Prop :=
  ∀ {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    WfContext context →
      HasTypeDescPi profile context subject classifier →
        ∀ (substitution : RawTermSubst scope (targetScope + 1)),
          ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution →
            ∀ _predLevel : Nat,
              IsStronglyNormalizing (RawTerm.subst substitution subject) ∧
                IsStronglyNormalizing (RawTerm.subst substitution classifier)

/-- **Closed strong-normalization theorem interface for `HasTypeDescPi`.**  A profile has closed strong
normalization when every closed grown typing derivation has a strongly normalizing subject and classifier. -/
def HasTypeDescPiClosedStrongNormalizationTheorem (profile : PolyProfile) : Prop :=
  ∀ {subject classifier : RawTerm 0},
    HasTypeDescPi profile TypingContext.empty subject classifier →
      IsStronglyNormalizing subject ∧ IsStronglyNormalizing classifier

/-- **Bundled multi-universe reducibility and strong normalization theorem.**  This is the exported
metatheory package for the grown dependent typing judgment once the type-value boundary is available:

* the full type-value-candidate fundamental theorem;
* substituted strong normalization under proof-relevant type-value environments; and
* closed subject/classifier strong normalization.

The package is deliberately a theorem interface, not a certificate for the decidable formation checker.
It ranges over arbitrary `LevelExpr`/`UniverseFlag` through the type-value fundamental theorem, and it
does not encode any roadmap label in the declaration name. -/
def HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem
    (profile : PolyProfile) : Prop :=
  HasTypeDescPiTypeValueCandidateFundamentalTheorem profile ∧
    HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem profile ∧
      HasTypeDescPiClosedStrongNormalizationTheorem profile

/-- Project the type-value fundamental theorem from the bundled metatheory package. -/
theorem HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.fundamentalTheorem
    {profile : PolyProfile}
    (metatheory :
      HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile) :
    HasTypeDescPiTypeValueCandidateFundamentalTheorem profile :=
  metatheory.1

/-- Project substituted strong normalization from the bundled metatheory package. -/
theorem HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.substitutedStrongNormalizationTheorem
    {profile : PolyProfile}
    (metatheory :
      HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile) :
    HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem profile :=
  metatheory.2.1

/-- Project closed strong normalization from the bundled metatheory package. -/
theorem HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.closedStrongNormalizationTheorem
    {profile : PolyProfile}
    (metatheory :
      HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile) :
    HasTypeDescPiClosedStrongNormalizationTheorem profile :=
  metatheory.2.2

/-- **Type-value validity from an all-level member theorem plus type-value completion.**  An exact
all-level fundamental conclusion already supplies ordinary member reducibility under the stronger
type-value environment by forgetting that environment to its all-level projection.  The only additional
payload needed for bundled type-value validity is the global multi-universe type-value completion principle,
which turns all-positive universe membership into the all-positive candidate carried by type values.

This bridge is deliberately generic: it removes the need to duplicate a full `HasTypeDescPi` recursor for
the type-value motive once the exact all-level fundamental theorem is available. -/
theorem FundamentalConclusionAtAll.toTypeValueCandidateValidityOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectFundamental : FundamentalConclusionAtAll context subject classifier)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    FundamentalValidityWithTypeValueCandidates context subject classifier := by
  refine
    FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
      ?subjectFundamentalWithTypeValueCandidates allReducibleTypesHaveTypeValueCandidates
  intro _targetScope substitution envWithTypeValueCandidates predLevel
  exact subjectFundamental substitution envWithTypeValueCandidates.toAllLevels predLevel

/-- **Promote the exact all-level `HasTypeDescPi` fundamental theorem to the bundled type-value interface.**
The theorem remains fully multi-universe: the completion hypothesis quantifies over every raw type code,
and the type-value payload is conditional on arbitrary substituted universe classifiers
`universeCodeCell levelExpr flag`. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    HasTypeDescPiTypeValueCandidateFundamentalTheorem profile := by
  intro _scope _context _subject _classifier typed
  exact
    FundamentalConclusionAtAll.toTypeValueCandidateValidityOfAllReducibleTypesHaveTypeValueCandidates
      (fundamentalTheorem typed) allReducibleTypesHaveTypeValueCandidates

/-- **Promote the exact all-level `HasTypeDescPi` fundamental theorem using positive-member extension.**
The positive-member-extension premise is the operational binder/telescope bridge: a member of a strongly
normalizing type reducible at every fuel extends from one positive fuel to all positive fuels.  The candidate
formulation used by the bundled type-value interface is equivalent to it, so this theorem exposes the
sharper premise directly instead of forcing callers to package it manually. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfPositiveMemberExtension
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    HasTypeDescPiTypeValueCandidateFundamentalTheorem profile :=
  HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
    fundamentalTheorem
    (hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension.mpr
      positiveMemberExtension)

/-- **Substituted strong normalization from an all-level fundamental conclusion.**  This is the exact CR1
handoff for the dependent `HasTypeDescPi` theorem: after a closing substitution into a positive target
scope, the substituted subject strongly normalizes whenever the derivation's all-level fundamental
conclusion is available. -/
theorem HasTypeDescPi.subjectStronglyNormalizingFromFundamentalAtAll {profile : PolyProfile}
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (_typed : HasTypeDescPi profile context subject classifier)
    (subjectFundamental : FundamentalConclusionAtAll context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (subjectFundamental substitution env predLevel).stronglyNormalizing

/-- **Closed reducibility from an all-level fundamental conclusion.**  In the empty context, the all-level
environment is vacuous, so a closed grown derivation's fundamental conclusion immediately yields closed
semantic membership under any closing substitution. -/
theorem HasTypeDescPi.closedSubjectReducibleUnderSubstFromFundamentalAtAll {profile : PolyProfile}
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (_typed : HasTypeDescPi profile TypingContext.empty subject classifier)
    (subjectFundamental :
      FundamentalConclusionAtAll
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  subjectFundamental substitution (ReducibleEnvAtAllLevels.empty substitution) predLevel

/-- **Closed substituted strong normalization from an all-level fundamental conclusion.**  The CR1
projection of `closedSubjectReducibleUnderSubstFromFundamentalAtAll`. -/
theorem HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFundamentalAtAll {profile : PolyProfile}
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier)
    (subjectFundamental :
      FundamentalConclusionAtAll
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (HasTypeDescPi.closedSubjectReducibleUnderSubstFromFundamentalAtAll
    substitution predLevel typed subjectFundamental).stronglyNormalizing

/-- **Closed strong normalization from an all-level fundamental conclusion.**  This is the final downstream
shape for the grown description engine: once the real all-level fundamental theorem supplies
`subjectFundamental`, a closed subject is strongly normalizing. -/
theorem HasTypeDescPi.closedSubjectStronglyNormalizingFromFundamentalAtAll {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier)
    (subjectFundamental :
      FundamentalConclusionAtAll
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing subject := by
  let emptyRenaming : RawRenaming 0 1 := fun emptyIndex => emptyIndex.elim0
  let emptySubstitution : RawTermSubst 0 1 :=
    RawRenaming.thenSubst emptyRenaming (RawTermSubst.identity : RawTermSubst 1 1)
  have subjectNormalizing :
      IsStronglyNormalizing (RawTerm.subst emptySubstitution subject) :=
    HasTypeDescPi.subjectStronglyNormalizingFromFundamentalAtAll
      typed subjectFundamental emptySubstitution
      (ReducibleEnvAtAllLevels.empty emptySubstitution) 0
  have renamedSubjectNormalizing :
      IsStronglyNormalizing (RawTerm.rename emptyRenaming subject) := by
    rw [← RawTerm.subst_identity_apply (RawTerm.rename emptyRenaming subject)]
    rwa [RawTerm.rename_subst_commute emptyRenaming
      (RawTermSubst.identity : RawTermSubst 1 1) subject]
  exact StepStar.isStronglyNormalizing_of_rename emptyRenaming renamedSubjectNormalizing

/-- **Substituted strong normalization from the all-level fundamental theorem.**  Once the exact
`HasTypeDescPi` fundamental theorem is available as a function, this theorem packages the CR1 projection in
the substituted setting. -/
theorem HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  HasTypeDescPi.subjectStronglyNormalizingFromFundamentalAtAll typed
    (fundamentalTheorem typed) substitution reducibleEnv predLevel

/-- **Substituted classifier strong normalization from the all-level fundamental theorem.**  Validity turns
the classifier of a grown typing derivation into a grown type, and the exact all-level fundamental theorem
then applies to that classifier-as-subject.  This is the classifier-side CR1 handoff needed by typed
conversion/canonicity after the unconditional FT lands. -/
theorem HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc contextWellFormed
  exact HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
    fundamentalTheorem classifierTyped substitution reducibleEnv predLevel

/-- **Substituted subject strong normalization from the strengthened positive-candidate fundamental
theorem.**  CR1 projects the subject out of the strengthened reducibility conclusion under the caller's
proof-relevant closing environment. -/
theorem HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (fundamentalTheorem typed substitution envWithCandidates predLevel).stronglyNormalizing

/-- **Substituted classifier strong normalization from the strengthened positive-candidate fundamental
theorem.**  Validity turns the classifier into a grown type; the strengthened FT then normalizes that
classifier-as-subject under the SAME strengthened environment. -/
theorem HasTypeDescPi.classifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc contextWellFormed
  exact HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    fundamentalTheorem classifierTyped substitution envWithCandidates predLevel

/-- **Substituted subject strong normalization from the bundled type-value-candidate fundamental theorem.**
CR1 projects through the member component of the bundled validity result; the extra type-value component
stays present in the theorem interface for universe-polymorphic/type-variable consumers. -/
theorem HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (FundamentalValidityWithTypeValueCandidates.memberConclusion (fundamentalTheorem typed)
    substitution envWithTypeValueCandidates predLevel).stronglyNormalizing

/-- **Substituted classifier strong normalization from the bundled type-value-candidate fundamental theorem.**
Validity turns the classifier into a grown type, and the same bundled theorem normalizes that
classifier-as-subject under the same strengthened environment. -/
theorem HasTypeDescPi.classifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    (substitution : RawTermSubst scope (targetScope + 1))
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (predLevel : Nat) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc contextWellFormed
  exact HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    fundamentalTheorem classifierTyped substitution envWithTypeValueCandidates predLevel

/-- **Closed reducibility from the all-level fundamental theorem.**  Empty contexts have a vacuous all-level
environment, so the exact fundamental theorem immediately yields closed reducibility under any closing
substitution. -/
theorem HasTypeDescPi.closedSubjectReducibleUnderSubstFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  HasTypeDescPi.closedSubjectReducibleUnderSubstFromFundamentalAtAll
    substitution predLevel typed (fundamentalTheorem typed)

/-- **Closed substituted strong normalization from the all-level fundamental theorem.** -/
theorem HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFundamentalAtAll
    substitution predLevel typed (fundamentalTheorem typed)

/-- **Closed substituted classifier strong normalization from the all-level fundamental theorem.** -/
theorem HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) :=
  HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
    fundamentalTheorem (WfContext.emptyIsWellFormed (profile := profile)) typed
    substitution (ReducibleEnvAtAllLevels.empty substitution) predLevel

/-- **Closed strong normalization from the all-level fundamental theorem.**  This is the downstream final
shape for full `HasTypeDescPi` strong normalization once the unconditional all-level FT is supplied. -/
theorem HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing subject :=
  HasTypeDescPi.closedSubjectStronglyNormalizingFromFundamentalAtAll typed
    (fundamentalTheorem typed)

/-- **Closed classifier strong normalization from the all-level fundamental theorem.**  The closed classifier
is a grown type by validity, so the same closed-SN corollary applies to the classifier-as-subject. -/
theorem HasTypeDescPi.closedClassifierStronglyNormalizingFromAllLevelFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing classifier := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc (WfContext.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
    fundamentalTheorem classifierTyped

/-- **Closed reducibility from the strengthened positive-candidate fundamental theorem.**  Empty contexts
have a vacuous strengthened environment, so the proof-relevant FT interface immediately yields closed
semantic membership under any closing substitution.  This is intentionally a CLOSED handoff: a nonempty
substituted handoff would need a caller-supplied strengthened environment, not merely an ordinary all-level
environment. -/
theorem HasTypeDescPi.closedSubjectReducibleUnderSubstFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  fundamentalTheorem typed substitution
    (ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.empty substitution) predLevel

/-- **Closed substituted subject strong normalization from the strengthened positive-candidate fundamental
theorem.** -/
theorem HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (HasTypeDescPi.closedSubjectReducibleUnderSubstFromPositiveCandidateFundamentalTheorem
    fundamentalTheorem substitution predLevel typed).stronglyNormalizing

/-- **Closed substituted classifier strong normalization from the strengthened positive-candidate
fundamental theorem.**  Validity turns the classifier into a grown type, then the same strengthened
fundamental theorem applies to it as a subject. -/
theorem HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc (WfContext.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    fundamentalTheorem substitution predLevel classifierTyped

/-- **Closed subject strong normalization from the strengthened positive-candidate fundamental theorem.** -/
theorem HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing subject := by
  let emptyRenaming : RawRenaming 0 1 := fun emptyIndex => emptyIndex.elim0
  let emptySubstitution : RawTermSubst 0 1 :=
    RawRenaming.thenSubst emptyRenaming (RawTermSubst.identity : RawTermSubst 1 1)
  have subjectNormalizing :
      IsStronglyNormalizing (RawTerm.subst emptySubstitution subject) :=
    HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
      fundamentalTheorem emptySubstitution 0 typed
  have renamedSubjectNormalizing :
      IsStronglyNormalizing (RawTerm.rename emptyRenaming subject) := by
    rw [← RawTerm.subst_identity_apply (RawTerm.rename emptyRenaming subject)]
    rwa [RawTerm.rename_subst_commute emptyRenaming
      (RawTermSubst.identity : RawTermSubst 1 1) subject]
  exact StepStar.isStronglyNormalizing_of_rename emptyRenaming renamedSubjectNormalizing

/-- **Closed classifier strong normalization from the strengthened positive-candidate fundamental theorem.**
Validity turns the closed classifier into a grown type, then the closed subject theorem applies. -/
theorem HasTypeDescPi.closedClassifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing classifier := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc (WfContext.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
    fundamentalTheorem classifierTyped

/-- **Closed reducibility from the bundled type-value-candidate fundamental theorem.**  Empty contexts
have a vacuous type-value-candidate environment, so the strongest proof-relevant FT interface immediately
specializes to closed semantic membership under any closing substitution. -/
theorem HasTypeDescPi.closedSubjectReducibleUnderSubstFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  FundamentalValidityWithTypeValueCandidates.memberConclusion (fundamentalTheorem typed)
    substitution (ReducibleEnvAtAllLevelsWithTypeValueCandidates.empty substitution) predLevel

/-- **Closed substituted subject strong normalization from the bundled type-value-candidate fundamental
theorem.** -/
theorem HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution subject) :=
  (HasTypeDescPi.closedSubjectReducibleUnderSubstFromTypeValueCandidateFundamentalTheorem
    fundamentalTheorem substitution predLevel typed).stronglyNormalizing

/-- **Closed substituted classifier strong normalization from the bundled type-value-candidate fundamental
theorem.**  Validity turns the classifier into a grown type, then the same bundled theorem applies to that
classifier-as-subject. -/
theorem HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing (RawTerm.subst substitution classifier) := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc (WfContext.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    fundamentalTheorem substitution predLevel classifierTyped

/-- **Closed subject strong normalization from the bundled type-value-candidate fundamental theorem.** -/
theorem HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing subject := by
  let emptyRenaming : RawRenaming 0 1 := fun emptyIndex => emptyIndex.elim0
  let emptySubstitution : RawTermSubst 0 1 :=
    RawRenaming.thenSubst emptyRenaming (RawTermSubst.identity : RawTermSubst 1 1)
  have subjectNormalizing :
      IsStronglyNormalizing (RawTerm.subst emptySubstitution subject) :=
    HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
      fundamentalTheorem emptySubstitution 0 typed
  have renamedSubjectNormalizing :
      IsStronglyNormalizing (RawTerm.rename emptyRenaming subject) := by
    rw [← RawTerm.subst_identity_apply (RawTerm.rename emptyRenaming subject)]
    rwa [RawTerm.rename_subst_commute emptyRenaming
      (RawTermSubst.identity : RawTermSubst 1 1) subject]
  exact StepStar.isStronglyNormalizing_of_rename emptyRenaming renamedSubjectNormalizing

/-- **Closed classifier strong normalization from the bundled type-value-candidate fundamental theorem.**
Validity turns the closed classifier into a grown type, then the closed subject theorem applies. -/
theorem HasTypeDescPi.closedClassifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    IsStronglyNormalizing classifier := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ :=
    typed.classifierIsTypeDesc (WfContext.emptyIsWellFormed (profile := profile))
  exact HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
    fundamentalTheorem classifierTyped

/-- **Substituted subject-and-classifier strong normalization from the all-level fundamental theorem.**
This packages the exact theorem interface consumed by typed conversion: the same reducible closing
substitution normalizes both the term being typed and its classifier. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile) :
    HasTypeDescPiSubstitutedStrongNormalizationTheorem profile := by
  intro _scope _targetScope _context _subject _classifier contextWellFormed typed
    substitution env predLevel
  exact ⟨
    HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
      fundamentalTheorem typed substitution env predLevel,
    HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
      fundamentalTheorem contextWellFormed typed substitution env predLevel⟩

/-- **Substituted subject-and-classifier strong normalization from the strengthened positive-candidate
fundamental theorem.**  This packages the exact nonempty-context handoff for the proof-relevant FT
interface: the substituted subject and classifier normalize under any supplied strengthened closing
environment. -/
theorem HasTypeDescPiPositiveCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile) :
    HasTypeDescPiPositiveCandidateSubstitutedStrongNormalizationTheorem profile := by
  intro _scope _targetScope _context _subject _classifier contextWellFormed typed
    substitution envWithCandidates predLevel
  exact ⟨
    HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
      fundamentalTheorem typed substitution envWithCandidates predLevel,
    HasTypeDescPi.classifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
      fundamentalTheorem contextWellFormed typed substitution envWithCandidates predLevel⟩

/-- **Substituted subject-and-classifier strong normalization from the bundled type-value-candidate
fundamental theorem.**  This is the strongest exported substituted SN handoff: the same proof-relevant
environment that carries arbitrary-universe/type-variable candidate payloads also normalizes both sides of a
grown typing derivation. -/
theorem HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile) :
    HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem profile := by
  intro _scope _targetScope _context _subject _classifier contextWellFormed typed
    substitution envWithTypeValueCandidates predLevel
  exact ⟨
    HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
      fundamentalTheorem typed substitution envWithTypeValueCandidates predLevel,
    HasTypeDescPi.classifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
      fundamentalTheorem contextWellFormed typed substitution envWithTypeValueCandidates predLevel⟩

/-- **Substituted strong normalization in the bundled type-value environment from the exact all-level
fundamental theorem.**  This composes the all-level FT with the multi-universe type-value completion bridge,
then reuses the strongest substituted SN handoff. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
  HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem profile :=
  HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
    (HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
      fundamentalTheorem allReducibleTypesHaveTypeValueCandidates)

/-- **Substituted strong normalization in the bundled type-value environment from positive-member
extension.**  This is the strongest current exported handoff for the multi-universe dependent theorem:
exact all-level reducibility plus the operational positive-member-extension bridge yields substituted
strong normalization under the proof-relevant type-value environment. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfPositiveMemberExtension
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem profile :=
  HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
    fundamentalTheorem
    (hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension.mpr
      positiveMemberExtension)

/-- **Closed subject-and-classifier strong normalization from the all-level fundamental theorem.** -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toClosedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile) :
    HasTypeDescPiClosedStrongNormalizationTheorem profile := by
  intro _subject _classifier typed
  exact ⟨
    HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
      fundamentalTheorem typed,
    HasTypeDescPi.closedClassifierStronglyNormalizingFromAllLevelFundamentalTheorem
      fundamentalTheorem typed⟩

/-- **Closed subject-and-classifier strong normalization from the strengthened positive-candidate
fundamental theorem.**  This is the closed downstream handoff for the proof-relevant FT interface. -/
theorem HasTypeDescPiPositiveCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiPositiveCandidateFundamentalTheorem profile) :
    HasTypeDescPiClosedStrongNormalizationTheorem profile := by
  intro _subject _classifier typed
  exact ⟨
    HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
      fundamentalTheorem typed,
    HasTypeDescPi.closedClassifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
      fundamentalTheorem typed⟩

/-- **Closed subject-and-classifier strong normalization from the bundled type-value-candidate fundamental
theorem.**  This is the closed downstream handoff for the strongest current proof-relevant FT interface. -/
theorem HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile) :
    HasTypeDescPiClosedStrongNormalizationTheorem profile := by
  intro _subject _classifier typed
  exact ⟨
    HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
      fundamentalTheorem typed,
    HasTypeDescPi.closedClassifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
      fundamentalTheorem typed⟩

/-- **Package the direct type-value fundamental theorem with its SN consequences.**  The strongest
proof-relevant FT interface already contains enough data for both substituted and closed strong
normalization: CR1 projects the substituted theorem, and the empty-context corollary gives the closed
theorem.  This constructor is the direct handoff for a future unconditional proof of the type-value
fundamental theorem, without routing through the all-level theorem plus an external completion premise. -/
theorem HasTypeDescPiTypeValueCandidateFundamentalTheorem.toReducibilityAndStrongNormalizationTheorem
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiTypeValueCandidateFundamentalTheorem profile) :
    HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile :=
  ⟨fundamentalTheorem,
    HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
      fundamentalTheorem,
    HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
      fundamentalTheorem⟩

/-- **The bundled type-value metatheory is equivalent to the direct type-value FT.**  The extra strong
normalization fields are not additional assumptions: they are consequences of the fundamental theorem
itself.  This theorem keeps the exported package honest and convenient: downstream code may consume the
bundle, while proof-producing code only needs to establish the FT. -/
theorem hasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem_iff_typeValueCandidateFundamentalTheorem
    {profile : PolyProfile} :
    HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile ↔
      HasTypeDescPiTypeValueCandidateFundamentalTheorem profile :=
  ⟨HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.fundamentalTheorem,
    HasTypeDescPiTypeValueCandidateFundamentalTheorem.toReducibilityAndStrongNormalizationTheorem⟩

/-- **Bundled multi-universe metatheory from all-level FT plus type-value completion.**  This composes the
exact all-level dependent fundamental theorem with the candidate-completion principle and packages the
resulting type-value FT, substituted SN theorem, and closed SN theorem as one reusable theorem value. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (allReducibleTypesHaveTypeValueCandidates :
      HasTypeValueCandidatesForAllReducibleTypesAtAllLevels) :
    HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile := by
  let typeValueFundamentalTheorem :
      HasTypeDescPiTypeValueCandidateFundamentalTheorem profile :=
    HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
      fundamentalTheorem allReducibleTypesHaveTypeValueCandidates
  exact ⟨
    typeValueFundamentalTheorem,
    HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
      typeValueFundamentalTheorem,
    HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
      typeValueFundamentalTheorem⟩

/-- **Bundled multi-universe metatheory from the operational positive-member-extension bridge.**  This is
the strongest current honest package: the exact all-level dependent FT plus the operational bridge
(`member at one positive fuel -> member at every positive fuel` for strongly-normalizing all-level types)
gives the type-value FT, substituted SN under type-value environments, and closed SN. -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfPositiveMemberExtension
    {profile : PolyProfile}
    (fundamentalTheorem : HasTypeDescPiAllLevelFundamentalTheorem profile)
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes) :
    HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem profile :=
  HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
    fundamentalTheorem
    positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates

end FX1Poly.Typed

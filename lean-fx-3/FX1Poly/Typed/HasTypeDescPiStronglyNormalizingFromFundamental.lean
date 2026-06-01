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

/-- **Closed strong-normalization theorem interface for `HasTypeDescPi`.**  A profile has closed strong
normalization when every closed grown typing derivation has a strongly normalizing subject and classifier. -/
def HasTypeDescPiClosedStrongNormalizationTheorem (profile : PolyProfile) : Prop :=
  ∀ {subject classifier : RawTerm 0},
    HasTypeDescPi profile TypingContext.empty subject classifier →
      IsStronglyNormalizing subject ∧ IsStronglyNormalizing classifier

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

end FX1Poly.Typed

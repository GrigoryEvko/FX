import FX1Poly.Typed.HasTypeCheck
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.HasTypeFormationNoLambdaApplication
import FX1Poly.Typed.HasTypeStronglyNormalizing

/-! # FX1Poly/Typed/HasTypePiSigmaFormationCheckingCertificate
    — a typed-checking certificate for the native pi/sigma-formation HasType core

`polycell.md`'s Phase Z typed-core target includes decidable typed conversion and decidable typed checking
for the semantic core.  This file does NOT claim that full semantic-core result.  It packages the proved
decidability/coherence facts for the smaller native pi/sigma-formation `HasType` core:

* direct typed checking: `HasType.decidableOfWellFormed`;
* bidirectional checking: `HasType.infer` / `HasType.check` plus `infer_complete`;
* description-engine typed checking: `HasTypeDesc.decidableOfWellFormed`;
* formation-engine equivalence: `HasType.toHasTypeDesc` and `HasTypeDesc.toHasType`;
* typed classifier conversion: `Conv.decidableOfTyped` and `Conv.decidableOfHasTypeDesc`;
* validity: `HasType.classifierIsType`;
* native-pi-sigma HasType normalization: subject normalization plus classifier normalization from validity.
* description-engine validity and normalization: `HasTypeDesc.classifierIsTypeDesc` and
  subject/classifier normalization.
* formation-boundary rejection: native `HasType` and `HasTypeDesc` cannot type lambda/application subjects.

This file packages those pieces as a single kernel object,
`HasTypePiSigmaFormationCheckingCertificate`, so downstream semantic-core work can depend on one explicit
capability record rather than re-discovering the individual declarations.  It is intentionally scoped to the
native pi/sigma-formation HasType core; it does not claim the still-open `HasTypeDescPi` reducibility
assembly or the later cubical/HIT layers.

## Zero-axiom verification

The builder is pure record assembly from already-gated declarations.  No new recursion and no proof search:
each field delegates to an existing zero-axiom theorem/definition.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Typed checking certificate for the native pi/sigma-formation `HasType` core.**  From a well-formed context, the
typed core exposes both forms of native typed checking (direct and bidirectional), the equivalent
description-engine checker, typed classifier conversion, and the metatheoretic facts that make those deciders
sound inputs to the larger semantic-core program. -/
structure HasTypePiSigmaFormationCheckingCertificate {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : Type where
  /-- The context whose checker is certified is well-formed. -/
  contextIsWellFormed : WfContext context
  /-- Direct typed-checking decision procedure for the native pi/sigma-formation HasType core. -/
  decideHasType : ∀ subject classifier : RawTerm scope,
    Decidable (HasType profile context subject classifier)
  /-- Bidirectional synthesis procedure: synthesize a classifier and derivation when the subject is accepted. -/
  inferClassifier : ∀ subject : RawTerm scope,
    Option (Σ' classifier : RawTerm scope, HasType profile context subject classifier)
  /-- Bidirectional checking decision procedure against a caller-supplied target type. -/
  checkHasType : ∀ subject targetType : RawTerm scope,
    Decidable (HasType profile context subject targetType)
  /-- Direct typed-checking decision procedure for the equivalent `HasTypeDesc` formation engine. -/
  decideHasTypeDesc : ∀ subject classifier : RawTerm scope,
    Decidable (HasTypeDesc profile context subject classifier)
  /-- Completeness of the description engine relative to native `HasType`. -/
  translateHasTypeToDesc : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier →
      HasTypeDesc profile context subject classifier
  /-- Soundness of the description engine relative to native `HasType`. -/
  translateDescToHasType : ∀ {subject classifier : RawTerm scope},
    HasTypeDesc profile context subject classifier →
      HasType profile context subject classifier
  /-- Completeness of synthesis on the typeable domain, with the synthesized classifier convertible to any
  actual classifier. -/
  inferCompletes : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier →
      ∃ inferred, inferClassifier subject = some inferred ∧ Conv classifier inferred.1
  /-- Typed conversion is decidable between classifiers of two well-typed subjects. -/
  decideTypedClassifierConv :
    ∀ {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope},
      HasType profile context firstSubject firstClassifier →
      HasType profile context secondSubject secondClassifier →
        Decidable (Conv firstClassifier secondClassifier)
  /-- Description-engine typed conversion is decidable between classifiers of two well-typed subjects. -/
  decideHasTypeDescClassifierConv :
    ∀ {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope},
      HasTypeDesc profile context firstSubject firstClassifier →
      HasTypeDesc profile context secondSubject secondClassifier →
        Decidable (Conv firstClassifier secondClassifier)
  /-- Description-engine validity: every classifier produced by description typing is itself a
  description-engine type. -/
  proveHasTypeDescClassifierIsTypeDesc : ∀ {subject classifier : RawTerm scope},
    HasTypeDesc profile context subject classifier → IsTypeDesc profile context classifier
  /-- Validity: every classifier produced by typing is itself a type. -/
  proveClassifierIsType : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier → IsType profile context classifier
  /-- Description-engine normalization: every description-typed subject is strongly normalizing. -/
  proveHasTypeDescSubjectIsStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasTypeDesc profile context subject classifier → StepStar.IsStronglyNormalizing subject
  /-- Description-engine classifier normalization in well-formed contexts. -/
  proveHasTypeDescClassifierIsStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasTypeDesc profile context subject classifier → StepStar.IsStronglyNormalizing classifier
  /-- Description-engine subject and classifier normalization in one package. -/
  proveHasTypeDescSubjectAndClassifierStronglyNormalizing :
    ∀ {subject classifier : RawTerm scope},
      HasTypeDesc profile context subject classifier →
        StepStar.IsStronglyNormalizing subject ∧ StepStar.IsStronglyNormalizing classifier
  /-- Native pi/sigma-formation HasType normalization: every typed subject is strongly normalizing. -/
  proveSubjectIsStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier → StepStar.IsStronglyNormalizing subject
  /-- Native pi/sigma-formation HasType classifier normalization in well-formed contexts. -/
  proveClassifierIsStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier → StepStar.IsStronglyNormalizing classifier
  /-- Native pi/sigma-formation HasType subject and classifier normalization in one package. -/
  proveSubjectAndClassifierStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier →
      StepStar.IsStronglyNormalizing subject ∧ StepStar.IsStronglyNormalizing classifier
  /-- Native pi/sigma-formation `HasType` rejects lambda subjects. -/
  rejectHasTypeLambda : ∀ {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasType profile context (lamCell body) classifier → False
  /-- Native pi/sigma-formation `HasType` rejects application subjects. -/
  rejectHasTypeApplication :
    ∀ {functionTerm argument classifier : RawTerm scope},
      HasType profile context (appCell functionTerm argument) classifier → False
  /-- The equivalent description formation engine rejects lambda subjects. -/
  rejectHasTypeDescLambda : ∀ {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasTypeDesc profile context (lamCell body) classifier → False
  /-- The equivalent description formation engine rejects application subjects. -/
  rejectHasTypeDescApplication :
    ∀ {functionTerm argument classifier : RawTerm scope},
      HasTypeDesc profile context (appCell functionTerm argument) classifier → False

/-- Build the native-pi-sigma formation checking certificate from a well-formed context.  This is the explicit
record-level aggregation of the already-proved native typed checking, equivalent description-engine checking,
bidirectional checking, typed conversion, validity, and strong-normalization facts. -/
def buildHasTypePiSigmaFormationCheckingCertificate {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (contextIsWellFormed : WfContext context) :
    HasTypePiSigmaFormationCheckingCertificate context where
  contextIsWellFormed := contextIsWellFormed
  decideHasType := HasType.decidableOfWellFormed contextIsWellFormed
  inferClassifier := HasType.infer contextIsWellFormed
  checkHasType := HasType.check contextIsWellFormed
  decideHasTypeDesc := HasTypeDesc.decidableOfWellFormed contextIsWellFormed
  translateHasTypeToDesc := fun typed => HasType.toHasTypeDesc typed
  translateDescToHasType := fun typed => HasTypeDesc.toHasType typed
  inferCompletes := fun typed => HasType.infer_complete contextIsWellFormed typed
  decideTypedClassifierConv := fun firstTyped secondTyped =>
    Conv.decidableOfTyped contextIsWellFormed firstTyped secondTyped
  decideHasTypeDescClassifierConv := fun firstTyped secondTyped =>
    Conv.decidableOfHasTypeDesc contextIsWellFormed firstTyped secondTyped
  proveHasTypeDescClassifierIsTypeDesc := fun typed =>
    HasTypeDesc.classifierIsTypeDesc contextIsWellFormed typed
  proveClassifierIsType := fun typed => HasType.classifierIsType contextIsWellFormed typed
  proveHasTypeDescSubjectIsStronglyNormalizing := fun typed => typed.isStronglyNormalizing
  proveHasTypeDescClassifierIsStronglyNormalizing := fun typed =>
    typed.classifierStronglyNormalizing contextIsWellFormed
  proveHasTypeDescSubjectAndClassifierStronglyNormalizing := fun typed =>
    typed.subjectAndClassifierStronglyNormalizing contextIsWellFormed
  proveSubjectIsStronglyNormalizing := fun typed => typed.isStronglyNormalizing
  proveClassifierIsStronglyNormalizing := fun typed =>
    (HasType.classifierIsType contextIsWellFormed typed).isStronglyNormalizing
  proveSubjectAndClassifierStronglyNormalizing := fun typed =>
    ⟨typed.isStronglyNormalizing,
      (HasType.classifierIsType contextIsWellFormed typed).isStronglyNormalizing⟩
  rejectHasTypeLambda := fun typed => HasType.subjectCannotBeLambda typed
  rejectHasTypeApplication := fun typed => HasType.subjectCannotBeApplication typed
  rejectHasTypeDescLambda := fun typed => HasTypeDesc.subjectCannotBeLambda typed
  rejectHasTypeDescApplication := fun typed => HasTypeDesc.subjectCannotBeApplication typed

/-- Native empty-context subject regularity exposed through the checking certificate.  This is scoped to the
native pi/sigma-formation `HasType` core: a closed typed subject is itself a native type. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsType {profile : PolyProfile}
    (_checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    IsType profile TypingContext.empty subject :=
  HasType.closedSubjectIsType typed

/-- Native empty-context canonical-form shape exposed through the checking certificate: a closed subject in
the native pi/sigma-formation `HasType` core is a universe, Pi-code, or Sigma-code cell. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsTypeFormer
    {profile : PolyProfile}
    (_checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) :=
  HasType.closedSubjectIsTypeFormer typed

/-- Native empty-context classifier shape exposed through the checking certificate: every closed typed
subject's classifier is convertible to a universe code. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedClassifierConvUniverseCode
    {profile : PolyProfile}
    (_checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasType profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) :=
  HasType.closedClassifierConvUniverseCode typed

/-- Description-engine empty-context subject regularity exposed through the checking certificate.  The proof
uses the certificate's soundness map from `HasTypeDesc` to the native pi/sigma-formation `HasType` core, then
transports the resulting native type witness back to `IsTypeDesc`. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeDesc
    {profile : PolyProfile}
    (checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    IsTypeDesc profile TypingContext.empty subject :=
  (HasType.closedSubjectIsType (checkingCertificate.translateDescToHasType typed)).toIsTypeDesc

/-- Description-engine empty-context canonical-form shape exposed through the checking certificate: after
transporting to the native pi/sigma-formation `HasType` core, a closed `HasTypeDesc` subject is a universe,
Pi-code, or Sigma-code cell. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeFormer
    {profile : PolyProfile}
    (checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) :=
  HasType.closedSubjectIsTypeFormer (checkingCertificate.translateDescToHasType typed)

/-- Description-engine empty-context classifier shape exposed through the checking certificate: after
transporting to the native pi/sigma-formation `HasType` core, every closed `HasTypeDesc` subject's
classifier is convertible to a universe code. -/
theorem HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescClassifierConvUniverseCode
    {profile : PolyProfile}
    (checkingCertificate :
      HasTypePiSigmaFormationCheckingCertificate
        (TypingContext.empty : TypingContext profile 0))
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) :=
  HasType.closedClassifierConvUniverseCode (checkingCertificate.translateDescToHasType typed)

end FX1Poly.Typed

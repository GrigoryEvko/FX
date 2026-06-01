import FX1Poly.Typed.HasTypeCheck
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeStronglyNormalizing

/-! # FX1Poly/Typed/HasTypePiSigmaFormationCheckingCertificate
    — a typed-checking certificate for the native pi/sigma-formation HasType core

`polycell.md` defines revised Milestone A as **decidable TYPED conversion + decidable TYPED checking**
for the semantic core.  This file does NOT claim that full semantic-core result.  It packages the proved
decidability/coherence facts for the smaller native pi/sigma-formation `HasType` core:

* direct typed checking: `HasType.decidableOfWellFormed`;
* bidirectional checking: `HasType.infer` / `HasType.check` plus `infer_complete`;
* description-engine typed checking: `HasTypeDesc.decidableOfWellFormed`;
* formation-engine equivalence: `HasType.toHasTypeDesc` and `HasTypeDesc.toHasType`;
* typed classifier conversion: `Conv.decidableOfTyped`;
* validity: `HasType.classifierIsType`;
* native-pi-sigma HasType normalization: `HasType.isStronglyNormalizing`.

This file packages those pieces as a single kernel object,
`HasTypePiSigmaFormationCheckingCertificate`, so downstream semantic-core work can depend on one explicit
capability record rather than re-discovering the individual declarations.  It is intentionally scoped to the
native pi/sigma-formation HasType core; it does not claim the still-open `HasTypeDescPi` reducibility assembly or the future A+/A++
cubical/HIT layers.

## Zero-axiom verification

The builder is pure record assembly from already-gated declarations.  No new recursion and no proof search:
each field delegates to an existing zero-axiom theorem/definition.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

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
  /-- Validity: every classifier produced by typing is itself a type. -/
  proveClassifierIsType : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier → IsType profile context classifier
  /-- Native pi/sigma-formation HasType normalization: every typed subject is strongly normalizing. -/
  proveSubjectIsStronglyNormalizing : ∀ {subject classifier : RawTerm scope},
    HasType profile context subject classifier → StepStar.IsStronglyNormalizing subject

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
  proveClassifierIsType := fun typed => HasType.classifierIsType contextIsWellFormed typed
  proveSubjectIsStronglyNormalizing := fun typed => typed.isStronglyNormalizing

end FX1Poly.Typed

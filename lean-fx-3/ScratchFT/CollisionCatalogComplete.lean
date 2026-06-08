import FX1Poly.Modal.SoundnessCollisionCatalog

namespace FX1Poly.Modal

-- CT × Async: constant-time broken by secret-dependent async TIMING (scoping-refined).
inductive ConstantTimeDemand where
  | constantTimeRequired
  | variableTimeOk
  deriving DecidableEq

def ConstantTimeDemand.isConstantTimeRequired : ConstantTimeDemand → Bool
  | .constantTimeRequired => true
  | .variableTimeOk => false

inductive AsyncTimingBehavior where
  | secretDependentTiming
  | secretIndependentTiming
  deriving DecidableEq

def AsyncTimingBehavior.isSecretIndependent : AsyncTimingBehavior → Bool
  | .secretIndependentTiming => true
  | .secretDependentTiming => false

def constantTimeAsyncSchema : SoundnessCollisionSchema where
  Demand := ConstantTimeDemand
  Capability := AsyncTimingBehavior
  isStrongDemand := ConstantTimeDemand.isConstantTimeRequired
  preservesInvariant := AsyncTimingBehavior.isSecretIndependent

theorem constantTimeCollidesWithSecretDependentAsync :
    ¬ constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
        AsyncTimingBehavior.secretDependentTiming :=
  (constantTimeAsyncSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem constantTimeConsistentWithSecretIndependentAsync :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      AsyncTimingBehavior.secretIndependentTiming :=
  fun _ => rfl

theorem variableTimeConsistentWithAnyAsync (timing : AsyncTimingBehavior) :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.variableTimeOk timing :=
  fun absurdFlag => Bool.noConfusion absurdFlag

-- classified × Fail: secret leaked by a secret-controlled FAILURE being observable (implicit flow).
inductive ClassifiedFailureDemand where
  | secretControlsFailure
  | failureSecretIndependent
  deriving DecidableEq

def ClassifiedFailureDemand.isSecretControllingFailure : ClassifiedFailureDemand → Bool
  | .secretControlsFailure => true
  | .failureSecretIndependent => false

inductive FailureObservability where
  | observableToUnclassified
  | failureClassified
  deriving DecidableEq

def FailureObservability.isFailureContained : FailureObservability → Bool
  | .failureClassified => true
  | .observableToUnclassified => false

def classifiedFailSchema : SoundnessCollisionSchema where
  Demand := ClassifiedFailureDemand
  Capability := FailureObservability
  isStrongDemand := ClassifiedFailureDemand.isSecretControllingFailure
  preservesInvariant := FailureObservability.isFailureContained

theorem secretControlledFailureCollidesWithObservableFailure :
    ¬ classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
        FailureObservability.observableToUnclassified :=
  (classifiedFailSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem secretControlledFailureConsistentWithClassifiedFailure :
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
      FailureObservability.failureClassified :=
  fun _ => rfl

theorem secretIndependentFailureConsistentWithAnyObservability (observability : FailureObservability) :
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.failureSecretIndependent observability :=
  fun absurdFlag => Bool.noConfusion absurdFlag

-- CT × Fail-on-secret: constant-time broken by a secret-dependent FAILURE PATH.
inductive FailurePathBehavior where
  | secretDependentFailure
  | secretIndependentFailure
  deriving DecidableEq

def FailurePathBehavior.isSecretIndependent : FailurePathBehavior → Bool
  | .secretIndependentFailure => true
  | .secretDependentFailure => false

def constantTimeFailOnSecretSchema : SoundnessCollisionSchema where
  Demand := ConstantTimeDemand
  Capability := FailurePathBehavior
  isStrongDemand := ConstantTimeDemand.isConstantTimeRequired
  preservesInvariant := FailurePathBehavior.isSecretIndependent

theorem constantTimeCollidesWithSecretDependentFailure :
    ¬ constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
        FailurePathBehavior.secretDependentFailure :=
  (constantTimeFailOnSecretSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem constantTimeConsistentWithSecretIndependentFailure :
    constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      FailurePathBehavior.secretIndependentFailure :=
  fun _ => rfl

-- Capstone: all three new entries are CONTROL-REFINED (each co-occurs soundly when the control is withheld),
-- completing the §6.8 catalog's control-refined family.
theorem sec68RemainingCatalogControlRefined :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      AsyncTimingBehavior.secretIndependentTiming ∧
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
      FailureObservability.failureClassified ∧
    constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      FailurePathBehavior.secretIndependentFailure :=
  ⟨constantTimeConsistentWithSecretIndependentAsync,
   secretControlledFailureConsistentWithClassifiedFailure,
   constantTimeConsistentWithSecretIndependentFailure⟩

end FX1Poly.Modal

#print axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentAsync
#print axioms FX1Poly.Modal.variableTimeConsistentWithAnyAsync
#print axioms FX1Poly.Modal.secretControlledFailureCollidesWithObservableFailure
#print axioms FX1Poly.Modal.secretIndependentFailureConsistentWithAnyObservability
#print axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentFailure
#print axioms FX1Poly.Modal.sec68RemainingCatalogControlRefined

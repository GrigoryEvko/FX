import FX1Poly.Modal.SoundnessCollisionSchema
import FX1Poly.Modal.ThreeWayCollisionClassifiedAsyncSession
import FX1Poly.Modal.UnifiedGradeMonoid

namespace FX1Poly.Modal

-- Part 1: implicit-flow refinement of the 3-way classified × async × session collision.

def IsImplicitFlowAdmissible (classifiedControlsScheduling async session : Bool) : Prop :=
  ¬ (classifiedControlsScheduling = true ∧ async = true ∧ session = true)

theorem encryptAndSendImplicitFlowAdmissible :
    IsImplicitFlowAdmissible false true true :=
  fun conjunction => Bool.noConfusion conjunction.1

theorem secretControlsSchedulingCollision :
    ¬ IsImplicitFlowAdmissible true true true :=
  fun admissible => admissible ⟨rfl, rfl, rfl⟩

theorem implicitFlowAdmissible_ofCoOccurrenceAdmissible
    {classifiedPresent classifiedControlsScheduling async session : Bool}
    (coarseAdmissible : IsClassifiedAsyncSessionAdmissible classifiedPresent async session)
    (controlBoundedByPresence : classifiedControlsScheduling = true → classifiedPresent = true) :
    IsImplicitFlowAdmissible classifiedControlsScheduling async session :=
  fun conjunction =>
    coarseAdmissible ⟨controlBoundedByPresence conjunction.1, conjunction.2.1, conjunction.2.2⟩

theorem flagshipDistinguishesModels :
    ¬ IsClassifiedAsyncSessionAdmissible true true true ∧
    IsImplicitFlowAdmissible false true true :=
  ⟨classifiedAsyncSessionCollision, encryptAndSendImplicitFlowAdmissible⟩

-- Part 2: the concrete ≥3-dimension grade vector for the signature site.

def encryptAndSendGradeMonoid : CommutativeGradeMonoid :=
  fxUsageSemiring.toCommutativeGradeMonoid.product securityEffectGradeMonoid

theorem encryptAndSendGradeMonoidIsLawful :
    IsLawfulCommutativeGradeMonoid encryptAndSendGradeMonoid :=
  CommutativeGradeMonoid.productIsLawful
    (fxUsageSemiring.toCommutativeGradeMonoid_isLawful fxUsageSemiring_isLawful)
    securityEffectGradeMonoidIsLawful

def encryptAndSendKeyGrade : encryptAndSendGradeMonoid.Carrier :=
  (UsageGrade.omega, (SecurityGrade.classified, EffectGrade.impureEffect))

theorem encryptAndSendKeyGrade_combine_identity :
    encryptAndSendGradeMonoid.combine encryptAndSendKeyGrade encryptAndSendGradeMonoid.identity
      = encryptAndSendKeyGrade :=
  encryptAndSendGradeMonoidIsLawful.combine_identity encryptAndSendKeyGrade

-- Part 3: the signature lands in the §6.8-admissible region across every relevant collision.

theorem encryptAndSendMutationConcurrencyConsistent :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential MutationGrade.immutable :=
  sequentialConsistentWithEveryMutation MutationGrade.immutable

theorem encryptAndSendPrecisionOverflowConsistent :
    decimalOverflowSchema.IsConsistent PrecisionGrade.inexactPrecision OverflowGrade.wrapGrade :=
  fun absurdFlag => Bool.noConfusion absurdFlag

theorem encryptAndSendJointlyAdmissible :
    IsImplicitFlowAdmissible false true true ∧
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential MutationGrade.immutable ∧
    decimalOverflowSchema.IsConsistent PrecisionGrade.inexactPrecision OverflowGrade.wrapGrade :=
  ⟨encryptAndSendImplicitFlowAdmissible,
   encryptAndSendMutationConcurrencyConsistent,
   encryptAndSendPrecisionOverflowConsistent⟩

end FX1Poly.Modal

#print axioms FX1Poly.Modal.encryptAndSendImplicitFlowAdmissible
#print axioms FX1Poly.Modal.implicitFlowAdmissible_ofCoOccurrenceAdmissible
#print axioms FX1Poly.Modal.flagshipDistinguishesModels
#print axioms FX1Poly.Modal.encryptAndSendGradeMonoidIsLawful
#print axioms FX1Poly.Modal.encryptAndSendKeyGrade_combine_identity
#print axioms FX1Poly.Modal.encryptAndSendJointlyAdmissible

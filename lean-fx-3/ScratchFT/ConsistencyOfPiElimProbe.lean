import FX1Poly.Typed.HasTypeDescPiSubjectReductionMutual
import FX1Poly.Typed.ConsistencyConditionalOnSubjectReduction

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- SRD-3: iterated (multi-step) subject reduction, conditional on the single piElim crux.
theorem HasTypeDescPi.subjectReductionStarOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : StepStar subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  match chain with
  | .refl _ => typed
  | .trans firstStep rest =>
      HasTypeDescPi.subjectReductionStarOfPiElimArm piElimArm wellFormed
        (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm typed wellFormed _ firstStep) rest

-- SN-050 consistency, conditional on EXACTLY the single piElim crux (GCC-5).
theorem HasTypeDescPi.consistencyOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType
    (fun startTyped chain =>
      HasTypeDescPi.subjectReductionStarOfPiElimArm piElimArm WfContextDescPi.emptyIsWellFormed
        startTyped chain)
    typed

#print axioms HasTypeDescPi.subjectReductionStarOfPiElimArm
#print axioms HasTypeDescPi.consistencyOfPiElimArm

end FX1Poly.Typed

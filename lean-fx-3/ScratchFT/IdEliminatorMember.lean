import FX1Poly.Core.IdentityEliminatorCanonicalComputation
import FX1Poly.Core.IdentityEliminatorStrongNormalization
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

namespace FX1Poly.Core

open StepStar

theorem idJClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness)
    (baseCaseMember : CanonicalFormsPredicate isValue baseCase) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))) := by
  have idJStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))) :=
    idJ_isStronglyNormalizing_of_strongly_normalizing_base
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (idJCanonicalWitnessReducesToBase witnessMember)
    idJStronglyNormalizing baseCaseMember.closedReducesToValue

theorem idStrictRecClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness)
    (baseCaseMember : CanonicalFormsPredicate isValue baseCase) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))) := by
  have idStrictRecStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))) :=
    idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base
      baseCaseMember.stronglyNormalizing witnessMember.stronglyNormalizing
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (idStrictRecCanonicalWitnessReducesToBase witnessMember)
    idStrictRecStronglyNormalizing baseCaseMember.closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.idJClosedIsMember_probe
#print axioms FX1Poly.Core.idStrictRecClosedIsMember_probe

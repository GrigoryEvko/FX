import FX1Poly.Core.RecursorClosedMembership
import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationLeaves

namespace FX1Poly.Core
open StepStar

-- natElim on natZero fires to the zero-branch (base case, no recursion)
theorem natElimZeroClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_natElim ()
        (.childCons natZeroCell (.childCons boolTrueCell (.childCons boolTrueCell .childNil)))) :=
  CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.trans Step.iotaNatElimZero (StepStar.refl _))
    (natElimZero_isStronglyNormalizing_of_branches
      boolTrue_isStronglyNormalizing boolTrue_isStronglyNormalizing)
    boolTrueCell_isMember.closedReducesToValue

-- natRec on natZero (dependent twin)
theorem natRecZeroClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_natRec ()
        (.childCons natZeroCell (.childCons boolTrueCell (.childCons boolTrueCell .childNil)))) :=
  CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.trans Step.iotaNatRecZero (StepStar.refl _))
    (natRecZero_isStronglyNormalizing_of_branches
      boolTrue_isStronglyNormalizing boolTrue_isStronglyNormalizing)
    boolTrueCell_isMember.closedReducesToValue

-- listElim on listNil fires to the nil-branch (base case, no recursion)
theorem listElimNilClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_listElim ()
        (.childCons listNilCell (.childCons boolTrueCell (.childCons boolTrueCell .childNil)))) :=
  CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.trans Step.iotaListElimNil (StepStar.refl _))
    (listElimNil_isStronglyNormalizing_of_branches
      boolTrue_isStronglyNormalizing boolTrue_isStronglyNormalizing)
    boolTrueCell_isMember.closedReducesToValue

#print axioms natElimZeroClosedMembershipSmoke
#print axioms natRecZeroClosedMembershipSmoke
#print axioms listElimNilClosedMembershipSmoke

end FX1Poly.Core

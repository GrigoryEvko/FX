import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Core.BoolElimStrongNormalization
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

namespace FX1Poly.Core

open StepStar

-- Closed boolElim on a canonical bool scrutinee, with member branches, is itself a data-candidate member.
theorem boolElimClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee)
    (thenMember : CanonicalFormsPredicate isValue thenBranch)
    (elseMember : CanonicalFormsPredicate isValue elseBranch) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_boolElim ()
        (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))) := by
  have boolElimStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_boolElim ()
          (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))) :=
    boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
      scrutineeMember.1 thenMember.1 elseMember.1
  rcases boolElimCanonicalScrutineeReducesToBranch
      (thenBranch := thenBranch) (elseBranch := elseBranch) scrutineeMember with
    reducesToThen | reducesToElse
  · exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToThen
      boolElimStronglyNormalizing thenMember.closedReducesToValue
  · exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToElse
      boolElimStronglyNormalizing elseMember.closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.boolElimClosedIsMember_probe

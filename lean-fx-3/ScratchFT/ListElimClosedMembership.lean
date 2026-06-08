import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.NeutralTerm

namespace FX1Poly.Core

open StepStar

private abbrev listElimCell (scrutinee nilBranch consBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_listElim () (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

private abbrev listElimConsContractumClosed (consBranch head tail nilBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (listElimCell tail nilBranch consBranch)
        .childNil))

theorem listElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {scrutinee nilBranch consBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate IsListValue scrutinee)
    (nilBranchMember : CanonicalFormsPredicate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm 0},
        RawTerm.isStepNormalForm head → IsListValue tail → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons result .childNil))))
    (consContractumTerminates : ∀ head tail : RawTerm 0,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractumClosed consBranch head tail nilBranch)) :
    CanonicalFormsPredicate isValue (listElimCell scrutinee nilBranch consBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsListValue value →
      IsStronglyNormalizing (listElimCell value nilBranch consBranch) :=
    fun valueIsList =>
      listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
        (isListValue_isMember valueIsList).stronglyNormalizing
        nilBranchMember.stronglyNormalizing consBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (listElimCell scrutinee nilBranch consBranch) :=
    listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
      scrutineeMember.stronglyNormalizing nilBranchMember.stronglyNormalizing consBranchTerminates
  obtain ⟨listValue, scrutineeToList, listValueIsList⟩ := scrutineeMember.closedReducesToValue
  have listValueMember : CanonicalFormsPredicate isValue (listElimCell listValue nilBranch consBranch) :=
    listElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand nilBranchMember consBranchApplication recursorSN listValueIsList
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.listElimScrutinee scrutineeToList) cellStronglyNormalizing
    listValueMember.closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.listElimClosedIsMember

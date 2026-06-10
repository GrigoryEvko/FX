import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.NeutralTerm

namespace FX1Poly.Core

open StepStar

private abbrev listElimCell (motive : RawTerm 1) (scrutinee nilBranch consBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch (.childCons scrutinee .childNil))))

private abbrev listElimConsContractumClosed (motive : RawTerm 1)
    (consBranch head tail nilBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (listElimCell motive tail nilBranch consBranch)
        .childNil))

theorem listElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee nilBranch consBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
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
        IsStronglyNormalizing (listElimConsContractumClosed motive consBranch head tail nilBranch)) :
    CanonicalFormsPredicate isValue (listElimCell motive scrutinee nilBranch consBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  -- PINNED SN-helper order: scrutinee FIRST, motive SECOND, nil THIRD, cons FOURTH.
  have recursorSN : ∀ {value : RawTerm 0}, IsListValue value →
      IsStronglyNormalizing (listElimCell motive value nilBranch consBranch) :=
    fun valueIsList =>
      listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
        (isListValue_isMember valueIsList).stronglyNormalizing motiveStronglyNormalizing
        nilBranchMember.stronglyNormalizing consBranchTerminates
  have cellStronglyNormalizing :
      IsStronglyNormalizing (listElimCell motive scrutinee nilBranch consBranch) :=
    listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      nilBranchMember.stronglyNormalizing consBranchTerminates
  obtain ⟨listValue, scrutineeToList, listValueIsList⟩ := scrutineeMember.closedReducesToValue
  have listValueMember :
      CanonicalFormsPredicate isValue (listElimCell motive listValue nilBranch consBranch) :=
    listElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand nilBranchMember consBranchApplication recursorSN listValueIsList
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.listElimScrutinee scrutineeToList) cellStronglyNormalizing
    listValueMember.closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.listElimClosedIsMember

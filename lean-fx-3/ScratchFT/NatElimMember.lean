import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.NeutralTerm

namespace FX1Poly.Core

open StepStar

private abbrev natElimCellProbe (scrutinee zeroBranch succBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natElim () (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

private abbrev natElimSuccContractumProbe (succBranch predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons (natElimCellProbe predecessor zeroBranch succBranch) .childNil))

theorem natElimClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {scrutinee zeroBranch succBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm 0, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractumProbe succBranch predecessor zeroBranch)) :
    CanonicalFormsPredicate isValue (natElimCellProbe scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natElimCellProbe value zeroBranch succBranch) :=
    fun valueIsNat =>
      natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natElimCellProbe scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natElimCellProbe numeral zeroBranch succBranch) :=
    natElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember succBranchApplication recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natElimScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

private abbrev natRecCellProbe (scrutinee zeroBranch succBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natRec () (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

private abbrev natRecSuccContractumProbe (succBranch predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons (natRecCellProbe predecessor zeroBranch succBranch) .childNil))

theorem natRecClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {scrutinee zeroBranch succBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm 0, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractumProbe succBranch predecessor zeroBranch)) :
    CanonicalFormsPredicate isValue (natRecCellProbe scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natRecCellProbe value zeroBranch succBranch) :=
    fun valueIsNat =>
      natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natRecCellProbe scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natRecCellProbe numeral zeroBranch succBranch) :=
    natRecValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember succBranchApplication recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natRecScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.natElimClosedIsMember_probe
#print axioms FX1Poly.Core.natRecClosedIsMember_probe

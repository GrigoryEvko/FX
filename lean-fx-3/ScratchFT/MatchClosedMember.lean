import FX1Poly.Core.OptionEitherMatchCanonicalComputation
import FX1Poly.Core.StrongNormalizationMatch
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.ApplicationStrongNormalizationForward

namespace FX1Poly.Core

open StepStar

private abbrev applyCellProbe (function argument : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

theorem optionMatchClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isOptionValue scrutinee)
    (noneBranchMember : CanonicalFormsPredicate isValue noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (someBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applyCellProbe someBranch value)) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_optionMatch ()
        (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_optionMatch ()
          (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))) :=
    optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches
      (fun value valueTerminates => (someBranchRespectsSN value valueTerminates).stronglyNormalizing)
      scrutineeMember.stronglyNormalizing noneBranchMember.stronglyNormalizing someBranchTerminates
  rcases optionMatchCanonicalScrutineeReduces
      (noneBranch := noneBranch) (someBranch := someBranch) scrutineeMember with
    reducesToNone | ⟨payload, scrutineeToSome, reducesToApp⟩
  · exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToNone
      cellStronglyNormalizing noneBranchMember.closedReducesToValue
  · have payloadTerminates : IsStronglyNormalizing payload :=
      value_isStronglyNormalizing_of_optionSome
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToSome)
    exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToApp
      cellStronglyNormalizing (someBranchRespectsSN payload payloadTerminates).closedReducesToValue

theorem eitherMatchClosedIsMember_probe {isValue : RawTerm 0 → Prop}
    {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isEitherValue scrutinee)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (leftBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applyCellProbe leftBranch value))
    (rightBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applyCellProbe rightBranch value)) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_eitherMatch ()
        (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_eitherMatch ()
          (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))) :=
    eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches
      (fun value valueTerminates => (leftBranchRespectsSN value valueTerminates).stronglyNormalizing)
      (fun value valueTerminates => (rightBranchRespectsSN value valueTerminates).stronglyNormalizing)
      scrutineeMember.stronglyNormalizing leftBranchTerminates rightBranchTerminates
  rcases eitherMatchCanonicalScrutineeReduces
      (leftBranch := leftBranch) (rightBranch := rightBranch) scrutineeMember with
    ⟨payload, scrutineeToInl, reducesToLeftApp⟩ | ⟨payload, scrutineeToInr, reducesToRightApp⟩
  · have payloadTerminates : IsStronglyNormalizing payload :=
      value_isStronglyNormalizing_of_eitherInl
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToInl)
    exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToLeftApp
      cellStronglyNormalizing (leftBranchRespectsSN payload payloadTerminates).closedReducesToValue
  · have payloadTerminates : IsStronglyNormalizing payload :=
      value_isStronglyNormalizing_of_eitherInr
        (IsStronglyNormalizing.descendStepStar scrutineeMember.stronglyNormalizing scrutineeToInr)
    exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToRightApp
      cellStronglyNormalizing (rightBranchRespectsSN payload payloadTerminates).closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.optionMatchClosedIsMember_probe
#print axioms FX1Poly.Core.eitherMatchClosedIsMember_probe

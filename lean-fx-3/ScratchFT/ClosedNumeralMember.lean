import FX1Poly.Core.NatElimValueMember
import FX1Poly.Core.ListElimValueMember
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.NeutralTerm

namespace FX1Poly.Core
open StepStar

/-- Closed weak-head-expansion for any data candidate: a closed contractum is non-neutral. -/
private theorem closedHeadExpand {isValue : RawTerm 0 → Prop}
    {redexTerm contractum : RawTerm 0}
    (weakHeadStep : WeakHeadStep redexTerm contractum)
    (memberContractum : CanonicalFormsPredicate isValue contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm) :
    CanonicalFormsPredicate isValue redexTerm :=
  CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep
    redexStronglyNormalizing memberContractum IsNeutral.noClosed

/-- **A closed `natElim` on a NUMERAL with reducible branches is a data-candidate member, UNCONDITIONALLY.**
The value-case of the closed recursor membership with NO `succContractumTerminates` hypothesis: instantiates
`natElimValueMember` at the closed data candidate, discharging CR1 (`stronglyNormalizing`), CR2
(`closedUnderStep`), and weak-head-expansion (`closedHeadExpand` via `IsNeutral.noClosed`) concretely. -/
theorem natElimClosedNumeralIsMember {isValue : RawTerm 0 → Prop}
    {zeroBranch succBranch : RawTerm 0}
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    {numeral : RawTerm 0} (numeralIsNat : IsNatValue numeral) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_natElim ()
        (.childCons numeral (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  natElimValueMember (CanonicalFormsPredicate isValue)
    CanonicalFormsPredicate.stronglyNormalizing
    (fun member step =>
      CanonicalFormsPredicate.closedUnderStep IsNeutral.closedUnderStep isNatValue_impliesStepNormalForm
        member step)
    closedHeadExpand numeralIsNat zeroBranch succBranch zeroBranchMember succBranchTerminates
    succBranchApplication

/-- The `natRec` twin of `natElimClosedNumeralIsMember`. -/
theorem natRecClosedNumeralIsMember {isValue : RawTerm 0 → Prop}
    {zeroBranch succBranch : RawTerm 0}
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    {numeral : RawTerm 0} (numeralIsNat : IsNatValue numeral) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_natRec ()
        (.childCons numeral (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  natRecValueMember (CanonicalFormsPredicate isValue)
    CanonicalFormsPredicate.stronglyNormalizing
    (fun member step =>
      CanonicalFormsPredicate.closedUnderStep IsNeutral.closedUnderStep isNatValue_impliesStepNormalForm
        member step)
    closedHeadExpand numeralIsNat zeroBranch succBranch zeroBranchMember succBranchTerminates
    succBranchApplication

/-- **A closed `listElim` on a LIST VALUE with reducible branches is a data-candidate member,
UNCONDITIONALLY** — the SN-064 twin (cons branch is the 3-argument application). -/
theorem listElimClosedValueIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {nilBranch consBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
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
    {value : RawTerm 0} (valueIsList : IsListValue value) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch (.childCons value .childNil))))) :=
  listElimValueMember (CanonicalFormsPredicate isValue)
    CanonicalFormsPredicate.stronglyNormalizing
    (fun member step =>
      CanonicalFormsPredicate.closedUnderStep IsNeutral.closedUnderStep isListValue_impliesStepNormalForm
        member step)
    closedHeadExpand valueIsList motive nilBranch consBranch motiveStronglyNormalizing nilBranchMember
    consBranchTerminates consBranchApplication

end FX1Poly.Core

#print axioms FX1Poly.Core.natElimClosedNumeralIsMember
#print axioms FX1Poly.Core.natRecClosedNumeralIsMember
#print axioms FX1Poly.Core.listElimClosedValueIsMember

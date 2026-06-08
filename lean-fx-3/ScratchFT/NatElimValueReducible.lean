import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepSubsumes

namespace FX1Poly.Core

open StepStar

-- Non-dependent natElim recursor reducibility, VALUE case (numeral scrutinee), by IsNatValue induction.
-- Conditional on the result candidate C's weak-head-expansion + zero-branch membership + succ-branch
-- application + SN-of-redex (the honest interface the eventual full recursor proof supplies).
theorem natElimValueReducible_probe {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (C : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → C contractum →
        IsStronglyNormalizing redexTerm → C redexTerm)
    (zeroBranchMember : C zeroBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → C result →
        C (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing
          (.mkGen .gen_natElim ()
            (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))))
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    C (.mkGen .gen_natElim ()
        (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))) := by
  induction valueIsNat with
  | zero =>
      exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember
        (redexStronglyNormalizing IsNatValue.zero)
  | @succ predecessor predecessorIsValue predecessorIH =>
      exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep
        (succBranchApplication predecessorIsValue predecessorIH)
        (redexStronglyNormalizing (IsNatValue.succ predecessorIsValue))

end FX1Poly.Core

#print axioms FX1Poly.Core.natElimValueReducible_probe

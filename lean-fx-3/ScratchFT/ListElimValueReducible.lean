import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepSubsumes

namespace FX1Poly.Core

open StepStar

-- listElim value-case recursor reducibility (SN-064 recursor value-case), the recursive parallel of #732.
theorem listElimValueReducible_probe {scope : Nat}
    {nilBranch consBranch : RawTerm scope}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (nilBranchMember : resultCandidate nilBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → resultCandidate result →
        resultCandidate (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                (.childCons tail .childNil)))
            (.childCons result .childNil))))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsListValue value →
        IsStronglyNormalizing
          (.mkGen .gen_listElim ()
            (.childCons value (.childCons nilBranch (.childCons consBranch .childNil)))))
    {value : RawTerm scope} (valueIsList : IsListValue value) :
    resultCandidate (.mkGen .gen_listElim ()
        (.childCons value (.childCons nilBranch (.childCons consBranch .childNil)))) := by
  induction valueIsList with
  | nil =>
      exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember
        (redexStronglyNormalizing IsListValue.nil)
  | @cons head tail headNormal tailIsValue tailIH =>
      exact headExpand IotaHeadStep.iotaListElimCons.toWeakHeadStep
        (consBranchApplication headNormal tailIsValue tailIH)
        (redexStronglyNormalizing (IsListValue.cons headNormal tailIsValue))

end FX1Poly.Core

#print axioms FX1Poly.Core.listElimValueReducible_probe

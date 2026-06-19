import FX1Poly.Core.Eliminators.List.ListElimValueReducibility
import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim
import FX1Poly.Core.Metatheory.Canonicity.RecursiveEliminatorBaseComputation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/Eliminators/Core/ListElimDataTaitMember
    — `listElim` reducibility over the head-expansion-closed data candidate (FTGEN-11, list recursor)

The list-recursor companion to `natElimDataTaitMember`.  `listElim`'s cons ι rule fires to a NESTED `gen_app`
spine `app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)` (NOT a substitution), so the
recursive premise is `consBranchApplication` (the cons branch applied to a normal head, a list-value tail, and a
reducible recursive result lands in the candidate) rather than a `…Reduct` membership.  Proved DIRECTLY over the
head-expansion-closed `dataTaitCandidate` with the `headExpand` Tait hypothesis ABSENT (supplied free by
confluence through the scrutinee congruence).  Same three-move shape as `natElim`/`boolElim`.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas (`listElimValueReducibility`,
`listElim_isStronglyNormalizing_of_strongly_normalizing_branches`, `StepStar.listElimScrutinee`,
`IsNeutral.listElim`, plus the `dataTaitCandidate` lift lemmas).  The file-local `private abbrev`
`listElimConsContractum` mirrors Core's own private cons-contractum abbreviation byte-for-byte.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- The `listElim` cons-ι contractum — `app (app (app consBranch head) tail) (listElim tail nilBranch
consBranch)` (mirrors Core's private `listElimConsContractum` byte-for-byte). -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons tail .childNil)))))
        .childNil))

/-- **★ FTGEN-11 — `listElim` reducibility over `dataTaitCandidate`, no `headExpand`.**  A `listElim` whose
scrutinee is a member of the list data candidate, with a strongly-normalizing motive, a member nil-branch, a
strongly-normalizing cons-branch, the cons-branch application premise (the recursive piece, over the candidate),
and the cons-contractum termination premise, is a member of the result data candidate.  No head-expansion
interface hypothesis: the lift through the scrutinee congruence is supplied unconditionally by confluence. -/
theorem listElimDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsListValue scrutinee)
    (nilBranchMember : dataTaitCandidate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → dataTaitCandidate isValue result →
        dataTaitCandidate isValue (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                (.childCons tail .childNil)))
            (.childCons result .childNil))))
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum motive consBranch head tail nilBranch)) :
    dataTaitCandidate isValue (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) :=
    listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      nilBranchMember.stronglyNormalizing consBranchTerminates
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (listElimCellSpine motive scrutinee nilBranch consBranch)
        (listElimCellSpine motive scrutineeNormalForm nilBranch consBranch) :=
    StepStar.listElimScrutinee scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsList | normalFormIsNeutral
  · have redexStronglyNormalizing : ∀ {listValue : RawTerm scope}, IsListValue listValue →
        IsStronglyNormalizing (listElimCellSpine motive listValue nilBranch consBranch) :=
      fun listValueIsList =>
        listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
          (isListValue_isMember listValueIsList).stronglyNormalizing motiveStronglyNormalizing
          nilBranchMember.stronglyNormalizing consBranchTerminates
    have normalFormCellMember :
        dataTaitCandidate isValue (listElimCellSpine motive scrutineeNormalForm nilBranch consBranch) :=
      listElimValueReducibility (dataTaitCandidate isValue)
        (fun weakHeadStep contractumMember redexStronglyNormalizing =>
          dataTaitCandidate_memberWeakHeadExpansion weakHeadStep redexStronglyNormalizing contractumMember)
        nilBranchMember consBranchApplication redexStronglyNormalizing normalFormIsList
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (listElimCellSpine motive scrutineeNormalForm nilBranch consBranch) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (listElimCellSpine motive scrutineeNormalForm nilBranch consBranch) :=
      dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.listElim normalFormIsNeutral)
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember

end FX1Poly.Core

import FX1Poly.Core.Eliminators.Nat.NatElimValueReducibility
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.RecursiveEliminatorBaseComputation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/Eliminators/Core/NatRecDataTaitMember
    — `natRec` reducibility over the head-expansion-closed data candidate (FTGEN-11, dependent recursor)

The dependent-recursor twin of `natElimDataTaitMember`.  `gen_natRec` shares `gen_natElim`'s substrate metadata
and its SUBSTITUTING successor ι rule, so this is the `gen_natElim → gen_natRec` clone of the `natElim` arm:
proved DIRECTLY over the head-expansion-closed `dataTaitCandidate`, the recursive `succReductMember` premise
threaded over that candidate, and the `headExpand` Tait hypothesis ABSENT (supplied free by confluence through
the scrutinee congruence).  Same three-move shape as `natElim`/`boolElim`.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas (`natRecValueReducibility`,
`natRec_isStronglyNormalizing_of_strongly_normalizing_branches`, `StepStar.natRecScrutinee`, `IsNeutral.natRec`,
plus the `dataTaitCandidate` lift lemmas).  The two file-local `private abbrev`s mirror Core's own private
successor-reduct abbreviations byte-for-byte.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- The `natRec` successor-ι substituted reduct, the `natRecValueReducibility` spelling (mirrors Core's private
`natRecSuccReduct` byte-for-byte). -/
private abbrev natRecSuccReduct {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The `natRec` successor-ι substituted reduct, the SN-helper spelling (mirrors Core's private
`natRecSuccContractum` byte-for-byte; same term as `natRecSuccReduct`, different argument order). -/
private abbrev natRecSuccContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **★ FTGEN-11 — `natRec` reducibility over `dataTaitCandidate`, no `headExpand`.**  The dependent-recursor
twin of `natElimDataTaitMember`. -/
theorem natRecDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsNatValue scrutinee)
    (zeroBranchMember : dataTaitCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succReductMember : ∀ {predecessor : RawTerm scope}, IsNatValue predecessor →
        dataTaitCandidate isValue (natRecSuccReduct motive zeroBranch succBranch predecessor))
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractum currentMotive currentSucc predecessor currentZero)) :
    dataTaitCandidate isValue (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch)
        (natRecCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
    StepStar.natRecScrutinee scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsNat | normalFormIsNeutral
  · have redexStronglyNormalizing : ∀ {natValue : RawTerm scope}, IsNatValue natValue →
        IsStronglyNormalizing (natRecCellSpine motive natValue zeroBranch succBranch) :=
      fun natValueIsNat =>
        natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
          (isNatValue_isMember natValueIsNat).stronglyNormalizing motiveStronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have normalFormCellMember :
        dataTaitCandidate isValue (natRecCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      natRecValueReducibility (dataTaitCandidate isValue)
        (fun weakHeadStep contractumMember redexStronglyNormalizing =>
          dataTaitCandidate_memberWeakHeadExpansion weakHeadStep redexStronglyNormalizing contractumMember)
        zeroBranchMember (fun predecessorIsNat => succReductMember predecessorIsNat)
        redexStronglyNormalizing normalFormIsNat
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (natRecCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (natRecCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.natRec normalFormIsNeutral)
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember

end FX1Poly.Core

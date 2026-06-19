import FX1Poly.Core.Eliminators.Nat.NatElimValueReducibility
import FX1Poly.Core.Eliminators.Nat.NatElimValueMember
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.RecursiveEliminatorBaseComputation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/Eliminators/Core/NatElimDataTaitMember
    — `natElim` reducibility over the head-expansion-closed data candidate (FTGEN-11, RECURSIVE eliminator)

The recursive-eliminator companion to `boolElimDataTaitMember`.  Where `boolElim` is the trivial
(non-recursive) match, `natElim`'s successor ι rule produces a RECURSIVE call (`natElim` on the predecessor),
so Tait's value case needs the recursive `succReductMember` premise — the substantive part of the method.
This file proves the `natElim` arm DIRECTLY over `dataTaitCandidate` (the head-expansion-closed,
formation-side candidate) with the recursive premise threaded over that candidate and the contextual
`headExpand` Tait hypothesis once again ABSENT (supplied free by confluence).  It confirms the FTGEN-11
reconciliation handles recursion, not just the trivial match — the same three-move shape as `boolElim`:
cell SN; scrutinee normal form value-or-neutral dispatch (VALUE → ι via `natElimValueReducibility` with
`dataTaitCandidate_memberWeakHeadExpansion` as the free head-expansion; NEUTRAL → `IsNeutral.natElim` +
`memberOfStronglyNormalizingNeutral`); lift through `StepStar.natElimScrutinee` by
`dataTaitCandidate_memberStepStarExpansion`.

`natRec` and `listElim` are the same proof verbatim modulo their own value-reducibility / SN-helper /
scrutinee-congruence names; option/either and fst/snd/idJ follow the identical shape from their closed
canonical-computation reductions.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas.  The two file-local `private abbrev`s mirror Core's
own private successor-reduct abbreviations byte-for-byte (so the premise types stay definitionally equal to
what the Core lemmas expect).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- The `natElim` successor-ι substituted reduct, the `natElimValueReducibility` spelling (mirrors Core's
private `natElimSuccReduct` byte-for-byte). -/
private abbrev natElimSuccReduct {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The `natElim` successor-ι substituted reduct, the SN-helper spelling (mirrors Core's private
`natElimSuccContractum` byte-for-byte; same term as `natElimSuccReduct`, different argument order). -/
private abbrev natElimSuccContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (succBranch : RawTerm (scope + 2)) (predecessor zeroBranch : RawTerm scope) : RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **★ FTGEN-11 — `natElim` reducibility over `dataTaitCandidate`, no `headExpand`.**  A `natElim` whose
scrutinee is a member of the Nat data candidate, with a strongly-normalizing motive, a member zero-branch, a
strongly-normalizing succ-branch, the recursive succ-reduct membership premise, and the succ-contractum
termination premise, is a member of the result data candidate.  No head-expansion interface hypothesis: the
lift through the scrutinee congruence is supplied unconditionally by confluence. -/
theorem natElimDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsNatValue scrutinee)
    (zeroBranchMember : dataTaitCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succReductMember : ∀ {predecessor : RawTerm scope}, IsNatValue predecessor →
        dataTaitCandidate isValue (natElimSuccReduct motive zeroBranch succBranch predecessor))
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum currentMotive currentSucc predecessor currentZero)) :
    dataTaitCandidate isValue (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
        (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
    StepStar.natElimScrutinee scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsNat | normalFormIsNeutral
  · have redexStronglyNormalizing : ∀ {natValue : RawTerm scope}, IsNatValue natValue →
        IsStronglyNormalizing (natElimCellSpine motive natValue zeroBranch succBranch) :=
      fun natValueIsNat =>
        natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
          (isNatValue_isMember natValueIsNat).stronglyNormalizing motiveStronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have normalFormCellMember :
        dataTaitCandidate isValue (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      natElimValueReducibility (dataTaitCandidate isValue)
        (fun weakHeadStep contractumMember redexStronglyNormalizing =>
          dataTaitCandidate_memberWeakHeadExpansion weakHeadStep redexStronglyNormalizing contractumMember)
        zeroBranchMember (fun predecessorIsNat => succReductMember predecessorIsNat)
        redexStronglyNormalizing normalFormIsNat
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.natElim normalFormIsNeutral)
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember

/-- **★ FTGEN-11.1 propagated — `natElim` reducibility over `dataTaitCandidate`, RECURSION DISCHARGED.**
The self-contained companion of `natElimDataTaitMember`: the recursive `succReductMember` premise (which baked
the recursive call `natElim … predecessor` into the substituted reduct) is replaced by the recursion-FREE
`succBranchSubstClosed` — the succ branch's substitution-closure (substituting a member recursive result and a
numeral predecessor lands in the candidate), exactly the fundamental-theorem-of-the-branch content with no
recursion folded in.  The value case now routes through `natElimValueMemberSelfContained`, which performs the
recursive descent internally via the structural `IsNatValue` IH; the neutral case and the scrutinee-congruence
lift are unchanged.  `succContractumTerminates` is still required (it gives the cell SN at the not-yet-a-value
scrutinee, over an arbitrary SN predecessor — strictly more than the numeral coverage of
`succBranchSubstClosed`). -/
theorem natElimDataTaitMemberSelfContained {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate IsNatValue scrutinee)
    (zeroBranchMember : dataTaitCandidate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchSubstClosed :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentZero : RawTerm scope)
          (currentSucc : RawTerm (scope + 2)) (predecessor recursiveResult : RawTerm scope),
          IsStronglyNormalizing currentMotive → dataTaitCandidate isValue currentZero →
          IsStronglyNormalizing currentSucc → IsNatValue predecessor →
          dataTaitCandidate isValue recursiveResult →
          dataTaitCandidate isValue (RawTerm.subst
            (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor)) currentSucc))
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum currentMotive currentSucc predecessor currentZero)) :
    dataTaitCandidate isValue (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
        (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
    StepStar.natElimScrutinee scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsNat | normalFormIsNeutral
  · have normalFormCellMember :
        dataTaitCandidate isValue (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      natElimValueMemberSelfContained (dataTaitCandidate isValue)
        (fun member => member.stronglyNormalizing)
        (fun member step => member.closedUnderStep step)
        (fun weakHeadStep contractumMember redexStronglyNormalizing =>
          dataTaitCandidate_memberWeakHeadExpansion weakHeadStep redexStronglyNormalizing contractumMember)
        succBranchSubstClosed normalFormIsNat motive zeroBranch succBranch
        motiveStronglyNormalizing zeroBranchMember succBranchTerminates
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (natElimCellSpine motive scrutineeNormalForm zeroBranch succBranch) :=
      dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.natElim normalFormIsNeutral)
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember

end FX1Poly.Core

import FX1Poly.Core.Eliminators.Core.DataEliminatorReducibleScrutineeMember
import FX1Poly.Core.Metatheory.Canonicity.BoolElimCanonicalComputation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Core/Eliminators/Core/BoolElimDataTaitMember
    — `boolElim` reducibility over the HEAD-EXPANSION-CLOSED data candidate (FTGEN-11 reconciliation PoC)

The Core eliminator-reducibility theorems (`boolElimReducibleScrutineeMember` and the recursor twins) are
stated over `CanonicalFormsPredicate isValue` and take a contextual `headExpand` Tait interface hypothesis —
because `CanonicalFormsPredicate` is NOT head-expansion-closed (its "term itself neutral" disjunct breaks under
β-redex head-expansion).  That candidate is incomparable to the `dataTaitCandidate` the fundamental theorem's
FORMATION arm assigns ("SN ∧ every reachable NF is value-or-neutral"), so the generic FT cannot compose
intro+elim over one candidate while the elim arms live over `CanonicalFormsPredicate`.

This file proves the `boolElim` arm DIRECTLY over `dataTaitCandidate` — the head-expansion-closed candidate —
and the `headExpand` hypothesis DISAPPEARS: head-expansion through the scrutinee congruence is supplied
unconditionally by `dataTaitCandidate_memberStepStarExpansion` (confluence).  It is the proof-of-concept that
the FTGEN-11 reconciliation lands: the elim arms CAN be re-based onto the formation-side candidate, so the
generic FT composes intro+elim on ONE candidate with only the natural premises.  The recursor / match /
projection / path-induction arms follow the same three-move shape.

## The three moves

(1) cell SN from the members' SN (`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`);
(2) the scrutinee's normal form is value-or-neutral (`dataTaitCandidate`'s second projection on the SN-supplied
normal form), and the cell reduces to the NF-cell by the scrutinee congruence (`StepStar.boolElimScrutinee`) —
VALUE → ι fires into the candidate (`boolElimValueReducibility` with `dataTaitCandidate_memberWeakHeadExpansion`
as the now-FREE head-expansion), NEUTRAL → the NF-cell is a stuck neutral, a member by
`dataTaitCandidate.memberOfStronglyNormalizingNeutral`;
(3) lift the NF-cell's membership back to the original cell by `dataTaitCandidate_memberStepStarExpansion`.

## Zero-axiom verification

Direct composition of the shipped, audited Core lemmas above.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **★ FTGEN-11 reconciliation PoC — `boolElim` reducibility over `dataTaitCandidate`, no `headExpand`.**  A
`boolElim` whose scrutinee is a member of the bool data candidate, with a strongly-normalizing motive and
member branches, is a member of the result data candidate.  Unlike `boolElimReducibleScrutineeMember` (over
`CanonicalFormsPredicate`), this takes NO head-expansion interface hypothesis — the lift through the scrutinee
congruence is supplied unconditionally by confluence (`dataTaitCandidate_memberStepStarExpansion`). -/
theorem boolElimDataTaitMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : dataTaitCandidate boolIsValue scrutinee)
    (thenBranchMember : dataTaitCandidate isValue thenBranch)
    (elseBranchMember : dataTaitCandidate isValue elseBranch) :
    dataTaitCandidate isValue (boolElimSpine motive scrutinee thenBranch elseBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (boolElimSpine motive scrutinee thenBranch elseBranch) :=
    boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      thenBranchMember.stronglyNormalizing elseBranchMember.stronglyNormalizing
  obtain ⟨scrutineeNormalForm, scrutineeToNormalForm, scrutineeNormalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing scrutineeMember.stronglyNormalizing
  have cellToNormalFormCell :
      StepStar (boolElimSpine motive scrutinee thenBranch elseBranch)
        (boolElimSpine motive scrutineeNormalForm thenBranch elseBranch) :=
    StepStar.boolElimScrutinee scrutineeToNormalForm
  rcases scrutineeMember.2 scrutineeNormalForm scrutineeToNormalForm scrutineeNormalFormIsNormal with
    normalFormIsBool | normalFormIsNeutral
  · have redexStronglyNormalizing : ∀ {boolValue : RawTerm scope}, boolIsValue boolValue →
        IsStronglyNormalizing (boolElimSpine motive boolValue thenBranch elseBranch) :=
      fun boolValueIsBool =>
        boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
          (boolValue_isStronglyNormalizing boolValueIsBool) motiveStronglyNormalizing
          thenBranchMember.stronglyNormalizing elseBranchMember.stronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (boolElimSpine motive scrutineeNormalForm thenBranch elseBranch) :=
      boolElimValueReducibility (dataTaitCandidate isValue)
        (fun weakHeadStep contractumMember redexStronglyNormalizing =>
          dataTaitCandidate_memberWeakHeadExpansion weakHeadStep redexStronglyNormalizing contractumMember)
        thenBranchMember elseBranchMember redexStronglyNormalizing normalFormIsBool
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember
  · have normalFormCellStronglyNormalizing :
        IsStronglyNormalizing (boolElimSpine motive scrutineeNormalForm thenBranch elseBranch) :=
      isStronglyNormalizing_of_stepStar cellToNormalFormCell cellStronglyNormalizing
    have normalFormCellMember :
        dataTaitCandidate isValue (boolElimSpine motive scrutineeNormalForm thenBranch elseBranch) :=
      dataTaitCandidate.memberOfStronglyNormalizingNeutral normalFormCellStronglyNormalizing
        (IsNeutral.boolElim normalFormIsNeutral)
    exact dataTaitCandidate_memberStepStarExpansion cellToNormalFormCell cellStronglyNormalizing
      normalFormCellMember

end FX1Poly.Core

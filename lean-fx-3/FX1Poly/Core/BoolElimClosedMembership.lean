import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Core.BoolElimStrongNormalization
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

/-! # FX1Poly/Core/BoolElimClosedMembership
    — a closed `boolElim` with member branches is a data-candidate member (the elimination half of bool reducibility)

The data-canonicity track has, for `bool`:
* INTRODUCTION membership — `boolTrue` / `boolFalse` are members (`BoolCanonicalFormsCandidate`);
* SCRUTINEE canonicity — a closed bool member reduces to `boolTrue` / `boolFalse`
  (`boolClosedReducesToTrueOrFalse`);
* ELIMINATION computation — a closed `boolElim` on a canonical scrutinee reduces to one of its branches
  (`boolElimCanonicalScrutineeReducesToBranch`).

This file closes the ELIMINATION MEMBERSHIP: a closed `boolElim` whose scrutinee is a canonical bool member
and whose branches are members of a result candidate is ITSELF a member of that result candidate.  This is the
eliminator half of `bool` + `boolElim` reducibility at the closed layer — the recursor lands in the
candidate, not merely normalizes.

## Why this assembles cleanly (and is fundamental-independent)

bool is the simplest eliminator: non-recursive, two branches, no inductive hypothesis.  The three shipped
pieces compose directly (Phase-Z motive shape: the cell carries a stored motive head child, so a motive-SN
hypothesis joins the branch-SN witnesses):

1. The cell is strongly normalizing — `boolElim_isStronglyNormalizing_of_strongly_normalizing_branches` fed
   the motive's SN plus the members' CR1 witnesses (`.stronglyNormalizing`, the `.1` projections).
2. The cell reduces to its then- or else-branch — `boolElimCanonicalScrutineeReducesToBranch` on the canonical
   scrutinee (the scrutinee reaches `boolTrue`/`boolFalse`, the ι rule fires).
3. The chosen branch, being a CLOSED member, reduces to a value (`closedReducesToValue` — a closed member is
   non-neutral by `IsNeutral.noClosed`, so its disjunct collapses to reduces-to-value).

Steps 2 + 3 give `boolElim ↝* branch ↝* value`; with step 1 that is exactly the value-reaching weak-head
expansion `CanonicalFormsPredicate.ofStepStarReachingValue`.  No fundamental theorem, no member
extension — this is pure closed-canonicity assembly, the regime where data weak-head expansion
holds unconditionally.

## Zero-axiom verification

`rcases` on the branch the scrutinee selects, then `ofStepStarReachingValue` fed `closedReducesToValue` on the
selected branch.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(verified by `#print axioms` in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A closed `boolElim` with member branches is a member of the result candidate.**  Given a canonical bool
scrutinee (a member of the bool candidate) and then/else branches that are members of a result candidate
`isValue`, the closed `boolElim` cell is itself a member.  The cell is SN
(`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches` on the members' SN), it reduces to the
selected branch (`boolElimCanonicalScrutineeReducesToBranch`), and that branch — closed and a member — reaches
a value (`closedReducesToValue`); value-reaching weak-head expansion (`ofStepStarReachingValue`) lifts the
membership back to the cell.  The eliminator half of bool reducibility, closed-layer, fundamental-independent. -/
theorem boolElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee thenBranch elseBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee)
    (thenBranchMember : CanonicalFormsPredicate isValue thenBranch)
    (elseBranchMember : CanonicalFormsPredicate isValue elseBranch) :
    CanonicalFormsPredicate isValue
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons scrutinee .childNil))))) := by
  have boolElimStronglyNormalizing :
      IsStronglyNormalizing
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch
                (.childCons scrutinee .childNil))))) :=
    boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      thenBranchMember.stronglyNormalizing elseBranchMember.stronglyNormalizing
  rcases boolElimCanonicalScrutineeReducesToBranch
      (motive := motive) (thenBranch := thenBranch) (elseBranch := elseBranch) scrutineeMember with
    reducesToThen | reducesToElse
  · exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToThen
      boolElimStronglyNormalizing thenBranchMember.closedReducesToValue
  · exact CanonicalFormsPredicate.ofStepStarReachingValue reducesToElse
      boolElimStronglyNormalizing elseBranchMember.closedReducesToValue

end FX1Poly.Core

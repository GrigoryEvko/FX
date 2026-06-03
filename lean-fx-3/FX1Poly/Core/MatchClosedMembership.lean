import FX1Poly.Core.OptionEitherMatchCanonicalComputation
import FX1Poly.Core.StrongNormalizationMatch
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.ApplicationStrongNormalizationForward

/-! # FX1Poly/Core/MatchClosedMembership
    — a closed `optionMatch` / `eitherMatch` with member-respecting branches is a data-candidate member
      (the elimination half of SN-065 / SN-066)

`BoolElimClosedMembership.lean` and `IdEliminatorClosedMembership.lean` closed the elimination MEMBERSHIP for the
PASSIVE-branch eliminators (`boolElim`, `idJ`, `idStrictRec`) — whose ι selects a branch DIRECTLY.  This file is
the APPLIED-branch twin: the elimination membership for the non-recursive sum matchers `optionMatch` and
`eitherMatch`, whose ι rules APPLY the chosen branch to the scrutinee's wrapped payload
(`optionMatch (some v) n s ↝ app s v`, `eitherMatch (inl v) l r ↝ app l v`, …).

The applied-branch shape is exactly why these need more than `boolElim`: the contractum `app branch payload` is
not the branch itself, so (a) the cell-SN ingredient needs the SN-from-SN-branches matcher lemma
(`optionMatch/eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches`) rather than the trivial
branch-SN, and (b) the branch must be a member of a result candidate AT the payload — captured by the
"branch respects SN arguments" hypothesis `∀ value, SN value → member (app branch value)` (the data-candidate
analogue of `branch : SN-candidate ⟶ resultCandidate`, the shape the eventual Tait fundamental theorem supplies
for the some/inl/inr branch).  The `∀ SN value` quantification — rather than "∀ payloadCandidate member" — is
forced by the cell-SN lemma's `someContractumTerminates : ∀ value, SN value → SN (app branch value)` premise; it
is the honest cost of the unparameterized closed-layer data candidate.

## Why this assembles (and is `#672`-independent)

For each ι-arm the scrutinee is a canonical member, so it reduces to its constructor (option/either data
canonicity), the matcher ι fires to `app branch payload`, and:

1. The cell is SN — the SN-from-SN-branches matcher lemma fed the scrutinee's CR1 SN, the branches' SN, and the
   contractum-SN derived from `branchRespectsSN` (member ⟹ SN by CR1).
2. The cell reduces to `app branch payload` — `optionMatch/eitherMatchCanonicalScrutineeReduces` (#692).
3. The payload is SN — the canonical scrutinee `↝* some/inl/inr payload`, which is SN
   (`IsStronglyNormalizing.descendStepStar` from the scrutinee's SN), and the wrapped payload is a subterm
   (`value_isStronglyNormalizing_of_optionSome` / `_of_eitherInl` / `_of_eitherInr`).
4. `app branch payload`, being `branchRespectsSN payload payloadSN`, is a member, hence reaches a value
   (`closedReducesToValue`).

Steps 2 + 4 give `cell ↝* app branch payload ↝* value`; with step 1 that is value-reaching weak-head expansion
`CanonicalFormsPredicate.ofStepStarReachingValue` (#735).  No fundamental theorem, no member extension, no
`#672` — pure closed-canonicity assembly.

## Zero-axiom verification

`rcases` on the canonical computation's branch disjunction, then `ofStepStarReachingValue` fed the cell-SN and
the branch-application member's `closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A closed `optionMatch` with member-respecting branches is a member of the result candidate.**  Given a
canonical option scrutinee, a none-branch member, an SN some-branch, and a some-branch that maps SN arguments to
result-candidate members (`someBranchRespectsSN`), the closed `optionMatch` cell is a member.  The cell is SN
(`optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches`), reduces to the none-branch or to
`app someBranch payload` (`optionMatchCanonicalScrutineeReduces`), and that contractum reaches a value
(`noneBranchMember`/`someBranchRespectsSN` ⟹ `closedReducesToValue`); `ofStepStarReachingValue` lifts membership
to the cell.  The elimination half of SN-065, closed-layer, `#672`-independent. -/
theorem optionMatchClosedIsMember {isValue : RawTerm 0 → Prop}
    {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isOptionValue scrutinee)
    (noneBranchMember : CanonicalFormsPredicate isValue noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch)
    (someBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applicationCell someBranch value)) :
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

/-- **A closed `eitherMatch` with member-respecting branches is a member of the result candidate.**  Symmetric to
`optionMatchClosedIsMember`, but BOTH ι-arms apply a branch (no passive base), so both the left- and
right-branch respect-SN hypotheses are consumed.  The cell is SN
(`eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches` on both contractum-SN witnesses), reduces
to `app leftBranch payload` or `app rightBranch payload` (`eitherMatchCanonicalScrutineeReduces`), and that
contractum reaches a value (`leftBranchRespectsSN`/`rightBranchRespectsSN` ⟹ `closedReducesToValue`).  The
elimination half of SN-066, closed-layer, `#672`-independent. -/
theorem eitherMatchClosedIsMember {isValue : RawTerm 0 → Prop}
    {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isEitherValue scrutinee)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch)
    (leftBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applicationCell leftBranch value))
    (rightBranchRespectsSN : ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate isValue (applicationCell rightBranch value)) :
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

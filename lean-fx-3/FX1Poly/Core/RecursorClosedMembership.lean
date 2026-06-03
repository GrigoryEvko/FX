import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.NeutralTerm

/-! # FX1Poly/Core/RecursorClosedMembership
    — a closed `natElim` / `natRec` on a member Nat scrutinee with reducible branches is a data-candidate member
      (the deferred half of SN-061)

`MatchClosedMembership` / `SigmaProjectionClosedMembership` closed the elimination membership for the
NON-RECURSIVE eliminators.  This file is the RECURSIVE twin: the elimination membership for the Nat recursors
`natElim` / `natRec`, whose ι rule on `natSucc` re-invokes the recursor on the predecessor.  It is the deferred
half of SN-061 — `NatElimValueReducibility` (#732) supplied the numeral VALUE case (parameterized over the result
candidate); this file discharges the SCRUTINEE-REDUCES-TO-NUMERAL regime, instantiating that value case at the
closed data candidate and lifting through the scrutinee reduction.

The assembly consumes the recursive substrate built one step earlier:

* cell SN at the original scrutinee AND `redexStronglyNormalizing` at every numeral come from
  `natElim/natRec_isStronglyNormalizing_of_strongly_normalizing_branches` (the SN-from-SN-branches recursors),
  fed the honest `succContractumTerminates` IH-premise (the recursor-SN obligation the eventual full WF recursion
  discharges — the same conditional-arm discipline `natElimValueReducibility` itself uses);
* the numeral-case membership is `natElimValueReducibility` / `natRecValueReducibility` instantiated at
  `CanonicalFormsPredicate isValue`, with `headExpand` for the CLOSED data candidate (weak-head-expansion holds
  unconditionally at scope 0: a closed contractum is non-neutral by `IsNeutral.noClosed`, so
  `weakHeadExpansionOfMemberNotNeutral` applies via `WeakHeadStep.toStep`);
* the scrutinee, a closed Nat-candidate member, reduces to a numeral (`closedReducesToValue` — Nat canonicity),
  the recursor cell follows under the scrutinee congruence (`StepStar.natElimScrutinee` / `natRecScrutinee`), and
  the numeral cell reaches a value, so `ofStepStarReachingValue` (#735) lifts membership to the original cell.

`succBranchApplication` is the function-space behaviour of the successor branch (its application to a numeral
predecessor and a candidate result lands in the candidate) — exactly the Tait interface the recursor arm of the
fundamental theorem supplies for a reducible succ branch.  `#672`-independent: pure closed-canonicity assembly.

## Zero-axiom verification

`headExpand` from `weakHeadExpansionOfMemberNotNeutral` + `WeakHeadStep.toStep` + `IsNeutral.noClosed`; cell/
recursor SN from the SN-from-SN-branches recursors; numeral membership from `nat(Elim/Rec)ValueReducibility`;
`closedReducesToValue` + scrutinee congruence + `ofStepStarReachingValue`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `natElim` cell over its (scrutinee, zeroBranch, succBranch) spine. -/
private abbrev natElimCell (scrutinee zeroBranch succBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natElim () (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The `natElim` succ-contractum `app (app succBranch predecessor) (natElim predecessor zeroBranch succBranch)`. -/
private abbrev natElimSuccContractumClosed (succBranch predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons (natElimCell predecessor zeroBranch succBranch) .childNil))

/-- **A closed `natElim` on a member Nat scrutinee with reducible branches is a member of the result
candidate.**  The deferred (scrutinee-reduction) half of SN-061: the scrutinee reduces to a numeral
(Nat canonicity), `natElimValueReducibility` lands the numeral recursor cell in the candidate (instantiated at the
closed data candidate, fed the SN-from-SN-branches recursor for `redexStronglyNormalizing` and the data
candidate's closed weak-head-expansion for `headExpand`), and `ofStepStarReachingValue` lifts membership through
the scrutinee congruence to the original cell.  `succContractumTerminates` is the honest recursor-SN IH-premise.
`#672`-independent. -/
theorem natElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {scrutinee zeroBranch succBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm 0, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractumClosed succBranch predecessor zeroBranch)) :
    CanonicalFormsPredicate isValue (natElimCell scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natElimCell value zeroBranch succBranch) :=
    fun valueIsNat =>
      natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natElimCell scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natElimCell numeral zeroBranch succBranch) :=
    natElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember succBranchApplication recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natElimScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

/-- The `natRec` cell over its (scrutinee, zeroBranch, succBranch) spine. -/
private abbrev natRecCell (scrutinee zeroBranch succBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_natRec () (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- The `natRec` succ-contractum `app (app succBranch predecessor) (natRec predecessor zeroBranch succBranch)`. -/
private abbrev natRecSuccContractumClosed (succBranch predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons (natRecCell predecessor zeroBranch succBranch) .childNil))

/-- **A closed `natRec` on a member Nat scrutinee with reducible branches is a member of the result candidate** —
the dependent-recursor twin of `natElimClosedIsMember`, identical assembly via `natRecValueReducibility` and the
`natRec` SN-from-SN-branches recursor. -/
theorem natRecClosedIsMember {isValue : RawTerm 0 → Prop}
    {scrutinee zeroBranch succBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm 0},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm 0, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractumClosed succBranch predecessor zeroBranch)) :
    CanonicalFormsPredicate isValue (natRecCell scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natRecCell value zeroBranch succBranch) :=
    fun valueIsNat =>
      natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natRecCell scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natRecCell numeral zeroBranch succBranch) :=
    natRecValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember succBranchApplication recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natRecScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

end FX1Poly.Core

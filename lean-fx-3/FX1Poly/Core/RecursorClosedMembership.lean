import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.NeutralTerm

/-! # FX1Poly/Core/RecursorClosedMembership
    — a closed `natElim` / `natRec` / `listElim` on a member recursive scrutinee with reducible branches is a
      data-candidate member (the recursor scrutinee-reduction halves)

`MatchClosedMembership` / `SigmaProjectionClosedMembership` close the elimination membership for the
NON-RECURSIVE eliminators.  This file is the RECURSIVE twin: the elimination membership for the recursors
`natElim` / `natRec` (whose ι rule on `natSucc` re-invokes the recursor on the predecessor) and `listElim`
(whose ι rule on `listCons` re-invokes the recursor on the tail).  It is the scrutinee-reduction half —
`NatElimValueReducibility` / `ListElimValueReducibility` supply the numeral / list-value VALUE
case (parameterized over the result candidate); this file discharges the SCRUTINEE-REDUCES-TO-VALUE regime,
instantiating that value case at the closed data candidate and lifting through the scrutinee reduction.

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
  the numeral cell reaches a value, so `ofStepStarReachingValue` lifts membership to the original cell.

`succBranchApplication` is the function-space behaviour of the successor branch (its application to a numeral
predecessor and a candidate result lands in the candidate) — exactly the Tait interface the recursor arm of the
fundamental theorem supplies for a reducible succ branch.  Fundamental-independent: pure closed-canonicity assembly.

## Zero-axiom verification

`headExpand` from `weakHeadExpansionOfMemberNotNeutral` + `WeakHeadStep.toStep` + `IsNeutral.noClosed`; cell/
recursor SN from the SN-from-SN-branches recursors; numeral membership from `nat(Elim/Rec)ValueReducibility`;
`closedReducesToValue` + scrutinee congruence + `ofStepStarReachingValue`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `natElim` cell — `gen_natElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 2, 0]`).  Author order `(motive, scrutinee, zeroBranch, succBranch)`; emitted spine
`(motive, zeroBranch, succBranch, scrutinee)` with the motive under one binder, the succ-branch under TWO
binders, and the scrutinee LAST. -/
private abbrev natElimCell (motive : RawTerm 1) (scrutinee zeroBranch : RawTerm 0)
    (succBranch : RawTerm 2) : RawTerm 0 :=
  .mkGen .gen_natElim ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The `natElim` succ-contractum — now SUBSTITUTING (the Phase-Z succ-iota substitutes the recursive call
into var 0 and the predecessor into var 1 of the two-binder succ-branch):
`succBranch[var 0 := natElim motive zeroBranch succBranch predecessor, var 1 := predecessor]`.  The recursive
call THREADS the same motive and branches at the predecessor. -/
private abbrev natElimSuccContractumClosed (motive : RawTerm 1) (succBranch : RawTerm 2)
    (predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **A closed `natElim` on a member Nat scrutinee with reducible branches is a member of the result
candidate.**  The scrutinee-reduction half: the scrutinee reduces to a numeral
(Nat canonicity), `natElimValueReducibility` lands the numeral recursor cell in the candidate (instantiated at the
closed data candidate, fed the SN-from-SN-branches recursor for `redexStronglyNormalizing` and the data
candidate's closed weak-head-expansion for `headExpand`), and `ofStepStarReachingValue` lifts membership through
the scrutinee congruence to the original cell.

Phase-Z SUBSTITUTING shape: the cell carries a stored motive head child, so a motive-SN hypothesis
(`motiveStronglyNormalizing`) joins the branch-SN witnesses, fed to the SN helper in the PINNED Lane-4 order
`(substitutedReductTerminates, scrutinee, motive, zero, succ)`.  Because the succ-iota SUBSTITUTES rather than
building an app-chain, the succ-branch interface is `substitutedReductMember` — the SUBSTITUTED reduct is a
member of the candidate (universally quantified over the current motive/branches/predecessor; the
substitution-shaped analogue of the old `succBranchApplication`, mirroring the substituting
`substitutedReductTerminates` SN premise).  Fundamental-independent. -/
theorem natElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm 0},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue
          (natElimSuccContractumClosed motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natElimSuccContractumClosed currentMotive currentSucc predecessor currentZero)) :
    CanonicalFormsPredicate isValue (natElimCell motive scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  -- PINNED SN-helper order: substituted-reduct FIRST, scrutinee SECOND, motive THIRD, zero FOURTH, succ FIFTH.
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natElimCell motive value zeroBranch succBranch) :=
    fun valueIsNat =>
      natElim_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing motiveStronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natElimCell motive scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natElimCell motive numeral zeroBranch succBranch) :=
    natElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember (fun predIsValue => substitutedReductMember predIsValue)
      recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natElimScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

/-- The `natRec` cell — `gen_natRec` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 2, 0]`).  Author order `(motive, scrutinee, zeroBranch, succBranch)`; emitted spine
`(motive, zeroBranch, succBranch, scrutinee)` with the motive under one binder, the succ-branch under TWO
binders, and the scrutinee LAST. -/
private abbrev natRecCell (motive : RawTerm 1) (scrutinee zeroBranch : RawTerm 0)
    (succBranch : RawTerm 2) : RawTerm 0 :=
  .mkGen .gen_natRec ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The `natRec` succ-contractum — now SUBSTITUTING (the Phase-Z succ-iota substitutes the recursive call into
var 0 and the predecessor into var 1 of the two-binder succ-branch):
`succBranch[var 0 := natRec motive zeroBranch succBranch predecessor, var 1 := predecessor]`. -/
private abbrev natRecSuccContractumClosed (motive : RawTerm 1) (succBranch : RawTerm 2)
    (predecessor zeroBranch : RawTerm 0) : RawTerm 0 :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **A closed `natRec` on a member Nat scrutinee with reducible branches is a member of the result candidate** —
the dependent-recursor twin of `natElimClosedIsMember`, identical assembly via `natRecValueReducibility` and the
`natRec` SN-from-SN-branches recursor.  Phase-Z SUBSTITUTING shape: a motive-SN hypothesis and the
substituted-reduct membership/termination premises in the PINNED Lane-4 order. -/
theorem natRecClosedIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee zeroBranch : RawTerm 0} {succBranch : RawTerm 2}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm 0},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue
          (natRecSuccContractumClosed motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm 1) (currentSucc : RawTerm 2)
          (predecessor currentZero : RawTerm 0), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natRecSuccContractumClosed currentMotive currentSucc predecessor currentZero)) :
    CanonicalFormsPredicate isValue (natRecCell motive scrutinee zeroBranch succBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  have recursorSN : ∀ {value : RawTerm 0}, IsNatValue value →
      IsStronglyNormalizing (natRecCell motive value zeroBranch succBranch) :=
    fun valueIsNat =>
      natRec_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
        (isNatValue_isMember valueIsNat).stronglyNormalizing motiveStronglyNormalizing
        zeroBranchMember.stronglyNormalizing succBranchTerminates
  have cellStronglyNormalizing : IsStronglyNormalizing (natRecCell motive scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  obtain ⟨numeral, scrutineeToNumeral, numeralIsNat⟩ := scrutineeMember.closedReducesToValue
  have numeralMember : CanonicalFormsPredicate isValue (natRecCell motive numeral zeroBranch succBranch) :=
    natRecValueReducibility (CanonicalFormsPredicate isValue)
      headExpand zeroBranchMember (fun predIsValue => substitutedReductMember predIsValue)
      recursorSN numeralIsNat
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.natRecScrutinee scrutineeToNumeral) cellStronglyNormalizing
    numeralMember.closedReducesToValue

/-- The `listElim` cell — `gen_listElim` in the Phase-Z motive shape (arity 4, `binderShifts =
[1, 0, 0, 0]`).  Author order `(motive, scrutinee, nilBranch, consBranch)`; emitted spine
`(motive, nilBranch, consBranch, scrutinee)` with the motive under one binder and the scrutinee LAST. -/
private abbrev listElimCell (motive : RawTerm 1) (scrutinee nilBranch consBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_listElim ()
    (.childCons motive
      (.childCons nilBranch
        (.childCons consBranch
          (.childCons scrutinee .childNil))))

/-- The `listElim` cons-contractum `app (app (app consBranch head) tail) (listElim motive tail nilBranch
consBranch)` — the Phase-Z cons ι THREADS the same motive into the recursive call. -/
private abbrev listElimConsContractumClosed (motive : RawTerm 1)
    (consBranch head tail nilBranch : RawTerm 0) : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (listElimCell motive tail nilBranch consBranch)
        .childNil))

/-- **A closed `listElim` on a member List scrutinee with reducible branches is a member of the result
candidate.**  The scrutinee-reduction half — the list twin of `natElimClosedIsMember`: the
scrutinee reduces to a list value (List canonicity), `listElimValueReducibility` lands the list-value
recursor cell in the candidate (instantiated at the closed data candidate, fed the SN-from-SN-branches recursor
for `redexStronglyNormalizing` and the data candidate's closed weak-head-expansion for `headExpand`), and
`ofStepStarReachingValue` lifts membership through the scrutinee congruence to the original cell.
`consContractumTerminates` is the honest recursor-SN IH-premise (the same conditional-arm discipline
`listElimValueReducibility` itself uses for `redexStronglyNormalizing`).  `consBranchApplication` takes the head
in `RawTerm.isStepNormalForm` form (not SN) and the tail as an `IsListValue` — exactly the Tait interface the
list recursor arm supplies for a reducible cons branch.  Phase-Z motive shape: the cell carries a stored motive
head child, so a motive-SN hypothesis (`motiveStronglyNormalizing`) joins the branch-SN witnesses, fed to the
SN helper in the PINNED order (scrutinee, motive, nil, cons).  Fundamental-independent: pure closed-canonicity
assembly. -/
theorem listElimClosedIsMember {isValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {scrutinee nilBranch consBranch : RawTerm 0}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsListValue scrutinee)
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
    (consContractumTerminates : ∀ head tail : RawTerm 0,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractumClosed motive consBranch head tail nilBranch)) :
    CanonicalFormsPredicate isValue (listElimCell motive scrutinee nilBranch consBranch) := by
  have headExpand : ∀ {redexTerm contractum : RawTerm 0},
      WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
      IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm :=
    fun weakHeadStep memberContractum redexSN =>
      CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral weakHeadStep.toStep redexSN
        memberContractum IsNeutral.noClosed
  -- PINNED SN-helper order: scrutinee FIRST, motive SECOND, nil THIRD, cons FOURTH.
  have recursorSN : ∀ {value : RawTerm 0}, IsListValue value →
      IsStronglyNormalizing (listElimCell motive value nilBranch consBranch) :=
    fun valueIsList =>
      listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
        (isListValue_isMember valueIsList).stronglyNormalizing motiveStronglyNormalizing
        nilBranchMember.stronglyNormalizing consBranchTerminates
  have cellStronglyNormalizing :
      IsStronglyNormalizing (listElimCell motive scrutinee nilBranch consBranch) :=
    listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      nilBranchMember.stronglyNormalizing consBranchTerminates
  obtain ⟨listValue, scrutineeToList, listValueIsList⟩ := scrutineeMember.closedReducesToValue
  have listValueMember :
      CanonicalFormsPredicate isValue (listElimCell motive listValue nilBranch consBranch) :=
    listElimValueReducibility (CanonicalFormsPredicate isValue)
      headExpand nilBranchMember consBranchApplication recursorSN listValueIsList
  exact CanonicalFormsPredicate.ofStepStarReachingValue
    (StepStar.listElimScrutinee scrutineeToList) cellStronglyNormalizing
    listValueMember.closedReducesToValue

end FX1Poly.Core

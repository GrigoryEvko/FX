import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

/-! # FX1Poly/Core/RecursorReducibleScrutineeMember
    — the GENERAL-scrutinee regime of `natElim` / `natRec` recursor reducibility: the full SN-061 dispatch

`NatElimValueReducibility` (#732) discharged the VALUE regime (`natElim numeral …` lands in the candidate) and
`NatElimNeutralScrutineeMember` (the neutral arm) the NEUTRAL regime (`natElim neutral …` is itself neutral, so
a member by CR3).  Both deferred "the scrutinee-reduction outer recursion (a non-value non-neutral scrutinee
threading down to its numeral)" as the remaining half of SN-061.  This file ships that outer recursion as a
single GENERAL-scrutinee theorem, completing recursor reducibility over an ARBITRARY reducible Nat scrutinee.

The key is that the Nat data candidate `CanonicalFormsPredicate IsNatValue` BUILDS IN the value-or-neutral
dichotomy: a member is strongly normalizing AND `IsNeutral ∨ ∃ numeral, StepStar scrutinee numeral ∧ IsNatValue
numeral`.  So a reducible scrutinee splits exactly into the two shipped regimes, dispatched here:

  * **neutral disjunct** → `CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral` on the recursor cell's SN
    (`natElim_isStronglyNormalizing_of_strongly_normalizing_branches`) and its neutrality (`IsNeutral.natElim`);
  * **value disjunct** (scrutinee reduces to a numeral) → `natElimValueReducibility` lands the numeral recursor
    cell in the candidate, and `ofStepStarReachingValue` (#735) lifts that membership back through the scrutinee
    congruence `StepStar.natElimScrutinee` to the original cell — but the lift needs the numeral cell to REACH A
    VALUE, which is the value side of ITS disjunct, extracted by refuting its neutrality.

`<recursor>_notNeutral_ofNatValueScrutinee` is that refutation: a recursor over a NUMERAL scrutinee is never
neutral, because `IsNeutral.natElim`/`natRec` is the unique neutral-recursor constructor and demands a neutral
scrutinee, while a numeral's head is a constructor (`IsNeutral.rootGenerator_ne_natZero` / `_ne_natSucc`).  This
is the open-scope generalization of `RecursorClosedMembership.natElimClosedIsMember`: at scope 0 the neutral
disjunct is vacuous (`IsNeutral.noClosed`), so the closed theorem needed no dispatch; here the neutral arm is
live.  `#672`-independent — pure Tait dispatch over the shipped candidate regimes.

The conditional hypotheses (`headExpand`, the branch interface, `succContractumTerminates`) are exactly the
honest Tait interface `natElimValueReducibility` already exposes; this file adds the scrutinee dichotomy on top.

## Zero-axiom verification

The non-neutrality refutations are `cases` on the (concrete-index) recursor-cell neutrality giving scrutinee
neutrality, then `cases` on `IsNatValue` + the shipped `rootGenerator_ne_natZero` / `_ne_natSucc` discriminators
(`Generator.noConfusion`-clean, no propext leak).  The dispatch is `rcases` on the candidate disjunct +
`memberOfStronglyNormalizingNeutral` / (`natElimValueReducibility` + `ofStepStarReachingValue` + `resolve_left`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print
axioms` in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **A `natElim` over a numeral scrutinee is never neutral.**  `IsNeutral.natElim` is the unique constructor
producing a neutral `natElim` cell and it demands a neutral scrutinee, but a numeral's head is `natZero` /
`natSucc` (refuted by the `rootGenerator_ne_natZero` / `_ne_natSucc` discriminators).  The fact the value-case
lift consumes to extract "the numeral cell reaches a value" from the cell's candidate membership. -/
theorem natElim_notNeutral_ofNatValueScrutinee {scope : Nat}
    {numeral zeroBranch succBranch : RawTerm scope}
    (numeralIsNat : IsNatValue numeral) :
    ¬ IsNeutral (natElimCellSpine numeral zeroBranch succBranch) := by
  intro cellNeutral
  cases cellNeutral with
  | natElim scrutineeNeutral =>
      cases numeralIsNat with
      | zero => exact scrutineeNeutral.rootGenerator_ne_natZero rfl
      | succ _ => exact scrutineeNeutral.rootGenerator_ne_natSucc rfl

/-- **A `natRec` over a numeral scrutinee is never neutral** — the dependent-recursor twin of
`natElim_notNeutral_ofNatValueScrutinee`, via the `IsNeutral.natRec` constructor and the same numeral-head
discriminators. -/
theorem natRec_notNeutral_ofNatValueScrutinee {scope : Nat}
    {numeral zeroBranch succBranch : RawTerm scope}
    (numeralIsNat : IsNatValue numeral) :
    ¬ IsNeutral (natRecCellSpine numeral zeroBranch succBranch) := by
  intro cellNeutral
  cases cellNeutral with
  | natRec scrutineeNeutral =>
      cases numeralIsNat with
      | zero => exact scrutineeNeutral.rootGenerator_ne_natZero rfl
      | succ _ => exact scrutineeNeutral.rootGenerator_ne_natSucc rfl

/-- **`natElim` reducibility over a general reducible scrutinee (the SN-061 outer recursion).**  Given a
scrutinee that is a member of the Nat data candidate (so strongly normalizing AND neutral-or-reduces-to-a-
numeral), reducible branches, and the honest Tait interface (`headExpand` weak-head expansion of the result
candidate, the succ-branch application interface, the succ-contractum SN premise), the `natElim` cell is a member
of the result candidate.  Dispatches on the scrutinee's built-in disjunct: NEUTRAL → the recursor cell is neutral
and SN, hence a member by CR3 (`memberOfStronglyNormalizingNeutral`); VALUE → the numeral recursor cell is a
member (`natElimValueReducibility`) that reaches a value (its non-neutrality forces the value side of its
disjunct), lifted back through the scrutinee congruence by `ofStepStarReachingValue`.  Completes SN-061 for
`natElim`; the closed `natElimClosedIsMember` is the scope-0 special case (neutral disjunct vacuous). -/
theorem natElimReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons (natElimCellSpine predecessor zeroBranch succBranch) .childNil)))) :
    CanonicalFormsPredicate isValue (natElimCellSpine scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natElimCellSpine scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨numeral, scrutineeToNumeral, numeralIsNat⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.natElim scrutineeNeutral)
  · have recursorStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing (natElimCellSpine value zeroBranch succBranch) :=
      fun valueIsNat =>
        natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
          (isNatValue_isMember valueIsNat).stronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have numeralMember :
        CanonicalFormsPredicate isValue (natElimCellSpine numeral zeroBranch succBranch) :=
      natElimValueReducibility (CanonicalFormsPredicate isValue)
        headExpand zeroBranchMember succBranchApplication recursorStronglyNormalizing numeralIsNat
    have numeralCellReachesValue :
        ∃ value : RawTerm scope,
          StepStar (natElimCellSpine numeral zeroBranch succBranch) value ∧ isValue value :=
      numeralMember.2.resolve_left (natElim_notNeutral_ofNatValueScrutinee numeralIsNat)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.natElimScrutinee scrutineeToNumeral) cellStronglyNormalizing numeralCellReachesValue

/-- **`natRec` reducibility over a general reducible scrutinee** — the dependent-recursor twin of
`natElimReducibleScrutineeMember`.  Identical dispatch on the Nat-candidate disjunct via `natRecValueReducibility`
and `StepStar.natRecScrutinee`, with `natRec_notNeutral_ofNatValueScrutinee` extracting the value side.  Completes
SN-061 for `natRec`. -/
theorem natRecReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (succContractumTerminates : ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons (natRecCellSpine predecessor zeroBranch succBranch) .childNil)))) :
    CanonicalFormsPredicate isValue (natRecCellSpine scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natRecCellSpine scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
      scrutineeMember.stronglyNormalizing zeroBranchMember.stronglyNormalizing succBranchTerminates
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨numeral, scrutineeToNumeral, numeralIsNat⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.natRec scrutineeNeutral)
  · have recursorStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing (natRecCellSpine value zeroBranch succBranch) :=
      fun valueIsNat =>
        natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
          (isNatValue_isMember valueIsNat).stronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have numeralMember :
        CanonicalFormsPredicate isValue (natRecCellSpine numeral zeroBranch succBranch) :=
      natRecValueReducibility (CanonicalFormsPredicate isValue)
        headExpand zeroBranchMember succBranchApplication recursorStronglyNormalizing numeralIsNat
    have numeralCellReachesValue :
        ∃ value : RawTerm scope,
          StepStar (natRecCellSpine numeral zeroBranch succBranch) value ∧ isValue value :=
      numeralMember.2.resolve_left (natRec_notNeutral_ofNatValueScrutinee numeralIsNat)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.natRecScrutinee scrutineeToNumeral) cellStronglyNormalizing numeralCellReachesValue

end FX1Poly.Core

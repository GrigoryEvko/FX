import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.ListElimNeutralScrutineeMember
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

/-! # FX1Poly/Core/RecursorReducibleScrutineeMember
    — the GENERAL-scrutinee regime of the recursive eliminators `natElim` / `natRec` / `listElim`: the full
      reducible-scrutinee dispatch

`NatElimValueReducibility` / `ListElimValueReducibility` discharge the VALUE regime (`natElim
numeral …` / `listElim listValue …` lands in the candidate) and `NatElimNeutralScrutineeMember` /
`ListElimNeutralScrutineeMember` the NEUTRAL regime (the recursor over a neutral scrutinee is itself neutral, so
a member by CR3).  The remaining half is "the scrutinee-reduction outer recursion (a non-value non-neutral
scrutinee threading down to its constructor)".  This file ships that outer
recursion as a single GENERAL-scrutinee theorem per recursor, completing recursive-eliminator reducibility over
an ARBITRARY reducible scrutinee — bringing the three recursive eliminators to general-scrutinee parity.

The key is that the Nat data candidate `CanonicalFormsPredicate IsNatValue` BUILDS IN the value-or-neutral
dichotomy: a member is strongly normalizing AND `IsNeutral ∨ ∃ numeral, StepStar scrutinee numeral ∧ IsNatValue
numeral`.  So a reducible scrutinee splits exactly into the two shipped regimes, dispatched here:

  * **neutral disjunct** → `CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral` on the recursor cell's SN
    (`natElim_isStronglyNormalizing_of_strongly_normalizing_branches`) and its neutrality (`IsNeutral.natElim`);
  * **value disjunct** (scrutinee reduces to a numeral) → `natElimValueReducibility` lands the numeral recursor
    cell in the candidate, and `ofStepStarReachingValue` lifts that membership back through the scrutinee
    congruence `StepStar.natElimScrutinee` to the original cell — but the lift needs the numeral cell to REACH A
    VALUE, which is the value side of ITS disjunct, extracted by refuting its neutrality.

`<recursor>_notNeutral_ofNatValueScrutinee` is that refutation: a recursor over a NUMERAL scrutinee is never
neutral, because `IsNeutral.natElim`/`natRec` is the unique neutral-recursor constructor and demands a neutral
scrutinee, while a numeral's head is a constructor (`IsNeutral.rootGenerator_ne_natZero` / `_ne_natSucc`).  This
is the open-scope generalization of `RecursorClosedMembership.natElimClosedIsMember`: at scope 0 the neutral
disjunct is vacuous (`IsNeutral.noClosed`), so the closed theorem needs no dispatch; here the neutral arm is
live.  Fundamental-independent — pure Tait dispatch over the shipped candidate regimes.

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

/-- The `natElim` succ-iota SUBSTITUTED reduct (Phase-Z shape):
`succBranch[var 0 := natElim motive zeroBranch succBranch predecessor, var 1 := predecessor]`.  Spelled to
match the substituting `succContractumTerminates` premise of
`natElim_isStronglyNormalizing_of_strongly_normalizing_branches`. -/
private abbrev natElimSuccContractumOn {scope : Nat} (motive : RawTerm (scope + 1))
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

/-- The `natRec` succ-iota SUBSTITUTED reduct — the `gen_natRec` mirror of `natElimSuccContractumOn`. -/
private abbrev natRecSuccContractumOn {scope : Nat} (motive : RawTerm (scope + 1))
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

/-- **A `natElim` over a numeral scrutinee is never neutral.**  `IsNeutral.natElim` is the unique constructor
producing a neutral `natElim` cell and it demands a neutral scrutinee, but a numeral's head is `natZero` /
`natSucc` (refuted by the `rootGenerator_ne_natZero` / `_ne_natSucc` discriminators).  The fact the value-case
lift consumes to extract "the numeral cell reaches a value" from the cell's candidate membership. -/
theorem natElim_notNeutral_ofNatValueScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {numeral zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (numeralIsNat : IsNatValue numeral) :
    ¬ IsNeutral (natElimCellSpine motive numeral zeroBranch succBranch) := by
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
    {motive : RawTerm (scope + 1)} {numeral zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (numeralIsNat : IsNatValue numeral) :
    ¬ IsNeutral (natRecCellSpine motive numeral zeroBranch succBranch) := by
  intro cellNeutral
  cases cellNeutral with
  | natRec scrutineeNeutral =>
      cases numeralIsNat with
      | zero => exact scrutineeNeutral.rootGenerator_ne_natZero rfl
      | succ _ => exact scrutineeNeutral.rootGenerator_ne_natSucc rfl

/-- **`natElim` reducibility over a general reducible scrutinee (the outer recursion).**  Given a
scrutinee that is a member of the Nat data candidate (so strongly normalizing AND neutral-or-reduces-to-a-
numeral), reducible branches, and the honest Tait interface (`headExpand` weak-head expansion of the result
candidate, the succ-branch application interface, the succ-contractum SN premise), the `natElim` cell is a member
of the result candidate.  Dispatches on the scrutinee's built-in disjunct: NEUTRAL → the recursor cell is neutral
and SN, hence a member by CR3 (`memberOfStronglyNormalizingNeutral`); VALUE → the numeral recursor cell is a
member (`natElimValueReducibility`) that reaches a value (its non-neutrality forces the value side of its
disjunct), lifted back through the scrutinee congruence by `ofStepStarReachingValue`.  Completes general-scrutinee
reducibility for `natElim`; the closed `natElimClosedIsMember` is the scope-0 special case (neutral disjunct vacuous). -/
theorem natElimReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue (natElimSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
          (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natElimSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    CanonicalFormsPredicate isValue (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  -- PINNED SN-helper order: substituted-reduct FIRST, scrutinee SECOND, motive THIRD, zero FOURTH, succ FIFTH.
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
    natElim_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨numeral, scrutineeToNumeral, numeralIsNat⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.natElim scrutineeNeutral)
  · have recursorStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing (natElimCellSpine motive value zeroBranch succBranch) :=
      fun valueIsNat =>
        natElim_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
          (isNatValue_isMember valueIsNat).stronglyNormalizing motiveStronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have numeralMember :
        CanonicalFormsPredicate isValue (natElimCellSpine motive numeral zeroBranch succBranch) :=
      natElimValueReducibility (CanonicalFormsPredicate isValue)
        headExpand zeroBranchMember (fun predIsValue => substitutedReductMember predIsValue)
        recursorStronglyNormalizing numeralIsNat
    have numeralCellReachesValue :
        ∃ value : RawTerm scope,
          StepStar (natElimCellSpine motive numeral zeroBranch succBranch) value ∧ isValue value :=
      numeralMember.2.resolve_left (natElim_notNeutral_ofNatValueScrutinee numeralIsNat)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.natElimScrutinee scrutineeToNumeral) cellStronglyNormalizing numeralCellReachesValue

/-- **`natRec` reducibility over a general reducible scrutinee** — the dependent-recursor twin of
`natElimReducibleScrutineeMember`.  Identical dispatch on the Nat-candidate disjunct via `natRecValueReducibility`
and `StepStar.natRecScrutinee`, with `natRec_notNeutral_ofNatValueScrutinee` extracting the value side.  Completes
general-scrutinee reducibility for `natRec`. -/
theorem natRecReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsNatValue scrutinee)
    (zeroBranchMember : CanonicalFormsPredicate isValue zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch)
    (substitutedReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor →
        CanonicalFormsPredicate isValue (natRecSuccContractumOn motive succBranch predecessor zeroBranch))
    (substitutedReductTerminates :
        ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
          (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
          IsStronglyNormalizing
            (natRecSuccContractumOn currentMotive currentSucc predecessor currentZero)) :
    CanonicalFormsPredicate isValue (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
    natRec_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      zeroBranchMember.stronglyNormalizing succBranchTerminates
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨numeral, scrutineeToNumeral, numeralIsNat⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.natRec scrutineeNeutral)
  · have recursorStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing (natRecCellSpine motive value zeroBranch succBranch) :=
      fun valueIsNat =>
        natRec_isStronglyNormalizing_of_strongly_normalizing_branches substitutedReductTerminates
          (isNatValue_isMember valueIsNat).stronglyNormalizing motiveStronglyNormalizing
          zeroBranchMember.stronglyNormalizing succBranchTerminates
    have numeralMember :
        CanonicalFormsPredicate isValue (natRecCellSpine motive numeral zeroBranch succBranch) :=
      natRecValueReducibility (CanonicalFormsPredicate isValue)
        headExpand zeroBranchMember (fun predIsValue => substitutedReductMember predIsValue)
        recursorStronglyNormalizing numeralIsNat
    have numeralCellReachesValue :
        ∃ value : RawTerm scope,
          StepStar (natRecCellSpine motive numeral zeroBranch succBranch) value ∧ isValue value :=
      numeralMember.2.resolve_left (natRec_notNeutral_ofNatValueScrutinee numeralIsNat)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.natRecScrutinee scrutineeToNumeral) cellStronglyNormalizing numeralCellReachesValue

/-- **A `listElim` over a list-value scrutinee is never neutral** — the list twin of
`natElim_notNeutral_ofNatValueScrutinee`.  `IsNeutral.listElim` is the unique constructor producing a neutral
`listElim` cell and it demands a neutral scrutinee, but a list value's head is `listNil` / `listCons` (refuted by
the `rootGenerator_ne_listNil` / `_ne_listCons` discriminators).  The fact the value-case lift consumes to
extract "the list-value cell reaches a value" from the cell's candidate membership. -/
theorem listElim_notNeutral_ofListValueScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {value nilBranch consBranch : RawTerm scope}
    (valueIsList : IsListValue value) :
    ¬ IsNeutral (listElimCellSpine motive value nilBranch consBranch) := by
  intro cellNeutral
  cases cellNeutral with
  | listElim scrutineeNeutral =>
      cases valueIsList with
      | nil => exact scrutineeNeutral.rootGenerator_ne_listNil rfl
      | cons _ _ => exact scrutineeNeutral.rootGenerator_ne_listCons rfl

/-- **`listElim` reducibility over a general reducible scrutinee (the outer recursion)** — the list twin
of `natElimReducibleScrutineeMember`, completing recursive-eliminator reducibility for `listElim`.  Given a
scrutinee that is a member of the List data candidate (so strongly normalizing AND neutral-or-reduces-to-a-list-
value), reducible branches, and the honest Tait interface (`headExpand`, the 3-argument cons-branch application
interface, the cons-contractum SN premise), the `listElim` cell is a member of the result candidate.  Phase-Z
motive shape: the cell carries a stored motive head child, so a motive-SN premise (`motiveStronglyNormalizing`)
joins the witnesses (fed to the SN helper in the PINNED order scrutinee, motive, nil, cons).  Dispatches
on the scrutinee's built-in disjunct: NEUTRAL → the recursor cell is neutral and SN, a member by CR3
(`memberOfStronglyNormalizingNeutral`); VALUE → the list-value recursor cell is a member
(`listElimValueReducibility`) that reaches a value (its non-neutrality forces the value side), lifted back
through the scrutinee congruence by `ofStepStarReachingValue`. -/
theorem listElimReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate IsListValue scrutinee)
    (nilBranchMember : CanonicalFormsPredicate isValue nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → CanonicalFormsPredicate isValue result →
        CanonicalFormsPredicate isValue
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons result .childNil))))
    (consContractumTerminates : ∀ head tail : RawTerm scope,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons (listElimCellSpine motive tail nilBranch consBranch) .childNil)))) :
    CanonicalFormsPredicate isValue (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  -- PINNED SN-helper order: scrutinee FIRST, motive SECOND, nil THIRD, cons FOURTH.
  have cellStronglyNormalizing :
      IsStronglyNormalizing (listElimCellSpine motive scrutinee nilBranch consBranch) :=
    listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      nilBranchMember.stronglyNormalizing consBranchTerminates
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨value, scrutineeToValue, valueIsList⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.listElim scrutineeNeutral)
  · have recursorStronglyNormalizing : ∀ {listValue : RawTerm scope}, IsListValue listValue →
        IsStronglyNormalizing (listElimCellSpine motive listValue nilBranch consBranch) :=
      fun listValueIsList =>
        listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
          (isListValue_isMember listValueIsList).stronglyNormalizing motiveStronglyNormalizing
          nilBranchMember.stronglyNormalizing consBranchTerminates
    have valueMember :
        CanonicalFormsPredicate isValue (listElimCellSpine motive value nilBranch consBranch) :=
      listElimValueReducibility (CanonicalFormsPredicate isValue)
        headExpand nilBranchMember consBranchApplication recursorStronglyNormalizing valueIsList
    have valueCellReachesValue :
        ∃ reached : RawTerm scope,
          StepStar (listElimCellSpine motive value nilBranch consBranch) reached ∧ isValue reached :=
      valueMember.2.resolve_left (listElim_notNeutral_ofListValueScrutinee valueIsList)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.listElimScrutinee scrutineeToValue) cellStronglyNormalizing valueCellReachesValue

end FX1Poly.Core

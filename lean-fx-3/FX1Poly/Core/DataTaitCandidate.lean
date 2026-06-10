import FX1Poly.Core.EmptyTaitCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate

/-! # FX1Poly/Core/DataTaitCandidate
    — the HEAD-EXPANSION-CLOSED data (canonical-forms) Tait candidate, parameterized by a value
    predicate, zero-axiom

This generalizes `EmptyTaitCandidate` from the empty type (whose value set is empty) to ANY data type
with a value predicate `isValue` (bool → `{boolTrue, boolFalse}`, nat → numerals, …).  It is the single
candidate the §5 candidate-bridge edit pins each data type code to, exactly as `emptyTypeCell` is pinned
to `emptyTaitCandidate`.

The naive choice `CanonicalFormsPredicate isValue` (= `SN ∧ (term itself neutral ∨ term reduces to a
value)`) is a reducibility candidate but is NOT head-expansion-closed: when a member sits in the LEFT
(`term itself neutral`) disjunct, a β-redex reducing to that neutral member is itself not neutral (its
head is a λ) and does not reduce to a value (a neutral never reaches a value), so it falls out of the
candidate.  That breaks the fundamental theorem's Π-INTRODUCTION arm, which needs every codomain candidate
to be `HeadExpansionClosed` — and a data type genuinely appears as a Π codomain after a polymorphic
instantiation `X ↦ DataType` (a λ into the data type).  This is exactly the obstruction `emptyTaitCandidate`
fixed for the empty type; `dataTaitCandidate` fixes it uniformly for every data type.

`dataTaitCandidate isValue` is the CORRECT data candidate: "strongly normalizing AND every reachable normal
form is a value or neutral".  The reduction-stable formulation (a property of the term's reachable normal
forms, not of the term itself) is head-expansion-closed by per-term confluence, exactly as in
`emptyTaitCandidate` (which is the `isValue := fun _ => False` instance — see
`dataTaitCandidate_false_iff_emptyTaitCandidate`).

  * **No closed member is non-value** — a closed strongly-normalizing term reaches a closed normal form,
    which the candidate forces value-or-neutral, but closed neutrals do not exist (`IsNeutral.noClosed`), so
    it is a value.  This is `closedReducesToValue`: closed data canonicity (a closed member reduces to a
    constructor) — the SN-047/SN-049 payload, candidate-bridge-ready.
  * **Reducibility candidate** (CR1/CR2/CR3) — CR1 is the first conjunct; CR2 prepends the step to each
    reachable-normal-form chain; CR3 splits the reduction chain at its head (refl gives the term's own
    value-or-neutral status via `Or.inr` neutrality, trans delegates to a reduct member).  No appeal to
    `isValue`, so it holds for every data value predicate uniformly.
  * **Head-expansion-closed** (`HeadExpansionClosed`) — a spined β-redex inherits membership from its
    contractum, by per-term confluence (`confluence_of_localJoin_and_accessible`) with the single betaSpine
    step plus the normal form's rigidity (`eq_of_noStep`).  The Π-codomain property the FT consumes.
  * **Member weak-head expansion** — the general-`WeakHeadStep` analogue, by the same confluence argument.

## Zero-axiom verification

CR1/CR2/CR3 are projections + a two-arm `cases` on `StepStar`; head-expansion and member weak-head
expansion are per-term confluence (`Acc.ndrec`, axiom-clean) + `eq_of_noStep`.  No `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The head-expansion-closed data (canonical-forms) Tait candidate**, parameterized by a value
predicate.  "Strongly normalizing AND every reachable normal form is a value or neutral."  The Girard
canonical-forms candidate in reduction-stable form, so it is head-expansion-closed.  Contrast
`CanonicalFormsPredicate isValue` (members may be neutral THEMSELVES), which is not head-expansion-closed.
`emptyTaitCandidate` is the `isValue := fun _ => False` instance. -/
def dataTaitCandidate {scope : Nat} (isValue : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    ∀ normalForm : RawTerm scope, StepStar term normalForm →
      RawTerm.isStepNormalForm normalForm → (isValue normalForm ∨ IsNeutral normalForm)

/-- **CR1: every member is strongly normalizing** — the first conjunct. -/
theorem dataTaitCandidate.stronglyNormalizing {scope : Nat} {isValue : RawTerm scope → Prop}
    {term : RawTerm scope} (member : dataTaitCandidate isValue term) : IsStronglyNormalizing term :=
  member.1

/-- **CR2: forward closure under one `Step`.**  A reduct is strongly normalizing (`Acc.inv`), and any
reachable normal form of the reduct is reachable from the term (prepend the step), hence value-or-neutral. -/
theorem dataTaitCandidate.closedUnderStep {scope : Nat} {isValue : RawTerm scope → Prop}
    {term reduct : RawTerm scope} (member : dataTaitCandidate isValue term) (step : Step term reduct) :
    dataTaitCandidate isValue reduct := by
  refine ⟨member.1.inv step, ?_⟩
  intro normalForm reductToNF nfIsNormal
  exact member.2 normalForm (StepStar.trans step reductToNF) nfIsNormal

/-- **CR3: neutral expansion.**  A neutral term whose every one-step reduct is a member is a member: it is
strongly normalizing (all reducts are, `Acc.intro`), and any reachable normal form chain splits at the head
— the reflexive chain gives the term's own neutrality (`Or.inr`), a `trans` chain delegates to the reduct
member. -/
theorem dataTaitCandidate.neutralExpansion {scope : Nat} {isValue : RawTerm scope → Prop}
    {term : RawTerm scope} (termIsNeutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm scope, Step term reduct → dataTaitCandidate isValue reduct) :
    dataTaitCandidate isValue term := by
  refine ⟨Acc.intro term (fun reduct stepToReduct => (reductsMembers reduct stepToReduct).1), ?_⟩
  intro normalForm termToNF nfIsNormal
  cases termToNF with
  | refl _ => exact Or.inr termIsNeutral
  | trans termHeadStep tailChain =>
      exact (reductsMembers _ termHeadStep).2 normalForm tailChain nfIsNormal

/-- **The data Tait candidate IS a Girard reducibility candidate** (CR1+CR2+CR3), for every value
predicate. -/
theorem dataTaitCandidate_isReducibilityCandidate {scope : Nat} {isValue : RawTerm scope → Prop} :
    IsReducibilityCandidate (dataTaitCandidate isValue) :=
  ⟨dataTaitCandidate.stronglyNormalizing,
   dataTaitCandidate.closedUnderStep,
   dataTaitCandidate.neutralExpansion⟩

/-- **Head-expansion-closed — the property `CanonicalFormsPredicate isValue` lacks.**  A spined β-redex
inherits membership from its contractum: it is strongly normalizing (`betaSpineHeadExpansion`), and any
reachable normal form — by per-term confluence with the single `betaSpine` step to the contractum, plus the
normal form's rigidity (`eq_of_noStep`) collapsing the join apex onto it — is reachable from the contractum,
hence value-or-neutral.  Exactly what the fundamental theorem's Π-introduction arm needs of every codomain
candidate (`DependentArrowCandidate.abstraction`). -/
theorem dataTaitCandidate_headExpansionClosed {scope : Nat} {isValue : RawTerm scope → Prop} :
    HeadExpansionClosed (dataTaitCandidate isValue) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  refine ⟨betaSpineHeadExpansion domainAnnSN argumentSN contractumMember.1, ?_⟩
  intro normalForm redexToNF nfIsNormal
  have redexToContractum : StepStar
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine)
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    StepStar.single (WeakHeadStep.betaSpine).toStep
  obtain ⟨commonReduct, normalFormToCommon, contractumToCommon⟩ :=
    confluence_of_localJoin_and_accessible
      (betaSpineHeadExpansion domainAnnSN argumentSN contractumMember.1) redexToNF redexToContractum
  have commonEqNormalForm : commonReduct = normalForm :=
    StepStar.eq_of_noStep (fun reduct step =>
      (RawTerm.isStepNormalForm_blocks_step nfIsNormal reduct step).elim) normalFormToCommon
  rw [commonEqNormalForm] at contractumToCommon
  exact contractumMember.2 normalForm contractumToCommon nfIsNormal

/-- **Member weak-head expansion (general `WeakHeadStep`).**  A strongly-normalizing term that
weak-head-steps to a member is a member: by the same confluence argument as `headExpansionClosed`, any
reachable normal form is reachable from the contractum, hence value-or-neutral. -/
theorem dataTaitCandidate_memberWeakHeadExpansion {scope : Nat} {isValue : RawTerm scope → Prop}
    {source reduct : RawTerm scope} (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : dataTaitCandidate isValue reduct) :
    dataTaitCandidate isValue source := by
  refine ⟨sourceStronglyNormalizing, ?_⟩
  intro normalForm sourceToNF nfIsNormal
  obtain ⟨commonReduct, normalFormToCommon, reductToCommon⟩ :=
    confluence_of_localJoin_and_accessible sourceStronglyNormalizing sourceToNF
      (StepStar.single weakHeadStep.toStep)
  have commonEqNormalForm : commonReduct = normalForm :=
    StepStar.eq_of_noStep (fun reduct step =>
      (RawTerm.isStepNormalForm_blocks_step nfIsNormal reduct step).elim) normalFormToCommon
  rw [commonEqNormalForm] at reductToCommon
  exact reductMember.2 normalForm reductToCommon nfIsNormal

/-- **★ Closed data canonicity: a CLOSED member reduces to a VALUE.**  The neutral disjunct is ruled out
by `IsNeutral.noClosed` (no closed term is a stuck eliminator), so the member's reachable normal form is a
value.  Combined with a proof that a closed well-typed term is a member (the candidate bridge + fundamental
theorem), this is data canonicity — a closed term of the data type reduces to a constructor. -/
theorem dataTaitCandidate.closedReducesToValue {isValue : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : dataTaitCandidate isValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isValue value ∧ RawTerm.isStepNormalForm value := by
  obtain ⟨normalForm, reachesNF, nfIsNormal⟩ := exists_normalForm_of_isStronglyNormalizing member.1
  rcases member.2 normalForm reachesNF nfIsNormal with isVal | isNeutral
  · exact ⟨normalForm, reachesNF, isVal, nfIsNormal⟩
  · exact (IsNeutral.noClosed isNeutral).elim

/-- **A normal value is a member of its data Tait candidate.**  A value that is a structural normal form is
strongly normalizing (no `Step`, `Acc.intro` vacuous) and reduces only to itself, a value.  The
constructor-reducibility helper a data type instantiates for its normal constructors. -/
theorem dataTaitCandidate.memberOfValue {scope : Nat} {isValue : RawTerm scope → Prop}
    {value : RawTerm scope} (valueIsNormal : RawTerm.isStepNormalForm value) (valueIsValue : isValue value) :
    dataTaitCandidate isValue value := by
  refine ⟨Acc.intro value (fun reduct step =>
    (RawTerm.isStepNormalForm_blocks_step valueIsNormal reduct step).elim), ?_⟩
  intro normalForm valueToNF _nfIsNormal
  cases valueToNF with
  | refl _ => exact Or.inl valueIsValue
  | trans valueHeadStep _ =>
      exact (RawTerm.isStepNormalForm_blocks_step valueIsNormal _ valueHeadStep).elim

/-- **`emptyTaitCandidate` is the `fun _ => False` instance** — the generalization is faithful.  With the
empty value predicate, "value or neutral" collapses to "neutral", recovering `emptyTaitCandidate` exactly
(up to `False ∨ ·`).  Confirms `dataTaitCandidate` subsumes the candidate-bridge's empty candidate. -/
theorem dataTaitCandidate_false_iff_emptyTaitCandidate {scope : Nat} (term : RawTerm scope) :
    dataTaitCandidate (fun _ => False) term ↔ emptyTaitCandidate term := by
  dsimp only [dataTaitCandidate, emptyTaitCandidate]
  constructor
  · rintro ⟨sn, reach⟩
    exact ⟨sn, fun nf chain nfNormal => (reach nf chain nfNormal).resolve_left (fun isFalse => isFalse)⟩
  · rintro ⟨sn, reach⟩
    exact ⟨sn, fun nf chain nfNormal => Or.inr (reach nf chain nfNormal)⟩

/-- **The bool data Tait candidate** — the candidate-bridge-ready candidate for `boolTypeCell` (the
`isValue := boolIsValue` instance).  A closed member reduces to `boolTrue` or `boolFalse`
(`closedBoolTaitReducesToValue`): closed bool canonicity (SN-047), candidate-bridge-ready exactly as
`emptyTaitCandidate` is for `emptyTypeCell`. -/
def boolTaitCandidate {scope : Nat} : RawTerm scope → Prop := dataTaitCandidate boolIsValue

/-- **The bool Tait candidate is a reducibility candidate.** -/
theorem boolTaitCandidate_isReducibilityCandidate {scope : Nat} :
    IsReducibilityCandidate (boolTaitCandidate (scope := scope)) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The bool Tait candidate is head-expansion-closed** — Π-codomain-ready (the property a generic data
candidate must have to serve as the `X ↦ Bool` instantiation codomain). -/
theorem boolTaitCandidate_headExpansionClosed {scope : Nat} :
    HeadExpansionClosed (boolTaitCandidate (scope := scope)) :=
  dataTaitCandidate_headExpansionClosed

/-- **★ Closed bool canonicity: a closed member of the bool Tait candidate reduces to `boolTrue` or
`boolFalse`.**  The SN-047 payload shape — the bool analogue of `emptyTaitCandidate.noClosedMember`. -/
theorem closedBoolTaitReducesToValue {term : RawTerm 0} (member : boolTaitCandidate term) :
    ∃ value : RawTerm 0, StepStar term value ∧ boolIsValue value ∧ RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue member

end FX1Poly.Core

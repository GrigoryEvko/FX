import FX1Poly.Core.EmptyTaitCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate

/-! Probe: generic head-expansion-closed data Tait candidate, generalizing emptyTaitCandidate
    from "every reachable NF is neutral" to "every reachable NF is isValue-or-neutral". -/

namespace FX1Poly.Core

open StepStar

/-- The head-expansion-closed data (canonical-forms) Tait candidate, parameterized by a value predicate:
"strongly normalizing AND every reachable normal form is a value or neutral".  The reduction-stable
formulation (contrast `CanonicalFormsPredicate isValue`, whose "term itself neutral" left disjunct is not
head-expansion-closed).  `emptyTaitCandidate` is the `isValue := fun _ => False` instance. -/
def dataTaitCandidate {scope : Nat} (isValue : RawTerm scope → Prop) (term : RawTerm scope) : Prop :=
  IsStronglyNormalizing term ∧
    ∀ normalForm : RawTerm scope, StepStar term normalForm →
      RawTerm.isStepNormalForm normalForm → (isValue normalForm ∨ IsNeutral normalForm)

theorem dataTaitCandidate.stronglyNormalizing {scope : Nat} {isValue : RawTerm scope → Prop}
    {term : RawTerm scope} (member : dataTaitCandidate isValue term) : IsStronglyNormalizing term :=
  member.1

theorem dataTaitCandidate.closedUnderStep {scope : Nat} {isValue : RawTerm scope → Prop}
    {term reduct : RawTerm scope} (member : dataTaitCandidate isValue term) (step : Step term reduct) :
    dataTaitCandidate isValue reduct := by
  refine ⟨member.1.inv step, ?_⟩
  intro normalForm reductToNF nfIsNormal
  exact member.2 normalForm (StepStar.trans step reductToNF) nfIsNormal

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

theorem dataTaitCandidate_isReducibilityCandidate {scope : Nat} {isValue : RawTerm scope → Prop} :
    IsReducibilityCandidate (dataTaitCandidate isValue) :=
  ⟨dataTaitCandidate.stronglyNormalizing,
   dataTaitCandidate.closedUnderStep,
   dataTaitCandidate.neutralExpansion⟩

theorem dataTaitCandidate_headExpansionClosed {scope : Nat} {isValue : RawTerm scope → Prop} :
    HeadExpansionClosed (dataTaitCandidate isValue) := by
  intro body argument spine argumentSN contractumMember
  refine ⟨betaSpineHeadExpansion argumentSN contractumMember.1, ?_⟩
  intro normalForm redexToNF nfIsNormal
  have redexToContractum : StepStar
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine)
      (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) :=
    StepStar.single (WeakHeadStep.betaSpine).toStep
  obtain ⟨commonReduct, normalFormToCommon, contractumToCommon⟩ :=
    confluence_of_localJoin_and_accessible
      (betaSpineHeadExpansion argumentSN contractumMember.1) redexToNF redexToContractum
  have commonEqNormalForm : commonReduct = normalForm :=
    StepStar.eq_of_noStep (fun reduct step =>
      (RawTerm.isStepNormalForm_blocks_step nfIsNormal reduct step).elim) normalFormToCommon
  rw [commonEqNormalForm] at contractumToCommon
  exact contractumMember.2 normalForm contractumToCommon nfIsNormal

theorem dataTaitCandidate_memberWeakHeadExpansion {scope : Nat} {isValue : RawTerm scope → Prop}
    {source reduct : RawTerm scope} (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source) (reductMember : dataTaitCandidate isValue reduct) :
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

/-- THE canonicity payload: a CLOSED member reduces to a VALUE (the neutral disjunct is ruled out by
`IsNeutral.noClosed`). -/
theorem dataTaitCandidate.closedReducesToValue {isValue : RawTerm 0 → Prop} {term : RawTerm 0}
    (member : dataTaitCandidate isValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isValue value ∧ RawTerm.isStepNormalForm value := by
  obtain ⟨normalForm, reachesNF, nfIsNormal⟩ := exists_normalForm_of_isStronglyNormalizing member.1
  rcases member.2 normalForm reachesNF nfIsNormal with isVal | isNeutral
  · exact ⟨normalForm, reachesNF, isVal, nfIsNormal⟩
  · exact (IsNeutral.noClosed isNeutral).elim

/-- A normal value is a member of its data Tait candidate. -/
theorem dataTaitCandidate.memberOfValue {scope : Nat} {isValue : RawTerm scope → Prop}
    {value : RawTerm scope} (valueIsNormal : RawTerm.isStepNormalForm value) (valueIsValue : isValue value) :
    dataTaitCandidate isValue value := by
  refine ⟨Acc.intro value (fun reduct step =>
    (RawTerm.isStepNormalForm_blocks_step valueIsNormal reduct step).elim), ?_⟩
  intro normalForm valueToNF nfIsNormal
  cases valueToNF with
  | refl _ => exact Or.inl valueIsValue
  | trans valueHeadStep _ =>
      exact (RawTerm.isStepNormalForm_blocks_step valueIsNormal _ valueHeadStep).elim

-- Bool instantiation + closed-bool canonicity (the SN-047 payload shape).
def boolTaitCandidate {scope : Nat} : RawTerm scope → Prop := dataTaitCandidate boolIsValue

theorem closedBoolTaitReducesToValue {term : RawTerm 0} (member : boolTaitCandidate term) :
    ∃ value : RawTerm 0, StepStar term value ∧ boolIsValue value ∧ RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue member

-- emptyTaitCandidate is the fun _ => False instance (up to False-or simp), confirming the generalization.
example {scope : Nat} (term : RawTerm scope) :
    dataTaitCandidate (fun _ => False) term ↔ emptyTaitCandidate term := by
  unfold dataTaitCandidate emptyTaitCandidate
  constructor
  · rintro ⟨sn, reach⟩
    exact ⟨sn, fun nf chain nfNormal => (reach nf chain nfNormal).resolve_left (fun h => h)⟩
  · rintro ⟨sn, reach⟩
    exact ⟨sn, fun nf chain nfNormal => Or.inr (reach nf chain nfNormal)⟩

end FX1Poly.Core

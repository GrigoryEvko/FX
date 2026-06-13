import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepTable
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/IntervalCanonicalFormsCandidate
    — the interval (bridge-dimension) data reducibility candidate, unconditional + zero-axiom

The data-candidate family (`BoolCanonicalFormsCandidate` … `UnitCanonicalFormsCandidate`) instantiates the
generic `CanonicalFormsPredicate isValue` Tait candidate at each data type.  This file provides the instance
for the INTERVAL — the bridge-dimension type of the gen_param internal-parametricity substrate
(`gen_intervalCode`, inhabited by the endpoint constructors `gen_interval0` / `gen_interval1`).  Structurally
the interval is the bool twin: two nullary value constructors.

`isIntervalValue term` holds when `term` is an endpoint cell.  The candidate
`CanonicalFormsPredicate isIntervalValue` is the Tait reducibility set for the interval: the
strongly-normalizing terms that are neutral or reduce to an endpoint.  This is the valueConstructor-role
sconing coverage for the interval endpoints — the data core of the OP1-INT bridge-row admission.

Like the other data candidates, the fundamental-gated half ("a closed well-typed interval term is a
member") is NOT claimed here; the canonical-form extraction shown is fundamental-free.

## Zero-axiom verification

Endpoint values are normal forms by `rfl` over the decidable structural `isStepNormalForm` (the endpoint
cells are no redex roots and have empty children).  Membership uses `Acc.intro` over the nullary
no-step inversion (the endpoints admit no reduction) and `StepStar.refl`.  The candidate is
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`; canonicity is
`CanonicalFormsPredicate.closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open StepStar

/-- The left endpoint cell `0 : dim` — `reducible` so it transparently unfolds for `rfl`/inversion. -/
abbrev intervalZeroValueCell {scope : Nat} : RawTerm scope := .mkGen .gen_interval0 () .childNil

/-- The right endpoint cell `1 : dim`. -/
abbrev intervalOneValueCell {scope : Nat} : RawTerm scope := .mkGen .gen_interval1 () .childNil

/-- **The interval value predicate**: a term is an interval value when it is one of the two endpoint
constructors.  The `isValue` instance the generic canonical-forms candidate is specialized at to obtain
the interval reducibility candidate — the bool twin (two nullary values). -/
def isIntervalValue {scope : Nat} (term : RawTerm scope) : Prop :=
  term = intervalZeroValueCell ∨ term = intervalOneValueCell

/-- **Interval endpoints are structural normal forms.**  An endpoint cell is no redex root and has empty
children, so `isStepNormalFormBool` computes to `true`.  The sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isIntervalValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsEndpoint : isIntervalValue value) : RawTerm.isStepNormalForm value := by
  rcases valueIsEndpoint with valueEq | valueEq <;> (rw [valueEq]; rfl)

/-- **The interval data reducibility candidate.**  `CanonicalFormsPredicate isIntervalValue` — the
strongly-normalizing terms that are neutral or reduce to an endpoint — is a full Girard reducibility
candidate (CR1+CR2+CR3), unconditionally.  The Tait candidate for the bridge-dimension type, the
valueConstructor-role sconing coverage of the interval endpoints. -/
theorem intervalCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isIntervalValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal
    isIntervalValue_impliesStepNormalForm

/-- **The left endpoint admits no Step reduction** (nullary non-redex head). -/
theorem Step.no_step_from_interval0 {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_interval0 () .childNil) target := by
  intro reduction
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The right endpoint admits no Step reduction.** -/
theorem Step.no_step_from_interval1 {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_interval1 () .childNil) target := by
  intro reduction
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The left endpoint is a member of the interval candidate** — strongly normalizing (no step fires)
and reflexively reaching itself, an interval value. -/
theorem intervalZeroValueCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) isIntervalValue intervalZeroValueCell :=
  ⟨Acc.intro intervalZeroValueCell
      (fun _reduct stepFromEndpoint => absurd stepFromEndpoint Step.no_step_from_interval0),
    Or.inr ⟨intervalZeroValueCell, StepStar.refl intervalZeroValueCell, Or.inl rfl⟩⟩

/-- **The right endpoint is a member of the interval candidate** — dual of
`intervalZeroValueCell_isMember`. -/
theorem intervalOneValueCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) isIntervalValue intervalOneValueCell :=
  ⟨Acc.intro intervalOneValueCell
      (fun _reduct stepFromEndpoint => absurd stepFromEndpoint Step.no_step_from_interval1),
    Or.inr ⟨intervalOneValueCell, StepStar.refl intervalOneValueCell, Or.inr rfl⟩⟩

/-- **Closed interval-candidate members reduce to an endpoint** — canonicity for the bridge dimension,
modulo membership; the extraction is fundamental-free. -/
theorem intervalClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isIntervalValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isIntervalValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

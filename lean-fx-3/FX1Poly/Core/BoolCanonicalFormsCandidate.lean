import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/BoolCanonicalFormsCandidate
    — the first concrete data reducibility candidate: bool (SN-063 data core), unconditional + zero-axiom

`CanonicalFormsCandidate.lean` proved the GENERIC canonical-forms reducibility candidate
(`CanonicalFormsPredicate isValue` is an `IsReducibilityCandidate` once data values are normal forms, the
neutral-closure half discharged unconditionally by `IsNeutral.closedUnderStep`).  This file instantiates that
machine at the simplest data type — **bool** — producing the first honest, unconditional, zero-axiom data
reducibility candidate.

`boolIsValue term` holds when `term` is the `true` or the `false` constructor cell.  The candidate
`CanonicalFormsPredicate boolIsValue` is the Tait reducibility set for the boolean type: the strongly-
normalizing terms that are neutral or reduce to a boolean constructor.  Both canonical inhabitants
(`boolTrueCell`, `boolFalseCell`) are members.

This is the data core of SN-063 (bool reducibility).  The remaining SN-063 content — `boolElim` preserving
reducibility under a dependent motive — is the eliminator-reducibility step that consumes this candidate, and
SN-047 (closed-bool canonicity) is the cascade of this candidate into the `ReducibleTypeStep` model.

## Zero-axiom verification

`boolIsValue`-values are normal forms by `decide` over the decidable structural `isStepNormalForm` (a boolean
constructor is no redex root and has empty children).  Membership uses `Acc.intro` over `Step.no_step_from_-
boolTrue` / `Step.no_step_from_boolFalse` (the constructors admit no reduction) and `StepStar.refl`.  The
candidate itself is `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal` (whose only obligation is
the normality fact).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `true` constructor cell — `reducible` so it transparently unfolds for `decide`/inversion. -/
abbrev boolTrueCell {scope : Nat} : RawTerm scope := .mkGen .gen_boolTrue () .childNil

/-- The `false` constructor cell. -/
abbrev boolFalseCell {scope : Nat} : RawTerm scope := .mkGen .gen_boolFalse () .childNil

/-- **The bool value predicate**: a term is a boolean value when it is the `true` or the `false`
constructor.  This is the `isValue` instance the generic canonical-forms candidate is specialized at to
obtain the bool reducibility candidate. -/
def boolIsValue {scope : Nat} (term : RawTerm scope) : Prop :=
  term = boolTrueCell ∨ term = boolFalseCell

/-- **Boolean values are structural normal forms.**  A `true` / `false` constructor cell is no redex root
and has empty children, so `isStepNormalFormBool` computes to `true`.  This is the sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem boolIsValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsBool : boolIsValue value) : RawTerm.isStepNormalForm value := by
  rcases valueIsBool with valueEq | valueEq <;> (rw [valueEq]; rfl)

/-- **The bool data reducibility candidate.**  `CanonicalFormsPredicate boolIsValue` — the strongly-
normalizing terms that are neutral or reduce to a boolean constructor — is a full Girard reducibility
candidate (CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and
the only data fact, value-normality, is `boolIsValue_impliesStepNormalForm`.  This is the Tait candidate for
the boolean type, the data core of SN-063. -/
theorem boolCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) boolIsValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal boolIsValue_impliesStepNormalForm

/-- **`true` is a member of the bool candidate.**  It is strongly normalizing (a normal form: no `Step`
fires, `Step.no_step_from_boolTrue`) and reduces (reflexively) to itself, a boolean value.  The boolean
constructor's reducibility — `true` inhabits its type's reducibility candidate. -/
theorem boolTrueCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) boolIsValue boolTrueCell :=
  ⟨Acc.intro boolTrueCell
      (fun _reduct stepFromBool => absurd stepFromBool Step.no_step_from_boolTrue),
    Or.inr ⟨boolTrueCell, StepStar.refl boolTrueCell, Or.inl rfl⟩⟩

/-- **`false` is a member of the bool candidate.**  Dual of `boolTrueCell_isMember` via
`Step.no_step_from_boolFalse`. -/
theorem boolFalseCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) boolIsValue boolFalseCell :=
  ⟨Acc.intro boolFalseCell
      (fun _reduct stepFromBool => absurd stepFromBool Step.no_step_from_boolFalse),
    Or.inr ⟨boolFalseCell, StepStar.refl boolFalseCell, Or.inr rfl⟩⟩

/-- **Closed bool-candidate members reduce to `true` or `false`** — canonicity for booleans, modulo
membership.  A closed member of the bool candidate is non-neutral (no closed neutral, `IsNeutral.noClosed`),
so by `CanonicalFormsPredicate.closedReducesToValue` it reduces to a boolean value, i.e. to `boolTrueCell` or
`boolFalseCell`.  Combined with "a closed well-typed term of bool type is a member" (the fundamental theorem,
gated on `#672` / SN-043) this is SN-047 closed-bool canonicity.  The extraction shown here is `#672`-free. -/
theorem boolClosedReducesToTrueOrFalse {term : RawTerm 0}
    (member : CanonicalFormsPredicate boolIsValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ (value = boolTrueCell ∨ value = boolFalseCell) :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

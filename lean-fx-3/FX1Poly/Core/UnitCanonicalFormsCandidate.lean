import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/UnitCanonicalFormsCandidate
    — the unit data reducibility candidate, unconditional + zero-axiom

The data-candidate family (`BoolCanonicalFormsCandidate` … `PairCanonicalFormsCandidate`) instantiates the
generic `CanonicalFormsPredicate isValue` Tait candidate at each standard data type.  This file provides the
instance for the SIMPLEST possible data candidate: the unit type has a single nullary constructor.

`isUnitValue term` holds when `term` is the unit constructor cell `gen_unit ()`.  The candidate
`CanonicalFormsPredicate isUnitValue` is the Tait reducibility set for the unit type: the strongly-normalizing
terms that are neutral or reduce to the unit value.  Because unit has exactly one inhabitant, closed
canonicity is sharper than for the other data types — a closed candidate member reduces to THE unit cell, not
merely to "some value" (`unitClosedReducesToUnitCell`).

This is the data core of unit canonicity.  Like the other data
candidates, the fundamental-gated half ("a closed well-typed term of unit type is a member", via the fundamental
theorem) is NOT claimed here; the canonical-form extraction shown is fundamental-free.

## Zero-axiom verification

`isUnitValue`-values are normal forms by `rfl` over the decidable structural `isStepNormalForm` (the unit
cell is no redex root and has empty children).  Membership uses `Acc.intro` over `Step.no_step_from_unit`
(the unit constructor admits no reduction) and `StepStar.refl`.  The candidate is
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal` (whose only obligation is the normality
fact); canonicity is `CanonicalFormsPredicate.closedReducesToValue`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The unit constructor cell — `reducible` so it transparently unfolds for `rfl`/inversion. -/
abbrev unitCell {scope : Nat} : RawTerm scope := .mkGen .gen_unit () .childNil

/-- **The unit value predicate**: a term is a unit value when it is the unit constructor.  This is the
`isValue` instance the generic canonical-forms candidate is specialized at to obtain the unit reducibility
candidate. -/
def isUnitValue {scope : Nat} (term : RawTerm scope) : Prop :=
  term = unitCell

/-- **The unit value is a structural normal form.**  The unit constructor cell is no redex root and has
empty children, so `isStepNormalFormBool` computes to `true`.  This is the sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isUnitValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsUnit : isUnitValue value) : RawTerm.isStepNormalForm value := by
  rw [valueIsUnit]; rfl

/-- **The unit data reducibility candidate.**  `CanonicalFormsPredicate isUnitValue` — the strongly-
normalizing terms that are neutral or reduce to the unit constructor — is a full Girard reducibility
candidate (CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and
the only data fact, value-normality, is `isUnitValue_impliesStepNormalForm`.  The Tait candidate for the unit
type. -/
theorem unitCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isUnitValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isUnitValue_impliesStepNormalForm

/-- **The unit value is a member of the unit candidate.**  It is strongly normalizing (a normal form: no
`Step` fires, `Step.no_step_from_unit`) and reduces (reflexively) to itself, the unit value.  The unit
constructor's reducibility — the unit cell inhabits its type's reducibility candidate. -/
theorem unitCell_isMember {scope : Nat} :
    CanonicalFormsPredicate (scope := scope) isUnitValue unitCell :=
  ⟨Acc.intro unitCell
      (fun _reduct stepFromUnit => absurd stepFromUnit Step.no_step_from_unit),
    Or.inr ⟨unitCell, StepStar.refl unitCell, rfl⟩⟩

/-- **Closed unit-candidate members reduce to a unit value** — canonicity for unit, modulo membership.  A
closed member of the unit candidate is non-neutral (no closed neutral, `IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to the unit constructor.  Combined with "a closed
well-typed term of unit type is a member" (the fundamental theorem) this is the
unit slice of closed-data canonicity.  The extraction shown here is fundamental-free. -/
theorem unitClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isUnitValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isUnitValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

/-- **Closed unit-candidate members reduce to THE unit cell** — the sharper unit canonicity.  Because the
unit type has exactly one inhabitant, the canonical-form extraction collapses to a single reduct: every
closed member reduces to `unitCell`.  (For multi-constructor data types the analogue is only "reduces to some
value"; unit's uniqueness makes the target definite.) -/
theorem unitClosedReducesToUnitCell {term : RawTerm 0}
    (member : CanonicalFormsPredicate isUnitValue term) :
    StepStar term unitCell := by
  obtain ⟨value, reducesToValue, valueIsUnit⟩ := unitClosedReducesToValue member
  rw [valueIsUnit] at reducesToValue
  exact reducesToValue

end FX1Poly.Core

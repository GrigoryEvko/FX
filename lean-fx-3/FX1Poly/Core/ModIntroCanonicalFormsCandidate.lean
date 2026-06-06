import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/ModIntroCanonicalFormsCandidate
    — the modal box data reducibility candidate, unconditional + zero-axiom

The data-candidate family (`BoolCanonicalFormsCandidate` … `UnitCanonicalFormsCandidate`) instantiates the
generic `CanonicalFormsPredicate isValue` Tait candidate at the standard data types.  This file moves into the
MODAL layer — the FX-specific graded-modal core — with the first modal reducibility candidate: the modal box
introduction `modIntro`.

`gen_modIntro` is a one-child constructor (the boxed payload): structurally it is exactly the `option some`
shape (a single unary constructor carrying one payload), so its reducibility candidate is the unary-constructor
instance of the generic machine, mirroring `OptionCanonicalFormsCandidate`'s `some` branch.  `isModIntroValue
term` holds when `term` is `modIntro payload` with the payload a structural normal form; the candidate
`CanonicalFormsPredicate isModIntroValue` is the Tait reducibility set for the modal box type.

The candidate is over the β+ι reduction relation `Step` (not the separate raw-η `Step.eta`): `modIntro` is a
constructor, not an eliminator, so no β/ι rule has it as the outer redex head, and a `Step` out of it reduces
exactly its payload child (`Step.from_modIntro`).  This is the data core of modal modIntro
reducibility.  The remaining modal-modIntro content — modal `O`-fire confinement and `modElim` preserving
reducibility — is the eliminator-reducibility step that consumes this candidate, separately.

## Zero-axiom verification

`isModIntroValue`-values are normal forms: `modIntro payload` with a normal payload is no redex root and its
`isStepNormalFormBool` reduces to the payload's (the one-child spine, `Bool.and_true`).  Membership is the
generic `CanonicalFormsPredicate.memberOfValue`; the candidate is `isReducibilityCandidateOfValuesNormal`
(whose only obligation is the normality fact); canonicity is `closedReducesToValue`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The modal box introduction cell over one payload — `reducible` so it transparently unfolds for
inversion. -/
abbrev modIntroCell {scope : Nat} (payload : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_modIntro () (.childCons payload .childNil)

/-- **The modal box value predicate**: a term is a modal value when it is `modIntro payload` with the payload
a structural normal form.  The single unary constructor of the modal box type — the `isValue` instance the
generic canonical-forms candidate is specialized at to obtain the modal box reducibility candidate. -/
def isModIntroValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ payload : RawTerm scope, term = modIntroCell payload ∧ RawTerm.isStepNormalForm payload

/-- **Modal box values are structural normal forms.**  `modIntro payload` with a normal payload is no redex
root (the modal box is a constructor, not an eliminator) and its `isStepNormalFormBool` reduces to the
payload's (the one-child spine).  This is the sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isModIntroValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsModIntro : isModIntroValue value) : RawTerm.isStepNormalForm value := by
  obtain ⟨payload, valueEq, payloadNormal⟩ := valueIsModIntro
  subst valueEq
  show (RawTerm.isStepNormalFormBool payload && true) = true
  rw [Bool.and_true]
  exact payloadNormal

/-- **The modal box data reducibility candidate.**  `CanonicalFormsPredicate isModIntroValue` — the strongly-
normalizing terms that are neutral or reduce to a modal box value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the only
data fact, value-normality, is `isModIntroValue_impliesStepNormalForm`.  The Tait candidate for the modal box
type, the first modal-layer reducibility candidate. -/
theorem modIntroCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isModIntroValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isModIntroValue_impliesStepNormalForm

/-- **A modal box of a normal payload is a member of the modal candidate.**  Given a normal payload,
`modIntro payload` is a normal value, so it is strongly normalizing and reduces (reflexively) to itself — the
modal box introduction's reducibility: `modIntro` of a reducible-normal payload inhabits its type's
reducibility candidate. -/
theorem modIntroValue_isMember {scope : Nat} {payload : RawTerm scope}
    (payloadNormal : RawTerm.isStepNormalForm payload) :
    CanonicalFormsPredicate isModIntroValue (modIntroCell payload) :=
  CanonicalFormsPredicate.memberOfValue
    (isModIntroValue_impliesStepNormalForm ⟨payload, rfl, payloadNormal⟩)
    ⟨payload, rfl, payloadNormal⟩

/-- **Closed modal-candidate members reduce to a modal box** — canonicity for the modal box, modulo
membership.  A closed member of the modal candidate is non-neutral (no closed neutral, `IsNeutral.noClosed`),
so by `CanonicalFormsPredicate.closedReducesToValue` it reduces to a `modIntro` constructor.  Combined with "a
closed well-typed term of modal box type is a member" (the fundamental theorem) this
is the modal slice of canonicity.  The extraction shown here is fundamental-free. -/
theorem modIntroClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isModIntroValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isModIntroValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

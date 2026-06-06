import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/OptionCanonicalFormsCandidate
    — the option data candidate: a nullary + a unary constructor, zero-axiom

The option type pairs a NULLARY constructor `none` with a UNARY constructor `some value` whose payload is a
value of the element type (carried as a structural normal form, not a recursive option).  So `IsOptionValue`
is a plain disjunction: `none`, or `some value` with `value` normal — combining the `bool` nullary shape and
the `pair`-component normal-child shape, without recursion.

`CanonicalFormsPredicate IsOptionValue` is the Tait reducibility candidate for the option type; every option
value is a member, and a CLOSED member reduces to `none` or a `some` (option-canonicity).

## Zero-axiom verification

`none` is a structural normal form by computation; `some value` with `value` normal is no redex root and its
`isStepNormalFormBool` reduces to the payload's (the one-child spine recursion).  Membership uses
`CanonicalFormsPredicate.memberOfValue`; the candidate is `isReducibilityCandidateOfValuesNormal`; canonicity
is `closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `none` constructor cell. -/
abbrev optionNoneCell {scope : Nat} : RawTerm scope := .mkGen .gen_optionNone () .childNil

/-- The `some` constructor cell over a payload. -/
abbrev optionSomeCell {scope : Nat} (payload : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionSome () (.childCons payload .childNil)

/-- **The option value predicate.**  A term is an option value when it is `none`, or `some payload` with the
payload a structural normal form (a value of the element type).  A plain disjunction (no recursion — the
payload's type is the element type, not the option type). -/
def isOptionValue {scope : Nat} (term : RawTerm scope) : Prop :=
  term = optionNoneCell ∨ ∃ payload : RawTerm scope,
    term = optionSomeCell payload ∧ RawTerm.isStepNormalForm payload

/-- **Option values are structural normal forms.**  `none` computes to a normal form; `some payload` with a
normal payload is no redex root and its `isStepNormalFormBool` reduces to the payload's (the one-child spine).
This is the sole data obligation of `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isOptionValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsOption : isOptionValue value) : RawTerm.isStepNormalForm value := by
  rcases valueIsOption with valueIsNone | ⟨payload, valueEq, payloadNormal⟩
  · rw [valueIsNone]; rfl
  · subst valueEq
    show (RawTerm.isStepNormalFormBool payload && true) = true
    rw [Bool.and_true]
    exact payloadNormal

/-- **The option data reducibility candidate.**  `CanonicalFormsPredicate isOptionValue` — the strongly-
normalizing terms that are neutral or reduce to an option value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the
value-normality fact is `isOptionValue_impliesStepNormalForm`.  The Tait candidate for the option type, the
data core of option reducibility. -/
theorem optionCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isOptionValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isOptionValue_impliesStepNormalForm

/-- **Every option value is a member of the option candidate.**  An option value is a normal value, so it is
strongly normalizing and reduces (reflexively) to itself — the constructor reducibility for `none` and
`some`. -/
theorem isOptionValue_isMember {scope : Nat} {value : RawTerm scope}
    (valueIsOption : isOptionValue value) :
    CanonicalFormsPredicate isOptionValue value :=
  CanonicalFormsPredicate.memberOfValue (isOptionValue_impliesStepNormalForm valueIsOption) valueIsOption

/-- **Closed option-candidate members reduce to `none` or a `some`** — canonicity for options, modulo
membership.  A closed member of the option candidate is non-neutral (`IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to an option value.  Combined with "a closed
well-typed term of option type is a member" (the fundamental theorem) this is
closed-option canonicity.  The extraction shown here is fundamental-free. -/
theorem optionClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isOptionValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isOptionValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

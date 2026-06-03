import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/EitherCanonicalFormsCandidate
    — the either (sum) data candidate (SN-066): two unary tagged constructors, zero-axiom

The either (sum) type has two UNARY constructors `inl payload` and `inr payload`, each carrying a value of one
of the two summand types (as a structural normal form).  So `isEitherValue` is the disjunction of the two
tagged-payload shapes — the two-armed analogue of `option` (`OptionCanonicalFormsCandidate.lean`), with both
arms unary rather than one nullary and one unary.

`CanonicalFormsPredicate isEitherValue` is the Tait reducibility candidate for the sum type; every either
value is a member, and a CLOSED member reduces to an `inl` or an `inr` (sum-canonicity, SN-066).  This
completes the tagged-union extraction family (option + either).

## Zero-axiom verification

An `inl`/`inr` cell with a normal payload is no redex root and its `isStepNormalFormBool` reduces to the
payload's (the one-child spine recursion).  Membership uses `CanonicalFormsPredicate.memberOfValue`; the
candidate is `isReducibilityCandidateOfValuesNormal`; canonicity is `closedReducesToValue`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `inl` constructor cell over a payload. -/
abbrev eitherInlCell {scope : Nat} (payload : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherInl () (.childCons payload .childNil)

/-- The `inr` constructor cell over a payload. -/
abbrev eitherInrCell {scope : Nat} (payload : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherInr () (.childCons payload .childNil)

/-- **The either value predicate.**  A term is a sum value when it is `inl payload` or `inr payload` with the
payload a structural normal form (a value of the corresponding summand type).  The two-armed disjunction — the
analogue of `option` with both arms unary. -/
def isEitherValue {scope : Nat} (term : RawTerm scope) : Prop :=
  (∃ payload : RawTerm scope, term = eitherInlCell payload ∧ RawTerm.isStepNormalForm payload)
    ∨ ∃ payload : RawTerm scope, term = eitherInrCell payload ∧ RawTerm.isStepNormalForm payload

/-- **Either values are structural normal forms.**  An `inl`/`inr` cell with a normal payload is no redex
root and its `isStepNormalFormBool` reduces to the payload's (the one-child spine recursion).  This is the
sole data obligation of `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isEitherValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsEither : isEitherValue value) : RawTerm.isStepNormalForm value := by
  rcases valueIsEither with ⟨payload, valueEq, payloadNormal⟩ | ⟨payload, valueEq, payloadNormal⟩
  · subst valueEq
    show (RawTerm.isStepNormalFormBool payload && true) = true
    rw [Bool.and_true]
    exact payloadNormal
  · subst valueEq
    show (RawTerm.isStepNormalFormBool payload && true) = true
    rw [Bool.and_true]
    exact payloadNormal

/-- **The either data reducibility candidate.**  `CanonicalFormsPredicate isEitherValue` — the strongly-
normalizing terms that are neutral or reduce to a sum value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the
value-normality fact is `isEitherValue_impliesStepNormalForm`.  The Tait candidate for the sum type, the data
core of SN-066. -/
theorem eitherCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isEitherValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isEitherValue_impliesStepNormalForm

/-- **Every either value is a member of the either candidate.**  A sum value is a normal value, so it is
strongly normalizing and reduces (reflexively) to itself — the constructor reducibility for `inl` and `inr`. -/
theorem isEitherValue_isMember {scope : Nat} {value : RawTerm scope}
    (valueIsEither : isEitherValue value) :
    CanonicalFormsPredicate isEitherValue value :=
  CanonicalFormsPredicate.memberOfValue (isEitherValue_impliesStepNormalForm valueIsEither) valueIsEither

/-- **Closed either-candidate members reduce to an `inl` or `inr`** — canonicity for sums, modulo membership.
A closed member of the either candidate is non-neutral (`IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to a sum value.  Combined with "a closed well-typed
term of sum type is a member" (the fundamental theorem, gated on `#672` / SN-043) this is SN-049 closed-sum
canonicity.  The extraction shown here is `#672`-free. -/
theorem eitherClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isEitherValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isEitherValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

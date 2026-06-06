import FX1Poly.Core.CanonicalFormsCandidate

/-! # Foundation/PolyCell/Core/EmptyCanonicalFormsCandidate
    — the empty type's reducibility candidate + the consistency core, zero-axiom

The data candidates so far (bool, Nat, pair) interpret types that HAVE value constructors.  The empty type
(`never` / `Empty`) is the opposite extreme: it has NO value constructors, so NO term is an empty value.  Its
reducibility candidate is therefore `CanonicalFormsPredicate (fun _ => False)` — the strongly-normalizing
terms that are neutral or reduce to a value, but since there are no values, exactly the strongly-normalizing
NEUTRAL terms.  This is the canonical Tait interpretation of the empty type (the "bottom" candidate).

The payoff is the consistency core: a CLOSED member cannot exist.  A closed candidate member reduces to a
value (`CanonicalFormsPredicate.closedReducesToValue`, since no closed term is neutral), but an empty value is
a proof of `False`.  So `CanonicalFormsPredicate (fun _ => False)` has no closed inhabitants — the structural
heart of "no closed proof of the empty type" (consistency).

## Honest scope

This is the fundamental-FREE half of consistency.  Full consistency (`HasTypeDescPi .empty t Empty → False`) also
needs "a closed well-typed term of empty type is a member of the empty candidate", which is supplied by the
typed reducibility fundamental theorem.  The extraction shown here — no closed
member of the empty candidate — is unconditional.

## Zero-axiom verification

The candidate is `isReducibilityCandidateOfValuesNormal` with a VACUOUS value-normality obligation (`False`
eliminates to anything — the empty type genuinely has no values).  No-closed-member is
`closedReducesToValue` followed by elimination of the `False`-valued witness.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The empty value predicate.**  The empty type has no value constructors, so no term is an empty value —
the predicate is identically `False`.  This is the `isValue` instance the generic canonical-forms candidate is
specialized at to obtain the empty type's (bottom) reducibility candidate. -/
def emptyIsValue {scope : Nat} (_term : RawTerm scope) : Prop := False

/-- **The empty type's reducibility candidate** — the strongly-normalizing neutral terms.  It is a full
Girard reducibility candidate (CR1+CR2+CR3): the neutral-closure obligation is `IsNeutral.closedUnderStep` and
the value-normality obligation is vacuous (an empty value is a proof of `False`, which eliminates to anything).
The canonical Tait interpretation of the empty / `never` type. -/
theorem emptyCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) emptyIsValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal (fun valueIsEmpty => valueIsEmpty.elim)

/-- **No closed term inhabits the empty candidate** — the consistency core.  A closed member of the empty
candidate reduces to a value (`CanonicalFormsPredicate.closedReducesToValue`, since no closed term is
neutral), but an empty value is a proof of `False`.  Hence the empty candidate has no closed inhabitants.
Combined with "a closed well-typed term of empty type is a member" (the fundamental theorem) this is
consistency: no closed proof of the empty type.  The extraction here is fundamental-free. -/
theorem emptyHasNoClosedMember {term : RawTerm 0}
    (member : CanonicalFormsPredicate emptyIsValue term) : False := by
  obtain ⟨_value, _termReducesToValue, valueIsEmpty⟩ :=
    CanonicalFormsPredicate.closedReducesToValue member
  exact valueIsEmpty

end FX1Poly.Core

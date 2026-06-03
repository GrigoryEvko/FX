import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/ListCanonicalFormsCandidate
    — the richest data candidate: lists (SN-064), combining nullary + binary-recursive constructors

Lists combine every structure the earlier data candidates exhibited separately: a NULLARY constructor `nil`
(like `bool`'s `true`/`false`), and a BINARY constructor `cons head tail` whose `tail` recurses into the list
predicate (like `Nat`'s `succ`) while its `head` is a normal value of an arbitrary element type (like a
`pair` component).  So `IsListValue` is an inductive predicate: `nil`, or `cons head tail` with `head` a
structural normal form and `tail` a list value.

`CanonicalFormsPredicate IsListValue` is the Tait reducibility candidate for the list type; every list value
is a member, and a CLOSED member reduces to a list constructor (list-canonicity, SN-064).  The `listElim`
eliminator-reducibility consumes this candidate.

## Zero-axiom verification

List values are normal forms by induction: `nil` computes to a normal form; a `cons` cell is no redex root
and its `isStepNormalFormBool` reduces to the conjunction of the head's and tail's (the two-child spine
recursion), closed by the head's normality and the tail's induction hypothesis.  Membership uses
`CanonicalFormsPredicate.memberOfValue`; the candidate is `isReducibilityCandidateOfValuesNormal`; canonicity
is `closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `nil` constructor cell. -/
abbrev listNilCell {scope : Nat} : RawTerm scope := .mkGen .gen_listNil () .childNil

/-- The `cons` constructor cell over a head and a tail. -/
abbrev listConsCell {scope : Nat} (head tail : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_listCons () (.childCons head (.childCons tail .childNil))

/-- **The list value predicate.**  A term is a list value when it is `nil`, or `cons head tail` with `head` a
structural normal form (a value of the element type) and `tail` itself a list value — the fully-evaluated
lists.  The head's normality is carried directly (its element type is arbitrary), while the tail recurses,
combining the `pair` and `Nat` value-predicate shapes. -/
inductive IsListValue {scope : Nat} : RawTerm scope → Prop where
  /-- `nil` is a list value. -/
  | nil : IsListValue listNilCell
  /-- `cons` of a normal head onto a list value is a list value. -/
  | cons {head tail : RawTerm scope}
      (headNormal : RawTerm.isStepNormalForm head) (tailIsValue : IsListValue tail) :
      IsListValue (listConsCell head tail)

/-- **List values are structural normal forms.**  By induction: `nil` is a normal form; a `cons` cell is no
redex root and its `isStepNormalFormBool` reduces to `isStepNormalFormBool head && (isStepNormalFormBool tail
&& true)` (the two-child spine recursion), closed by the head's normality and the tail's induction
hypothesis.  This is the sole data obligation of `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isListValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsList : IsListValue value) : RawTerm.isStepNormalForm value := by
  induction valueIsList with
  | nil => rfl
  | @cons head tail headNormal _tailIsValue tailIH =>
      show (RawTerm.isStepNormalFormBool head
          && (RawTerm.isStepNormalFormBool tail && true)) = true
      rw [show RawTerm.isStepNormalFormBool head = true from headNormal,
        show RawTerm.isStepNormalFormBool tail = true from tailIH]
      rfl

/-- **The list data reducibility candidate.**  `CanonicalFormsPredicate IsListValue` — the strongly-
normalizing terms that are neutral or reduce to a list value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the
value-normality fact is `isListValue_impliesStepNormalForm`.  The Tait candidate for the list type, the data
core of SN-064. -/
theorem listCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) IsListValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isListValue_impliesStepNormalForm

/-- **Every list value is a member of the list candidate.**  A list value is a normal value, so it is
strongly normalizing and reduces (reflexively) to itself — the constructor reducibility for `nil` and `cons`:
the lists inhabit their type's reducibility candidate. -/
theorem isListValue_isMember {scope : Nat} {value : RawTerm scope} (valueIsList : IsListValue value) :
    CanonicalFormsPredicate IsListValue value :=
  CanonicalFormsPredicate.memberOfValue (isListValue_impliesStepNormalForm valueIsList) valueIsList

/-- **Closed list-candidate members reduce to a list constructor** — canonicity for lists, modulo membership.
A closed member of the list candidate is non-neutral (`IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to a list value (`nil` or a `cons`).  Combined with
"a closed well-typed term of list type is a member" (the fundamental theorem, gated on `#672` / SN-043) this
is SN-049 closed-list canonicity.  The extraction shown here is `#672`-free. -/
theorem listClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate IsListValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsListValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

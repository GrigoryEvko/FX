import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/PairCanonicalFormsCandidate
    — the binary data reducibility candidate: Σ-pairs (SN-057/059), unconditional + zero-axiom

Bool (`BoolCanonicalFormsCandidate.lean`) was a NULLARY constructor; Nat (`NatCanonicalFormsCandidate.lean`)
was a UNARY recursive constructor.  The Σ pair `(a, b)` is the BINARY case — two children of arbitrary
type.  Unlike the numerals (whose children are themselves numerals), a pair's components are values of OTHER
types, so the pair value predicate carries the children's normality directly rather than recursing into the
pair predicate.  A pair is a value when it is `pairCell first second` with both components structural normal
forms.

`CanonicalFormsPredicate isPairValue` is the Tait reducibility candidate for the Σ-type (the WHNF-pair
canonical forms); every normal pair is a member, and a CLOSED member reduces to a pair constructor
(Σ-canonicity, SN-059).  This is the data core of SN-057 (Σ-introduction reducibility member); the fst/snd
projection-reducibility (SN-058) consumes this candidate.

## Zero-axiom verification

A pair of normal children is a structural normal form: `pairCell` is no redex root, and its
`isStepNormalFormBool` reduces to the conjunction of the children's (the structural recursion over the
two-child spine), closed by the component normality.  Membership is the generic
`CanonicalFormsPredicate.memberOfValue`; the candidate is `isReducibilityCandidateOfValuesNormal`; canonicity
is `closedReducesToValue`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The pair constructor cell over two components. -/
abbrev pairCell {scope : Nat} (first second : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pair () (.childCons first (.childCons second .childNil))

/-- **The pair value predicate.**  A term is a Σ value when it is `pairCell first second` with both
components structural normal forms — the weak-head-normal pair.  The components' normality is carried
explicitly (a pair's children are values of other types, not sub-pairs), which is exactly what makes the pair
cell a normal form. -/
def isPairValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ first second : RawTerm scope,
    term = pairCell first second ∧ RawTerm.isStepNormalForm first ∧ RawTerm.isStepNormalForm second

/-- **Pair values are structural normal forms.**  A `pairCell` with normal components is no redex root and
its `isStepNormalFormBool` reduces to `isStepNormalFormBool first && (isStepNormalFormBool second && true)`
(the structural recursion over the two-child spine); the component normality closes it.  This is the sole
data obligation of `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isPairValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsPair : isPairValue value) : RawTerm.isStepNormalForm value := by
  obtain ⟨first, second, valueEq, firstNormal, secondNormal⟩ := valueIsPair
  subst valueEq
  show (RawTerm.isStepNormalFormBool first
      && (RawTerm.isStepNormalFormBool second && true)) = true
  rw [show RawTerm.isStepNormalFormBool first = true from firstNormal,
    show RawTerm.isStepNormalFormBool second = true from secondNormal]
  rfl

/-- **The Σ data reducibility candidate.**  `CanonicalFormsPredicate isPairValue` — the strongly-normalizing
terms that are neutral or reduce to a normal pair — is a full Girard reducibility candidate (CR1+CR2+CR3),
unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the value-normality fact is
`isPairValue_impliesStepNormalForm`.  The Tait candidate for the Σ-type, the data core of SN-057/059. -/
theorem pairCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isPairValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isPairValue_impliesStepNormalForm

/-- **A normal pair is a member of the Σ candidate.**  Given normal components, `pairCell first second` is a
normal value, so it is strongly normalizing and reduces (reflexively) to itself — the Σ-introduction
reducibility (SN-057): a pair of reducible-normal components inhabits its type's reducibility candidate. -/
theorem pairValue_isMember {scope : Nat} {first second : RawTerm scope}
    (firstNormal : RawTerm.isStepNormalForm first) (secondNormal : RawTerm.isStepNormalForm second) :
    CanonicalFormsPredicate isPairValue (pairCell first second) :=
  CanonicalFormsPredicate.memberOfValue
    (isPairValue_impliesStepNormalForm ⟨first, second, rfl, firstNormal, secondNormal⟩)
    ⟨first, second, rfl, firstNormal, secondNormal⟩

/-- **Closed Σ-candidate members reduce to a pair** — canonicity for Σ, modulo membership.  A closed member
of the Σ candidate is non-neutral (`IsNeutral.noClosed`), so by `CanonicalFormsPredicate.closedReducesToValue`
it reduces to a pair constructor.  Combined with "a closed well-typed term of Σ type is a member" (the
fundamental theorem, gated on `#672` / SN-043) this is SN-059 closed-Σ canonicity.  The extraction shown here
is `#672`-free. -/
theorem pairClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isPairValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isPairValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

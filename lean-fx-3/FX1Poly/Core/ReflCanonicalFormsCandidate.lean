import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/ReflCanonicalFormsCandidate
    — the identity-type introduction candidate (SN-067): the unary `refl` constructor, zero-axiom

The identity type `Id A x y` has a single introduction `refl witness` (the reflexivity proof, with `witness`
the reflected point — a value of the underlying type carried as a structural normal form).  So `isReflValue`
is the single unary tagged-payload shape — the same one-child recipe as `option`'s `some` and `either`'s
`inl`/`inr`, here as the sole constructor.

`CanonicalFormsPredicate isReflValue` is the Tait reducibility candidate for the identity type; every `refl`
value is a member, and a CLOSED member reduces to a `refl` (identity-canonicity, SN-067).  This completes the
data-introduction extraction family.

## Zero-axiom verification

A `refl` cell with a normal witness is no redex root and its `isStepNormalFormBool` reduces to the witness's
(the one-child spine recursion).  Membership uses `CanonicalFormsPredicate.memberOfValue`; the candidate is
`isReducibilityCandidateOfValuesNormal`; canonicity is `closedReducesToValue`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `refl` constructor cell over a reflected witness. -/
abbrev reflCell {scope : Nat} (witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_refl () (.childCons witness .childNil)

/-- **The refl value predicate.**  A term is an identity value when it is `refl witness` with the witness a
structural normal form (a value of the underlying type).  The single unary tagged shape — `refl` is the
identity type's only introduction. -/
def isReflValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ witness : RawTerm scope, term = reflCell witness ∧ RawTerm.isStepNormalForm witness

/-- **Refl values are structural normal forms.**  A `refl` cell with a normal witness is no redex root and
its `isStepNormalFormBool` reduces to the witness's (the one-child spine recursion).  This is the sole data
obligation of `CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isReflValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsRefl : isReflValue value) : RawTerm.isStepNormalForm value := by
  obtain ⟨witness, valueEq, witnessNormal⟩ := valueIsRefl
  subst valueEq
  show (RawTerm.isStepNormalFormBool witness && true) = true
  rw [Bool.and_true]
  exact witnessNormal

/-- **The identity data reducibility candidate.**  `CanonicalFormsPredicate isReflValue` — the strongly-
normalizing terms that are neutral or reduce to a `refl` value — is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the
value-normality fact is `isReflValue_impliesStepNormalForm`.  The Tait candidate for the identity type, the
data core of SN-067. -/
theorem reflCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) isReflValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isReflValue_impliesStepNormalForm

/-- **Every refl value is a member of the identity candidate.**  A `refl` value is a normal value, so it is
strongly normalizing and reduces (reflexively) to itself — the constructor reducibility for `refl`. -/
theorem isReflValue_isMember {scope : Nat} {value : RawTerm scope} (valueIsRefl : isReflValue value) :
    CanonicalFormsPredicate isReflValue value :=
  CanonicalFormsPredicate.memberOfValue (isReflValue_impliesStepNormalForm valueIsRefl) valueIsRefl

/-- **Closed identity-candidate members reduce to a `refl`** — canonicity for the identity type, modulo
membership.  A closed member of the identity candidate is non-neutral (`IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to a `refl` value.  Combined with "a closed
well-typed term of identity type is a member" (the fundamental theorem, gated on `#672` / SN-043) this is
closed-identity canonicity.  The extraction shown here is `#672`-free. -/
theorem reflClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate isReflValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isReflValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

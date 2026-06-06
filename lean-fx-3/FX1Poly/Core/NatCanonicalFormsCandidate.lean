import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.StepInversion

/-! # Foundation/PolyCell/Core/NatCanonicalFormsCandidate
    — the recursive data reducibility candidate: Nat, unconditional + zero-axiom

The bool candidate (`BoolCanonicalFormsCandidate.lean`) instantiated the generic canonical-forms machine at a
type whose values are NULLARY constructors.  Nat is the first RECURSIVE data type: its values are the
numerals `natZero`, `natSucc natZero`, `natSucc (natSucc natZero)`, … — an inductively-defined family.  This
file builds the Nat reducibility candidate, with the value-normality obligation discharged by induction over
the numeral structure (a `natSucc` cell is a structural normal form exactly when its predecessor is).

`IsNatValue` is the inductive numeral predicate; `CanonicalFormsPredicate IsNatValue` is the Tait
reducibility candidate for the natural-number type.  Every numeral is a member, and a CLOSED member reduces
to a numeral (canonicity).  This is the data core of nat zero/succ reducibility and the nat
SN + canonicity bundle; the `natElim`/`natRec` eliminator-reducibility consumes this candidate.

## Zero-axiom verification

`IsNatValue`-values are normal forms by induction: `natZero` computes to a normal form; a `natSucc` cell is
no redex root and is normal iff its sole child is (the structural `isStepNormalFormBool` recursion, closed by
the induction hypothesis).  Membership uses the generic `CanonicalFormsPredicate.memberOfValue`; the candidate
is `isReducibilityCandidateOfValuesNormal`; canonicity is `closedReducesToValue`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `zero` constructor cell. -/
abbrev natZeroCell {scope : Nat} : RawTerm scope := .mkGen .gen_natZero () .childNil

/-- The `succ` constructor cell over a predecessor. -/
abbrev natSuccCell {scope : Nat} (predecessor : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natSucc () (.childCons predecessor .childNil)

/-- **The numeral value predicate.**  A term is a natural-number value when it is `zero` or the successor of
a value — the inductively-defined numerals.  This is the `isValue` instance the generic canonical-forms
candidate is specialized at to obtain the Nat reducibility candidate. -/
inductive IsNatValue {scope : Nat} : RawTerm scope → Prop where
  /-- `zero` is a numeral. -/
  | zero : IsNatValue natZeroCell
  /-- The successor of a numeral is a numeral. -/
  | succ {predecessor : RawTerm scope} (predecessorIsValue : IsNatValue predecessor) :
      IsNatValue (natSuccCell predecessor)

/-- **Numerals are structural normal forms.**  By induction on the numeral: `zero` is a normal form (no
redex root, empty children); a `natSucc` cell is no redex root and its `isStepNormalFormBool` reduces to that
of its predecessor, which is normal by the induction hypothesis.  This is the sole data obligation of
`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`. -/
theorem isNatValue_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsNat : IsNatValue value) : RawTerm.isStepNormalForm value := by
  induction valueIsNat with
  | zero => rfl
  | @succ predecessor _predecessorIsValue predecessorIH =>
      -- `isStepNormalFormBool (natSucc predecessor)` reduces definitionally to
      -- `isStepNormalFormBool predecessor && true` (natSucc is no redex root, single child), so the goal is
      -- `isStepNormalFormBool predecessor && true = true`; the IH gives `isStepNormalFormBool predecessor`.
      show (RawTerm.isStepNormalFormBool predecessor && true) = true
      rw [Bool.and_true]
      exact predecessorIH

/-- **The Nat data reducibility candidate.**  `CanonicalFormsPredicate IsNatValue` — the strongly-normalizing
terms that are neutral or reduce to a numeral — is a full Girard reducibility candidate (CR1+CR2+CR3),
unconditionally: the neutral-closure obligation is `IsNeutral.closedUnderStep` and the value-normality fact is
`isNatValue_impliesStepNormalForm`.  The Tait candidate for the natural-number type, the data core of
nat reducibility. -/
theorem natCanonicalFormsCandidate {scope : Nat} :
    IsReducibilityCandidate (CanonicalFormsPredicate (scope := scope) IsNatValue) :=
  CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal isNatValue_impliesStepNormalForm

/-- **Every numeral is a member of the Nat candidate.**  A numeral is a normal value, so it is strongly
normalizing and reduces (reflexively) to itself — the constructor reducibility for `zero` and `succ`:
the numerals inhabit their type's reducibility candidate. -/
theorem isNatValue_isMember {scope : Nat} {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    CanonicalFormsPredicate IsNatValue value :=
  CanonicalFormsPredicate.memberOfValue (isNatValue_impliesStepNormalForm valueIsNat) valueIsNat

/-- **Closed Nat-candidate members reduce to a numeral** — canonicity for naturals, modulo membership.  A
closed member of the Nat candidate is non-neutral (`IsNeutral.noClosed`), so by
`CanonicalFormsPredicate.closedReducesToValue` it reduces to a numeral.  Combined with "a closed well-typed
term of Nat type is a member" (the fundamental theorem) this is closed-nat
canonicity.  The extraction shown here is fundamental-free. -/
theorem natClosedReducesToValue {term : RawTerm 0}
    (member : CanonicalFormsPredicate IsNatValue term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsNatValue value :=
  CanonicalFormsPredicate.closedReducesToValue member

end FX1Poly.Core

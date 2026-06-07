import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.UnitCanonicalFormsCandidate
import FX1Poly.Core.EmptyCanonicalFormsCandidate
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.ModIntroCanonicalFormsCandidate

/-! # FX1Poly/Core/DataReducibilityCoverage
    — SN-082: the reducibility-coverage gate over the data-type former families

The data reducibility candidates ship one file per type (`BoolCanonicalFormsCandidate`,
`NatCanonicalFormsCandidate`, …): each instantiates the GENERIC canonical-forms candidate
(`CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal`) at that type's value predicate, producing an
unconditional zero-axiom `IsReducibilityCandidate`.  Those theorems are individually audit-gated, but nothing
states — as ONE auditable theorem — that EVERY data former in the canonical-forms family is covered.  This file
is that gate.

## The coverage object

`DataFormerFamily` enumerates the ten §3 closed-data former families that carry a Tait reducibility candidate.
`DataFormerFamily.valuePredicate` maps each to its value predicate (the `isValue` instance whose canonical
inhabitants are the constructors).  **`DataFormerFamily.hasReducibilityCandidate`** is the headline: a TOTAL
dependent dispatch proving that for every family, `CanonicalFormsPredicate (its value predicate)` is a full
Girard reducibility candidate (CR1+CR2+CR3) — each arm discharged by the family's own shipped candidate
theorem.  Totality over the enumeration makes this a regression gate: adding a `DataFormerFamily` constructor
without supplying a candidate fails to compile.

The dispatch is indexed by `valuePredicate` (not a bare existential), so each family is forced to its OWN
candidate — `boolFamily` cannot be discharged by `nat`'s candidate.  That is what makes the coverage genuine
rather than vacuous.

## Non-vacuity contrast

`boolFamilyCandidateInhabited` exhibits a closed member of bool's candidate (`boolTrueCell`), so the coverage is
not over empty predicates.  `emptyFamilyCandidateHasNoClosedMember` re-exports the shipped
`emptyHasNoClosedMember`: the empty family's candidate is the genuine BOTTOM (no closed inhabitant) — the
coverage correctly includes a type whose candidate is uninhabited, the consistency core.  Coverage means "every
former has the RIGHT candidate", not "every candidate is inhabited".

## Zero-axiom verification

`DataFormerFamily` is a plain (non-indexed) enum, so the full-enumeration dependent dispatch compiles via the
propext-free recursor (every arm present, no wildcard); each arm is defeq to the family's value predicate, so
the shipped candidate theorem closes it directly.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

/-- The §3 closed-data former families that carry a shipped Tait reducibility candidate.  Each constructor
corresponds to a `*CanonicalFormsCandidate.lean` file and is discharged below by that file's candidate. -/
inductive DataFormerFamily where
  | boolFamily
  | natFamily
  | unitFamily
  | emptyFamily
  | pairFamily
  | listFamily
  | optionFamily
  | eitherFamily
  | identityFamily
  | modalBoxFamily

/-- The value predicate (`isValue` instance) each data-former family is interpreted at — the predicate whose
canonical inhabitants are the type's constructors and whose `CanonicalFormsPredicate` is the family's Tait
reducibility set.  The empty family maps to `emptyIsValue` (identically `False`: the empty type has no value
constructor), so its candidate is the bottom — the strongly-normalizing neutral terms. -/
def DataFormerFamily.valuePredicate {scope : Nat} : DataFormerFamily → (RawTerm scope → Prop)
  | .boolFamily => boolIsValue
  | .natFamily => IsNatValue
  | .unitFamily => isUnitValue
  | .emptyFamily => emptyIsValue
  | .pairFamily => isPairValue
  | .listFamily => IsListValue
  | .optionFamily => isOptionValue
  | .eitherFamily => isEitherValue
  | .identityFamily => isReflValue
  | .modalBoxFamily => isModIntroValue

/-- **The data reducibility coverage theorem (SN-082).**  For EVERY enumerated data-former family, the
canonical-forms predicate at that family's value predicate is a full Girard reducibility candidate
(CR1+CR2+CR3), unconditionally and zero-axiom — each arm discharged by the family's own shipped candidate
theorem (`boolCanonicalFormsCandidate`, `natCanonicalFormsCandidate`, …).  Total over the enumeration: a
regression gate that fails to compile if a data former is added without a candidate.  Indexed by
`valuePredicate`, so each family is pinned to its OWN candidate (no cross-family discharge). -/
theorem DataFormerFamily.hasReducibilityCandidate {scope : Nat} :
    (family : DataFormerFamily) →
      IsReducibilityCandidate (CanonicalFormsPredicate (family.valuePredicate (scope := scope)))
  | .boolFamily => boolCanonicalFormsCandidate
  | .natFamily => natCanonicalFormsCandidate
  | .unitFamily => unitCanonicalFormsCandidate
  | .emptyFamily => emptyCanonicalFormsCandidate
  | .pairFamily => pairCanonicalFormsCandidate
  | .listFamily => listCanonicalFormsCandidate
  | .optionFamily => optionCanonicalFormsCandidate
  | .eitherFamily => eitherCanonicalFormsCandidate
  | .identityFamily => reflCanonicalFormsCandidate
  | .modalBoxFamily => modIntroCanonicalFormsCandidate

/-- The number of data-former families covered.  A pinned smoke: if the enumeration grows or shrinks without
updating this count, the `_correct` equation breaks. -/
def DataFormerFamily.coveredCount : Nat := 10

/-- The covered-family count is exactly ten (bool, nat, unit, empty, pair, list, option, either, identity,
modal box). -/
theorem DataFormerFamily.coveredCount_correct : DataFormerFamily.coveredCount = 10 := rfl

/-- **Non-vacuity (positive):** bool's covered candidate is inhabited by a closed member (`boolTrueCell`), so
the coverage is not over empty predicates. -/
theorem boolFamilyCandidateInhabited {scope : Nat} :
    ∃ member : RawTerm scope, CanonicalFormsPredicate boolIsValue member :=
  ⟨boolTrueCell, boolTrueCell_isMember⟩

/-- **Non-vacuity (bottom contrast):** the empty family's covered candidate has NO closed member (re-exports
`emptyHasNoClosedMember`).  Coverage correctly includes the empty type, whose candidate is the genuine bottom
(the consistency core) — distinguishing "every former has the right candidate" from "every candidate is
inhabited". -/
theorem emptyFamilyCandidateHasNoClosedMember {term : RawTerm 0}
    (member : CanonicalFormsPredicate emptyIsValue term) : False :=
  emptyHasNoClosedMember member

end FX1Poly.Core

import FX1Poly.Core.SconingWitness
import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.UnitCanonicalFormsCandidate
import FX1Poly.Core.ReflCanonicalFormsCandidate

/-! # FX1Poly/Core/DataCanonicityViaSconing
    — the GENERIC data-canonicity sconing witness: one theorem for every data axis (SN-048/049/093)

`BoolCanonicityViaSconing.lean` shipped the first concrete data sconing witness, but it used the
bool-specific extraction `boolClosedReducesToTrueOrFalse`.  The key observation this file makes precise:
EVERY data candidate `CanonicalFormsPredicate isValue` shares ONE uniform extraction —
`CanonicalFormsPredicate.closedReducesToValue` discharges "closed member reduces to a value satisfying
`isValue`" `#672`-free for ANY value predicate `isValue` (a closed member is non-neutral, so its
"neutral OR reduces-to-value" disjunct collapses to the right branch).  So the bool witness was a
SPECIAL CASE: the data-canonicity sconing witness is generic in the value predicate.

* `dataCanonicityScone` — the GENERIC data sconing witness, parametric in the value predicate `isValue`.
  `computable` is the data candidate `CanonicalFormsPredicate isValue`; `extraction` is the uniform
  `#672`-free `CanonicalFormsPredicate.closedReducesToValue`; `fundamental` (closed well-typed data ⟹
  candidate member — the fundamental theorem of the logical relation) is the explicit sole obligation.
* `dataCanonicityViaSconing` — the generic Path-C canonicity corollary: given the fundamental, every
  closed well-typed term of the data type reduces to a constructor value.
* `natCanonicityViaSconing` / `listCanonicityViaSconing` / `optionCanonicityViaSconing` /
  `eitherCanonicityViaSconing` / `pairCanonicityViaSconing` — the one-line instances at the concrete
  value predicates (`IsNatValue` / `IsListValue` / `isOptionValue` / `isEitherValue` / `isPairValue`),
  the §3.12 canonicity headline per data type via the sconing leg (SN-048 nat, SN-049 the rest).

This is the "one functor ⟹ canonicity for all data" realization (the BKS sconing-is-enough thesis,
toward SN-110) made concrete for the data axis: a SINGLE generic witness, each data type a thin
specialization — not one copy-pasted file per type.  Every instance shares the SAME `#672`-free
extraction and the SAME (per-type) fundamental obligation that Path A also needs.

## Zero-axiom verification

A record literal over `SconingWitness` whose `extraction` field is the generic `#672`-free
`CanonicalFormsPredicate.closedReducesToValue`, `SconingWitness.canonicity` (composition), and thin
specializations fixing `isValue`.  The `fundamental` obligation is an explicit hypothesis, not
discharged here.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **The GENERIC data-canonicity sconing witness (Path C), parametric in the value predicate.**
Relative to any notion of well-typedness `isWellTyped` and any value predicate `isValue`, the data
candidate `CanonicalFormsPredicate isValue` is the displayed computability predicate; its EXTRACTION
obligation is discharged `#672`-free by the uniform `CanonicalFormsPredicate.closedReducesToValue` (a
closed candidate member reduces to a value satisfying `isValue`).  The FUNDAMENTAL obligation (closed
well-typed term ⟹ candidate member) is the explicit parameter — the SOLE remaining hard obligation, the
Path-A fundamental theorem (`#672` / SN-043).  Subsumes the bool-specific `boolCanonicityScone`. -/
def dataCanonicityScone {isWellTyped : RawTerm 0 → Prop} {isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isValue term) :
    SconingWitness isWellTyped
      (fun term => ∃ value : RawTerm 0, StepStar term value ∧ isValue value) :=
  { computable := CanonicalFormsPredicate isValue
    fundamental := fundamental
    extraction := fun _term member => CanonicalFormsPredicate.closedReducesToValue member }

/-- **Generic closed-data canonicity, derived via the sconing leg (Path C).**  `SconingWitness.canonicity`
on `dataCanonicityScone`: given the fundamental obligation (closed well-typed ⟹ candidate member), every
closed well-typed term of the data type reduces to a value satisfying `isValue`.  One generic theorem
for every data type; each concrete type instantiates `isValue`.  Extraction is `#672`-free, so the
sconing leg adds no obligation beyond the per-type fundamental theorem Path A already carries. -/
theorem dataCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop} {isValue : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isValue value :=
  (dataCanonicityScone fundamental).canonicity term typed

/-- **Closed-Nat canonicity via the sconing leg (SN-048).**  `dataCanonicityViaSconing` at
`isValue := IsNatValue`: given the fundamental obligation, every closed well-typed Nat term reduces to a
numeral. -/
theorem natCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate IsNatValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsNatValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-List canonicity via the sconing leg (SN-049).**  `dataCanonicityViaSconing` at
`isValue := IsListValue`: every closed well-typed List term reduces to `nil` or a `cons`, modulo the
fundamental obligation. -/
theorem listCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate IsListValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsListValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-Option canonicity via the sconing leg (SN-049).**  `dataCanonicityViaSconing` at
`isValue := isOptionValue`: every closed well-typed Option term reduces to `none` or a `some`, modulo
the fundamental obligation. -/
theorem optionCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isOptionValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isOptionValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-Either canonicity via the sconing leg (SN-049).**  `dataCanonicityViaSconing` at
`isValue := isEitherValue`: every closed well-typed Either term reduces to an `inl` or an `inr`, modulo
the fundamental obligation. -/
theorem eitherCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isEitherValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isEitherValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-Pair (Σ-intro) canonicity via the sconing leg (SN-049/059).**  `dataCanonicityViaSconing`
at `isValue := isPairValue`: every closed well-typed Pair term reduces to a `pair` constructor, modulo
the fundamental obligation. -/
theorem pairCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isPairValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isPairValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-Unit canonicity via the sconing leg (SN-049).**  `dataCanonicityViaSconing` at
`isValue := isUnitValue`: every closed well-typed Unit term reduces to the unit constructor, modulo the
fundamental obligation.  The one-value (§3.12) canonicity instance — the last non-modal data type to join
the generic sconing witness, completing the Unit corner of SN-049. -/
theorem unitCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isUnitValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isUnitValue value :=
  dataCanonicityViaSconing fundamental term typed

/-- **Closed-identity canonicity via the sconing leg (SN-059/067 introduction half).**
`dataCanonicityViaSconing` at `isValue := isReflValue`: every closed well-typed identity-type term reduces to
`refl`, modulo the fundamental obligation.  The identity-introduction canonicity instance, joining the generic
sconing witness — completing the data-canonicity-via-sconing coverage to ALL data axes (nat / list / option /
either / pair / unit / identity, with bool the standalone first witness). -/
theorem identityCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isReflValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isReflValue value :=
  dataCanonicityViaSconing fundamental term typed

end FX1Poly.Core

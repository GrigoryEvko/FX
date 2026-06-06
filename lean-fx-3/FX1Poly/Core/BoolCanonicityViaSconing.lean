import FX1Poly.Core.SconingWitness
import FX1Poly.Core.BoolCanonicalFormsCandidate

/-! # FX1Poly/Core/BoolCanonicityViaSconing
    — a concrete data-type sconing witness: bool canonicity (`→ true`/`false`) via Path C

`SconingWitness.lean` ships the generic BKS "sconing is enough" machinery — a `SconingWitness` bundles the
displayed computability predicate with the FUNDAMENTAL obligation (well-typed ⟹ computable) and the EXTRACTION
obligation (computable ⟹ canonical), and `SconingWitness.canonicity` derives canonicity as
`extraction ∘ fundamental`.  The generic bridge `reducibilityScone` discharges extraction by CR1, so it only
yields the WEAK `IsStronglyNormalizing` canonical-form notion.

This file instantiates the machinery CONCRETELY for the bool data type with the SHARP canonical-form notion —
"reduces to `true` or `false`" — and discharges its EXTRACTION obligation fundamental-free:

* `boolCanonicityScone` — the concrete bool sconing witness.  `computable` is the bool reducibility candidate
  (`CanonicalFormsPredicate boolIsValue`); `extraction` is exactly the shipped fundamental-free
  `boolClosedReducesToTrueOrFalse` (a closed candidate member reduces to a boolean value); `fundamental` (every
  closed well-typed bool term is a candidate member — the fundamental theorem of the logical relation) is the
  explicit parameter, the SOLE remaining obligation (= the Path-A fundamental theorem).
* `boolCanonicityViaSconing` — the Path-C derivation of closed-bool canonicity: `SconingWitness.canonicity`
  applied, so given the fundamental obligation, every closed well-typed bool term reduces to `true` or `false`.

The point is the BKS thesis made concrete: for bool canonicity the EXTRACTION half is already done fundamental-free
(it is just the candidate's own canonicity extraction), so the sconing leg (Path C, the INDEPENDENT canonicity
route) reduces bool canonicity to EXACTLY the same fundamental theorem the Tait leg (Path A) needs — "two
methods, one object", and one shared fundamental obligation.

## Zero-axiom verification

A record literal over `SconingWitness` whose `extraction` field is `boolClosedReducesToTrueOrFalse` (the shipped
fundamental-free canonicity extraction) plus `SconingWitness.canonicity` (composition).  The `fundamental` obligation
is an explicit hypothesis, not discharged here.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **The concrete bool-canonicity sconing witness (Path C), fundamental-free EXTRACTION.**  Relative to any
notion of well-typedness `isWellTyped` and the sharp canonical-form notion "reduces to `true` or `false`", the
bool reducibility candidate `CanonicalFormsPredicate boolIsValue` is the displayed computability predicate; its
EXTRACTION obligation is discharged fundamental-free by `boolClosedReducesToTrueOrFalse` (a closed candidate member
reduces to a boolean value).  The FUNDAMENTAL obligation (closed well-typed bool ⟹ candidate member) is the
explicit parameter — the SOLE remaining hard obligation, the Path-A fundamental theorem. -/
def boolCanonicityScone {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate boolIsValue term) :
    SconingWitness isWellTyped
      (fun term => ∃ value : RawTerm 0,
        StepStar term value ∧ (value = boolTrueCell ∨ value = boolFalseCell)) :=
  { computable := CanonicalFormsPredicate boolIsValue
    fundamental := fundamental
    extraction := fun _term member => boolClosedReducesToTrueOrFalse member }

/-- **Closed-bool canonicity, derived via the sconing leg (Path C).**  `SconingWitness.canonicity` on the
concrete `boolCanonicityScone`: given the fundamental obligation (closed well-typed bool ⟹ candidate member),
every closed well-typed bool term reduces to `true` or `false`.  This is the BKS boilerplate-free derivation —
canonicity is `extraction ∘ fundamental` — and it shows the INDEPENDENT sconing route reaches the SAME bool
canonicity as the Tait route, modulo the SAME fundamental theorem.  The extraction half is
fundamental-free, so the sconing leg adds no new obligation beyond the one Path A already carries. -/
theorem boolCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate boolIsValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ (value = boolTrueCell ∨ value = boolFalseCell) :=
  (boolCanonicityScone fundamental).canonicity term typed

end FX1Poly.Core

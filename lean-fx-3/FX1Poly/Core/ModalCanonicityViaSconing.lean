import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.ModIntroCanonicalFormsCandidate

/-! # FX1Poly/Core/ModalCanonicityViaSconing
    — modal box canonicity via the sconing leg (SN-073), completing canonicity-via-sconing to the modal axis

`DataCanonicityViaSconing.lean` ships the generic data-canonicity sconing witness `dataCanonicityViaSconing`,
parametric in the value predicate `isValue`, with thin specializations for every DATA type (nat / list / option
/ either / pair / unit / identity; bool the standalone first witness).  The modal box former is the one
remaining positive type with a shipped `CanonicalFormsPredicate` candidate (`ModIntroCanonicalFormsCandidate`,
`#721`) that had no sconing-canonicity instance.  This file adds it, completing canonicity-via-sconing coverage
to ALL formers carrying a canonical-forms candidate.

The modal box `□A` is `isValue := isModIntroValue` (a `modIntro payload` cell with a normal payload — the modal
introduction, `ModIntroCanonicalFormsCandidate` mirrors `OptionCanonicalFormsCandidate`'s `some` branch).  The
extraction is the SAME uniform `#672`-free `CanonicalFormsPredicate.closedReducesToValue` the data witnesses use,
so this canonicity is conditional ONLY on the per-type fundamental obligation (closed well-typed box ⟹
box-candidate member) — NOT on typed SN (`#672` / SN-043).  Genuinely unblocked, like the data instances.

* `modIntroCanonicityViaSconing` — `dataCanonicityViaSconing` at `isValue := isModIntroValue`: every closed
  well-typed modal-box term reduces to a `modIntro` constructor, modulo the fundamental obligation.  The §3.12
  canonicity headline for the modal box via the sconing leg, advancing SN-073.

The modal ELIMINATOR (`modElim`) progress is NOT shipped here: the modal former's only collapse is the raw-η
`modIntro (modElim m) ↝ m` (`StrongNormalizationModalEliminators`), not a scrutinee-firing iota, so the
non-recursive eliminator-progress pattern of `DataEliminatorProgressViaSconing` does not transfer directly.

## Zero-axiom verification

One-line specialization of `dataCanonicityViaSconing` at `isModIntroValue`.  No induction, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **Closed modal-box canonicity via the sconing leg (SN-073).**  `dataCanonicityViaSconing` at
`isValue := isModIntroValue`: given the fundamental obligation (closed well-typed modal box ⟹ box-candidate
member), every closed well-typed modal-box term reduces to a `modIntro` constructor.  The modal-box instance of
the generic `#672`-free data-canonicity sconing witness — completing the canonicity-via-sconing coverage to all
formers carrying a canonical-forms candidate (data + modal box). -/
theorem modIntroCanonicityViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate isModIntroValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isModIntroValue value :=
  dataCanonicityViaSconing fundamental term typed

end FX1Poly.Core

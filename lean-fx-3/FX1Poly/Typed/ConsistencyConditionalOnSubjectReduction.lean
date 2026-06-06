import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization

/-! # FX1Poly/Typed/ConsistencyConditionalOnSubjectReduction
    — the SN-050 consistency route made concrete, gated on exactly one residual: SR-along-`↝*`

**STATUS (2026-06-05): SUPERSEDED for TODAY's engine by `HasTypeDescPi.emptyTypeConsistency`
(`EmptyTypeConsistencyUnconditional.lean`, commit f7172cfa) — UNCONDITIONAL via validity, no SR hypothesis.
RETAINED as the SUBSTANTIVE-Empty FUTURE route: once CON-A1's `gen_emptyCode` formation row makes emptyTypeCell
a real type, the validity route breaks and consistency needs THIS SR/canonicity link.  Not dead; do not delete.**

`GrownCanonicalForms.noClosedNormalTermAtEmptyType` proved that no closed NORMAL term inhabits the empty
type.  Strong normalization (open SN-043, `HasTypeDescPi.stronglyNormalizingOfWfContext`, OB-5/`#794`) reduces
an ARBITRARY closed `t : EmptyType` to a normal form.  The only missing link is subject reduction along the
reduction chain — carrying the `EmptyType` classifier from `t` down to its normal form.  This file ships the
consistency theorem with that link as the single explicit hypothesis `subjectReductionStar`, so the residual
to close the ★ SN-050 milestone is named precisely and the rest is discharged unconditionally.

This mirrors the established conditional-package discipline (`UB-SD-conditionalPackage`, `#664`): bundle the
shipped machinery and expose the lone remaining gate as a hypothesis, rather than leave the whole route
implicit.

## Why the syntactic route (this file), not the bounded-semantic route

The bounded-reducibility model (`DenoteKeyedBoundedReducibility`, the SN engine behind OB-5) assigns
`emptyTypeCell` the candidate `IsStronglyNormalizing` via its `neutral` arm — `gen_emptyCode` is
weak-head-normal, non-`gen_piTyCode`, non-`gen_universeCode`, so it falls into the neutral leaf whose member
predicate is "every SN term".  That candidate is far too COARSE to refute consistency (a closed `λx.x` is SN,
hence a "member").  So the bounded model is an SN model, NOT a canonicity model: `CON-A3`/`#810`
("EmptyType's reducibility candidate is the empty candidate") is NOT dischargeable from the shipped bounded
closed-member bridge (`BFT-13`/`BFT-14`).  A genuine canonicity model (the `CanonicalFormsPredicate` data
candidates, `emptyHasNoClosedMember`/`#680`) would need its own closed-well-typed-`→`-canonicity-member
fundamental theorem.  The syntactic route here reuses only the shipped SN + grown canonical forms, leaving
SR-along-`↝*` as the lone gate — and SR (the SN-055 dispatcher) is independently on the critical path.

## The remaining gate

`subjectReductionStar` for the empty context at `EmptyType` is the iterated SN-055 master SR dispatcher
(`SRD-1`/`#844`, `SRD-3`/`#846`), itself blocked on the grown fundamental-metatheory bundle (the
`WfContext` ↔ `WfContextDescPi` mismatch, `WFG-3`/`#857`; the `HasTypeDescPi → IsType` bridge `WfContext.cons`
needs).  Once that lands, `subjectReductionStar` is a `StepStar.rec` over the single-step master dispatcher and
this theorem becomes the unconditional SN-050 `HasTypeDescPi .empty t EmptyType → False`.

## Zero-axiom verification

OB-5 (`stronglyNormalizingOfWfContext`) + `exists_normalForm_of_isStronglyNormalizing` (weak normalization) +
`noClosedNormalTermAtEmptyType`; the hypothesis carries the classifier along the chain.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **SN-050 consistency, gated on SR-along-`↝*`.**  A closed term typed at the empty type yields `False`,
given subject reduction along the reduction chain.  OB-5 strong-normalizes the subject to a reachable normal
form; the hypothesis carries the `EmptyType` classifier to that normal form; `noClosedNormalTermAtEmptyType`
refutes a closed normal inhabitant of the empty type.  The `subjectReductionStar` hypothesis is the lone
residual — the iterated SN-055 master dispatcher — so this is the ★ SN-050 milestone modulo SR. -/
theorem HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType {profile : PolyProfile}
    {subject : RawTerm 0}
    (subjectReductionStar : ∀ {start finish : RawTerm 0},
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) start
        (emptyTypeCell (scope := 0)) →
      StepStar start finish →
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) finish
        (emptyTypeCell (scope := 0)))
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  have terminates : IsStronglyNormalizing subject :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtEmptyType
    (subjectReductionStar typed reachesNormalForm) normalFormIsNormal

end FX1Poly.Typed

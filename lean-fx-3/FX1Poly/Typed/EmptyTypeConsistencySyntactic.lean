import FX1Poly.Typed.ConsistencyConditionalOnSubjectReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/EmptyTypeConsistencySyntactic
    — the SYNTACTIC route to empty-type consistency, now UNCONDITIONAL

`ConsistencyConditionalOnSubjectReduction` ships `consistencyOfSubjectReductionStarToEmptyType`: a closed term
typed at the empty type yields `False`, GATED on one explicit hypothesis — subject reduction along the reduction
chain (`StepStar`) carrying the `EmptyType` classifier from the subject to its normal form.  At the time that
file was written, that hypothesis was the lone residual (the iterated master dispatcher, itself blocked on the
grown fundamental-metatheory bundle).

That gate is now discharged: `HasTypeDescPi.subjectReductionStar` is the UNCONDITIONAL iterated master subject
reduction (the `StepStar.rec` over the single-step master dispatcher, landed once the grown metatheory bundle
became unconditional).  Instantiated at the empty context (`WfContextDescPi.emptyIsWellFormed`) and the
`EmptyType` classifier, it discharges the hypothesis, turning the conditional consistency into an unconditional
theorem.

So FX now has TWO independent unconditional proofs that the empty type has no closed inhabitant:

  * the candidate / validity route — `HasTypeDescPi.emptyTypeConsistency` (no SR needed; the empty type's
    semantic validity has no member), and
  * **the syntactic route — `HasTypeDescPi.emptyTypeConsistencySyntactic` (this file): strong-normalize the
    subject to a normal form (open SN, SN-043), carry the classifier down (SR-along-`↝*`), and refute a closed
    normal inhabitant (`noClosedNormalTermAtEmptyType`).**

The syntactic route is the one that survives into the SUBSTANTIVE-`Empty` regime (a real `gen_emptyCode`
formation row), where the validity route breaks — so this is the consistency proof the future substantive-empty
kernel inherits.  It is also the concrete demonstration that the syntactic metatheory composes end-to-end:
SN-for-well-typed + subject-reduction-along-`↝*` + grown closed-canonical-forms ⟹ logical consistency.

## Zero-axiom verification

Discharges `consistencyOfSubjectReductionStarToEmptyType`'s hypothesis with `HasTypeDescPi.subjectReductionStar`
(unconditional, at `WfContextDescPi.emptyIsWellFormed`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **★ Empty-type consistency, syntactic route, UNCONDITIONAL.**  A closed term typed at the empty type
yields `False` — by strong-normalizing the subject (open SN), carrying the `EmptyType` classifier to its normal
form via the now-unconditional `subjectReductionStar`, and refuting a closed normal inhabitant
(`noClosedNormalTermAtEmptyType`).  The syntactic twin of the candidate-route
`HasTypeDescPi.emptyTypeConsistency`; the route that survives into the substantive-`Empty` regime. -/
theorem HasTypeDescPi.emptyTypeConsistencySyntactic {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType
    (fun startTyped chain =>
      HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed startTyped chain)
    typed

end FX1Poly.Typed

import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.GrownOpenTypeSafety
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc

/-! # FX1Poly/Typed/GrownTypeSafetyUnconditional
    — UNCONDITIONAL grown type safety (progress + preservation), discharging the SR-along-`↝*` hypothesis via SR-U4

`GrownTypeSafety` / `GrownOpenTypeSafety` shipped the grown-engine type-safety capstones (every closed/open
grown-typed term evaluates to a canonical [-or-neutral] value, with evaluation determinism) CONDITIONALLY on a
`subjectReductionStar` hypothesis — the iterated full-engine preservation along `↝*`.  At the time that was the
lone open gate (the grown context-conversion `piElim` arm).  SR-U5 closed it: `HasTypeDescPi.subjectReductionStar`
is now UNCONDITIONAL (master subject reduction along `↝*` under the benign well-formed-context presupposition).

This file harvests that closure — discharging the hypothesis and shipping the type-safety capstones
UNCONDITIONALLY:

  * **`HasTypeDescPi.closedTypeSafety`** — every closed grown-typed term EVALUATES TO A CANONICAL VALUE: a
    reachable normal form whose head is a λ value or a Π/Σ/universe/list/option type code.  Progress +
    preservation, no hypothesis.
  * **`HasTypeDescPi.closedTypeSafetyUnique`** — the same, with EVALUATION DETERMINISM: the canonical value is
    moreover the UNIQUE normal form (progress + preservation + confluence).
  * **`HasTypeDescPi.openTypeSafety` / `HasTypeDescPi.openTypeSafetyUnique`** — the open-context analogues (any
    `WfContextDesc`-well-formed context), whose canonical conclusion gains the neutral disjunct (a variable /
    stuck application is a good normal form).

The closed discharge supplies `WfContextDescPi.emptyIsWellFormed` to SR-U4; the open discharge lifts the
`WfContextDesc` presupposition to the grown `WfContextDescPi` via `WfContextDescPi.ofWfContextDesc` (the
formation→grown well-formedness bridge), feeding both SR-U4 (which needs grown wf) and the existing open SN
(which needs formation wf).

## Zero-axiom verification

A one-line composition: the existing conditional safety capstone + `HasTypeDescPi.subjectReductionStar` (SR-U4) as
the preservation witness (closed: `WfContextDescPi.emptyIsWellFormed`; open: `WfContextDescPi.ofWfContextDesc
wellFormed`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **★ Closed grown type safety (unconditional).**  Every closed grown-typed term evaluates to a canonical value:
a reachable normal form whose head is a λ value or a Π/Σ/universe/list/option type code.  Progress +
preservation with NO hypothesis — the `subjectReductionStar` gate of `closedTypeSafetyOfSubjectReductionStar` is
discharged by the unconditional SR-U4 (`HasTypeDescPi.subjectReductionStar` at the empty context, via
`WfContextDescPi.emptyIsWellFormed`). -/
theorem HasTypeDescPi.closedTypeSafety {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value :=
  HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typedStart steps)
    typed

/-- **★ Closed grown type safety + evaluation determinism (unconditional).**  The canonical value a closed
grown-typed term evaluates to is moreover its UNIQUE normal form — progress + preservation + confluence, no
hypothesis.  Discharges the gate of `closedTypeSafetyUniqueOfSubjectReductionStar` via SR-U4. -/
theorem HasTypeDescPi.closedTypeSafetyUnique {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value) ∧
      ∀ otherForm : RawTerm 0,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typedStart steps)
    typed

/-- **★ Open grown type safety (unconditional).**  Every grown-typed term in any `WfContextDesc`-well-formed
context evaluates to a normal form that is canonical-or-neutral.  Discharges the gate of
`openTypeSafetyOfSubjectReductionStar` via SR-U4, lifting the formation well-formedness to the grown
`WfContextDescPi` (`WfContextDescPi.ofWfContextDesc`) for the preservation witness. -/
theorem HasTypeDescPi.openTypeSafety {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
      (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value) :=
  HasTypeDescPi.openTypeSafetyOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar (WfContextDescPi.ofWfContextDesc wellFormed) typedStart steps)
    typed wellFormed

/-- **★ Open grown type safety + evaluation determinism (unconditional).**  The unique normal form of a
grown-typed term in any well-formed context is moreover canonical-or-neutral — the full open "evaluates to THE
canonical-or-neutral value" statement, no hypothesis.  Discharges the gate of
`openTypeSafetyUniqueOfSubjectReductionStar` via SR-U4 + `WfContextDescPi.ofWfContextDesc`. -/
theorem HasTypeDescPi.openTypeSafetyUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
        (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value)) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar
    (fun typedStart steps =>
      HasTypeDescPi.subjectReductionStar (WfContextDescPi.ofWfContextDesc wellFormed) typedStart steps)
    typed wellFormed

end FX1Poly.Typed

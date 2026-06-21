import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionCongruenceArms
    — per-arm congruence subject reduction for the union — TYTAB-2-FT gate-2 congruence half

The remaining residual of TYTAB-2-FT gate 2 is the CONGRUENCE closer: when one child of a `.mkGen` cell steps,
re-type the parent at a `Conv`-equal classifier.  A full congruence closer is a per-arm induction over the
union typing derivation; this file accumulates the per-arm legs.

This file ships the **ofGrown arm at the empty context** — discharged UNCONDITIONALLY through the grown
engine's own master `HasTypeDescPi.subjectReduction` (which is `Step`-total, already handling congruence via
`Step.cong`).  The grown master needs `WfContextDescPi`, which the native `WfContextUnion` does NOT in general
supply (union types ⊋ grown types) — but at the EMPTY context both well-formedness predicates are trivial
(`WfContextDescPi.emptyIsWellFormed`), and the consistency route reduces closed terms (the context never
grows), so the empty-context ofGrown leg is exactly what the consistency-facing congruence closer needs. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ The ofGrown congruence arm, at the empty context (UNCONDITIONAL).**  A `.mkGen` cell typed by the
GROWN engine whose children step is re-typed at the SAME classifier: route the child-congruence step through
the grown master `HasTypeDescPi.subjectReduction` (built as `Step.cong`), then re-embed via `ofGrown`.  The
empty-context well-formedness `WfContextDescPi.emptyIsWellFormed` discharges the grown master's obligation
trivially — sidestepping the `WfContextUnion → WfContextDescPi` non-bridge.  This is the ofGrown leg of the
empty-context union congruence closer; `var`/`universeFormation` are vacuous, `conv` is recursive, and only
the three native cell arms (intro/elim/formationRule) remain. -/
theorem HasTypeUnion.ofGrownCongruenceAtEmptyContext {profile : PolyProfile}
    {generator : Generator} {payload : generator.payload 0}
    {childrenBefore childrenAfter : RawTermChildren generator.binderShifts 0}
    {classifier : RawTerm 0}
    (hostTyped : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (RawTerm.mkGen generator payload childrenBefore) classifier)
    (childStep : StepChildren childrenBefore childrenAfter) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (RawTerm.mkGen generator payload childrenAfter) classifier :=
  HasTypeUnion.ofGrown
    (HasTypeDescPi.subjectReduction hostTyped WfContextDescPi.emptyIsWellFormed
      (RawTerm.mkGen generator payload childrenAfter)
      (Step.cong generator payload childStep))

end FX1Poly.Typed

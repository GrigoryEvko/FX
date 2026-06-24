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

/-- **★ The ofGrown congruence arm, at an ARBITRARY context (UNCONDITIONAL given grown well-formedness).**  A
`.mkGen` cell typed by the GROWN engine whose children step is re-typed at the SAME classifier: route the
child-congruence step through the grown master `HasTypeDescPi.subjectReduction` (which is `Step`-total and
already internalizes its own premise re-typing), built as `Step.cong`, then re-embed via `ofGrown`.  This is
the FULLY-dischargeable arm of the GENERAL union congruence closer — unlike the native cell arms it carries no
per-obligation re-typing residue (the grown SR handles its obligations internally), so it needs only
`WfContextDescPi context`.  The empty-context closer's leg is the `WfContextDescPi.emptyIsWellFormed`
specialization (`ofGrownCongruenceAtEmptyContext` below). -/
theorem HasTypeUnion.ofGrownCongruence {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {generator : Generator} {payload : generator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (wfDescPi : WfContextDescPi context)
    (hostTyped : HasTypeDescPi profile context
      (RawTerm.mkGen generator payload childrenBefore) classifier)
    (childStep : StepChildren childrenBefore childrenAfter) :
    HasTypeUnion profile context
      (RawTerm.mkGen generator payload childrenAfter) classifier :=
  HasTypeUnion.ofGrown
    (HasTypeDescPi.subjectReduction hostTyped wfDescPi
      (RawTerm.mkGen generator payload childrenAfter)
      (Step.cong generator payload childStep))

/-- **★ The ofGrown congruence arm, at the empty context (UNCONDITIONAL).**  The `WfContextDescPi`-free
specialization of `HasTypeUnion.ofGrownCongruence` to the EMPTY context, where the grown master's
well-formedness obligation is discharged by `WfContextDescPi.emptyIsWellFormed` (sidestepping the
`WfContextUnion → WfContextDescPi` non-bridge).  This is the ofGrown leg of the empty-context (consistency-
facing) union congruence closer; `var`/`universeFormation` are vacuous, `conv` is recursive, and only the
three native cell arms (intro/elim/formationRule) remain. -/
theorem HasTypeUnion.ofGrownCongruenceAtEmptyContext {profile : PolyProfile}
    {generator : Generator} {payload : generator.payload 0}
    {childrenBefore childrenAfter : RawTermChildren generator.binderShifts 0}
    {classifier : RawTerm 0}
    (hostTyped : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (RawTerm.mkGen generator payload childrenBefore) classifier)
    (childStep : StepChildren childrenBefore childrenAfter) :
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      (RawTerm.mkGen generator payload childrenAfter) classifier :=
  HasTypeUnion.ofGrownCongruence WfContextDescPi.emptyIsWellFormed hostTyped childStep

end FX1Poly.Typed

import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/EmptyTypeConsistencyUnconditional
    — ★ SN-050 grown consistency, UNCONDITIONAL (the validity route, superseding the piElim-conditional one)

`HasTypeDescPi.emptyTypeConsistency`: **no closed term is engine-typed at `emptyTypeCell`** —
`HasTypeDescPi profile .empty subject emptyTypeCell → False` — with NO hypotheses.  This DROPS the `piElim`
conditionality of `consistencyOfPiElimArm` (`ConsistencyOfPiElimArm.lean`, CON-A5wire) and the
subject-reduction conditionality of `consistencyOfSubjectReductionStarToEmptyType`: SN-050 holds outright.

## The proof (two lines)

By **validity** (`HasTypeDescPi.classifierIsTypeDescPi`, the unconditional grown-engine type-correctness, WFG-3)
every classifier of a grown-typed term is itself a TYPE — `IsTypeDescPi context classifier`, i.e.
`∃ levelExpr flag, HasTypeDescPi context classifier (universeCodeCell levelExpr flag)`.  Specialised to a closed
`subject : emptyTypeCell`, this forces `emptyTypeCell` to be typed at a universe code.  But
`emptyTypeCell` is NOT typeable as a subject — `emptyTypeCellHasNoTyping` (the data-head-boundary refutation,
since `gen_emptyCode`'s `typingRuleDescOf` is `none`, CON-A1's deferred row) — contradiction.

The unlock is exactly `emptyTypeCellHasNoTyping`: until that refutation existed, the validity route could not
discharge "`emptyTypeCell : universe`", so consistency was routed through subject reduction / the piElim crux
(CON-A6 / CON-A5wire).  With the data-head boundary complete, validity closes SN-050 directly.

## What this IS, honestly (and what it is NOT — no overclaim)

This is the consistency of the CURRENT grown engine, in which `emptyTypeCell` is NOT a substantive type: the
engine has no `genFormation` row for `gen_emptyCode` (`typingRuleDescOf gen_emptyCode = none`, CON-A1), so
`emptyTypeCell` cannot be typed at a universe — and therefore, by validity, nothing can be typed AT it.  The
proof is genuine (validity + the boundary refutation), not vacuous and not a placeholder; the statement is
exactly the SN-050 / `#553` goal `HasTypeDescPi .empty t Empty → False`.  It is the strongest honest form
available for today's engine.

It is NOT yet the canonicity-grounded consistency for a SUBSTANTIVE empty type: when a future engine extension
gives `gen_emptyCode` a formation row (making `emptyTypeCell : Type@0` derivable, GTL-15 / `#483`), THIS proof
breaks (emptyTypeCell would then BE typeable at a universe), and consistency must instead come from canonicity
(`emptyTypeCell`'s reducibility candidate is member-free, CON-A3 — confirmed a structural model change by the
airtight obstruction in `ConsistencyTargetSignature`).  That obstruction concerns the REDUCIBILITY route and
does NOT block this SYNTACTIC validity route — they are independent.

## Zero-axiom verification

A two-line composition: `classifierIsTypeDescPi` (validity, takes `WfContextDescPi.emptyIsWellFormed`) +
`Exists` destructuring + `emptyTypeCellHasNoTyping`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ SN-050, UNCONDITIONAL.**  No closed term is engine-typed at `emptyTypeCell`:
`HasTypeDescPi .empty subject emptyTypeCell → False`, with NO hypotheses (no piElim arm, no subject
reduction).  Validity (`classifierIsTypeDescPi`) forces the classifier `emptyTypeCell` to be typed at a
universe code, which `emptyTypeCellHasNoTyping` refutes.  Supersedes the conditional
`consistencyOfPiElimArm` (CON-A5wire).  The current-engine form — honest scope in the file header. -/
theorem HasTypeDescPi.emptyTypeConsistency {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨levelExpr, flag, emptyTyped⟩ :=
    typed.classifierIsTypeDescPi WfContextDescPi.emptyIsWellFormed
  exact emptyTyped.emptyTypeCellHasNoTyping

end FX1Poly.Typed

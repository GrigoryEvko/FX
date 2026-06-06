import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/EmptyTypeConsistencyUnconditional
    — grown consistency, UNCONDITIONAL (the validity route)

`HasTypeDescPi.emptyTypeConsistency`: **no closed term is engine-typed at `emptyTypeCell`** —
`HasTypeDescPi profile .empty subject emptyTypeCell → False` — with NO hypotheses.  This carries no `piElim`
conditionality (unlike `consistencyOfPiElimArm`, `ConsistencyOfPiElimArm.lean`) and no subject-reduction
conditionality (unlike `consistencyOfSubjectReductionStarToEmptyType`): consistency holds outright.

## The proof (two lines)

By **validity** (`HasTypeDescPi.classifierIsTypeDescPi`, the unconditional grown-engine type-correctness, WFG-3)
every classifier of a grown-typed term is itself a TYPE — `IsTypeDescPi context classifier`, i.e.
`∃ levelExpr flag, HasTypeDescPi context classifier (universeCodeCell levelExpr flag)`.  Specialised to a closed
`subject : emptyTypeCell`, this forces `emptyTypeCell` to be typed at a universe code.  But
`emptyTypeCell` is NOT typeable as a subject — `emptyTypeCellHasNoTyping` (the data-head-boundary refutation,
since `gen_emptyCode`'s `typingRuleDescOf` is `none`) — contradiction.

The unlock is exactly `emptyTypeCellHasNoTyping`: it discharges "`emptyTypeCell : universe`" so the validity
route closes consistency directly.  (A substantive empty type — once a `gen_emptyCode` formation row makes
`emptyTypeCell` a real type — would instead route consistency through subject reduction / the piElim crux.)

## What this IS, honestly (and what it is NOT — no overclaim)

This is the consistency of the CURRENT grown engine, in which `emptyTypeCell` is NOT a substantive type: the
engine has no `genFormation` row for `gen_emptyCode` (`typingRuleDescOf gen_emptyCode = none`), so
`emptyTypeCell` cannot be typed at a universe — and therefore, by validity, nothing can be typed AT it.  The
proof is genuine (validity + the boundary refutation), not vacuous and not a placeholder; the statement is
exactly `HasTypeDescPi .empty t Empty → False`.  It is the strongest honest form available for today's engine.

It is NOT yet the canonicity-grounded consistency for a SUBSTANTIVE empty type: when a future engine extension
gives `gen_emptyCode` a formation row (making `emptyTypeCell : Type@0` derivable), THIS proof
breaks (emptyTypeCell would then BE typeable at a universe), and consistency must instead come from canonicity
(`emptyTypeCell`'s reducibility candidate is member-free — a structural model change, per the
airtight obstruction in `ConsistencyTargetSignature`).  That obstruction concerns the REDUCIBILITY route and
does NOT block this SYNTACTIC validity route — they are independent.

## Zero-axiom verification

A two-line composition: `classifierIsTypeDescPi` (validity, takes `WfContextDescPi.emptyIsWellFormed`) +
`Exists` destructuring + `emptyTypeCellHasNoTyping`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Consistency, UNCONDITIONAL.**  No closed term is engine-typed at `emptyTypeCell`:
`HasTypeDescPi .empty subject emptyTypeCell → False`, with NO hypotheses (no piElim arm, no subject
reduction).  Validity (`classifierIsTypeDescPi`) forces the classifier `emptyTypeCell` to be typed at a
universe code, which `emptyTypeCellHasNoTyping` refutes.  The unconditional route, alongside the conditional
`consistencyOfPiElimArm`.  The current-engine form — honest scope in the file header. -/
theorem HasTypeDescPi.emptyTypeConsistency {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨levelExpr, flag, emptyTyped⟩ :=
    typed.classifierIsTypeDescPi WfContextDescPi.emptyIsWellFormed
  exact emptyTyped.emptyTypeCellHasNoTyping

end FX1Poly.Typed

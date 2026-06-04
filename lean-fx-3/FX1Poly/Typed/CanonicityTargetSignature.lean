import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.DataCanonicityViaSconing

/-! # FX1Poly/Typed/CanonicityTargetSignature
    — SN-047/048/049 target signature: engine canonicity from the data-candidate bridge (Phase-A boundary)

The canonicity twin of `ConsistencyTargetSignature.consistencyFromEmptyCandidateBridge` (CON-A0).  Together
they make the Phase-A boundary UNIFORM: BOTH typed consistency (SN-050) and typed canonicity (SN-047/048/049)
reduce, at the engine, to the SAME residual — the data-candidate bridge "closed engine-typing at the data
type's code ⟹ data-candidate membership".

## Refined CON-A0 cost finding (the engine data-representation is bounded, not cascade-death)

The HasTypeDesc TYPING of a former is cascade-free (P13): `typingRuleDescOf` is a tiny `Option TypingRuleDesc`
table and `genFormationPi` is GENERIC over it, so a new type-former is ONE ROW — never a new HasTypeDesc arm.
The remaining cost of naming a data type is purely a new GENERATOR (the type CODE, exactly as `gen_arrowCode`
/ `gen_piTyCode` are generators): a BOUNDED ~10-12-site generator-table addition (GeneratorCore enum / arity /
binderShifts / payload, GeneratorMetadata kind / childSpec, GeneratorAdmission, GeneratorTagRoundTrip,
RawCellCode), NOT the feared ~80-arm cascade-death.  The genuinely hard, multi-fire core is the CANDIDATE
identification (CON-A3 / BFT-15: the new code's reducibility interpretation IS the data candidate).

So Phase A is gated on a tractable-but-deliberate engine data-representation (a per-data-type generator + its
candidate), tracked at #483 / #485-#487 — NOT on intractable cascade-death.  This file ships the engine-side
target signature so the final canonicity wires are one-liners once the data codes + candidate bridges land.

## Zero-axiom verification

A one-line composition of the shipped `dataCanonicityViaSconing` with the engine typing predicate.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **SN-047/048/049 target signature: engine canonicity from the data-candidate bridge.**  For any value
predicate `isValue` and any closed type cell `dataTypeCode`, if every closed term engine-typed at
`dataTypeCode` is a member of the data reducibility candidate `CanonicalFormsPredicate isValue`
(`candidateBridge` — the typed reducibility fundamental theorem AT that data type), then every closed term
engine-typed at `dataTypeCode` reduces to a value satisfying `isValue`.  Specializes `dataCanonicityViaSconing`
(#695) to `isWellTyped := fun t => HasTypeDescPi profile .empty t dataTypeCode`.  Instantiating
`isValue := boolIsValue` / `IsNatValue` / `IsListValue` / … gives the per-type canonicity (SN-047/048/049),
each a one-liner once the data type's code + candidate bridge land (the deferred engine data-representation,
#483/#485-487).  The candidate twin of `consistencyFromEmptyCandidateBridge` (which is this at the empty value
predicate, where "reduces to a value" degenerates to absurdity). -/
theorem dataCanonicityFromCandidateBridge {profile : PolyProfile}
    {isValue : RawTerm 0 → Prop} {dataTypeCode : RawTerm 0}
    (candidateBridge : ∀ closedTerm : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm dataTypeCode →
        CanonicalFormsPredicate isValue closedTerm)
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm dataTypeCode) :
    ∃ value : RawTerm 0, StepStar closedTerm value ∧ isValue value :=
  dataCanonicityViaSconing candidateBridge closedTerm typed

end FX1Poly.Typed

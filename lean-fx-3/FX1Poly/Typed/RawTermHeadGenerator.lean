import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/RawTermHeadGenerator — the head-generator projection (unified to rootGenerator)

`RawTerm.headGenerator` — the head-generator projection (`RawTerm → Generator`, the `mkGen`
constructor's first field) used to refute cross-constructor equalities via
`congrArg … |>.noConfusion` — is a thin `abbrev` DELEGATING to the Core-canonical
`RawTerm.rootGenerator` (`ReducibilityCandidateArrow`): one projection logic, while the
name + the derived `eq_*_of_headGenerator` / `headGenerator_*Cell` family + its consumers
share that single definition (the abbrev is reducible, so every `rfl` / `congrArg` /
`noConfusion` use closes against `rootGenerator`).

## Zero-axiom verification

A `reducible` abbrev for a pure structural projection.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The head generator of a raw term — the Typed-layer name for the Core-canonical
`RawTerm.rootGenerator` (the single `mkGen` constructor's `generator` field). -/
abbrev RawTerm.headGenerator {scope : Nat} : RawTerm scope → Generator :=
  RawTerm.rootGenerator

end FX1Poly.Typed

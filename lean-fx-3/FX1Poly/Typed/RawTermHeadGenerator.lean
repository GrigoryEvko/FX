import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/RawTermHeadGenerator — the head-generator projection (unified to rootGenerator)

`RawTerm.headGenerator` — the head-generator projection (`RawTerm → Generator`, the `mkGen`
constructor's first field) used to refute cross-constructor equalities via
`congrArg … |>.noConfusion` — was historically a SEPARATE `def` inside the old
`HasTypeHonesty` engine file, duplicating the Core-canonical `RawTerm.rootGenerator`
(`ReducibilityCandidateArrow`).  Extracted here (out of the to-be-retired HasType cluster,
HT-C) as a thin `abbrev` DELEGATING to `rootGenerator`: one projection logic, while the
name + the derived `eq_*_of_headGenerator` / `headGenerator_*Cell` family + the ~33
consumers stay unchanged (the abbrev is reducible, so every `rfl` / `congrArg` /
`noConfusion` use closes exactly as before).

The eventual full unification (mechanically renaming `headGenerator → rootGenerator` at the
~170 use sites and dropping this alias) is a separate pure-rename follow-up; this step
removes the duplicate projection LOGIC and gets the definition out of the delete-cluster.

## Zero-axiom verification

A `reducible` abbrev for a pure structural projection.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The head generator of a raw term — the Typed-layer name for the Core-canonical
`RawTerm.rootGenerator` (the single `mkGen` constructor's `generator` field), unified to
one projection (HT-C dedup). -/
abbrev RawTerm.headGenerator {scope : Nat} : RawTerm scope → Generator :=
  RawTerm.rootGenerator

end FX1Poly.Typed

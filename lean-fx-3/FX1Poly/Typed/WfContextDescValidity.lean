import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.HasTypeDescValidity

/-! # FX1Poly/Typed/WfContextDescValidity — classifier-validity over WfContextDesc

The formation engine's validity (regularity / type-correctness) over the `WfContextDesc` substrate
(`WfContextDesc.lean` / `WfContextDescLookup.lean`): `IsTypeDesc`-based formation well-formedness, whose
`lookupIsTypeDesc` yields an `IsTypeDesc` directly.  The `var` arm reads `WfContextDesc.lookupIsTypeDesc` (one
line).  This is the canonical formation validity, threaded by the formation-engine consumers.  Mirrors the grown
`HasTypeDesc.classifierIsTypeDescPi` (over `WfContextDescPi`), at the lighter formation layer.

## Why each arm closes

* `var` — `WfContextDesc.lookupIsTypeDesc` concludes `IsTypeDesc` of the looked-up type directly.
* `conv` — the reclassifier's own typing IS the `IsTypeDesc` witness.
* `universeFormation` — `universeCodeCell ℓ.lsucc f` is typed one level up by `HasTypeDesc.universeFormation`.
* `genFormation` — the row-shape-agnostic `typingRuleDescOf_output_isUniverseCode` reduces the output to
  `universeCodeCell (lmaxAll levels) flag`, a universe code typed one level up.

## Zero-axiom verification

Full-enumeration term-mode `match` on the formation derivation + `WfContextDesc.lookupIsTypeDesc` +
`HasTypeDesc.universeFormation` + the `typingRuleDescOf_output_isUniverseCode` interface fact.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Formation validity over `WfContextDesc`.**  A `HasTypeDesc`-typed cell's classifier is itself a formation
type (`IsTypeDesc`), under the `IsTypeDesc`-based well-formedness `WfContextDesc`.  The `var` arm reads
`WfContextDesc.lookupIsTypeDesc` directly.  The canonical formation validity, threaded by the formation-engine
consumers. -/
theorem HasTypeDesc.classifierIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (derivation : HasTypeDesc profile context subject classifier) :
    IsTypeDesc profile context classifier :=
  match derivation with
  | .var context index => WfContextDesc.lookupIsTypeDesc context wellFormed index
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, reclassifierTyped⟩
  | .universeFormation context levelExpr flag =>
      ⟨_, _, HasTypeDesc.universeFormation context levelExpr.lsucc flag⟩
  | .genFormation context generator _payload _children levels flag rule
      isFormation _premises => by
      -- ROW-SHAPE-AGNOSTIC (UNIT-3a migration): the output is SOME universe code — true for the
      -- flag-using `universeFormerOutput` rows and any future flag-pinned nullary row alike.
      obtain ⟨outputLevel, outputFlag, hOutput⟩ :=
        typingRuleDescOf_output_isUniverseCode isFormation _ levels flag
      rw [hOutput]
      exact ⟨outputLevel.lsucc, outputFlag,
        HasTypeDesc.universeFormation context outputLevel outputFlag⟩

end FX1Poly.Typed

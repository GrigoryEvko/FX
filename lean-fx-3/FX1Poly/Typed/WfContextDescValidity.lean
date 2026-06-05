import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.HasTypeDescValidity

/-! # FX1Poly/Typed/WfContextDescValidity — classifier-validity over WfContextDesc (HasType-free)

`HasTypeDesc.classifierIsTypeDesc` (`HasTypeDescValidity.lean`) — the formation engine's validity (P3) — is
proved over the bespoke `WfContext`, and its `var` arm therefore unpacks a `WfContext.lookupIsType` (a bespoke
`IsType`) and lifts it through `HasType.toHasTypeDesc`.  That `toHasType` round-trip is the file's lone residual
coupling to the `HasType` engine; it is inherent to `WfContext` being `IsType`-based, not to validity itself.

This file ships the HasType-FREE twin over the `WfContextDesc` substrate (`WfContextDesc.lean` /
`WfContextDescLookup.lean`): `IsTypeDesc`-based formation well-formedness, whose `lookupIsTypeDesc` yields an
`IsTypeDesc` directly.  The validity proof is then identical to the original EXCEPT the `var` arm reads
`WfContextDesc.lookupIsTypeDesc` (one line, no bridge), so the whole theorem contains no `HasType`.  This is the
migration TARGET: once the formation-engine consumers thread `WfContextDesc` (the wholesale `WfContext →
WfContextDesc` re-thread), they call this in place of `classifierIsTypeDesc`, and at the bespoke-engine deletion
(HT-C) it becomes the canonical formation validity.  Mirrors the grown `HasTypeDesc.classifierIsTypeDescPi`
(over `WfContextDescPi`), at the lighter formation layer.

## Why each arm closes HasType-free

* `var` — `WfContextDesc.lookupIsTypeDesc` concludes `IsTypeDesc` of the looked-up type directly (no
  `HasType.toHasTypeDesc`; that bridge is exactly what the substrate removes).
* `conv` — the reclassifier's own typing IS the `IsTypeDesc` witness (as in the original — already HasType-free).
* `universeFormation` — `universeCodeCell ℓ.lsucc f` is typed one level up by `HasTypeDesc.universeFormation`.
* `genFormation` — the table-generic `typingRuleDescOf_outputIsUniverseFormer` reduces the output to
  `universeCodeCell (lmaxAll levels) flag`, a universe code typed one level up.

## Zero-axiom verification

Full-enumeration term-mode `match` on the formation derivation + `WfContextDesc.lookupIsTypeDesc` +
`HasTypeDesc.universeFormation` + the `typingRuleDescOf_outputIsUniverseFormer` table fact.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Formation validity (P3) over `WfContextDesc`, HasType-free.**  A `HasTypeDesc`-typed cell's classifier is
itself a formation type (`IsTypeDesc`), under the `IsTypeDesc`-based well-formedness `WfContextDesc`.  Identical
to `HasTypeDesc.classifierIsTypeDesc` except the `var` arm reads `WfContextDesc.lookupIsTypeDesc` directly — so
the whole proof contains no `HasType.toHasTypeDesc`.  The migration target the formation-engine consumers adopt
once they thread `WfContextDesc`; the canonical formation validity after the bespoke engine is deleted. -/
theorem HasTypeDesc.classifierIsTypeDescNative {profile : PolyProfile} {scope : Nat}
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
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDesc.universeFormation context (lmaxAll levels) flag⟩

end FX1Poly.Typed

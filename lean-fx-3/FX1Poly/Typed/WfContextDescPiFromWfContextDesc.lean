import FX1Poly.Typed.WfContextDesc
import FX1Poly.Typed.WfContextDescPiValidity

/-! # FX1Poly/Typed/WfContextDescPiFromWfContextDesc — the formation→grown well-formedness lift

`WfContextDesc` (`WfContextDesc.lean`) certifies each context binding is a FORMATION type (`IsTypeDesc`); the
grown `WfContextDescPi` (`WfContextDescPi.lean`) certifies each is a GROWN type (`IsTypeDescPi`).  Since every
formation type is a grown type (`IsTypeDesc.toIsTypeDescPi`, via `HasTypeDesc.toHasTypeDescPi = ofFormation`),
a formation-well-formed context is grown-well-formed.

This file ships that lift, `WfContextDescPi.ofWfContextDesc`.  The source of a grown-well-formed context is a
formation-well-formed one, and this is the clean formation→grown bridge.  Consumers that obtain a
`WfContextDesc` (e.g. the formation-side decidable checkers) but must feed a grown-engine consumer
(`HasTypeDescPi`-threaded, wanting `WfContextDescPi`) route through this single lift rather than re-threading.

## Zero-axiom verification

Structural recursion on the context telescope (full `.empty` / `.cons` coverage), assembled from the shipped
primitives `WfContextDescPi.emptyIsWellFormed` / `.cons` / `WfContextDesc.tailWellFormed` / `.headIsTypeDesc` /
`IsTypeDesc.toIsTypeDescPi`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The formation→grown well-formedness lift.**  A formation-well-formed context (each binding an
`IsTypeDesc`) is grown-well-formed (each binding an `IsTypeDescPi`), because each formation type is a grown type
(`IsTypeDesc.toIsTypeDescPi`).  By structural recursion on the context telescope: the empty context lifts to
`WfContextDescPi.emptyIsWellFormed`; a `cons` lifts its prefix by the induction hypothesis and its head binding
by the per-binding bridge. -/
theorem WfContextDescPi.ofWfContextDesc {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
      WfContextDesc context → WfContextDescPi context
  | _, .empty, _ => WfContextDescPi.emptyIsWellFormed
  | _, .cons _restContext _bindingType, wellFormed =>
      WfContextDescPi.cons
        (WfContextDescPi.ofWfContextDesc (WfContextDesc.tailWellFormed wellFormed))
        (WfContextDesc.headIsTypeDesc wellFormed).toIsTypeDescPi

end FX1Poly.Typed

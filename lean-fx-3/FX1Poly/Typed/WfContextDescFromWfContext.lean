import FX1Poly.Typed.WfContext
import FX1Poly.Typed.WfContextDesc

/-! # FX1Poly/Typed/WfContextDescFromWfContext — the `WfContext → WfContextDesc` bridge (HT-C delete-target)

`WfContextDesc.ofWfContext` embeds the (old, `HasType`/`IsType`-based) `WfContext` into the native
`WfContextDesc` (`IsTypeDesc`-based): each `IsType` binding lifts to `IsTypeDesc` via the completeness
bridge `HasType.toHasTypeDesc`.  It lets the migration consume shipped `WfContext` hypotheses at the
formation layer one site at a time.

## Why this lives in its own file (HT-B/HT-C)

It was originally defined inside `WfContextDesc.lean`, which forced `WfContextDesc.lean` to import the
old `WfContext` (and hence the `HasType` engine).  Extracting the bridge here lets `WfContextDesc.lean`
stand on the native description engine alone — the structural precondition for the eventual
`WfContext := WfContextDesc` rethread (the old `WfContext` may not transitively re-enter the native
predicate's dependency cone).  As one of the three `HasType` bridges, this whole file is deleted in HT-C
once its consumers are rerouted to the native `WfContextDesc` API.

## Zero-axiom verification

Structural recursion + `And` projections + `HasType.toHasTypeDesc` (the easy embedding).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Every `HasType`-well-formed context is formation-well-formed: each `IsType` binding embeds via
`HasType.toHasTypeDesc`.  The easy bridge (`IsType → IsTypeDesc`); lets the formation metatheory consume the
shipped `WfContext` hypotheses one migration site at a time. -/
theorem WfContextDesc.ofWfContext {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
      WfContext context → WfContextDesc context
  | _, .empty, _ => trivial
  | _, .cons _restContext _bindingType, wellFormed =>
      ⟨WfContextDesc.ofWfContext wellFormed.tailWellFormed,
        let ⟨levelExpr, flag, hasTypeDeriv⟩ := wellFormed.headIsType
        ⟨levelExpr, flag, hasTypeDeriv.toHasTypeDesc⟩⟩

end FX1Poly.Typed

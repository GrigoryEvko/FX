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

## REMOVE WHEN — the `WfContext := WfContextDesc` rethread lands (HT-C)

Precise expiry trigger: the single atomic rethread that makes the old `WfContext` defeq to the
native `WfContextDesc` (`abbrev WfContext := WfContextDesc`, or the in-place redefinition of
`WfContext` to the `IsTypeDesc`-based body).  At that instant the type of `ofWfContext` collapses
from `WfContext ctx → WfContextDesc ctx` to `WfContextDesc ctx → WfContextDesc ctx` — the IDENTITY,
carrying no content — so it is pure dead weight.  Delete it then, mechanically:

  1. At every call site (today exactly `HasTypeDescDecidable.lean` and
     `HasTypeDescPiCheckVariable.lean` — re-grep `WfContextDesc.ofWfContext` before deleting in case
     more landed), replace `WfContextDesc.ofWfContext wellFormed` with `wellFormed`, then drop
     `import FX1Poly.Typed.WfContextDescFromWfContext`.
  2. Delete this file.
  3. Remove the `#assert_no_axioms FX1Poly.Typed.WfContextDesc.ofWfContext` gate from
     `FX1PolyAudit/AuditTyped.lean`.

This is bridge 3 of the 3-bridge HT-C deletion cohort; the other two —
`HasType.toHasTypeDesc` (completeness, in the surviving `HasTypeDesc.lean`) and
`HasTypeDesc.toHasType` (soundness, in the delete-cluster `HasTypeDescSound.lean`) — fall in the
same atomic commit when the old `HasType` engine is deleted.  Do NOT delete earlier: until the
rethread the native deciders genuinely need this to accept a `WfContext` argument while keeping
their public signatures.  Full surgery census in `project_ht_bc_single_engine_surgery.md`.

## Zero-axiom verification

Structural recursion + `And` projections + `HasType.toHasTypeDesc` (the easy embedding).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- TODO: remove in HT-C (the HasType-engine delete) — this bridge becomes the identity
-- `WfContextDesc → WfContextDesc` the moment `WfContext := WfContextDesc`; deletion checklist is in the
-- file header above (REMOVE WHEN).  Bridge 3 of 3 in the HT-C cohort.
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

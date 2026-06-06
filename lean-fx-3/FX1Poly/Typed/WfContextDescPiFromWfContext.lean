import FX1Poly.Typed.WfContext
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/WfContextDescPiFromWfContext — the `WfContext → WfContextDescPi` bridge

`WfContextDescPi.ofWfContext` embeds the (old, `HasType`/`IsType`-based) `WfContext` into the GROWN
well-formedness `WfContextDescPi` (`IsTypeDescPi`-based): each `IsType` binding lifts to `IsTypeDescPi`
via `HasTypeDescPi.ofFormation ∘ HasType.toHasTypeDesc`.  It lets grown metatheory (e.g. the master SR
dispatcher, SN-055) consume the shipped `WfContext` hypotheses (OB-5's) at the grown layer.

## Why this lives in its own file (HT-B/HT-C)

It was defined inside `WfContextDescPi.lean`, forcing the GROWN well-formedness predicate to import the old
`WfContext`/`HasType` engine — and to transitively drag it into every consumer of the grown wf predicate.
Extracting the bridge here lets `WfContextDescPi.lean` stand on the grown description engine alone
(`HasTypeDescPi`), so the survivor predicate is `WfContext`-free.  Mirrors the formation-layer split
`WfContextDescFromWfContext.lean` (which holds `WfContextDesc.ofWfContext`).

## TODO — at the `WfContext := WfContextDesc` flip: RENAME, do not delete (this bridge is a KEEPER)

Unlike the three pure `HasType` bridges (`HasType.toHasTypeDesc`, `HasTypeDesc.toHasType`,
`WfContextDesc.ofWfContext` — which become identities/dead at the flip), this one survives as a genuine
function.  When `WfContext` becomes `WfContextDesc` (whose bindings are `IsTypeDesc`), rewrite the body to
read `wellFormed.headIsTypeDesc` (an `IsTypeDesc`, i.e. `∃ levelExpr flag, HasTypeDesc Γ T (universeCode)`)
and feed it straight to `HasTypeDescPi.ofFormation` — DROPPING the `HasType.toHasTypeDesc` call.  The result
is the formation→grown well-formedness lift `WfContextDesc → WfContextDescPi` (IsTypeDesc ⤳ IsTypeDescPi),
which the grown master SR genuinely needs.  So at HT-C: rewrite + rename to `ofWfContextDesc`, do not delete.

## Zero-axiom verification

Structural recursion + `And` projections + `HasTypeDescPi.ofFormation ∘ HasType.toHasTypeDesc` (the easy
embedding).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Every `HasType`-well-formed context is grown-well-formed: each `HasType` binding embeds via `ofFormation`
(after `HasType.toHasTypeDesc`).  The easy bridge (`IsType → IsTypeDescPi`); lets grown metatheory consume the
shipped `WfContext` hypotheses (e.g. OB-5's) at the grown layer. -/
theorem WfContextDescPi.ofWfContext {profile : PolyProfile} :
    {scope : Nat} → {context : TypingContext profile scope} →
      WfContext context → WfContextDescPi context
  | _, .empty, _ => trivial
  | _, .cons _restContext _bindingType, wellFormed =>
      ⟨WfContextDescPi.ofWfContext wellFormed.tailWellFormed,
        let ⟨levelExpr, flag, hasTypeDeriv⟩ := wellFormed.headIsType
        ⟨levelExpr, flag, HasTypeDescPi.ofFormation hasTypeDeriv.toHasTypeDesc⟩⟩

end FX1Poly.Typed

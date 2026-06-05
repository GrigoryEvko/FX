import FX1Poly.Typed.WfContextDesc
import FX1Poly.Typed.HasTypeDescWeakening

/-! # FX1Poly/Typed/WfContextDescLookup — lookup-validity for the formation context well-formedness

The formation twin of `WfContext.lookupIsType` (`HasTypeValidity.lean`) and of the grown
`WfContextDescPi.lookupIsType` (WFG-2): in a formation-well-formed context, the type of EVERY variable — not
just the most-recent binding — is a formation type (`IsTypeDesc`) in the full context.  This is the `var`-arm
engine that lets `HasTypeDesc.classifierIsTypeDesc` read its variable case off `WfContextDesc` directly, with no
`HasType` round-trip (the residual coupling the formation-engine decouple removes).

  * `IsTypeDesc.weakenUnderBinding` — `IsTypeDesc` survives a binding extension (the formation weakening of the
    universe-typing witness, via `HasTypeDesc.weakenUnderBinding`; the universe code renames to itself).
  * `WfContextDesc.lookupIsTypeDesc` — structural induction on the context: the head binding is a formation type
    by `headIsTypeDesc` (weakened over itself); a deeper binding by the IH on the prefix (weakened through the
    new binding).  Mirrors `WfContext.lookupIsType` / `WfContextDescPi.lookupIsType`, with the weakening at the
    formation `IsTypeDesc` / `HasTypeDesc` layer.

## Zero-axiom verification

Structural context induction + `HasTypeDesc.weakenUnderBinding` (formation renaming) + the `WfContextDesc`
`And`-projection inversions.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- `IsTypeDesc` survives a binding extension: if `classifier` is a formation type in `context`, its weakening is
a formation type in `context.cons newBinding`.  The formation weakening of the universe-typing witness (the
universe code is closed, so it renames to itself definitionally). -/
theorem IsTypeDesc.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsTypeDesc profile context classifier) (newBinding : RawTerm scope) :
    IsTypeDesc profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, typed.weakenUnderBinding newBinding⟩

/-- Lookup-validity for formation well-formedness: in a formation-well-formed context, the type of every
variable is a formation type in the full context.  Structural induction on the context (the head binding via
`headIsTypeDesc`, a deeper binding via the IH on the prefix), each weakened through the intervening binding.
The formation mirror of `WfContext.lookupIsType`; the `var`-arm engine of formation classifier-validity over
`WfContextDesc`. -/
theorem WfContextDesc.lookupIsTypeDesc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextDesc context →
      ∀ index : Fin scope, IsTypeDesc profile context (context.lookup index) := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          exact (WfContextDesc.headIsTypeDesc wellFormed).weakenUnderBinding bindingType
      | succ k =>
          exact (ih (WfContextDesc.tailWellFormed wellFormed)
            ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding bindingType

end FX1Poly.Typed

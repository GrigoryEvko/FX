import FX1Poly.Typed.IsTypeDesc

/-! # FX1Poly/Typed/WfContextDesc — formation-engine context well-formedness (`IsTypeDesc`-based)

`WfContextDesc` certifies each binding of a `TypingContext` is a FORMATION type
(`IsTypeDesc` = `∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell levelExpr flag)`).  Lookups and
extensions stay inside `HasTypeDesc`.  It mirrors `WfContextDescPi` exactly (a structural-recursion `def` +
`And`-projection inversions, propext-free), using the formation `IsTypeDesc` (lighter than the grown
`IsTypeDescPi` of `WfContextDescPi`).

The formation engine `HasTypeDesc` and `WfContextDesc` layer over the same raw telescope without any cycle.

## What this file ships

  * `WfContextDesc` — the predicate (computed by structural recursion, layered over the raw telescope).
  * `emptyIsWellFormed` / `tailWellFormed` / `headIsTypeDesc` / `cons` — the introduction + `And`-projection
    inversions (the primitives a formation metatheorem threads through a binder).
  * `wfContextDesc_universeBinding` — non-vacuity: a universe-code binding is formation-well-formed.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + a constructor-based witness.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Formation-engine context well-formedness: each binding is a formation type (`IsTypeDesc`) in the prefix
context that precedes it.  Computed by structural recursion on the telescope, `HasTypeDesc`-native. -/
def WfContextDesc {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextDesc restContext ∧ IsTypeDesc profile restContext bindingType

/-- The empty context is formation-well-formed. -/
theorem WfContextDesc.emptyIsWellFormed {profile : PolyProfile} :
    WfContextDesc (profile := profile) .empty :=
  trivial

/-- Inversion: the prefix of a formation-well-formed `cons` context is formation-well-formed. -/
theorem WfContextDesc.tailWellFormed {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDesc (restContext.cons bindingType)) :
    WfContextDesc restContext :=
  wellFormed.1

/-- Inversion: the most-recent binding of a formation-well-formed `cons` context is a formation type in the
prefix. -/
theorem WfContextDesc.headIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDesc (restContext.cons bindingType)) :
    IsTypeDesc profile restContext bindingType :=
  wellFormed.2

/-- Introduction: extending a formation-well-formed context by a binding that is a formation type in the prefix
yields a formation-well-formed context.  The primitive a formation metatheorem threads into a codomain/body
checked under `Γ.cons dom` — the binding witness is an `IsTypeDesc` read directly off the description engine. -/
theorem WfContextDesc.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextDesc restContext)
    (bindingIsTypeDesc : IsTypeDesc profile restContext bindingType) :
    WfContextDesc (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsTypeDesc⟩

/-- `WfContextDesc` is non-vacuous: a context binding a single universe code is formation-well-formed (the
universe code is a formation type via `universeFormation`). -/
theorem wfContextDesc_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextDesc (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial,
    ⟨levelExpr.lsucc, flag,
      HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
        levelExpr flag⟩⟩

end FX1Poly.Typed

import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.WfContext

/-! # FX1Poly/Typed/WfContextDesc — formation-engine context well-formedness (`IsTypeDesc`-based)

`WfContext` (`WfContext.lean`) certifies every binding of a `TypingContext` is a type, but via `IsType`,
which is `HasType`-based (the bespoke leaf engine).  So every formation-engine metatheorem that EXTENDS or
LOOKS UP a `WfContext` binding imports `HasType` data through the `HasType.toHasTypeDesc` /
`HasTypeDesc.toHasType` bridges — the residual `HasType` coupling behind `HasTypeDesc.classifierIsTypeDesc`'s
`var` arm and `DescTelescope.uniquenessAgree`'s leaf.  That coupling is not removable while the well-formedness
the formation engine threads is itself `HasType`-defined.

This file ships the formation-engine twin: `WfContextDesc`, certifying each binding is a FORMATION type
(`IsTypeDesc` = `∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell levelExpr flag)`).  Lookups and extensions
then stay inside `HasTypeDesc` — no `HasType` round-trip.  It mirrors `WfContext` / `WfContextDescPi` exactly (a
structural-recursion `def` + `And`-projection inversions, propext-free), swapping `IsType` for the formation
`IsTypeDesc` (lighter than the grown `IsTypeDescPi` of `WfContextDescPi`).

The formation engine `HasTypeDesc` does NOT import `WfContext`, so layering `WfContextDesc` over the same raw
telescope introduces no cycle.  This is a NEW predicate, not an in-place redefinition of `WfContext`: the
not-yet-removed bespoke `HasType` engine still consumes `WfContext`'s `IsType` bindings, so both coexist until
the bespoke engine is deleted — at which point `WfContext` is superseded by `WfContextDesc`.

## What this file ships

  * `WfContextDesc` — the predicate (computed by structural recursion, layered over the raw telescope).
  * `emptyIsWellFormed` / `tailWellFormed` / `headIsTypeDesc` / `cons` — the introduction + `And`-projection
    inversions (the primitives a formation metatheorem threads through a binder).
  * `WfContextDesc.ofWfContext` — the easy bridge: every `HasType`-well-formed context is formation-well-formed
    (each `IsType` binding embeds via `HasType.toHasTypeDesc`).  Lets the migration consume the shipped
    `WfContext` hypotheses at the formation layer one site at a time.
  * `wfContextDesc_universeBinding` — non-vacuity: a universe-code binding is formation-well-formed.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + `HasType.toHasTypeDesc` (the easy embedding) + a
constructor-based witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Formation-engine context well-formedness: each binding is a formation type (`IsTypeDesc`) in the prefix
context that precedes it.  Computed by structural recursion on the telescope; the `HasTypeDesc`-native twin of
the `HasType`-based `WfContext`. -/
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
checked under `Γ.cons dom` — and unlike `WfContext.cons`, the binding witness is an `IsTypeDesc` read directly
off the description engine (no `HasType` round-trip). -/
theorem WfContextDesc.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextDesc restContext)
    (bindingIsTypeDesc : IsTypeDesc profile restContext bindingType) :
    WfContextDesc (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsTypeDesc⟩

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

import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/WfContextDescPi — grown context well-formedness

`WfContextDescPi` certifies that each binding of a `TypingContext` is a GROWN type (`IsTypeDescPi`).  This
predicate extends cleanly at a grown binder: a grown domain typing `HasTypeDescPi Γ dom (universeCode)` IS an
`IsTypeDescPi`, so `WfContextDescPi.cons` is directly available at a `piIntro` binder — exactly what the master
subject-reduction dispatcher needs to extend context well-formedness when recursing into a body whose β-cases
depend on it.  It is a structural-recursion `def` + `And`-projection inversions (propext-free).

## What this file ships

  * `WfContextDescPi` — the predicate (computed by structural recursion, layered over the raw telescope).
  * `emptyIsWellFormed` / `tailWellFormed` / `headIsType` / `cons` — the introduction + `And`-projection
    inversions (the primitives the master SR threads through a `piIntro` codomain binder).
  * `wfContextDescPi_universeBinding` — non-vacuity: a universe-code binding is grown-well-formed.

The formation→grown lift `WfContextDesc → WfContextDescPi` lives in `WfContextDescPiFromWfContextDesc.lean`.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + `HasTypeDescPi.ofFormation ∘ universeFormation` (the
non-vacuity witness) + a constructor-based witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Grown context well-formedness: each binding is a GROWN type (`IsTypeDescPi`) in the prefix context that
precedes it.  Computed by structural recursion on the telescope; extendable at grown binders. -/
def WfContextDescPi {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Prop
  | _, .empty => True
  | _, .cons restContext bindingType =>
      WfContextDescPi restContext ∧ IsTypeDescPi profile restContext bindingType

/-- The empty context is grown-well-formed. -/
theorem WfContextDescPi.emptyIsWellFormed {profile : PolyProfile} :
    WfContextDescPi (profile := profile) .empty :=
  trivial

/-- Inversion: the prefix of a grown-well-formed `cons` context is grown-well-formed. -/
theorem WfContextDescPi.tailWellFormed {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDescPi (restContext.cons bindingType)) :
    WfContextDescPi restContext :=
  wellFormed.1

/-- Inversion: the most-recent binding of a grown-well-formed `cons` context is a grown type in the prefix. -/
theorem WfContextDescPi.headIsType {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (wellFormed : WfContextDescPi (restContext.cons bindingType)) :
    IsTypeDescPi profile restContext bindingType :=
  wellFormed.2

/-- Introduction: extending a grown-well-formed context by a binding that is a grown type in the prefix yields a
grown-well-formed context.  The primitive the master SR threads into a codomain/body checked under `Γ.cons dom`
— suppliable from a grown `piIntro` domain typing (`HasTypeDescPi Γ dom (universeCode)` is an `IsTypeDescPi`). -/
theorem WfContextDescPi.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextDescPi restContext)
    (bindingIsType : IsTypeDescPi profile restContext bindingType) :
    WfContextDescPi (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsType⟩

-- This GROWN well-formedness predicate stands on the grown description engine alone.  The source of a
-- grown-well-formed context is the `WfContextDesc → WfContextDescPi` formation→grown lift in
-- `WfContextDescPiFromWfContextDesc.lean`.

/-- `WfContextDescPi` is non-vacuous: a context binding a single universe code is grown-well-formed (the
universe code is a grown type via `ofFormation ∘ universeFormation`). -/
theorem wfContextDescPi_universeBinding {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    WfContextDescPi (profile := profile)
      ((TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag)) :=
  ⟨trivial,
    ⟨levelExpr.lsucc, flag,
      HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
          levelExpr flag)⟩⟩

end FX1Poly.Typed

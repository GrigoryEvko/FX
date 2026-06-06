import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/WfContextDescPi — grown context well-formedness (the structural-parity twin of WfContext)

`WfContext` (`WfContext.lean`) certifies that every binding of a `TypingContext` is a type — but via `IsType`,
which is `HasType`-based (the bespoke leaf engine).  That makes `WfContext` UN-EXTENDABLE at a grown binder: a
grown `piIntro` introduces a domain typed by `HasTypeDescPi` (richer than `HasType`), and there is no
`HasTypeDescPi → IsType` bridge, so `WfContext.cons` cannot be supplied from a grown domain typing.  OB-5 dodges
this — it only CONSUMES `WfContext` (via `headIsType`, the easy `IsType → HasTypeDescPi` direction) and threads
the reducible environment through binders, never extending `WfContext` from a grown binder.  But the master
subject-reduction dispatcher (SN-055 / TG-3) must extend context well-formedness at the `piIntro` binder, to
recurse into the body whose β-cases need it.

This file ships the grown twin: `WfContextDescPi`, certifying each binding is a GROWN type (`IsTypeDescPi`),
which DOES extend cleanly — a grown domain typing `HasTypeDescPi Γ dom (universeCode)` IS an `IsTypeDescPi`, so
`WfContextDescPi.cons` is directly available at a grown binder.  Mirrors `WfContext.lean` exactly (a
structural-recursion `def` + `And`-projection inversions, propext-free), swapping `IsType` for `IsTypeDescPi`.

## What this file ships

  * `WfContextDescPi` — the predicate (computed by structural recursion, layered over the raw telescope).
  * `emptyIsWellFormed` / `tailWellFormed` / `headIsType` / `cons` — the introduction + `And`-projection
    inversions (the primitives the master SR threads through a `piIntro` codomain binder).
  * `wfContextDescPi_universeBinding` — non-vacuity: a universe-code binding is grown-well-formed.

The `WfContext → WfContextDescPi` bridge (`WfContextDescPi.ofWfContext`) lives in the separate
`WfContextDescPiFromWfContext.lean` so this predicate file need not import the old `WfContext` / `HasType`
engine — keeping the grown wf predicate (and its consumers) off the old engine.

## Zero-axiom verification

Structural-recursion `def` + `And` projections + `HasTypeDescPi.ofFormation ∘ universeFormation` (the
non-vacuity witness) + a constructor-based witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Grown context well-formedness: each binding is a GROWN type (`IsTypeDescPi`) in the prefix context that
precedes it.  Computed by structural recursion on the telescope; the extendable-at-grown-binders twin of the
`HasType`-based `WfContext`. -/
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
— and unlike `WfContext.cons`, it IS suppliable from a grown `piIntro` domain typing
(`HasTypeDescPi Γ dom (universeCode)` is an `IsTypeDescPi`). -/
theorem WfContextDescPi.cons {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {bindingType : RawTerm scope}
    (restWellFormed : WfContextDescPi restContext)
    (bindingIsType : IsTypeDescPi profile restContext bindingType) :
    WfContextDescPi (restContext.cons bindingType) :=
  ⟨restWellFormed, bindingIsType⟩

-- The `WfContext → WfContextDescPi` bridge `WfContextDescPi.ofWfContext` was extracted to
-- `FX1Poly.Typed.WfContextDescPiFromWfContext` so this GROWN well-formedness predicate stands on the grown
-- description engine alone (no old `WfContext`/`HasType` import, so consumers of the grown wf predicate no
-- longer transitively drag the old engine).  At the `WfContext := WfContextDesc` flip that bridge is a
-- KEEPER — rewritten to the `WfContextDesc → WfContextDescPi` formation→grown lift (see its file header).

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

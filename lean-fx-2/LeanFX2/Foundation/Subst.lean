import LeanFX2.Foundation.Ty

/-! # Subst — Layer 0 joint type/raw substitution.

`Subst level source target` is the **unified** joint substitution
structure carrying BOTH:
* `forTy` — type substitution for `Ty.tyVar` positions
* `forRaw` — raw substitution for `Ty.id` endpoints (and downstream
   Term raw indices)

A single Subst handles both.  Per CLAUDE.md commitment: ONE singleton
operation, NO `dropNewest`, NO separate `termSingleton` variant.

## Definition

```lean
structure Subst (level source target : Nat) where
  forTy  : Fin source → Ty level target
  forRaw : RawTermSubst source target
```

## Operations

* `Subst.identity` — both forTy and forRaw are identity
* `Subst.lift` — under a binder; both fields lift in lockstep
* `Subst.singleton substituent rawArg` — single-binder substitution
* `Subst.compose` — sequential composition

## Critical: forRaw at singleton

`Subst.singleton substituent rawArg` has `forRaw =
RawTermSubst.singleton rawArg`.  This puts `rawArg` (NOT `RawTerm.unit`)
at position 0.  This is the architectural commitment that makes
`Term.subst σ (Term.refl r)` produce `Term.refl rawArg` after β-firing,
which makes the typed↔raw bridge `rfl` for refl-bearing β-redexes.

## Ty.subst

Defined here (not in `Foundation/Ty.lean`) to avoid cyclic import:
`Subst.forTy` returns `Ty`, so Subst's structure imports Ty; therefore
`Ty.subst` (which takes a Subst) belongs in this file.

## Composition + lift laws

* `subst_subst : (T.subst σ).subst τ = T.subst (compose σ τ)` — proved
  in Phase 1.C
* `lift_compose : (compose σ τ).lift = compose σ.lift τ.lift` — Phase 1.C
* `subst_id : T.subst Subst.identity = T` — Phase 1.C
* `weaken_subst_singleton : T.weaken.subst (singleton _ _) = T` — Phase 1.C
  (the load-bearing β-reduction cast)

These are axiom-free.  Phase 1.B ships the operations only; lemmas
land in Phase 1.C alongside Term.lean.
-/

namespace LeanFX2

/-! ## The joint Subst structure -/

/-- Joint type/raw substitution.  The `forTy` field substitutes type
variables (`Ty.tyVar` positions); the `forRaw` field substitutes raw
term variables (`Ty.id` endpoints, and downstream Term raw indices). -/
structure Subst (level source target : Nat) : Type where
  forTy  : Fin source → Ty level target
  forRaw : RawTermSubst source target

/-- Identity substitution: both fields are identity. -/
@[reducible] def Subst.identity {level scope : Nat} : Subst level scope scope where
  forTy  := fun position => Ty.tyVar position
  forRaw := RawTermSubst.identity

/-- Lift a substitution under a binder: both forTy and forRaw lift. -/
@[reducible] def Subst.lift {level source target : Nat}
    (sigma : Subst level source target) :
    Subst level (source + 1) (target + 1) where
  forTy
    | ⟨0, _⟩      => Ty.tyVar ⟨0, Nat.zero_lt_succ _⟩
    | ⟨k + 1, h⟩  => (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken
  forRaw := sigma.forRaw.lift

/-- Single-binder substitution.  Position 0 of forTy gets `substituent`;
position 0 of forRaw gets `rawArg` (NOT `RawTerm.unit`).  This is the
architectural commitment that closes the bridge β cases. -/
@[reducible] def Subst.singleton {level scope : Nat}
    (substituent : Ty level scope) (rawArg : RawTerm scope) :
    Subst level (scope + 1) scope where
  forTy
    | ⟨0, _⟩      => substituent
    | ⟨k + 1, h⟩  => Ty.tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩
  forRaw := RawTermSubst.singleton rawArg

/-! ## Ty.subst -/

/-- Apply a joint substitution to a type.  Type variables consult
`forTy`; identity-type endpoints consult `forRaw`.

Per `feedback_lean_match_arity_axioms.md`: `level` is hoisted to the
function header to keep pattern arity at 2 Nat indices (source +
target). -/
def Ty.subst {level : Nat} : ∀ {source target : Nat},
    Ty level source → Subst level source target → Ty level target
  | _, _, .unit, _ => .unit
  | _, _, .bool, _ => .bool
  | _, _, .nat, _ => .nat
  | _, _, .arrow domainType codomainType, sigma =>
      .arrow (domainType.subst sigma) (codomainType.subst sigma)
  | _, _, .piTy domainType codomainType, sigma =>
      .piTy (domainType.subst sigma) (codomainType.subst sigma.lift)
  | _, _, .sigmaTy firstType secondType, sigma =>
      .sigmaTy (firstType.subst sigma) (secondType.subst sigma.lift)
  | _, _, .tyVar position, sigma =>
      sigma.forTy position
  | _, _, .id carrier leftEndpoint rightEndpoint, sigma =>
      .id (carrier.subst sigma)
          (leftEndpoint.subst sigma.forRaw)
          (rightEndpoint.subst sigma.forRaw)
  | _, _, .listType elementType, sigma =>
      .listType (elementType.subst sigma)
  | _, _, .optionType elementType, sigma =>
      .optionType (elementType.subst sigma)
  | _, _, .eitherType leftType rightType, sigma =>
      .eitherType (leftType.subst sigma) (rightType.subst sigma)

/-- Single-variable substitution on Ty: substitute `argType` (and
its raw form `argRaw`) at position 0. -/
@[reducible] def Ty.subst0 {level scope : Nat}
    (codomainType : Ty level (scope + 1))
    (argType : Ty level scope)
    (argRaw : RawTerm scope) : Ty level scope :=
  codomainType.subst (Subst.singleton argType argRaw)

end LeanFX2

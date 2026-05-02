import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst

/-! # Ty — Layer 0 types indexed by `(level, scope)`.

`Ty level scope : Type` is the type-level syntax indexed by universe
level and de Bruijn scope size.

## Phase 1 ctor list

Foundational subset (matching lean-fx).  Modal types (`Ty.modal`)
land in Layer 6, refinement types (`Ty.refine`) in Layer 8, universe
types (`Ty.universe`) when cumulativity discipline is added.  Each
addition is a constructor extension, not a structural change.

## Why level + scope as indices

Per `fx_design.md` §3.1, FX types stratify into universe levels.
Every type `Ty level scope` lives at universe `level` with `scope`
free variables.  The level index is propagated trivially through
Layer 0–5; cumulativity (a Conv rule, per `feedback_lean_cumul_subst_mismatch`)
manages level subsumption at Layer 3+.

## Ty.id endpoints as RawTerm

Per CLAUDE.md commitment: `Ty.id carrier left right` carries `left`
and `right` as `RawTerm scope` (NOT as typed Term).  This sidesteps
Lean 4's mutual-index rule (per `feedback_lean_mutual_index_rule.md`)
which forbids `Term : Ctx → Ty Γ → Type` mutual where Ty references
Term in its index.

The trade-off: typed Term values' raw projections must align with
their identity-type endpoints.  In lean-fx-2 this is automatic
because Term's raw index IS the projection.

## Decidable equality

`deriving DecidableEq` — works for Nat-indexed families with universal
indices (Rule 3 of `feedback_lean_zero_axiom_match.md`).  If derive
leaks propext on this multi-index family, we fall back to manual
instance.

## Ty.rename

Single-pass structural recursion.  Uses `RawRenaming` for var
positions; uses `RawTerm.rename` for `Ty.id` endpoints.  Ty.subst
lives in `Foundation/Subst.lean` (avoids cyclic import — Subst's
`forTy` field requires Ty, so subst is downstream).

## Ty.weaken

Convenience: `Ty.weaken := Ty.rename RawRenaming.weaken`.
Marked `@[reducible]` per `feedback_lean_reducible_weaken.md` — used
inside Term constructor signatures (the `lam` ctor's body type is
`codomainType.weaken`).
-/

namespace LeanFX2

/-- Types indexed by universe level and de Bruijn scope size.

For Phase 1, we ship the foundational subset.  Universe / Modal /
Refinement constructors are added in their respective layers without
backward-incompatible changes to the existing ctors. -/
inductive Ty : Nat → Nat → Type
  -- Constants
  | unit {level scope : Nat} : Ty level scope
  | bool {level scope : Nat} : Ty level scope
  | nat  {level scope : Nat} : Ty level scope
  -- Function types
  | arrow {level scope : Nat}
      (domainType codomainType : Ty level scope) : Ty level scope
  | piTy {level scope : Nat}
      (domainType : Ty level scope)
      (codomainType : Ty level (scope + 1)) : Ty level scope
  -- Pair types
  | sigmaTy {level scope : Nat}
      (firstType : Ty level scope)
      (secondType : Ty level (scope + 1)) : Ty level scope
  -- Type variable (refers to a context-bound type via Fin position)
  | tyVar {level scope : Nat} (position : Fin scope) : Ty level scope
  -- Identity type with raw endpoints
  | id {level scope : Nat}
      (carrier : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope) : Ty level scope
  -- Structural type formers
  | listType   {level scope : Nat} (elementType : Ty level scope) : Ty level scope
  | optionType {level scope : Nat} (elementType : Ty level scope) : Ty level scope
  | eitherType {level scope : Nat}
      (leftType rightType : Ty level scope) : Ty level scope
  deriving DecidableEq

/-- Apply a renaming to a type.  Var positions and `Ty.id` raw
endpoints both transport along the renaming.

Per `feedback_lean_match_arity_axioms.md`: `level` is hoisted to the
function header (before `:`) to keep pattern arity at 2 Nat indices
(scope + sourceScope, before adding Ty + RawRenaming).  This avoids
the multi-Nat-index propext trap. -/
def Ty.rename {level : Nat} : ∀ {scope sourceScope : Nat},
    Ty level scope → RawRenaming scope sourceScope → Ty level sourceScope
  | _, _, .unit, _ => .unit
  | _, _, .bool, _ => .bool
  | _, _, .nat, _ => .nat
  | _, _, .arrow domainType codomainType, rho =>
      .arrow (domainType.rename rho) (codomainType.rename rho)
  | _, _, .piTy domainType codomainType, rho =>
      .piTy (domainType.rename rho) (codomainType.rename rho.lift)
  | _, _, .sigmaTy firstType secondType, rho =>
      .sigmaTy (firstType.rename rho) (secondType.rename rho.lift)
  | _, _, .tyVar position, rho =>
      .tyVar (rho position)
  | _, _, .id carrier leftEndpoint rightEndpoint, rho =>
      .id (carrier.rename rho)
          (leftEndpoint.rename rho)
          (rightEndpoint.rename rho)
  | _, _, .listType elementType, rho =>
      .listType (elementType.rename rho)
  | _, _, .optionType elementType, rho =>
      .optionType (elementType.rename rho)
  | _, _, .eitherType leftType rightType, rho =>
      .eitherType (leftType.rename rho) (rightType.rename rho)

/-- Single-binder weakening: shift all type-variable references up
by one to make room for a new binder at position 0. -/
@[reducible] def Ty.weaken {level scope : Nat} (someType : Ty level scope) :
    Ty level (scope + 1) :=
  someType.rename RawRenaming.weaken

/-! ## Pointwise + commute lemmas for Ty.rename.

Mirror of `RawTerm.rename_pointwise` / `rename_compose` /
`weaken_rename_commute`.  The `Ty.id` ctor's raw endpoints invoke
the corresponding RawTerm lemmas. -/

/-- Ty.rename respects pointwise renaming equality. -/
theorem Ty.rename_pointwise {level : Nat}
    {scope targetScope : Nat}
    {rho1 rho2 : RawRenaming scope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position) :
    ∀ (someType : Ty level scope), someType.rename rho1 = someType.rename rho2 := by
  intro someType
  induction someType generalizing targetScope with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.rename]; rw [dIH renamingEq, cIH renamingEq]
  | piTy d c dIH cIH =>
      simp only [Ty.rename]
      rw [dIH renamingEq, cIH (RawRenaming.lift_pointwise renamingEq)]
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.rename]
      rw [fIH renamingEq, sIH (RawRenaming.lift_pointwise renamingEq)]
  | tyVar position =>
      simp only [Ty.rename]; rw [renamingEq position]
  | id carrier left right carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq,
          RawTerm.rename_pointwise renamingEq left,
          RawTerm.rename_pointwise renamingEq right]
  | listType e eIH =>
      simp only [Ty.rename]; rw [eIH renamingEq]
  | optionType e eIH =>
      simp only [Ty.rename]; rw [eIH renamingEq]
  | eitherType l r lIH rIH =>
      simp only [Ty.rename]; rw [lIH renamingEq, rIH renamingEq]

/-- Compose two renamings on a Ty.  Mirrors `RawTerm.rename_compose`. -/
theorem Ty.rename_compose {level : Nat}
    {scope middleScope targetScope : Nat}
    (rho1 : RawRenaming scope middleScope)
    (rho2 : RawRenaming middleScope targetScope)
    (someType : Ty level scope) :
    (someType.rename rho1).rename rho2 =
      someType.rename (fun position => rho2 (rho1 position)) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.rename]; rw [dIH rho1 rho2, cIH rho1 rho2]
  | piTy d c dIH cIH =>
      simp only [Ty.rename]
      rw [dIH rho1 rho2, cIH rho1.lift rho2.lift]
      congr 1
      apply Ty.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.rename]
      rw [fIH rho1 rho2, sIH rho1.lift rho2.lift]
      congr 1
      apply Ty.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2,
          RawTerm.rename_compose rho1 rho2 left,
          RawTerm.rename_compose rho1 rho2 right]
  | listType e eIH => simp only [Ty.rename]; rw [eIH rho1 rho2]
  | optionType e eIH => simp only [Ty.rename]; rw [eIH rho1 rho2]
  | eitherType l r lIH rIH =>
      simp only [Ty.rename]; rw [lIH rho1 rho2, rIH rho1 rho2]

/-- weaken-after-rename equals rename-after-weaken on Ty.  Load-bearing
for the lam case of typed Term.rename. -/
theorem Ty.weaken_rename_commute {level : Nat} {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope) (someType : Ty level scope) :
    someType.weaken.rename rho.lift = (someType.rename rho).weaken := by
  show (someType.rename RawRenaming.weaken).rename rho.lift =
       (someType.rename rho).rename RawRenaming.weaken
  rw [Ty.rename_compose RawRenaming.weaken rho.lift someType,
      Ty.rename_compose rho RawRenaming.weaken someType]
  exact Ty.rename_pointwise (RawRenaming.weaken_lift_commute rho) someType

end LeanFX2

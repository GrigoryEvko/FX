import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Universe
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
  /-- Universe code.  `Ty.universe u (h : u.toNat + 1 ≤ level) :
      Ty level scope` lives at any level `≥ u + 1`.  No `Type : Type`
      (Girard's paradox forbids it: `u + 1 ≤ u` is impossible).
      Cumulativity is BUILT-IN to the constructor: a level-`u` universe
      can inhabit any `Ty l scope` for `l ≥ u + 1` directly — no
      `Term.cumulUp` wrapper needed at the Ty level.
      The propositional-inequality parameter is the standard
      P-3 (Universe Constructor Blocker) workaround per
      `feedback_lean_universe_constructor_block.md`: keeps `level` free
      so pattern-form match + `deriving DecidableEq` succeed.  Per
      Phase 12.A.B1.1, this replaced `level = universeLevel.toNat + 1`
      with `universeLevel.toNat + 1 ≤ level` to make cumul intrinsic. -/
  | «universe» {level scope : Nat} (universeLevel : UniverseLevel)
      (levelLe : universeLevel.toNat + 1 ≤ level) : Ty level scope
  -- D1.5 extension — 13 new foundational ctors.  All use RawTerm scope or
  -- Nat tags for raw payloads; richer semantic content (Modality, SessionProtocol,
  -- EffectRow, BoundaryCofib) is interpreted by downstream layers via tag dispatch
  -- so Foundation/Ty.lean stays at Layer 0 (no import cycles).
  /-- Empty/never type — uninhabited, subtype of everything. -/
  | empty {level scope : Nat} : Ty level scope
  /-- Cubical interval type — inhabitants are points in [i0, i1]. -/
  | interval {level scope : Nat} : Ty level scope
  /-- Path type over the cubical interval — `Path A x y` from x to y in A. -/
  | path {level scope : Nat}
      (carrier : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope) : Ty level scope
  /-- Glue type — base equipped with a boundary witness (CCHM Glue). -/
  | glue {level scope : Nat}
      (baseType : Ty level scope)
      (boundaryWitness : RawTerm scope) : Ty level scope
  /-- Observational equality at the type level (set-level OEq). -/
  | oeq {level scope : Nat}
      (carrier : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope) : Ty level scope
  /-- Strict (definitional, axiom-free) identity type. -/
  | idStrict {level scope : Nat}
      (carrier : Ty level scope)
      (leftEndpoint rightEndpoint : RawTerm scope) : Ty level scope
  /-- Type equivalence at the type level — `Equiv A B`. -/
  | equiv {level scope : Nat}
      (domainType codomainType : Ty level scope) : Ty level scope
  /-- Refinement type — base type with a predicate over the inhabitant.
      The predicate is a RawTerm at `scope+1` (binds the inhabitant). -/
  | refine {level scope : Nat}
      (baseType : Ty level scope)
      (predicate : RawTerm (scope + 1)) : Ty level scope
  /-- Single-field record type placeholder.  Multi-field records compose
      via nested `record (record ...)` until the surface elaborator's
      record-schema layer ships. -/
  | record {level scope : Nat}
      (singleFieldType : Ty level scope) : Ty level scope
  /-- Codata type — `(state, output)` pair characterising the destructor
      shape of a corecursive value. -/
  | codata {level scope : Nat}
      (stateType outputType : Ty level scope) : Ty level scope
  /-- Session type — protocol step represented as a raw term carrying
      send/receive/branch structure.  The richer SessionProtocol is
      interpreted at the Sessions layer. -/
  | session {level scope : Nat}
      (protocolStep : RawTerm scope) : Ty level scope
  /-- Effectful type — `(carrier, effectTag)` where the tag enumerates the
      effect row.  Bridge to EffectRow happens at the Effects layer. -/
  | effect {level scope : Nat}
      (carrierType : Ty level scope)
      (effectTag : RawTerm scope) : Ty level scope
  /-- Modal type — `□ M . T` carrying an opaque modality tag.  The full
      Modality 1-cell with mode parameters is interpreted at the Modal
      layer; here we just track the tag for kernel-level dispatch. -/
  | modal {level scope : Nat}
      (modalityTag : Nat)
      (carrierType : Ty level scope) : Ty level scope
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
  | _, _, .universe universeLevel levelLe, _ => .universe universeLevel levelLe
  -- D1.5 new ctor renaming
  | _, _, .empty, _ => .empty
  | _, _, .interval, _ => .interval
  | _, _, .path carrier leftEndpoint rightEndpoint, rho =>
      .path (carrier.rename rho)
            (leftEndpoint.rename rho)
            (rightEndpoint.rename rho)
  | _, _, .glue baseType boundaryWitness, rho =>
      .glue (baseType.rename rho) (boundaryWitness.rename rho)
  | _, _, .oeq carrier leftEndpoint rightEndpoint, rho =>
      .oeq (carrier.rename rho)
           (leftEndpoint.rename rho)
           (rightEndpoint.rename rho)
  | _, _, .idStrict carrier leftEndpoint rightEndpoint, rho =>
      .idStrict (carrier.rename rho)
                (leftEndpoint.rename rho)
                (rightEndpoint.rename rho)
  | _, _, .equiv domainType codomainType, rho =>
      .equiv (domainType.rename rho) (codomainType.rename rho)
  | _, _, .refine baseType predicate, rho =>
      .refine (baseType.rename rho) (predicate.rename rho.lift)
  | _, _, .record singleFieldType, rho =>
      .record (singleFieldType.rename rho)
  | _, _, .codata stateType outputType, rho =>
      .codata (stateType.rename rho) (outputType.rename rho)
  | _, _, .session protocolStep, rho =>
      .session (protocolStep.rename rho)
  | _, _, .effect carrierType effectTag, rho =>
      .effect (carrierType.rename rho) (effectTag.rename rho)
  | _, _, .modal modalityTag carrierType, rho =>
      .modal modalityTag (carrierType.rename rho)

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
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq,
          RawTerm.rename_pointwise renamingEq leftEndpoint,
          RawTerm.rename_pointwise renamingEq rightEndpoint]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.rename]
      rw [baseIH renamingEq,
          RawTerm.rename_pointwise renamingEq boundaryWitness]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq,
          RawTerm.rename_pointwise renamingEq leftEndpoint,
          RawTerm.rename_pointwise renamingEq rightEndpoint]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq,
          RawTerm.rename_pointwise renamingEq leftEndpoint,
          RawTerm.rename_pointwise renamingEq rightEndpoint]
  | equiv domainType codomainType domainIH codomainIH =>
      simp only [Ty.rename]
      rw [domainIH renamingEq, codomainIH renamingEq]
  | refine baseType predicate baseIH =>
      simp only [Ty.rename]
      rw [baseIH renamingEq,
          RawTerm.rename_pointwise (RawRenaming.lift_pointwise renamingEq) predicate]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.rename]
      rw [singleFieldIH renamingEq]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.rename]
      rw [stateIH renamingEq, outputIH renamingEq]
  | session protocolStep =>
      simp only [Ty.rename]
      rw [RawTerm.rename_pointwise renamingEq protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq,
          RawTerm.rename_pointwise renamingEq effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH renamingEq]

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
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2,
          RawTerm.rename_compose rho1 rho2 leftEndpoint,
          RawTerm.rename_compose rho1 rho2 rightEndpoint]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.rename]
      rw [baseIH rho1 rho2,
          RawTerm.rename_compose rho1 rho2 boundaryWitness]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2,
          RawTerm.rename_compose rho1 rho2 leftEndpoint,
          RawTerm.rename_compose rho1 rho2 rightEndpoint]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2,
          RawTerm.rename_compose rho1 rho2 leftEndpoint,
          RawTerm.rename_compose rho1 rho2 rightEndpoint]
  | equiv domainType codomainType domainIH codomainIH =>
      simp only [Ty.rename]
      rw [domainIH rho1 rho2, codomainIH rho1 rho2]
  | refine baseType predicate baseIH =>
      simp only [Ty.rename]
      rw [baseIH rho1 rho2, RawTerm.rename_compose rho1.lift rho2.lift predicate]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | record singleFieldType singleFieldIH =>
      simp only [Ty.rename]
      rw [singleFieldIH rho1 rho2]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.rename]
      rw [stateIH rho1 rho2, outputIH rho1 rho2]
  | session protocolStep =>
      simp only [Ty.rename]
      rw [RawTerm.rename_compose rho1 rho2 protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2, RawTerm.rename_compose rho1 rho2 effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.rename]
      rw [carrierIH rho1 rho2]

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

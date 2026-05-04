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

/-! ## Ty.lift_level — Phase 12.A.B1.2 cumulativity-as-data

Promote a `Ty sourceLevel scope` to `Ty targetLevel scope` given a
witness `sourceLevel ≤ targetLevel`.  Most ctors are level-uniform
(level is just a parameter), so lift is structural recursion.  The
ONE non-trivial arm is `Ty.universe`: combine its existing
`u + 1 ≤ sourceLevel` proof with `sourceLevel ≤ targetLevel` via
`Nat.le_trans` to get `u + 1 ≤ targetLevel`.

This is the operation that makes Phase 1's intrinsic-cumul Ty.universe
usable across the kernel: any `Ty sourceLevel scope` carrier can be
lifted to a higher universe.  Cumul-Subst-mismatch is escaped because
the kernel's other ctors don't carry level-mismatched payloads — they
just thread `level` through their subterms uniformly. -/
def Ty.lift_level {sourceLevel targetLevel : Nat}
    (cumulOk : sourceLevel ≤ targetLevel) :
    ∀ {scope : Nat}, Ty sourceLevel scope → Ty targetLevel scope
  | _, .unit => .unit
  | _, .bool => .bool
  | _, .nat  => .nat
  | _, .arrow domainType codomainType =>
      .arrow (Ty.lift_level cumulOk domainType)
             (Ty.lift_level cumulOk codomainType)
  | _, .piTy domainType codomainType =>
      .piTy (Ty.lift_level cumulOk domainType)
            (Ty.lift_level cumulOk codomainType)
  | _, .sigmaTy firstType secondType =>
      .sigmaTy (Ty.lift_level cumulOk firstType)
               (Ty.lift_level cumulOk secondType)
  | _, .tyVar position => .tyVar position
  | _, .id carrier leftEndpoint rightEndpoint =>
      .id (Ty.lift_level cumulOk carrier) leftEndpoint rightEndpoint
  | _, .listType elementType =>
      .listType (Ty.lift_level cumulOk elementType)
  | _, .optionType elementType =>
      .optionType (Ty.lift_level cumulOk elementType)
  | _, .eitherType leftType rightType =>
      .eitherType (Ty.lift_level cumulOk leftType)
                  (Ty.lift_level cumulOk rightType)
  | _, .universe universeLevel levelLe =>
      .universe universeLevel (Nat.le_trans levelLe cumulOk)
  | _, .empty => .empty
  | _, .interval => .interval
  | _, .path carrier leftEndpoint rightEndpoint =>
      .path (Ty.lift_level cumulOk carrier) leftEndpoint rightEndpoint
  | _, .glue baseType boundaryWitness =>
      .glue (Ty.lift_level cumulOk baseType) boundaryWitness
  | _, .oeq carrier leftEndpoint rightEndpoint =>
      .oeq (Ty.lift_level cumulOk carrier) leftEndpoint rightEndpoint
  | _, .idStrict carrier leftEndpoint rightEndpoint =>
      .idStrict (Ty.lift_level cumulOk carrier) leftEndpoint rightEndpoint
  | _, .equiv domainType codomainType =>
      .equiv (Ty.lift_level cumulOk domainType)
             (Ty.lift_level cumulOk codomainType)
  | _, .refine baseType predicate =>
      .refine (Ty.lift_level cumulOk baseType) predicate
  | _, .record singleFieldType =>
      .record (Ty.lift_level cumulOk singleFieldType)
  | _, .codata stateType outputType =>
      .codata (Ty.lift_level cumulOk stateType)
              (Ty.lift_level cumulOk outputType)
  | _, .session protocolStep => .session protocolStep
  | _, .effect carrierType effectTag =>
      .effect (Ty.lift_level cumulOk carrierType) effectTag
  | _, .modal modalityTag carrierType =>
      .modal modalityTag (Ty.lift_level cumulOk carrierType)

/-- Reflexivity of level-lifting: `Ty.lift_level (Nat.le_refl _) ty = ty`.
Structural induction over Ty.  Every recursive arm preserves the term
because the cumul witness becomes refl, and `Nat.le_trans levelLe (Nat.le_refl _)
= levelLe` by Subsingleton on Nat.le proofs.

NOTE: Subsingleton.elim on Nat.le may emit propext on some Lean
versions; we use direct structural equality with `proof_irrel_le` if
audit fires.  The version landed here uses `Subsingleton.elim` for
brevity; will refactor to direct match if axiom audit fails. -/
theorem Ty.lift_level_refl {level : Nat}
    (cumulOkRefl : level ≤ level) :
    ∀ {scope : Nat} (someType : Ty level scope),
      Ty.lift_level cumulOkRefl someType = someType := by
  intro scope someType
  induction someType with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | piTy d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | sigmaTy fT sT fIH sIH => simp only [Ty.lift_level]; rw [fIH, sIH]
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | listType e eIH => simp only [Ty.lift_level]; rw [eIH]
  | optionType e eIH => simp only [Ty.lift_level]; rw [eIH]
  | eitherType l r lIH rIH => simp only [Ty.lift_level]; rw [lIH, rIH]
  | «universe» universeLevel levelLe =>
      show Ty.universe universeLevel (Nat.le_trans levelLe cumulOkRefl) =
           Ty.universe universeLevel levelLe
      have proofIrrel : Nat.le_trans levelLe cumulOkRefl = levelLe :=
        Subsingleton.elim _ _
      rw [proofIrrel]
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.lift_level]; rw [baseIH]
  | oeq carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | equiv d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | refine baseType predicate baseIH =>
      simp only [Ty.lift_level]; rw [baseIH]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.lift_level]; rw [singleFieldIH]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.lift_level]; rw [stateIH, outputIH]
  | session protocolStep => rfl
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]

/-- Transitivity of level-lifting: lifting through the composite
witness equals lifting twice.  Proof reduces to `Nat.le_trans`
associativity (subsingleton on Nat.le proofs). -/
theorem Ty.lift_level_trans
    {sourceLevel midLevel targetLevel : Nat}
    (cumulOkLow : sourceLevel ≤ midLevel)
    (cumulOkHigh : midLevel ≤ targetLevel) :
    ∀ {scope : Nat} (someType : Ty sourceLevel scope),
      Ty.lift_level cumulOkHigh (Ty.lift_level cumulOkLow someType) =
        Ty.lift_level (Nat.le_trans cumulOkLow cumulOkHigh) someType := by
  intro scope someType
  induction someType with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | piTy d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | sigmaTy fT sT fIH sIH => simp only [Ty.lift_level]; rw [fIH, sIH]
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | listType e eIH => simp only [Ty.lift_level]; rw [eIH]
  | optionType e eIH => simp only [Ty.lift_level]; rw [eIH]
  | eitherType l r lIH rIH => simp only [Ty.lift_level]; rw [lIH, rIH]
  | «universe» universeLevel levelLe =>
      show Ty.universe universeLevel
            (Nat.le_trans (Nat.le_trans levelLe cumulOkLow) cumulOkHigh) =
           Ty.universe universeLevel
            (Nat.le_trans levelLe (Nat.le_trans cumulOkLow cumulOkHigh))
      have proofIrrel :
          Nat.le_trans (Nat.le_trans levelLe cumulOkLow) cumulOkHigh =
            Nat.le_trans levelLe (Nat.le_trans cumulOkLow cumulOkHigh) :=
        Subsingleton.elim _ _
      rw [proofIrrel]
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.lift_level]; rw [baseIH]
  | oeq carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | equiv d c dIH cIH => simp only [Ty.lift_level]; rw [dIH, cIH]
  | refine baseType predicate baseIH =>
      simp only [Ty.lift_level]; rw [baseIH]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.lift_level]; rw [singleFieldIH]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.lift_level]; rw [stateIH, outputIH]
  | session protocolStep => rfl
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.lift_level]; rw [carrierIH]

/-! ## Tier 3 / MEGA-Z2.A — `ActsOnTy` typeclass + `Ty.act` recursion engine.

The `Action` typeclass (`Foundation/Action.lean`) describes any
`Container : Nat → Nat → Type` that can lift through binders and
compose sequentially.  However, `Action` alone does NOT determine
how a Container acts on a `Ty` — different Containers map variables
to different things:

* `RawRenaming src tgt` maps `Fin src → Fin tgt` (a renaming);
  on a `Ty.tyVar position`, the action wraps the renamed Fin back
  as `Ty.tyVar`.
* `Subst level src tgt` maps `Fin src → Ty level tgt` (a typed
  substitution); on a `Ty.tyVar position`, the action looks up the
  substituent type directly.
* `RawTermSubst src tgt` maps `Fin src → RawTerm tgt` — this
  Container does NOT naturally act on `Ty` because `Ty.tyVar
  position` cannot be replaced by a `RawTerm` (mismatched syntactic
  category).  Hence `RawTermSubst` is intentionally NOT an
  `ActsOnTy` instance.

`ActsOnTy Container level` adds two methods on top of `Action`:

* `varToTy` — lookup at a Fin position in the source scope, producing
  a `Ty level tgt`.  `Ty.tyVar` arm of `Ty.act` invokes this.
* `actOnRawTerm` — apply the Container to a `RawTerm` (used by ctors
  whose subterms include raw payloads: `Ty.id` endpoints, `Ty.path`
  endpoints, `Ty.glue` boundary witness, `Ty.refine` predicate, etc.).

The `actOnRawTerm` method abstracts dispatch between
`RawTerm.rename` and `RawTerm.subst` — RawRenaming's instance
delegates to `RawTerm.rename`, Subst's instance delegates to
`RawTerm.subst sigma.forRaw`.  The eventual `RawTerm.act` (MEGA-Z4.A)
will fold these into a single `RawTerm.act` invocation; until then,
this typeclass-level dispatch is the cleanest interim handling for
the refine-arm's RawTerm-under-binder discipline (R8/R11).

For the refine arm specifically, the predicate lives at `scope + 1`
and must be acted upon under the RawTerm-level binder lift —
`Action.liftForRaw action`.  Because ActsOnTy is parametric in the
source/target scopes, the lifted Container `Container (src+1) (tgt+1)`
inherits the ActsOnTy capability automatically.

## Hoisted level

Per `feedback_lean_match_arity_axioms.md`, `level` is hoisted to the
function header (before `:`) on `Ty.act`, matching `Ty.rename` and
`Ty.subst`.  This keeps pattern arity at 2 Nat indices (scope +
sourceScope, before adding Ty + Container) and avoids the multi-Nat-
index propext trap.

## Universe arm caveat

The `Ty.universe universeLevel levelLe` arm passes through unchanged
under any `ActsOnTy` instance whose `level` matches the carrier's
level (this `Ty.act` is homogeneous — `Container` indexes only
scope, not level).  Heterogeneous-level actions (`SubstHet`) require
a separate `ActsOnTyHet` typeclass for their universe arm, which
threads `Nat.le_trans levelLe action.cumulOk` — that is a future
phase (currently `Ty.substHet` keeps its dedicated definition; per
Z1.B's SubstHet retreat). -/

/-- A `Container` that acts on `RawTerm`.  Provides the `actOnRawTerm`
dispatch used by Ty constructors with raw payloads (Ty.id endpoints,
Ty.path endpoints, Ty.glue boundary witness, Ty.refine predicate,
Ty.session protocol step, Ty.effect effect tag, Ty.oeq endpoints,
Ty.idStrict endpoints).

`ActsOnRawTerm` is split off from `ActsOnTy` because its capability
is level-independent — `RawTerm` doesn't carry a universe level.
This split also lets `RawTermSubst` (which acts on raw terms but
NOT on Ty.tyVar) admit an `ActsOnRawTerm` instance for use by
downstream RawTerm.act (MEGA-Z4.A) without forcing it into the
`ActsOnTy` typeclass. -/
class ActsOnRawTerm (Container : Nat → Nat → Type) where
  /-- Apply the Container to a `RawTerm`. -/
  actOnRawTerm : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      RawTerm sourceScope → RawTerm targetScope

/-- A `Container` that acts on `Ty level _` types' variable
positions.  Different Containers map variables to different things:
`RawRenaming` wraps the renamed Fin as `Ty.tyVar`; `Subst level`
looks up a substituent `Ty level tgt` directly.

The `level` parameter is a regular implicit argument (not `outParam`).
Typeclass resolution uses the surrounding `Ty level _` context to
determine which instance to pick:
* For `Subst level`, the Container's type already carries `level`
  in `Container = Subst level`, so the instance pins `level`.
* For `RawRenaming` (level-polymorphic), the instance is `∀ level,
  ActsOnTyVar RawRenaming level`, providing a witness at any level.

For `RawTermSubst`, no `ActsOnTyVar` instance is provided —
`RawTermSubst` cannot replace `Ty.tyVar position` with a `RawTerm`
(mismatched syntactic category).

`ActsOnTyVar` does NOT extend `Action`; the `Ty.act` engine takes
`[Action Container]`, `[ActsOnRawTerm Container]`, and
`[ActsOnTyVar Container level]` as separate constraints, keeping the
typeclass dependency lattice flat. -/
class ActsOnTyVar (Container : Nat → Nat → Type) (level : Nat) where
  /-- Variable lookup — convert a Fin position in the source scope
  to a `Ty level` value in the target scope.  `Ty.tyVar` arm of
  `Ty.act` calls this. -/
  varToTy : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Fin sourceScope → Ty level targetScope

/-- The generic Tier 3 recursion engine over `Ty`.  Single structural
recursion replaces parallel `Ty.rename` and `Ty.subst` engines.

For each of the 25 Ty constructors:
* Non-binder, non-raw arms simply recurse with `someAction`.
* Raw-payload arms (Ty.id, path, glue, oeq, idStrict, session,
  effect endpoints) invoke `ActsOnTy.actOnRawTerm someAction` on
  the raw subterm.
* Binder-bearing arms with Ty under binder (piTy, sigmaTy) recurse
  with `Action.liftForTy someAction`.
* The refine arm's predicate (RawTerm under binder) invokes
  `ActsOnTy.actOnRawTerm (Action.liftForRaw someAction)` on the
  predicate at `scope + 1`.
* `tyVar` invokes `ActsOnTy.varToTy someAction`.
* `«universe» universeLevel levelLe` passes through (level-uniform).

Per `feedback_lean_match_arity_axioms.md`: `level` is hoisted to the
function header to match `Ty.rename` and `Ty.subst`.

Marked `@[reducible]` so the unifier can chain through definitional
equalities (e.g. `Ty.act t Action.identity` should reduce to `t`
for representative ctors). -/
@[reducible] def Ty.act
    {Container : Nat → Nat → Type} [Action Container]
    [ActsOnRawTerm Container]
    {level : Nat} [ActsOnTyVar Container level] :
    ∀ {sourceScope targetScope : Nat},
      Ty level sourceScope →
      Container sourceScope targetScope →
      Ty level targetScope
  | _, _, .unit, _ => .unit
  | _, _, .bool, _ => .bool
  | _, _, .nat, _ => .nat
  | _, _, .arrow domainType codomainType, someAction =>
      .arrow (domainType.act someAction) (codomainType.act someAction)
  | _, _, .piTy domainType codomainType, someAction =>
      .piTy (domainType.act someAction)
            (codomainType.act (Action.liftForTy someAction))
  | _, _, .sigmaTy firstType secondType, someAction =>
      .sigmaTy (firstType.act someAction)
               (secondType.act (Action.liftForTy someAction))
  | _, _, .tyVar position, someAction =>
      ActsOnTyVar.varToTy someAction position
  | _, _, .id carrier leftEndpoint rightEndpoint, someAction =>
      .id (carrier.act someAction)
          (ActsOnRawTerm.actOnRawTerm someAction leftEndpoint)
          (ActsOnRawTerm.actOnRawTerm someAction rightEndpoint)
  | _, _, .listType elementType, someAction =>
      .listType (elementType.act someAction)
  | _, _, .optionType elementType, someAction =>
      .optionType (elementType.act someAction)
  | _, _, .eitherType leftType rightType, someAction =>
      .eitherType (leftType.act someAction) (rightType.act someAction)
  | _, _, .universe universeLevel levelLe, _ =>
      .universe universeLevel levelLe
  | _, _, .empty, _ => .empty
  | _, _, .interval, _ => .interval
  | _, _, .path carrier leftEndpoint rightEndpoint, someAction =>
      .path (carrier.act someAction)
            (ActsOnRawTerm.actOnRawTerm someAction leftEndpoint)
            (ActsOnRawTerm.actOnRawTerm someAction rightEndpoint)
  | _, _, .glue baseType boundaryWitness, someAction =>
      .glue (baseType.act someAction)
            (ActsOnRawTerm.actOnRawTerm someAction boundaryWitness)
  | _, _, .oeq carrier leftEndpoint rightEndpoint, someAction =>
      .oeq (carrier.act someAction)
           (ActsOnRawTerm.actOnRawTerm someAction leftEndpoint)
           (ActsOnRawTerm.actOnRawTerm someAction rightEndpoint)
  | _, _, .idStrict carrier leftEndpoint rightEndpoint, someAction =>
      .idStrict (carrier.act someAction)
                (ActsOnRawTerm.actOnRawTerm someAction leftEndpoint)
                (ActsOnRawTerm.actOnRawTerm someAction rightEndpoint)
  | _, _, .equiv domainType codomainType, someAction =>
      .equiv (domainType.act someAction) (codomainType.act someAction)
  | _, _, .refine baseType predicate, someAction =>
      .refine (baseType.act someAction)
              (ActsOnRawTerm.actOnRawTerm
                  (Action.liftForRaw someAction) predicate)
  | _, _, .record singleFieldType, someAction =>
      .record (singleFieldType.act someAction)
  | _, _, .codata stateType outputType, someAction =>
      .codata (stateType.act someAction) (outputType.act someAction)
  | _, _, .session protocolStep, someAction =>
      .session (ActsOnRawTerm.actOnRawTerm someAction protocolStep)
  | _, _, .effect carrierType effectTag, someAction =>
      .effect (carrierType.act someAction)
              (ActsOnRawTerm.actOnRawTerm someAction effectTag)
  | _, _, .modal modalityTag carrierType, someAction =>
      .modal modalityTag (carrierType.act someAction)

/-! ## ActsOnRawTerm + ActsOnTyVar instances for `RawRenaming`.

Renaming acts on `Ty.tyVar position` by wrapping the renamed Fin back
as `Ty.tyVar` (level-polymorphic).  `actOnRawTerm` delegates to the
unified `RawTerm.act` engine (Z4.A) — the alignment fix shipped by
Z2.A.1 means `actOnRawTerm someRenaming rawTerm` is `rfl`-equal to
`RawTerm.act rawTerm someRenaming`, allowing `Ty.act`-driven recursion
to dispatch through the same engine that drives `RawTerm.act`.  This
is the prerequisite for `Term.act` (Z5.A): once both `Ty.act` and
`RawTerm.act` agree on raw payloads, `Term.act` can be defined by a
single recursion that delegates to both. -/

instance : ActsOnRawTerm RawRenaming where
  actOnRawTerm := fun someRenaming rawTerm => RawTerm.act rawTerm someRenaming

instance ActsOnTyVarOfRawRenaming (level : Nat) :
    ActsOnTyVar RawRenaming level where
  varToTy := fun someRenaming position => Ty.tyVar (someRenaming position)

/-! ## Smoke equivalences with existing `Ty.rename`.

The `Ty.act` engine over `RawRenaming` should produce the same result
as the existing `Ty.rename`.  The proof would be a 25-case structural
induction; for Z2.A we ship the per-ctor `rfl` smokes that demonstrate
the engine reduces correctly at leaf and binder positions.  The full
equivalence theorem `Ty.act_rawRenaming_eq_rename` lands in Z2.B
(when `Ty.rename` is REDIRECTED to `Ty.act`). -/

theorem Ty.act_rawRenaming_unit_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope) :
    (Ty.unit (level := level) (scope := scope)).act someRenaming = .unit := rfl

theorem Ty.act_rawRenaming_tyVar_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (position : Fin scope) :
    (Ty.tyVar (level := level) position).act someRenaming =
      Ty.tyVar (someRenaming position) := rfl

theorem Ty.act_rawRenaming_arrow_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (domainType codomainType : Ty level scope) :
    (Ty.arrow domainType codomainType).act someRenaming =
      Ty.arrow (domainType.act someRenaming)
               (codomainType.act someRenaming) := rfl

theorem Ty.act_rawRenaming_piTy_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (domainType : Ty level scope)
    (codomainType : Ty level (scope + 1)) :
    (Ty.piTy domainType codomainType).act someRenaming =
      Ty.piTy (domainType.act someRenaming)
              (codomainType.act (Action.liftForTy someRenaming)) := rfl

theorem Ty.act_rawRenaming_refine_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (baseType : Ty level scope)
    (predicate : RawTerm (scope + 1)) :
    (Ty.refine baseType predicate).act someRenaming =
      Ty.refine (baseType.act someRenaming)
                (ActsOnRawTerm.actOnRawTerm
                    (Action.liftForRaw someRenaming) predicate) := rfl

theorem Ty.act_rawRenaming_id_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    (Ty.id carrier leftEndpoint rightEndpoint).act someRenaming =
      Ty.id (carrier.act someRenaming)
            (ActsOnRawTerm.actOnRawTerm someRenaming leftEndpoint)
            (ActsOnRawTerm.actOnRawTerm someRenaming rightEndpoint) := rfl

theorem Ty.act_rawRenaming_universe_smoke
    {level scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level) :
    (Ty.universe (scope := scope) universeLevel levelLe).act someRenaming =
      Ty.universe universeLevel levelLe := rfl

end LeanFX2

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

/-! ## Pointwise + commute lemmas for Ty.subst.

Mirror of the Ty rename-side foundation lemmas + the RawTerm
subst-side lemmas.  `Subst` is a record carrying TWO independent
pointwise components (forTy + forRaw); each lemma's hypothesis
decomposes into the two corresponding pointwise facts.  The
forRaw-side proofs defer to the RawTerm lemmas already proved
in `RawSubst.lean`. -/

/-- Lift respects pointwise equality on the forTy component. -/
theorem Subst.lift_forTy_pointwise {level sourceScope targetScope : Nat}
    {sigma1 sigma2 : Subst level sourceScope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position) :
    ∀ position, sigma1.lift.forTy position = sigma2.lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show (sigma1.forTy ⟨k, _⟩).weaken = (sigma2.forTy ⟨k, _⟩).weaken
      rw [forTyEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- Lift respects pointwise equality on the forRaw component. -/
theorem Subst.lift_forRaw_pointwise {level sourceScope targetScope : Nat}
    {sigma1 sigma2 : Subst level sourceScope targetScope}
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position) :
    ∀ position, sigma1.lift.forRaw position = sigma2.lift.forRaw position :=
  fun position => RawTermSubst.lift_pointwise forRawEq position

/-- Ty.subst respects pointwise Subst equality (both fields). -/
theorem Ty.subst_pointwise {level : Nat}
    {scope targetScope : Nat}
    {sigma1 sigma2 : Subst level scope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position)
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position) :
    ∀ (someType : Ty level scope), someType.subst sigma1 = someType.subst sigma2 := by
  intro someType
  induction someType generalizing targetScope with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.subst]; rw [dIH forTyEq forRawEq, cIH forTyEq forRawEq]
  | piTy d c dIH cIH =>
      simp only [Ty.subst]
      rw [dIH forTyEq forRawEq,
          cIH (Subst.lift_forTy_pointwise forTyEq)
              (Subst.lift_forRaw_pointwise forRawEq)]
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.subst]
      rw [fIH forTyEq forRawEq,
          sIH (Subst.lift_forTy_pointwise forTyEq)
              (Subst.lift_forRaw_pointwise forRawEq)]
  | tyVar position =>
      simp only [Ty.subst]; rw [forTyEq position]
  | id carrier left right carrierIH =>
      simp only [Ty.subst]
      rw [carrierIH forTyEq forRawEq,
          RawTerm.subst_pointwise forRawEq left,
          RawTerm.subst_pointwise forRawEq right]
  | listType e eIH =>
      simp only [Ty.subst]; rw [eIH forTyEq forRawEq]
  | optionType e eIH =>
      simp only [Ty.subst]; rw [eIH forTyEq forRawEq]
  | eitherType l r lIH rIH =>
      simp only [Ty.subst]; rw [lIH forTyEq forRawEq, rIH forTyEq forRawEq]

/-! ### Renaming after substitution: Ty.subst then rename. -/

/-- Post-compose a Subst with a renaming on the output side. -/
@[reducible] def Subst.renameOutput {level sourceScope middleScope targetScope : Nat}
    (sigma : Subst level sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    Subst level sourceScope targetScope where
  forTy  := fun position => (sigma.forTy position).rename rho
  forRaw := fun position => (sigma.forRaw position).rename rho

/-- Lift commutes with renameOutput on forTy. -/
theorem Subst.renameOutput_lift_forTy_pointwise {level sourceScope middleScope targetScope : Nat}
    (sigma : Subst level sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift.forTy position).rename rho.lift =
        (Subst.renameOutput sigma rho).lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show ((sigma.forTy ⟨k, _⟩).rename RawRenaming.weaken).rename rho.lift =
           ((sigma.forTy ⟨k, _⟩).rename rho).rename RawRenaming.weaken
      rw [Ty.rename_compose RawRenaming.weaken rho.lift
            (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          Ty.rename_compose rho RawRenaming.weaken
            (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply Ty.rename_pointwise
      intro p
      exact RawRenaming.weaken_lift_commute rho p

/-- Lift commutes with renameOutput on forRaw. -/
theorem Subst.renameOutput_lift_forRaw_pointwise {level sourceScope middleScope targetScope : Nat}
    (sigma : Subst level sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift.forRaw position).rename rho.lift =
        (Subst.renameOutput sigma rho).lift.forRaw position :=
  fun position => RawTermSubst.lift_then_rename_lift sigma.forRaw rho position

/-- subst-then-rename factors through Subst.renameOutput. -/
theorem Ty.subst_rename_commute {level : Nat}
    {scope middleScope targetScope : Nat}
    (sigma : Subst level scope middleScope)
    (rho : RawRenaming middleScope targetScope)
    (someType : Ty level scope) :
    (someType.subst sigma).rename rho =
      someType.subst (Subst.renameOutput sigma rho) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.subst, Ty.rename]; rw [dIH sigma rho, cIH sigma rho]
  | piTy d c dIH cIH =>
      simp only [Ty.subst, Ty.rename]
      rw [dIH sigma rho, cIH sigma.lift rho.lift]
      congr 1
      apply Ty.subst_pointwise
      · exact Subst.renameOutput_lift_forTy_pointwise sigma rho
      · exact Subst.renameOutput_lift_forRaw_pointwise sigma rho
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.subst, Ty.rename]
      rw [fIH sigma rho, sIH sigma.lift rho.lift]
      congr 1
      apply Ty.subst_pointwise
      · exact Subst.renameOutput_lift_forTy_pointwise sigma rho
      · exact Subst.renameOutput_lift_forRaw_pointwise sigma rho
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.subst, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho left,
          RawTerm.subst_rename_commute sigma.forRaw rho right]
  | listType e eIH => simp only [Ty.subst, Ty.rename]; rw [eIH sigma rho]
  | optionType e eIH => simp only [Ty.subst, Ty.rename]; rw [eIH sigma rho]
  | eitherType l r lIH rIH =>
      simp only [Ty.subst, Ty.rename]; rw [lIH sigma rho, rIH sigma rho]

/-! ### Substitution after renaming: Ty.rename then subst. -/

/-- Pre-compose a renaming with a Subst on the input side. -/
@[reducible] def Subst.precomposeRenaming {level sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : Subst level middleScope targetScope) :
    Subst level sourceScope targetScope where
  forTy  := fun position => sigma.forTy (rho position)
  forRaw := fun position => sigma.forRaw (rho position)

/-- Lift commutes with precomposeRenaming on forTy. -/
theorem Subst.precomposeRenaming_lift_forTy_pointwise
    {level sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : Subst level middleScope targetScope) :
    ∀ position,
      sigma.lift.forTy (rho.lift position) =
        (Subst.precomposeRenaming rho sigma).lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Lift commutes with precomposeRenaming on forRaw. -/
theorem Subst.precomposeRenaming_lift_forRaw_pointwise
    {level sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : Subst level middleScope targetScope) :
    ∀ position,
      sigma.lift.forRaw (rho.lift position) =
        (Subst.precomposeRenaming rho sigma).lift.forRaw position :=
  fun position => RawTermSubst.lift_renaming_pull rho sigma.forRaw position

/-- rename-then-subst factors through Subst.precomposeRenaming. -/
theorem Ty.rename_subst_commute {level : Nat}
    {scope middleScope targetScope : Nat}
    (rho : RawRenaming scope middleScope)
    (sigma : Subst level middleScope targetScope)
    (someType : Ty level scope) :
    (someType.rename rho).subst sigma =
      someType.subst (Subst.precomposeRenaming rho sigma) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.rename, Ty.subst]; rw [dIH rho sigma, cIH rho sigma]
  | piTy d c dIH cIH =>
      simp only [Ty.rename, Ty.subst]
      rw [dIH rho sigma, cIH rho.lift sigma.lift]
      congr 1
      apply Ty.subst_pointwise
      · exact Subst.precomposeRenaming_lift_forTy_pointwise rho sigma
      · exact Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.rename, Ty.subst]
      rw [fIH rho sigma, sIH rho.lift sigma.lift]
      congr 1
      apply Ty.subst_pointwise
      · exact Subst.precomposeRenaming_lift_forTy_pointwise rho sigma
      · exact Subst.precomposeRenaming_lift_forRaw_pointwise rho sigma
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.rename, Ty.subst]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw left,
          RawTerm.rename_subst_commute rho sigma.forRaw right]
  | listType e eIH => simp only [Ty.rename, Ty.subst]; rw [eIH rho sigma]
  | optionType e eIH => simp only [Ty.rename, Ty.subst]; rw [eIH rho sigma]
  | eitherType l r lIH rIH =>
      simp only [Ty.rename, Ty.subst]; rw [lIH rho sigma, rIH rho sigma]

/-! ### Singleton-rename pointwise + Ty.subst0_rename_commute. -/

/-- Pointwise: forTy of singleton-renamed = renamed forTy of singleton. -/
theorem Subst.singleton_rename_commute_forTy_pointwise {level sourceScope targetScope : Nat}
    (substituent : Ty level sourceScope) (rawArg : RawTerm sourceScope)
    (rho : RawRenaming sourceScope targetScope) :
    ∀ position,
      ((Subst.singleton substituent rawArg).forTy position).rename rho =
        (Subst.singleton (substituent.rename rho) (rawArg.rename rho)).forTy
          (rho.lift position)
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Pointwise: forRaw of singleton-renamed = renamed forRaw of singleton. -/
theorem Subst.singleton_rename_commute_forRaw_pointwise {level sourceScope targetScope : Nat}
    (substituent : Ty level sourceScope) (rawArg : RawTerm sourceScope)
    (rho : RawRenaming sourceScope targetScope) :
    ∀ position,
      ((Subst.singleton substituent rawArg).forRaw position).rename rho =
        (Subst.singleton (substituent.rename rho) (rawArg.rename rho)).forRaw
          (rho.lift position) :=
  fun position => RawTermSubst.singleton_rename_commute_pointwise rho rawArg position

/-- Renaming a single-variable substitution result equals single-variable
substitution after renaming under the lift.  Load-bearing for typed
`Term.rename` on β-redex result types: `(cod.subst0 dom argRaw).rename rho`
matches `(cod.rename rho.lift).subst0 (dom.rename rho) (argRaw.rename rho)`. -/
theorem Ty.subst0_rename_commute {level : Nat} {scope targetScope : Nat}
    (codomainType : Ty level (scope + 1))
    (argType : Ty level scope)
    (argRaw : RawTerm scope)
    (rho : RawRenaming scope targetScope) :
    (codomainType.subst0 argType argRaw).rename rho =
      (codomainType.rename rho.lift).subst0
        (argType.rename rho) (argRaw.rename rho) := by
  show (codomainType.subst (Subst.singleton argType argRaw)).rename rho =
       (codomainType.rename rho.lift).subst
         (Subst.singleton (argType.rename rho) (argRaw.rename rho))
  rw [Ty.subst_rename_commute (Subst.singleton argType argRaw) rho codomainType,
      Ty.rename_subst_commute rho.lift
        (Subst.singleton (argType.rename rho) (argRaw.rename rho)) codomainType]
  apply Ty.subst_pointwise
  · exact Subst.singleton_rename_commute_forTy_pointwise argType argRaw rho
  · exact Subst.singleton_rename_commute_forRaw_pointwise argType argRaw rho

end LeanFX2

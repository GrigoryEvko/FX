import LeanFX.Syntax.RawSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Substitution — the same trick scaled up.

`Subst level source target` is a function-typed family mapping `Fin source`
to `Ty level target`.  Just as with `Renaming`, the substitution data carries
both endpoints as free parameters; lifting under a binder advances both
to `source + 1` and `target + 1`, definitionally matching the
recursive call's indices.

For v1.0+ `Ty` (no `Ty.tyVar` constructor), `Subst` is never *queried*
by `Ty.subst` — it threads through the recursion as a token.  When
v1.5+ adds `Ty.tyVar`, the `var` case will look up the substituent
via `σ`. -/

/-- Joint substitution environment for all syntax indexed by the same scope.

`forTy` substitutes type variables.  `forRaw` substitutes raw-term
variables appearing in identity endpoints.  A `CoeFun` instance below
keeps existing Ty-facing code readable: `sigma i` means
`sigma.forTy i`. -/
structure Subst (level source target : Nat) where
  forTy : Fin source → Ty level target
  forRaw : RawTermSubst source target

instance {level source target : Nat} :
    CoeFun (Subst level source target) (fun _ => Fin source → Ty level target) where
  coe substitution := substitution.forTy

/-- Lift a substitution under a binder.  Var 0 in the lifted scope is
the freshly-bound variable, represented as `Ty.tyVar 0`.  Var `k + 1`
is the original substituent for `k` weakened to the extended target
scope. -/
@[reducible]
def Subst.lift {level source target : Nat} (σ : Subst level source target) :
    Subst level (source + 1) (target + 1) where
  forTy
    | ⟨0, _⟩      => .tyVar ⟨0, Nat.zero_lt_succ _⟩
    | ⟨k + 1, h⟩  => (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken
  forRaw := σ.forRaw.lift

/-- Single-variable substitution at the outermost binder: substitute
`substituent` for var 0, leave var `k + 1` as `tyVar k` — the
"identity" mapping that decrements the de Bruijn index by one
(reflecting that the outer scope has one fewer binder than the
input scope). -/
@[reducible]
def Subst.singleton {level scope : Nat} (substituent : Ty level scope) :
    Subst level (scope + 1) scope where
  forTy
    | ⟨0, _⟩      => substituent
    | ⟨k + 1, h⟩  => .tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩
  forRaw := RawTermSubst.dropNewest

/-- Single-variable substitution that carries a raw term substituent
for the eliminated binder.  Unlike `Subst.singleton`, whose `forRaw`
is `dropNewest` (treating the binder as a type-only binder), this
variant uses `RawTermSubst.singleton rawArg` so that raw terms in
identity types reference the actual term being substituted in.
This is the right joint substitution for term-level β-reduction:
`(λ x. body) arg` reduces to `body[arg/0]`, and identity-type
witnesses inside `body` should see `toRaw arg` at position 0,
not the placeholder unit. -/
@[reducible]
def Subst.termSingleton {level scope : Nat} (substituent : Ty level scope)
    (rawArg : RawTerm scope) : Subst level (scope + 1) scope where
  forTy
    | ⟨0, _⟩      => substituent
    | ⟨k + 1, h⟩  => .tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩
  forRaw := RawTermSubst.singleton rawArg

/-- Apply a parallel substitution to a type, structurally.  The
`piTy` case lifts the substitution under the new binder; just like
`Ty.rename`, the recursive call's indices are supplied definitionally
by `σ.lift`, no Nat arithmetic identities required.  Axiom-free. -/
def Ty.subst {level source target : Nat} :
    Ty level source → Subst level source target → Ty level target
  | .unit, _          => .unit
  | .arrow A B, σ     => .arrow (Ty.subst A σ) (Ty.subst B σ)
  | .piTy A B, σ      => .piTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .tyVar i, σ       => σ i
  | .sigmaTy A B, σ   => .sigmaTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .bool, _          => .bool
  | .universe u h, _  => .universe u h
  | .nat, _           => .nat
  | .list elemType, σ => .list (Ty.subst elemType σ)
  | .vec elemType length, σ => .vec (Ty.subst elemType σ) length
  | .option elemType, σ => .option (Ty.subst elemType σ)
  | .either leftType rightType, σ =>
      .either (Ty.subst leftType σ) (Ty.subst rightType σ)
  | .id carrier lhs rhs, σ =>
      .id (Ty.subst carrier σ) (lhs.subst σ.forRaw) (rhs.subst σ.forRaw)

/-- Substitute the outermost variable of a type with a `Ty` value.
Used by `Term.appPi` to compute the result type of dependent
application. -/
def Ty.subst0 {level scope : Nat} (codomain : Ty level (scope + 1))
    (substituent : Ty level scope) : Ty level scope :=
  Ty.subst codomain (Subst.singleton substituent)

/-! ## Substitution-lemma hierarchy.

How `Ty.subst` interacts with `Ty.rename`, with itself, and with
lifting.  All lemmas use pointwise substitution equivalence
(`Subst.equiv`) rather than Lean function-equality — funext would
pull in `propext`. -/

/-- Pointwise equivalence of substitutions.  Two substitutions
`σ₁ σ₂ : Subst level s t` are equivalent if they agree at every variable.
Used in lieu of Lean-level function equality (which would require
`funext` and thus `propext`). -/
def Subst.equiv {level s t : Nat} (σ₁ σ₂ : Subst level s t) : Prop :=
  (∀ position, σ₁.forTy position = σ₂.forTy position) ∧
    RawTermSubst.equiv σ₁.forRaw σ₂.forRaw

/-- Build a joint-substitution equivalence from its type and raw components. -/
theorem Subst.equiv_intro {level source target : Nat}
    {firstSubstitution secondSubstitution : Subst level source target}
    (typesAreEquivalent :
      ∀ position, firstSubstitution.forTy position = secondSubstitution.forTy position)
    (rawTermsAreEquivalent :
      RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw) :
    Subst.equiv firstSubstitution secondSubstitution :=
  And.intro typesAreEquivalent rawTermsAreEquivalent

/-- Project the type component of a joint-substitution equivalence. -/
theorem Subst.equiv_forTy {level source target : Nat}
    {firstSubstitution secondSubstitution : Subst level source target}
    (areEquivalent : Subst.equiv firstSubstitution secondSubstitution) :
    ∀ position, firstSubstitution.forTy position = secondSubstitution.forTy position :=
  areEquivalent.left

/-- Project the raw-term component of a joint-substitution equivalence. -/
theorem Subst.equiv_forRaw {level source target : Nat}
    {firstSubstitution secondSubstitution : Subst level source target}
    (areEquivalent : Subst.equiv firstSubstitution secondSubstitution) :
    RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw :=
  areEquivalent.right

/-- Reflexivity for joint-substitution equivalence. -/
theorem Subst.equiv_refl {level source target : Nat}
    (substitution : Subst level source target) : Subst.equiv substitution substitution :=
  Subst.equiv_intro (fun _ => rfl) (RawTermSubst.equiv_refl substitution.forRaw)

/-- Lifting preserves substitution equivalence: if `σ₁ ≡ σ₂` pointwise
then `σ₁.lift ≡ σ₂.lift` pointwise. -/
theorem Subst.lift_equiv {level s t : Nat} {σ₁ σ₂ : Subst level s t}
    (h : Subst.equiv σ₁ σ₂) : Subst.equiv σ₁.lift σ₂.lift :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨k + 1, hk⟩ =>
          congrArg Ty.weaken
            (Subst.equiv_forTy h ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    (RawTermSubst.lift_equiv (Subst.equiv_forRaw h))

/-- `Ty.subst` respects substitution equivalence: pointwise-equivalent
substitutions produce equal results.  Proven by structural induction
on `T`, using `Subst.lift_equiv` for the binder cases. -/
theorem Ty.subst_congr {level s t : Nat} {σ₁ σ₂ : Subst level s t}
    (h : Subst.equiv σ₁ σ₂) : ∀ T : Ty level s, T.subst σ₁ = T.subst σ₂
  | .unit         => rfl
  | .arrow X Y    => by
      show Ty.arrow (X.subst σ₁) (Y.subst σ₁) = Ty.arrow (X.subst σ₂) (Y.subst σ₂)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr h Y
      exact hX ▸ hY ▸ rfl
  | .piTy X Y     => by
      show Ty.piTy (X.subst σ₁) (Y.subst σ₁.lift)
         = Ty.piTy (X.subst σ₂) (Y.subst σ₂.lift)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr (Subst.lift_equiv h) Y
      exact hX ▸ hY ▸ rfl
  | .tyVar i      => Subst.equiv_forTy h i
  | .sigmaTy X Y  => by
      show Ty.sigmaTy (X.subst σ₁) (Y.subst σ₁.lift)
         = Ty.sigmaTy (X.subst σ₂) (Y.subst σ₂.lift)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr (Subst.lift_equiv h) Y
      exact hX ▸ hY ▸ rfl
  | .bool         => rfl
  | .universe _ _ => rfl
  | .nat          => rfl
  | .list elemType => by
      show Ty.list (elemType.subst σ₁) = Ty.list (elemType.subst σ₂)
      have hElem := Ty.subst_congr h elemType
      exact hElem ▸ rfl
  | .vec elemType length => by
      show Ty.vec (elemType.subst σ₁) length = Ty.vec (elemType.subst σ₂) length
      have hElem := Ty.subst_congr h elemType
      exact hElem ▸ rfl
  | .option elemType => by
      show Ty.option (elemType.subst σ₁) = Ty.option (elemType.subst σ₂)
      have hElem := Ty.subst_congr h elemType
      exact hElem ▸ rfl
  | .either leftType rightType => by
      show Ty.either (leftType.subst σ₁) (rightType.subst σ₁)
         = Ty.either (leftType.subst σ₂) (rightType.subst σ₂)
      have hLeft  := Ty.subst_congr h leftType
      have hRight := Ty.subst_congr h rightType
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs => by
      show Ty.id (carrier.subst σ₁) (lhs.subst σ₁.forRaw) (rhs.subst σ₁.forRaw)
         = Ty.id (carrier.subst σ₂) (lhs.subst σ₂.forRaw) (rhs.subst σ₂.forRaw)
      have hCarrier := Ty.subst_congr h carrier
      have hLeft := RawTerm.subst_congr (Subst.equiv_forRaw h) lhs
      have hRight := RawTerm.subst_congr (Subst.equiv_forRaw h) rhs
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-- Substitution composed with rawRenaming: applies the substitution
first, then renames each substituent.  The "after" naming follows
the order of operations: `renameAfter σ ρ i = (σ i).rename ρ`. -/
def Subst.renameAfter {level s m t : Nat} (σ : Subst level s m) (ρ : Renaming m t) :
    Subst level s t where
  forTy := fun i => (σ i).rename ρ
  forRaw := RawTermSubst.beforeRenaming σ.forRaw ρ

/-- Type component of `renameAfter`. -/
theorem Subst.renameAfter_forTy {level source middle target : Nat}
    (substitution : Subst level source middle)
    (rawRenaming : Renaming middle target)
    (position : Fin source) :
    (Subst.renameAfter substitution rawRenaming).forTy position =
      (substitution.forTy position).rename rawRenaming :=
  rfl

/-- Raw component of `renameAfter`. -/
theorem Subst.renameAfter_forRaw {level source middle target : Nat}
    (substitution : Subst level source middle)
    (rawRenaming : Renaming middle target) :
    (Subst.renameAfter substitution rawRenaming).forRaw =
      RawTermSubst.beforeRenaming substitution.forRaw rawRenaming :=
  rfl

/-- Lifting commutes with the renameAfter composition (pointwise).
The non-trivial case `i = ⟨k+1, h⟩` reduces to `Ty.rename_weaken_commute`
applied to the substituent `σ ⟨k, _⟩`. -/
theorem Subst.lift_renameAfter_commute {level s m t : Nat}
    (σ : Subst level s m) (ρ : Renaming m t) :
    Subst.equiv (Subst.renameAfter σ.lift ρ.lift)
                ((Subst.renameAfter σ ρ).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨k + 1, hk⟩ =>
          Ty.rename_weaken_commute (σ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) ρ)
    fun position =>
      (RawTermSubst.lift_beforeRenaming_equiv σ.forRaw ρ position).symm

/-- **The substitution-rename commute lemma** — the mathematical
heart of the v1.7 layer.  Substituting then rawRenaming a type equals
substituting with renamed substituents (pointwise via `renameAfter`).

This is the load-bearing lemma for `Term.rename`'s `appPi`/`pair`/
`snd` cases (whose result types involve `Ty.subst0`) and ultimately
for β-reduction.  Proven by structural induction on `T`, with the
`piTy`/`sigmaTy` cases using `Subst.lift_renameAfter_commute` +
`Ty.subst_congr`. -/
theorem Ty.subst_rename_commute {level s m t : Nat} :
    ∀ (T : Ty level s) (σ : Subst level s m) (ρ : Renaming m t),
    (T.subst σ).rename ρ = T.subst (Subst.renameAfter σ ρ)
  | .unit, _, _ => rfl
  | .arrow X Y, σ, ρ => by
      show Ty.arrow ((X.subst σ).rename ρ) ((Y.subst σ).rename ρ)
         = Ty.arrow (X.subst (Subst.renameAfter σ ρ))
                    (Y.subst (Subst.renameAfter σ ρ))
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ ρ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, σ, ρ => by
      show Ty.piTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.piTy (X.subst (Subst.renameAfter σ ρ))
                   (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, σ, ρ => by
      show Ty.sigmaTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.sigmaTy (X.subst (Subst.renameAfter σ ρ))
                      (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, σ, ρ => by
      show Ty.list ((elemType.subst σ).rename ρ)
         = Ty.list (elemType.subst (Subst.renameAfter σ ρ))
      have hElem := Ty.subst_rename_commute elemType σ ρ
      exact hElem ▸ rfl
  | .vec elemType length, σ, ρ => by
      show Ty.vec ((elemType.subst σ).rename ρ) length
         = Ty.vec (elemType.subst (Subst.renameAfter σ ρ)) length
      have hElem := Ty.subst_rename_commute elemType σ ρ
      exact hElem ▸ rfl
  | .option elemType, σ, ρ => by
      show Ty.option ((elemType.subst σ).rename ρ)
         = Ty.option (elemType.subst (Subst.renameAfter σ ρ))
      have hElem := Ty.subst_rename_commute elemType σ ρ
      exact hElem ▸ rfl
  | .either leftType rightType, σ, ρ => by
      show Ty.either ((leftType.subst σ).rename ρ)
                     ((rightType.subst σ).rename ρ)
         = Ty.either (leftType.subst (Subst.renameAfter σ ρ))
                     (rightType.subst (Subst.renameAfter σ ρ))
      have hLeft  := Ty.subst_rename_commute leftType σ ρ
      have hRight := Ty.subst_rename_commute rightType σ ρ
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs, σ, ρ => by
      show Ty.id ((carrier.subst σ).rename ρ)
                 ((lhs.subst σ.forRaw).rename ρ)
                 ((rhs.subst σ.forRaw).rename ρ)
         = Ty.id (carrier.subst (Subst.renameAfter σ ρ))
                 (lhs.subst (Subst.renameAfter σ ρ).forRaw)
                 (rhs.subst (Subst.renameAfter σ ρ).forRaw)
      have hCarrier := Ty.subst_rename_commute carrier σ ρ
      have hLeft := RawTerm.rename_subst_commute lhs σ.forRaw ρ
      have hRight := RawTerm.rename_subst_commute rhs σ.forRaw ρ
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-- Renaming followed by substitution: precompose the rawRenaming, then
substitute.  `Subst.precompose ρ σ i = σ (ρ i)`. -/
def Subst.precompose {level s m t : Nat} (ρ : Renaming s m) (σ : Subst level m t) :
    Subst level s t where
  forTy := fun i => σ (ρ i)
  forRaw := RawTermSubst.afterRenaming ρ σ.forRaw

/-- Type component of `precompose`. -/
theorem Subst.precompose_forTy {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (substitution : Subst level middle target)
    (position : Fin source) :
    (Subst.precompose rawRenaming substitution).forTy position =
      substitution.forTy (rawRenaming position) :=
  rfl

/-- Raw component of `precompose`. -/
theorem Subst.precompose_forRaw {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (substitution : Subst level middle target) :
    (Subst.precompose rawRenaming substitution).forRaw =
      RawTermSubst.afterRenaming rawRenaming substitution.forRaw :=
  rfl

/-- Lifting commutes with precompose (pointwise).  Both `k = 0` and
`k+1` cases reduce to `rfl` thanks to Fin proof irrelevance. -/
theorem Subst.lift_precompose_commute {level s m t : Nat}
    (ρ : Renaming s m) (σ : Subst level m t) :
    Subst.equiv (Subst.precompose ρ.lift σ.lift)
                ((Subst.precompose ρ σ).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩       => rfl
      | ⟨_ + 1, _⟩   => rfl)
    fun position =>
      (RawTermSubst.lift_afterRenaming_equiv ρ σ.forRaw position).symm

/-- Precomposing a lifted substitution with weakening agrees with
rawRenaming each substituent by weakening. -/
theorem Subst.precompose_weaken_lift_equiv_renameAfter_weaken {level source target : Nat}
    (substitution : Subst level source target) :
    Subst.equiv
      (Subst.precompose Renaming.weaken substitution.lift)
      (Subst.renameAfter substitution Renaming.weaken) :=
  Subst.equiv_intro (fun _ => rfl) (RawTermSubst.equiv_refl _)

/-- **The rename-subst commute lemma** — the symmetric counterpart to
`Ty.subst_rename_commute`.  Renaming then substituting equals substituting
with a precomposed substitution.  This is the OTHER direction of the
substitution-rename interaction; together with `subst_rename_commute`
they let us derive `subst0_rename_commute` and the full β-reduction
soundness chain. -/
theorem Ty.rename_subst_commute {level s m t : Nat} :
    ∀ (T : Ty level s) (ρ : Renaming s m) (σ : Subst level m t),
    (T.rename ρ).subst σ = T.subst (Subst.precompose ρ σ)
  | .unit, _, _ => rfl
  | .arrow X Y, ρ, σ => by
      show Ty.arrow ((X.rename ρ).subst σ) ((Y.rename ρ).subst σ)
         = Ty.arrow (X.subst (Subst.precompose ρ σ))
                    (Y.subst (Subst.precompose ρ σ))
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ σ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, ρ, σ => by
      show Ty.piTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.piTy (X.subst (Subst.precompose ρ σ))
                   (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, ρ, σ => by
      show Ty.sigmaTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.sigmaTy (X.subst (Subst.precompose ρ σ))
                      (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, ρ, σ => by
      show Ty.list ((elemType.rename ρ).subst σ)
         = Ty.list (elemType.subst (Subst.precompose ρ σ))
      have hElem := Ty.rename_subst_commute elemType ρ σ
      exact hElem ▸ rfl
  | .vec elemType length, ρ, σ => by
      show Ty.vec ((elemType.rename ρ).subst σ) length
         = Ty.vec (elemType.subst (Subst.precompose ρ σ)) length
      have hElem := Ty.rename_subst_commute elemType ρ σ
      exact hElem ▸ rfl
  | .option elemType, ρ, σ => by
      show Ty.option ((elemType.rename ρ).subst σ)
         = Ty.option (elemType.subst (Subst.precompose ρ σ))
      have hElem := Ty.rename_subst_commute elemType ρ σ
      exact hElem ▸ rfl
  | .either leftType rightType, ρ, σ => by
      show Ty.either ((leftType.rename ρ).subst σ)
                     ((rightType.rename ρ).subst σ)
         = Ty.either (leftType.subst (Subst.precompose ρ σ))
                     (rightType.subst (Subst.precompose ρ σ))
      have hLeft  := Ty.rename_subst_commute leftType ρ σ
      have hRight := Ty.rename_subst_commute rightType ρ σ
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs, ρ, σ => by
      show Ty.id ((carrier.rename ρ).subst σ)
                 ((lhs.rename ρ).subst σ.forRaw)
                 ((rhs.rename ρ).subst σ.forRaw)
         = Ty.id (carrier.subst (Subst.precompose ρ σ))
                 (lhs.subst (Subst.precompose ρ σ).forRaw)
                 (rhs.subst (Subst.precompose ρ σ).forRaw)
      have hCarrier := Ty.rename_subst_commute carrier ρ σ
      have hLeft := RawTerm.subst_rename_commute lhs ρ σ.forRaw
      have hRight := RawTerm.subst_rename_commute rhs ρ σ.forRaw
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-! ## Renaming as a special case of substitution.

A rawRenaming is a substitution whose substituent at each position is a
`tyVar` reference.  All rawRenaming lemmas are derivable from the
corresponding substitution lemmas via this coercion. -/

/-- Coerce a rawRenaming into a substitution: each variable index `ρ i`
becomes the type-variable reference `Ty.tyVar (ρ i)`. -/
def Renaming.toSubst {s t : Nat} (ρ : Renaming s t) : Subst level s t where
  forTy := fun i => Ty.tyVar (ρ i)
  forRaw := fun i => RawTerm.var (ρ i)

/-- Type component of coercing a rawRenaming to a substitution. -/
theorem Renaming.toSubst_forTy {level source target : Nat}
    (rawRenaming : Renaming source target) (position : Fin source) :
    (Renaming.toSubst (level := level) rawRenaming).forTy position =
      Ty.tyVar (rawRenaming position) :=
  rfl

/-- Raw component of coercing a rawRenaming to a substitution. -/
theorem Renaming.toSubst_forRaw {level source target : Nat}
    (rawRenaming : Renaming source target) (position : Fin source) :
    (Renaming.toSubst (level := level) rawRenaming).forRaw position =
      RawTerm.var (rawRenaming position) :=
  rfl

/-- Lifting commutes with the rawRenaming-to-substitution coercion
(pointwise).  Both cases reduce to `rfl`. -/
theorem Renaming.lift_toSubst_equiv {s t : Nat} (ρ : Renaming s t) :
    Subst.equiv (Renaming.toSubst (level := level) ρ.lift)
                (Renaming.toSubst (level := level) ρ).lift :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl

/-- Raw renaming is raw substitution by variable terms. -/
theorem RawTerm.rename_eq_subst {level source target : Nat} :
    ∀ (rawTerm : RawTerm source) (rawRenaming : Renaming source target),
      rawTerm.rename rawRenaming =
        rawTerm.subst (Renaming.toSubst (level := level) rawRenaming).forRaw
  | rawTerm, rawRenaming => by
      have renamedThenIdentitySubstituted :
          (rawTerm.rename rawRenaming).subst RawTermSubst.identity =
            rawTerm.subst
              (RawTermSubst.afterRenaming rawRenaming RawTermSubst.identity) :=
        RawTerm.subst_rename_commute rawTerm rawRenaming RawTermSubst.identity
      have identitySubstitutionIsNeutral :
          (rawTerm.rename rawRenaming).subst RawTermSubst.identity =
            rawTerm.rename rawRenaming :=
        RawTerm.subst_id (rawTerm.rename rawRenaming)
      have rawSubstitutionsAreEquivalent :
          RawTermSubst.equiv
            (RawTermSubst.afterRenaming rawRenaming RawTermSubst.identity)
            (Renaming.toSubst (level := level) rawRenaming).forRaw :=
        fun _ => rfl
      have endpointsAreCongruent :=
        RawTerm.subst_congr rawSubstitutionsAreEquivalent rawTerm
      exact identitySubstitutionIsNeutral.symm.trans
        (renamedThenIdentitySubstituted.trans endpointsAreCongruent)

/-- Raw renaming by identity is neutral. -/
theorem RawTerm.rename_identity {level scope : Nat} (rawTerm : RawTerm scope) :
    rawTerm.rename Renaming.identity = rawTerm :=
  let renamingIdEqSubstId :
      RawTermSubst.equiv
        (Renaming.toSubst (level := level) (@Renaming.identity scope)).forRaw
        RawTermSubst.identity :=
    fun _ => rfl
  (RawTerm.rename_eq_subst (level := level) rawTerm Renaming.identity).trans
    ((RawTerm.subst_congr renamingIdEqSubstId rawTerm).trans
      (RawTerm.subst_id rawTerm))

/-- **Renaming = Substitution** under the natural coercion.  This is
the conceptual cap of the v1.7 substitution discipline: rawRenaming is
not a separate primitive operation but a special case of substitution
where the substituent for each variable is a `tyVar`.  All rawRenaming
lemmas are derivable from the corresponding substitution lemmas via
this isomorphism. -/
theorem Ty.rename_eq_subst {level s t : Nat} :
    ∀ (T : Ty level s) (ρ : Renaming s t),
    T.rename ρ = T.subst (Renaming.toSubst ρ)
  | .unit, _ => rfl
  | .arrow X Y, ρ => by
      show Ty.arrow (X.rename ρ) (Y.rename ρ)
         = Ty.arrow (X.subst (Renaming.toSubst ρ))
                    (Y.subst (Renaming.toSubst ρ))
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, ρ => by
      show Ty.piTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.piTy (X.subst (Renaming.toSubst ρ))
                   (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _ => rfl
  | .sigmaTy X Y, ρ => by
      show Ty.sigmaTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.sigmaTy (X.subst (Renaming.toSubst ρ))
                      (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _ => rfl
  | .universe _ _, _ => rfl
  | .nat, _ => rfl
  | .list elemType, ρ => by
      show Ty.list (elemType.rename ρ) = Ty.list (elemType.subst (Renaming.toSubst ρ))
      have hElem := Ty.rename_eq_subst elemType ρ
      exact hElem ▸ rfl
  | .vec elemType length, ρ => by
      show Ty.vec (elemType.rename ρ) length =
        Ty.vec (elemType.subst (Renaming.toSubst ρ)) length
      have hElem := Ty.rename_eq_subst elemType ρ
      exact hElem ▸ rfl
  | .option elemType, ρ => by
      show Ty.option (elemType.rename ρ) = Ty.option (elemType.subst (Renaming.toSubst ρ))
      have hElem := Ty.rename_eq_subst elemType ρ
      exact hElem ▸ rfl
  | .either leftType rightType, ρ => by
      show Ty.either (leftType.rename ρ) (rightType.rename ρ)
         = Ty.either (leftType.subst (Renaming.toSubst ρ))
                     (rightType.subst (Renaming.toSubst ρ))
      have hLeft  := Ty.rename_eq_subst leftType ρ
      have hRight := Ty.rename_eq_subst rightType ρ
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs, ρ => by
      show Ty.id (carrier.rename ρ) (lhs.rename ρ) (rhs.rename ρ)
         = Ty.id (carrier.subst (Renaming.toSubst ρ))
                 (lhs.subst (Renaming.toSubst (level := level) ρ).forRaw)
                 (rhs.subst (Renaming.toSubst (level := level) ρ).forRaw)
      have hCarrier := Ty.rename_eq_subst carrier ρ
      have hLeft := RawTerm.rename_eq_subst (level := level) lhs ρ
      have hRight := RawTerm.rename_eq_subst (level := level) rhs ρ
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-! ## Categorical structure: identity and composition.

These lemmas turn `Subst` into a category enriched over `Ty`:

  * `Subst.identity` is the identity object.
  * `Subst.compose` (defined below the supporting weaken-commute lemma)
    is the composition.
  * `Ty.subst` is the action of this category on `Ty`.
  * `Ty.subst_id` (identity law) and `Ty.subst_compose` (associativity
    of action) make the action functorial.

Together these say: substitution behaves algebraically. -/

/-- The identity substitution maps each variable to its own tyVar
reference.  Identity element of substitution composition. -/
def Subst.identity {level scope : Nat} : Subst level scope scope where
  forTy := fun i => Ty.tyVar i
  forRaw := RawTermSubst.identity

/-- Lifting the identity substitution gives the identity at the
extended scope (pointwise).  Both Fin cases are `rfl`. -/
theorem Subst.lift_identity_equiv {level scope : Nat} :
    Subst.equiv (@Subst.identity level scope).lift
                (@Subst.identity level (scope + 1)) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)
    RawTermSubst.lift_identity_equiv

/-- Weakening then substituting with a singleton substitution is the
identity substitution. -/
theorem Subst.precompose_weaken_singleton_equiv_identity {level scope : Nat}
    (substituent : Ty level scope) :
    Subst.equiv
      (Subst.precompose Renaming.weaken (Subst.singleton substituent))
      Subst.identity :=
  Subst.equiv_intro (fun _ => rfl) (RawTermSubst.equiv_refl _)

/-- Weakening then substituting with a term-singleton substitution is
the identity substitution.  The supplied `rawArg` is irrelevant after
weakening because position 0 (where it would land) is no longer
referenced. -/
theorem Subst.precompose_weaken_termSingleton_equiv_identity {level scope : Nat}
    (substituent : Ty level scope) (rawArg : RawTerm scope) :
    Subst.equiv
      (Subst.precompose Renaming.weaken (Subst.termSingleton substituent rawArg))
      Subst.identity :=
  Subst.equiv_intro (fun _ => rfl) (RawTermSubst.equiv_refl _)

/-- The classical singleton is pointwise equivalent to the
term-singleton with `unit` as the raw substituent.  Both produce
`RawTerm.unit` at position 0 and `RawTerm.var k` at position `k+1`,
which is exactly `RawTermSubst.dropNewest` and
`RawTermSubst.singleton RawTerm.unit` respectively.  Stated via
pointwise `Subst.equiv` to remain `propext`/`funext`-free. -/
theorem Subst.singleton_equiv_termSingleton_unit {level scope : Nat}
    (substituent : Ty level scope) :
    Subst.equiv
      (Subst.singleton substituent)
      (Subst.termSingleton substituent RawTerm.unit) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)

/-- **Identity law for substitution**: `T.subst Subst.identity = T`.
The substitution that maps every variable to itself is the identity
operation on `Ty`.  Proven by structural induction on `T`, using
`.symm ▸` to rewrite the goal toward `rfl`. -/
theorem Ty.subst_id {level scope : Nat} :
    ∀ (T : Ty level scope), T.subst Subst.identity = T
  | .unit => rfl
  | .arrow X Y => by
      have hX := Ty.subst_id X
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).arrow (Y.subst Subst.identity) = X.arrow Y
      exact hX.symm ▸ hY.symm ▸ rfl
  | .piTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).piTy (Y.subst Subst.identity.lift) = X.piTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | .tyVar _ => rfl
  | .sigmaTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).sigmaTy (Y.subst Subst.identity.lift)
         = X.sigmaTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elemType => by
      have hElem := Ty.subst_id elemType
      show (elemType.subst Subst.identity).list = elemType.list
      exact hElem.symm ▸ rfl
  | .vec elemType length => by
      have hElem := Ty.subst_id elemType
      show Ty.vec (elemType.subst Subst.identity) length = Ty.vec elemType length
      exact hElem.symm ▸ rfl
  | .option elemType => by
      have hElem := Ty.subst_id elemType
      show (elemType.subst Subst.identity).option = elemType.option
      exact hElem.symm ▸ rfl
  | .either leftType rightType => by
      have hLeft  := Ty.subst_id leftType
      have hRight := Ty.subst_id rightType
      show (leftType.subst Subst.identity).either
             (rightType.subst Subst.identity)
           = leftType.either rightType
      exact hLeft.symm ▸ hRight.symm ▸ rfl
  | .id carrier lhs rhs => by
      have hCarrier := Ty.subst_id carrier
      have hLeft := RawTerm.subst_id lhs
      have hRight := RawTerm.subst_id rhs
      show Ty.id (carrier.subst Subst.identity)
                 (lhs.subst Subst.identity.forRaw)
                 (rhs.subst Subst.identity.forRaw)
         = Ty.id carrier lhs rhs
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-- Substitution commutes with weakening: substituting after
weakening = weakening after substituting (with appropriately lifted
substitution).  Stepping stone for the composition law `Ty.subst_compose`.

In v1.10, with `Ty.weaken := T.rename Renaming.weaken`, this is derived
from `Ty.rename_subst_commute` and `Ty.subst_rename_commute` plus the
pointwise equivalence `Subst.precompose Renaming.weaken σ.lift ≡
Subst.renameAfter σ Renaming.weaken`.  The pointwise equivalence is
trivial (both forms reduce to `(σ i).rename Renaming.weaken` by
`Subst.lift`'s defn at successor positions). -/
theorem Ty.subst_weaken_commute {level s t : Nat} (T : Ty level s) (σ : Subst level s t) :
    (T.weaken).subst σ.lift = (T.subst σ).weaken := by
  show (T.rename Renaming.weaken).subst σ.lift
     = (T.subst σ).rename Renaming.weaken
  have hPointwise :
      Subst.equiv (Subst.precompose Renaming.weaken σ.lift)
                  (Subst.renameAfter σ Renaming.weaken) :=
    Subst.precompose_weaken_lift_equiv_renameAfter_weaken σ
  exact (Ty.rename_subst_commute T Renaming.weaken σ.lift).trans
          ((Ty.subst_congr hPointwise T).trans
            (Ty.subst_rename_commute T σ Renaming.weaken).symm)

/-- Composition of substitutions: apply `σ₁` first, then `σ₂` to each
substituent.  The category-theoretic composition. -/
def Subst.compose {level s m t : Nat} (σ₁ : Subst level s m) (σ₂ : Subst level m t) :
    Subst level s t where
  forTy := fun i => (σ₁ i).subst σ₂
  forRaw := RawTermSubst.compose σ₁.forRaw σ₂.forRaw

/-- Type component of substitution composition. -/
theorem Subst.compose_forTy {level source middle target : Nat}
    (firstSubstitution : Subst level source middle)
    (secondSubstitution : Subst level middle target)
    (position : Fin source) :
    (Subst.compose firstSubstitution secondSubstitution).forTy position =
      (firstSubstitution.forTy position).subst secondSubstitution :=
  rfl

/-- Raw component of substitution composition. -/
theorem Subst.compose_forRaw {level source middle target : Nat}
    (firstSubstitution : Subst level source middle)
    (secondSubstitution : Subst level middle target) :
    (Subst.compose firstSubstitution secondSubstitution).forRaw =
      RawTermSubst.compose firstSubstitution.forRaw secondSubstitution.forRaw :=
  rfl

/-- Lifting commutes with substitution composition (pointwise).  The
non-trivial `k+1` case reduces to `Ty.subst_weaken_commute`. -/
theorem Subst.lift_compose_equiv {level s m t : Nat}
    (σ₁ : Subst level s m) (σ₂ : Subst level m t) :
    Subst.equiv (Subst.compose σ₁.lift σ₂.lift)
                ((Subst.compose σ₁ σ₂).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨k + 1, hk⟩ =>
          Ty.subst_weaken_commute (σ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₂)
    fun position =>
      (RawTermSubst.lift_compose_equiv σ₁.forRaw σ₂.forRaw position).symm

/-- **Composition law for substitution**: `(T.subst σ₁).subst σ₂ =
T.subst (Subst.compose σ₁ σ₂)`.  Together with `Ty.subst_id`, this
makes `Subst` a category enriched over `Ty` and `Ty.subst` its
functorial action.  Proven by structural induction on `T`, using
`Subst.lift_compose_equiv` + `Ty.subst_congr` for the binder cases. -/
theorem Ty.subst_compose {level s m t : Nat} :
    ∀ (T : Ty level s) (σ₁ : Subst level s m) (σ₂ : Subst level m t),
    (T.subst σ₁).subst σ₂ = T.subst (Subst.compose σ₁ σ₂)
  | .unit, _, _ => rfl
  | .arrow X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).arrow ((Y.subst σ₁).subst σ₂)
         = (X.subst (Subst.compose σ₁ σ₂)).arrow
           (Y.subst (Subst.compose σ₁ σ₂))
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁ σ₂
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).piTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).piTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).sigmaTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).sigmaTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, σ₁, σ₂ => by
      show Ty.list ((elemType.subst σ₁).subst σ₂)
         = Ty.list (elemType.subst (Subst.compose σ₁ σ₂))
      have hElem := Ty.subst_compose elemType σ₁ σ₂
      exact hElem ▸ rfl
  | .vec elemType length, σ₁, σ₂ => by
      show Ty.vec ((elemType.subst σ₁).subst σ₂) length
         = Ty.vec (elemType.subst (Subst.compose σ₁ σ₂)) length
      have hElem := Ty.subst_compose elemType σ₁ σ₂
      exact hElem ▸ rfl
  | .option elemType, σ₁, σ₂ => by
      show Ty.option ((elemType.subst σ₁).subst σ₂)
         = Ty.option (elemType.subst (Subst.compose σ₁ σ₂))
      have hElem := Ty.subst_compose elemType σ₁ σ₂
      exact hElem ▸ rfl
  | .either leftType rightType, σ₁, σ₂ => by
      show Ty.either ((leftType.subst σ₁).subst σ₂)
                     ((rightType.subst σ₁).subst σ₂)
         = Ty.either (leftType.subst (Subst.compose σ₁ σ₂))
                     (rightType.subst (Subst.compose σ₁ σ₂))
      have hLeft  := Ty.subst_compose leftType σ₁ σ₂
      have hRight := Ty.subst_compose rightType σ₁ σ₂
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs, σ₁, σ₂ => by
      show Ty.id ((carrier.subst σ₁).subst σ₂)
                 ((lhs.subst σ₁.forRaw).subst σ₂.forRaw)
                 ((rhs.subst σ₁.forRaw).subst σ₂.forRaw)
         = Ty.id (carrier.subst (Subst.compose σ₁ σ₂))
                 (lhs.subst (Subst.compose σ₁ σ₂).forRaw)
                 (rhs.subst (Subst.compose σ₁ σ₂).forRaw)
      have hCarrier := Ty.subst_compose carrier σ₁ σ₂
      have hLeft := RawTerm.subst_compose lhs σ₁.forRaw σ₂.forRaw
      have hRight := RawTerm.subst_compose rhs σ₁.forRaw σ₂.forRaw
      exact congrArgThree (function := Ty.id) hCarrier hLeft hRight

/-! ## Monoid laws for Renaming and Subst.

Composition is associative and unital on both sides.  Stated as
pointwise equivalences to stay funext-free. -/

/-- Pointwise equivalence linking the two singleton-substitution
formulations: substitution-then-rename equals lifted-rename-then-
substitution-with-renamed-substituent.  The auxiliary lemma needed for
the `Ty.subst0_rename_commute` derivation. -/
theorem Subst.singleton_renameAfter_equiv_precompose {level scope target : Nat}
    (A : Ty level scope) (ρ : Renaming scope target) :
    Subst.equiv (Subst.renameAfter (Subst.singleton A) ρ)
                (Subst.precompose ρ.lift (Subst.singleton (A.rename ρ))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl

/-- Term-bearing analog of `singleton_renameAfter_equiv_precompose`:
substitution-then-rename equals lifted-rename-then-substitution-with-
renamed-substituent, where both the type substituent and the raw
substituent get renamed by `ρ`.  The forTy side is identical to the
classical singleton case; the forRaw side uses
`RawTermSubst.singleton (rawArg.rename ρ)` after renaming. -/
theorem Subst.termSingleton_renameAfter_equiv_precompose {level scope target : Nat}
    (A : Ty level scope) (rawArg : RawTerm scope) (ρ : Renaming scope target) :
    Subst.equiv
      (Subst.renameAfter (Subst.termSingleton A rawArg) ρ)
      (Subst.precompose ρ.lift
        (Subst.termSingleton (A.rename ρ) (rawArg.rename ρ))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩      => rfl
      | ⟨_ + 1, _⟩  => rfl

/-- **Single-variable substitution-rename commute** — the practical
specialisation that unblocks `Term.rename`'s `appPi`/`pair`/`snd`
cases.  Substituting the outermost variable then rawRenaming equals
lifted-rawRenaming the codomain then substituting with the renamed
substituent.

Proven by chaining the general lemmas (`subst_rename_commute`,
`rename_subst_commute`) with the singleton-substitution pointwise
equivalence — no fresh structural induction needed.  Showcases how
the v1.7 algebraic structure subsumes ad-hoc lemmas. -/
theorem Ty.subst0_rename_commute {level scope target : Nat}
    (T : Ty level (scope + 1)) (A : Ty level scope) (ρ : Renaming scope target) :
    (T.subst0 A).rename ρ = (T.rename ρ.lift).subst0 (A.rename ρ) := by
  have h1 := Ty.subst_rename_commute T (Subst.singleton A) ρ
  have h2 := Ty.subst_congr
    (Subst.singleton_renameAfter_equiv_precompose A ρ) T
  have h3 := Ty.rename_subst_commute T ρ.lift (Subst.singleton (A.rename ρ))
  exact h1.trans (h2.trans h3.symm)


end LeanFX.Syntax

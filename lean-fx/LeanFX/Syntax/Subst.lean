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
via `substitution`. -/

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
def Subst.lift {level source target : Nat}
    (substitution : Subst level source target) :
    Subst level (source + 1) (target + 1) where
  forTy
    | ⟨0, _⟩                  => .tyVar ⟨0, Nat.zero_lt_succ _⟩
    | ⟨predecessor + 1, succBound⟩  =>
        (substitution ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩).weaken
  forRaw := substitution.forRaw.lift

/-- Single-variable substitution at the outermost binder: substitute
`substituent` for var 0, leave var `k + 1` as `tyVar k` — the
"identity" mapping that decrements the de Bruijn index by one
(reflecting that the outer scope has one fewer binder than the
input scope). -/
@[reducible]
def Subst.singleton {level scope : Nat} (substituent : Ty level scope) :
    Subst level (scope + 1) scope where
  forTy
    | ⟨0, _⟩                        => substituent
    | ⟨predecessor + 1, succBound⟩  =>
        .tyVar ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩
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
    | ⟨0, _⟩                        => substituent
    | ⟨predecessor + 1, succBound⟩  =>
        .tyVar ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩
  forRaw := RawTermSubst.singleton rawArg

/-- Apply a parallel substitution to a type, structurally.  The
`piTy` case lifts the substitution under the new binder; just like
`Ty.rename`, the recursive call's indices are supplied definitionally
by `substitution.lift`, no Nat arithmetic identities required.
Axiom-free. -/
def Ty.subst {level source target : Nat} :
    Ty level source → Subst level source target → Ty level target
  | .unit, _                                         => .unit
  | .arrow domainType codomainType, substitution    =>
      .arrow (Ty.subst domainType substitution)
             (Ty.subst codomainType substitution)
  | .piTy domainType codomainType, substitution     =>
      .piTy (Ty.subst domainType substitution)
            (Ty.subst codomainType substitution.lift)
  | .tyVar position, substitution                   => substitution position
  | .sigmaTy firstType secondType, substitution     =>
      .sigmaTy (Ty.subst firstType substitution)
               (Ty.subst secondType substitution.lift)
  | .bool, _                                         => .bool
  | .universe universeLevel boundOk, _              =>
      .universe universeLevel boundOk
  | .nat, _                                          => .nat
  | .list elemType, substitution                    =>
      .list (Ty.subst elemType substitution)
  | .vec elemType length, substitution              =>
      .vec (Ty.subst elemType substitution) length
  | .option elemType, substitution                  =>
      .option (Ty.subst elemType substitution)
  | .either leftType rightType, substitution        =>
      .either (Ty.subst leftType substitution)
              (Ty.subst rightType substitution)
  | .id carrier leftEnd rightEnd, substitution      =>
      .id (Ty.subst carrier substitution)
          (leftEnd.subst substitution.forRaw)
          (rightEnd.subst substitution.forRaw)

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
`firstSubstitution secondSubstitution : Subst level source target` are
equivalent if they agree at every variable.  Used in lieu of Lean-level
function equality (which would require `funext` and thus `propext`). -/
def Subst.equiv {level source target : Nat}
    (firstSubstitution secondSubstitution : Subst level source target) : Prop :=
  (∀ position,
      firstSubstitution.forTy position = secondSubstitution.forTy position) ∧
    RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw

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

/-- Lifting preserves substitution equivalence: if two substitutions
agree pointwise, then so do their lifts under a binder. -/
theorem Subst.lift_equiv {level source target : Nat}
    {firstSubstitution secondSubstitution : Subst level source target}
    (areEquivalent : Subst.equiv firstSubstitution secondSubstitution) :
    Subst.equiv firstSubstitution.lift secondSubstitution.lift :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      =>
          congrArg Ty.weaken
            (Subst.equiv_forTy areEquivalent
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
    (RawTermSubst.lift_equiv (Subst.equiv_forRaw areEquivalent))

/-- `Ty.subst` respects substitution equivalence: pointwise-equivalent
substitutions produce equal results.  Proven by structural induction
on the type, using `Subst.lift_equiv` for the binder cases. -/
theorem Ty.subst_congr {level source target : Nat}
    {firstSubstitution secondSubstitution : Subst level source target}
    (areEquivalent : Subst.equiv firstSubstitution secondSubstitution) :
    ∀ tyValue : Ty level source,
      tyValue.subst firstSubstitution = tyValue.subst secondSubstitution
  | .unit             => rfl
  | .arrow domainType codomainType  => by
      show Ty.arrow (domainType.subst firstSubstitution)
                    (codomainType.subst firstSubstitution)
         = Ty.arrow (domainType.subst secondSubstitution)
                    (codomainType.subst secondSubstitution)
      have domainEq := Ty.subst_congr areEquivalent domainType
      have codomainEq := Ty.subst_congr areEquivalent codomainType
      exact domainEq ▸ codomainEq ▸ rfl
  | .piTy domainType codomainType   => by
      show Ty.piTy (domainType.subst firstSubstitution)
                   (codomainType.subst firstSubstitution.lift)
         = Ty.piTy (domainType.subst secondSubstitution)
                   (codomainType.subst secondSubstitution.lift)
      have domainEq := Ty.subst_congr areEquivalent domainType
      have codomainEq :=
        Ty.subst_congr (Subst.lift_equiv areEquivalent) codomainType
      exact domainEq ▸ codomainEq ▸ rfl
  | .tyVar position   => Subst.equiv_forTy areEquivalent position
  | .sigmaTy firstType secondType  => by
      show Ty.sigmaTy (firstType.subst firstSubstitution)
                       (secondType.subst firstSubstitution.lift)
         = Ty.sigmaTy (firstType.subst secondSubstitution)
                       (secondType.subst secondSubstitution.lift)
      have firstEq := Ty.subst_congr areEquivalent firstType
      have secondEq :=
        Ty.subst_congr (Subst.lift_equiv areEquivalent) secondType
      exact firstEq ▸ secondEq ▸ rfl
  | .bool             => rfl
  | .universe _ _     => rfl
  | .nat              => rfl
  | .list elemType    => by
      show Ty.list (elemType.subst firstSubstitution)
         = Ty.list (elemType.subst secondSubstitution)
      have elemEq := Ty.subst_congr areEquivalent elemType
      exact elemEq ▸ rfl
  | .vec elemType length => by
      show Ty.vec (elemType.subst firstSubstitution) length
         = Ty.vec (elemType.subst secondSubstitution) length
      have elemEq := Ty.subst_congr areEquivalent elemType
      exact elemEq ▸ rfl
  | .option elemType  => by
      show Ty.option (elemType.subst firstSubstitution)
         = Ty.option (elemType.subst secondSubstitution)
      have elemEq := Ty.subst_congr areEquivalent elemType
      exact elemEq ▸ rfl
  | .either leftType rightType  => by
      show Ty.either (leftType.subst firstSubstitution)
                     (rightType.subst firstSubstitution)
         = Ty.either (leftType.subst secondSubstitution)
                     (rightType.subst secondSubstitution)
      have leftEq  := Ty.subst_congr areEquivalent leftType
      have rightEq := Ty.subst_congr areEquivalent rightType
      exact leftEq ▸ rightEq ▸ rfl
  | .id carrier leftEnd rightEnd  => by
      show Ty.id (carrier.subst firstSubstitution)
                 (leftEnd.subst firstSubstitution.forRaw)
                 (rightEnd.subst firstSubstitution.forRaw)
         = Ty.id (carrier.subst secondSubstitution)
                 (leftEnd.subst secondSubstitution.forRaw)
                 (rightEnd.subst secondSubstitution.forRaw)
      have carrierEq := Ty.subst_congr areEquivalent carrier
      have leftEq :=
        RawTerm.subst_congr (Subst.equiv_forRaw areEquivalent) leftEnd
      have rightEq :=
        RawTerm.subst_congr (Subst.equiv_forRaw areEquivalent) rightEnd
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

/-- Substitution composed with renaming: applies the substitution
first, then renames each substituent.  The "after" naming follows
the order of operations: `renameAfter substitution rawRenaming position
= (substitution position).rename rawRenaming`. -/
def Subst.renameAfter {level source middle target : Nat}
    (substitution : Subst level source middle)
    (rawRenaming : Renaming middle target) :
    Subst level source target where
  forTy := fun position => (substitution position).rename rawRenaming
  forRaw := RawTermSubst.beforeRenaming substitution.forRaw rawRenaming

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

/-- Lifting commutes with the `renameAfter` composition (pointwise).
The non-trivial case `position = ⟨predecessor + 1, _⟩` reduces to
`Ty.rename_weaken_commute` applied to the substituent
`substitution ⟨predecessor, _⟩`. -/
theorem Subst.lift_renameAfter_commute {level source middle target : Nat}
    (substitution : Subst level source middle)
    (rawRenaming : Renaming middle target) :
    Subst.equiv (Subst.renameAfter substitution.lift rawRenaming.lift)
                ((Subst.renameAfter substitution rawRenaming).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      =>
          Ty.rename_weaken_commute
            (substitution
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            rawRenaming)
    fun position =>
      (RawTermSubst.lift_beforeRenaming_equiv
        substitution.forRaw rawRenaming position).symm

/-- **The substitution-rename commute lemma** — the mathematical
heart of the v1.7 layer.  Substituting then renaming a type equals
substituting with renamed substituents (pointwise via `renameAfter`).

This is the load-bearing lemma for `Term.rename`'s `appPi` / `pair` /
`snd` cases (whose result types involve `Ty.subst0`) and ultimately
for β-reduction.  Proven by structural induction on the type, with
the `piTy` / `sigmaTy` cases using `Subst.lift_renameAfter_commute`
+ `Ty.subst_congr`. -/
theorem Ty.subst_rename_commute {level source middle target : Nat} :
    ∀ (tyValue : Ty level source)
      (substitution : Subst level source middle)
      (rawRenaming : Renaming middle target),
    (tyValue.subst substitution).rename rawRenaming
      = tyValue.subst (Subst.renameAfter substitution rawRenaming)
  | .unit, _, _ => rfl
  | .arrow domainType codomainType, substitution, rawRenaming => by
      show Ty.arrow ((domainType.subst substitution).rename rawRenaming)
                    ((codomainType.subst substitution).rename rawRenaming)
         = Ty.arrow
             (domainType.subst (Subst.renameAfter substitution rawRenaming))
             (codomainType.subst (Subst.renameAfter substitution rawRenaming))
      have domainEq :=
        Ty.subst_rename_commute domainType substitution rawRenaming
      have codomainEq :=
        Ty.subst_rename_commute codomainType substitution rawRenaming
      exact domainEq ▸ codomainEq ▸ rfl
  | .piTy domainType codomainType, substitution, rawRenaming => by
      show Ty.piTy ((domainType.subst substitution).rename rawRenaming)
                   ((codomainType.subst substitution.lift).rename rawRenaming.lift)
         = Ty.piTy
             (domainType.subst (Subst.renameAfter substitution rawRenaming))
             (codomainType.subst (Subst.renameAfter substitution rawRenaming).lift)
      have domainEq :=
        Ty.subst_rename_commute domainType substitution rawRenaming
      have codomainEq :=
        Ty.subst_rename_commute codomainType substitution.lift rawRenaming.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_renameAfter_commute substitution rawRenaming) codomainType
      exact domainEq ▸ codomainEq ▸ liftCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy firstType secondType, substitution, rawRenaming => by
      show Ty.sigmaTy ((firstType.subst substitution).rename rawRenaming)
                       ((secondType.subst substitution.lift).rename rawRenaming.lift)
         = Ty.sigmaTy
             (firstType.subst (Subst.renameAfter substitution rawRenaming))
             (secondType.subst (Subst.renameAfter substitution rawRenaming).lift)
      have firstEq :=
        Ty.subst_rename_commute firstType substitution rawRenaming
      have secondEq :=
        Ty.subst_rename_commute secondType substitution.lift rawRenaming.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_renameAfter_commute substitution rawRenaming) secondType
      exact firstEq ▸ secondEq ▸ liftCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, substitution, rawRenaming => by
      show Ty.list ((elemType.subst substitution).rename rawRenaming)
         = Ty.list (elemType.subst (Subst.renameAfter substitution rawRenaming))
      have elemEq :=
        Ty.subst_rename_commute elemType substitution rawRenaming
      exact elemEq ▸ rfl
  | .vec elemType length, substitution, rawRenaming => by
      show Ty.vec ((elemType.subst substitution).rename rawRenaming) length
         = Ty.vec (elemType.subst (Subst.renameAfter substitution rawRenaming))
                  length
      have elemEq :=
        Ty.subst_rename_commute elemType substitution rawRenaming
      exact elemEq ▸ rfl
  | .option elemType, substitution, rawRenaming => by
      show Ty.option ((elemType.subst substitution).rename rawRenaming)
         = Ty.option (elemType.subst (Subst.renameAfter substitution rawRenaming))
      have elemEq :=
        Ty.subst_rename_commute elemType substitution rawRenaming
      exact elemEq ▸ rfl
  | .either leftType rightType, substitution, rawRenaming => by
      show Ty.either ((leftType.subst substitution).rename rawRenaming)
                     ((rightType.subst substitution).rename rawRenaming)
         = Ty.either
             (leftType.subst (Subst.renameAfter substitution rawRenaming))
             (rightType.subst (Subst.renameAfter substitution rawRenaming))
      have leftEq :=
        Ty.subst_rename_commute leftType substitution rawRenaming
      have rightEq :=
        Ty.subst_rename_commute rightType substitution rawRenaming
      exact leftEq ▸ rightEq ▸ rfl
  | .id carrier leftEnd rightEnd, substitution, rawRenaming => by
      show Ty.id ((carrier.subst substitution).rename rawRenaming)
                 ((leftEnd.subst substitution.forRaw).rename rawRenaming)
                 ((rightEnd.subst substitution.forRaw).rename rawRenaming)
         = Ty.id
             (carrier.subst (Subst.renameAfter substitution rawRenaming))
             (leftEnd.subst (Subst.renameAfter substitution rawRenaming).forRaw)
             (rightEnd.subst (Subst.renameAfter substitution rawRenaming).forRaw)
      have carrierEq :=
        Ty.subst_rename_commute carrier substitution rawRenaming
      have leftEq :=
        RawTerm.rename_subst_commute leftEnd substitution.forRaw rawRenaming
      have rightEq :=
        RawTerm.rename_subst_commute rightEnd substitution.forRaw rawRenaming
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

/-- Renaming followed by substitution: precompose the rawRenaming, then
substitute.  `Subst.precompose rawRenaming substitution position
= substitution (rawRenaming position)`. -/
def Subst.precompose {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (substitution : Subst level middle target) :
    Subst level source target where
  forTy := fun position => substitution (rawRenaming position)
  forRaw := RawTermSubst.afterRenaming rawRenaming substitution.forRaw

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

/-- Lifting commutes with precompose (pointwise).  Both
`position = ⟨0, _⟩` and `⟨predecessor + 1, _⟩` cases reduce to `rfl`
thanks to Fin proof irrelevance. -/
theorem Subst.lift_precompose_commute {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (substitution : Subst level middle target) :
    Subst.equiv (Subst.precompose rawRenaming.lift substitution.lift)
                ((Subst.precompose rawRenaming substitution).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩         => rfl
      | ⟨_ + 1, _⟩     => rfl)
    fun position =>
      (RawTermSubst.lift_afterRenaming_equiv
        rawRenaming substitution.forRaw position).symm

/-- Precomposing a lifted substitution with weakening agrees with
rawRenaming each substituent by weakening. -/
theorem Subst.precompose_weaken_lift_equiv_renameAfter_weaken {level source target : Nat}
    (substitution : Subst level source target) :
    Subst.equiv
      (Subst.precompose Renaming.weaken substitution.lift)
      (Subst.renameAfter substitution Renaming.weaken) :=
  Subst.equiv_intro (fun _ => rfl) (RawTermSubst.equiv_refl _)

/-- **The rename-subst commute lemma** — the symmetric counterpart to
`Ty.subst_rename_commute`.  Renaming then substituting equals
substituting with a precomposed substitution.  This is the OTHER
direction of the substitution-rename interaction; together with
`subst_rename_commute` they let us derive `subst0_rename_commute`
and the full β-reduction soundness chain. -/
theorem Ty.rename_subst_commute {level source middle target : Nat} :
    ∀ (tyValue : Ty level source)
      (rawRenaming : Renaming source middle)
      (substitution : Subst level middle target),
    (tyValue.rename rawRenaming).subst substitution
      = tyValue.subst (Subst.precompose rawRenaming substitution)
  | .unit, _, _ => rfl
  | .arrow domainType codomainType, rawRenaming, substitution => by
      show Ty.arrow ((domainType.rename rawRenaming).subst substitution)
                    ((codomainType.rename rawRenaming).subst substitution)
         = Ty.arrow
             (domainType.subst (Subst.precompose rawRenaming substitution))
             (codomainType.subst (Subst.precompose rawRenaming substitution))
      have domainEq :=
        Ty.rename_subst_commute domainType rawRenaming substitution
      have codomainEq :=
        Ty.rename_subst_commute codomainType rawRenaming substitution
      exact domainEq ▸ codomainEq ▸ rfl
  | .piTy domainType codomainType, rawRenaming, substitution => by
      show Ty.piTy ((domainType.rename rawRenaming).subst substitution)
                   ((codomainType.rename rawRenaming.lift).subst substitution.lift)
         = Ty.piTy
             (domainType.subst (Subst.precompose rawRenaming substitution))
             (codomainType.subst (Subst.precompose rawRenaming substitution).lift)
      have domainEq :=
        Ty.rename_subst_commute domainType rawRenaming substitution
      have codomainEq :=
        Ty.rename_subst_commute codomainType rawRenaming.lift substitution.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_precompose_commute rawRenaming substitution) codomainType
      exact domainEq ▸ codomainEq ▸ liftCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy firstType secondType, rawRenaming, substitution => by
      show Ty.sigmaTy ((firstType.rename rawRenaming).subst substitution)
                       ((secondType.rename rawRenaming.lift).subst substitution.lift)
         = Ty.sigmaTy
             (firstType.subst (Subst.precompose rawRenaming substitution))
             (secondType.subst (Subst.precompose rawRenaming substitution).lift)
      have firstEq :=
        Ty.rename_subst_commute firstType rawRenaming substitution
      have secondEq :=
        Ty.rename_subst_commute secondType rawRenaming.lift substitution.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_precompose_commute rawRenaming substitution) secondType
      exact firstEq ▸ secondEq ▸ liftCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, rawRenaming, substitution => by
      show Ty.list ((elemType.rename rawRenaming).subst substitution)
         = Ty.list (elemType.subst (Subst.precompose rawRenaming substitution))
      have elemEq :=
        Ty.rename_subst_commute elemType rawRenaming substitution
      exact elemEq ▸ rfl
  | .vec elemType length, rawRenaming, substitution => by
      show Ty.vec ((elemType.rename rawRenaming).subst substitution) length
         = Ty.vec (elemType.subst (Subst.precompose rawRenaming substitution))
                  length
      have elemEq :=
        Ty.rename_subst_commute elemType rawRenaming substitution
      exact elemEq ▸ rfl
  | .option elemType, rawRenaming, substitution => by
      show Ty.option ((elemType.rename rawRenaming).subst substitution)
         = Ty.option (elemType.subst (Subst.precompose rawRenaming substitution))
      have elemEq :=
        Ty.rename_subst_commute elemType rawRenaming substitution
      exact elemEq ▸ rfl
  | .either leftType rightType, rawRenaming, substitution => by
      show Ty.either ((leftType.rename rawRenaming).subst substitution)
                     ((rightType.rename rawRenaming).subst substitution)
         = Ty.either
             (leftType.subst (Subst.precompose rawRenaming substitution))
             (rightType.subst (Subst.precompose rawRenaming substitution))
      have leftEq :=
        Ty.rename_subst_commute leftType rawRenaming substitution
      have rightEq :=
        Ty.rename_subst_commute rightType rawRenaming substitution
      exact leftEq ▸ rightEq ▸ rfl
  | .id carrier leftEnd rightEnd, rawRenaming, substitution => by
      show Ty.id ((carrier.rename rawRenaming).subst substitution)
                 ((leftEnd.rename rawRenaming).subst substitution.forRaw)
                 ((rightEnd.rename rawRenaming).subst substitution.forRaw)
         = Ty.id
             (carrier.subst (Subst.precompose rawRenaming substitution))
             (leftEnd.subst (Subst.precompose rawRenaming substitution).forRaw)
             (rightEnd.subst (Subst.precompose rawRenaming substitution).forRaw)
      have carrierEq :=
        Ty.rename_subst_commute carrier rawRenaming substitution
      have leftEq :=
        RawTerm.subst_rename_commute leftEnd rawRenaming substitution.forRaw
      have rightEq :=
        RawTerm.subst_rename_commute rightEnd rawRenaming substitution.forRaw
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

/-! ## Renaming as a special case of substitution.

A rawRenaming is a substitution whose substituent at each position is a
`tyVar` reference.  All rawRenaming lemmas are derivable from the
corresponding substitution lemmas via this coercion. -/

/-- Coerce a rawRenaming into a substitution: each variable index
`rawRenaming position` becomes the type-variable reference
`Ty.tyVar (rawRenaming position)`. -/
def Renaming.toSubst {source target : Nat}
    (rawRenaming : Renaming source target) :
    Subst level source target where
  forTy := fun position => Ty.tyVar (rawRenaming position)
  forRaw := fun position => RawTerm.var (rawRenaming position)

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
theorem Renaming.lift_toSubst_equiv {source target : Nat}
    (rawRenaming : Renaming source target) :
    Subst.equiv (Renaming.toSubst (level := level) rawRenaming.lift)
                (Renaming.toSubst (level := level) rawRenaming).lift :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl

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
the conceptual cap of the v1.7 substitution discipline: renaming is
not a separate primitive operation but a special case of substitution
where the substituent for each variable is a `tyVar`.  All renaming
lemmas are derivable from the corresponding substitution lemmas via
this isomorphism. -/
theorem Ty.rename_eq_subst {level source target : Nat} :
    ∀ (tyValue : Ty level source) (rawRenaming : Renaming source target),
      tyValue.rename rawRenaming = tyValue.subst (Renaming.toSubst rawRenaming)
  | .unit, _ => rfl
  | .arrow domainType codomainType, rawRenaming => by
      show Ty.arrow (domainType.rename rawRenaming)
                    (codomainType.rename rawRenaming)
         = Ty.arrow (domainType.subst (Renaming.toSubst rawRenaming))
                    (codomainType.subst (Renaming.toSubst rawRenaming))
      have domainEq := Ty.rename_eq_subst domainType rawRenaming
      have codomainEq := Ty.rename_eq_subst codomainType rawRenaming
      exact domainEq ▸ codomainEq ▸ rfl
  | .piTy domainType codomainType, rawRenaming => by
      show Ty.piTy (domainType.rename rawRenaming)
                   (codomainType.rename rawRenaming.lift)
         = Ty.piTy (domainType.subst (Renaming.toSubst rawRenaming))
                   (codomainType.subst (Renaming.toSubst rawRenaming).lift)
      have domainEq := Ty.rename_eq_subst domainType rawRenaming
      have codomainEq := Ty.rename_eq_subst codomainType rawRenaming.lift
      have liftCong :=
        Ty.subst_congr (Renaming.lift_toSubst_equiv rawRenaming) codomainType
      exact domainEq ▸ codomainEq ▸ liftCong ▸ rfl
  | .tyVar _, _ => rfl
  | .sigmaTy firstType secondType, rawRenaming => by
      show Ty.sigmaTy (firstType.rename rawRenaming)
                       (secondType.rename rawRenaming.lift)
         = Ty.sigmaTy (firstType.subst (Renaming.toSubst rawRenaming))
                       (secondType.subst (Renaming.toSubst rawRenaming).lift)
      have firstEq := Ty.rename_eq_subst firstType rawRenaming
      have secondEq := Ty.rename_eq_subst secondType rawRenaming.lift
      have liftCong :=
        Ty.subst_congr (Renaming.lift_toSubst_equiv rawRenaming) secondType
      exact firstEq ▸ secondEq ▸ liftCong ▸ rfl
  | .bool, _ => rfl
  | .universe _ _, _ => rfl
  | .nat, _ => rfl
  | .list elemType, rawRenaming => by
      show Ty.list (elemType.rename rawRenaming)
         = Ty.list (elemType.subst (Renaming.toSubst rawRenaming))
      have elemEq := Ty.rename_eq_subst elemType rawRenaming
      exact elemEq ▸ rfl
  | .vec elemType length, rawRenaming => by
      show Ty.vec (elemType.rename rawRenaming) length
         = Ty.vec (elemType.subst (Renaming.toSubst rawRenaming)) length
      have elemEq := Ty.rename_eq_subst elemType rawRenaming
      exact elemEq ▸ rfl
  | .option elemType, rawRenaming => by
      show Ty.option (elemType.rename rawRenaming)
         = Ty.option (elemType.subst (Renaming.toSubst rawRenaming))
      have elemEq := Ty.rename_eq_subst elemType rawRenaming
      exact elemEq ▸ rfl
  | .either leftType rightType, rawRenaming => by
      show Ty.either (leftType.rename rawRenaming)
                     (rightType.rename rawRenaming)
         = Ty.either (leftType.subst (Renaming.toSubst rawRenaming))
                     (rightType.subst (Renaming.toSubst rawRenaming))
      have leftEq := Ty.rename_eq_subst leftType rawRenaming
      have rightEq := Ty.rename_eq_subst rightType rawRenaming
      exact leftEq ▸ rightEq ▸ rfl
  | .id carrier leftEnd rightEnd, rawRenaming => by
      show Ty.id (carrier.rename rawRenaming)
                 (leftEnd.rename rawRenaming)
                 (rightEnd.rename rawRenaming)
         = Ty.id (carrier.subst (Renaming.toSubst rawRenaming))
                 (leftEnd.subst (Renaming.toSubst (level := level) rawRenaming).forRaw)
                 (rightEnd.subst (Renaming.toSubst (level := level) rawRenaming).forRaw)
      have carrierEq := Ty.rename_eq_subst carrier rawRenaming
      have leftEq := RawTerm.rename_eq_subst (level := level) leftEnd rawRenaming
      have rightEq := RawTerm.rename_eq_subst (level := level) rightEnd rawRenaming
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

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
  forTy := fun position => Ty.tyVar position
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

/-- Wave 9 / Phase C — `forTy`-only equivalence: `Subst.singleton sub`
and `Subst.termSingleton sub rawArg` agree on the type-substitution
component for any `rawArg`.  The `forRaw` components differ
(`dropNewest` vs `singleton rawArg`) but they don't appear in the
equivalence's type since `Subst.equiv` only constrains `forTy` for
purposes of `Ty.subst`.  Wait — `Subst.equiv` does constrain forRaw
too.  This lemma is the term-Single weakening: we keep both the forTy
agreement (full) and stipulate raw equivalence at the rawArg level
that callers supply. -/
theorem Subst.singleton_forTy_eq_termSingleton {level scope : Nat}
    (substituent : Ty level scope) (rawArg : RawTerm scope) :
    ∀ position, (Subst.singleton substituent).forTy position
              = (Subst.termSingleton substituent rawArg).forTy position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-! ### Wave 5 strangle helpers

`Subst.singleton` and `Subst.termSingleton _ RawTerm.unit` agree
pointwise (`Subst.singleton_equiv_termSingleton_unit`).  The next
two corollaries lift that equivalence to the most common consumer
sites, `Ty.subst0` and bare `Ty.subst T (Subst.singleton _)`.  They
let downstream callers move from `singleton` to `termSingleton`
without touching their semantic core — the strangle pattern that
unblocks Wave 5/6 β-surgery without taking the whole Subst.singleton
deletion in one step. -/

/-- `Ty.subst T (Subst.singleton X) = Ty.subst T (Subst.termSingleton X RawTerm.unit)`.
A direct corollary of `Subst.singleton_equiv_termSingleton_unit` via
`Ty.subst_congr`.  Use to migrate type-only callers from the
`singleton` flavor to the `termSingleton` flavor without changing
semantics. -/
theorem Ty.subst_singleton_eq_termSingleton_unit
    {level scope : Nat} (T : Ty level (scope + 1))
    (substituent : Ty level scope) :
    T.subst (Subst.singleton substituent) =
      T.subst (Subst.termSingleton substituent RawTerm.unit) :=
  Ty.subst_congr
    (Subst.singleton_equiv_termSingleton_unit substituent) T

/-- `Ty.subst0 codomain domain = Ty.subst codomain (Subst.termSingleton domain RawTerm.unit)`.
The dependent-application-result-type form of the strangle; equal to
`Ty.subst_singleton_eq_termSingleton_unit` after unfolding `Ty.subst0`. -/
theorem Ty.subst0_eq_termSingleton_unit
    {level scope : Nat} (codomain : Ty level (scope + 1))
    (domain : Ty level scope) :
    codomain.subst0 domain =
      codomain.subst (Subst.termSingleton domain RawTerm.unit) :=
  Ty.subst_singleton_eq_termSingleton_unit codomain domain

/-- **Identity law for substitution**: `tyValue.subst Subst.identity = tyValue`.
The substitution that maps every variable to itself is the identity
operation on `Ty`.  Proven by structural induction on the type, using
`.symm ▸` to rewrite the goal toward `rfl`. -/
theorem Ty.subst_id {level scope : Nat} :
    ∀ (tyValue : Ty level scope), tyValue.subst Subst.identity = tyValue
  | .unit => rfl
  | .arrow domainType codomainType => by
      have domainEq := Ty.subst_id domainType
      have codomainEq := Ty.subst_id codomainType
      show (domainType.subst Subst.identity).arrow
            (codomainType.subst Subst.identity)
         = domainType.arrow codomainType
      exact domainEq.symm ▸ codomainEq.symm ▸ rfl
  | .piTy domainType codomainType => by
      have domainEq := Ty.subst_id domainType
      have liftCong :=
        Ty.subst_congr Subst.lift_identity_equiv codomainType
      have codomainEq := Ty.subst_id codomainType
      show (domainType.subst Subst.identity).piTy
            (codomainType.subst Subst.identity.lift)
         = domainType.piTy codomainType
      exact domainEq.symm ▸ liftCong.symm ▸ codomainEq.symm ▸ rfl
  | .tyVar _ => rfl
  | .sigmaTy firstType secondType => by
      have firstEq := Ty.subst_id firstType
      have liftCong :=
        Ty.subst_congr Subst.lift_identity_equiv secondType
      have secondEq := Ty.subst_id secondType
      show (firstType.subst Subst.identity).sigmaTy
            (secondType.subst Subst.identity.lift)
         = firstType.sigmaTy secondType
      exact firstEq.symm ▸ liftCong.symm ▸ secondEq.symm ▸ rfl
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elemType => by
      have elemEq := Ty.subst_id elemType
      show (elemType.subst Subst.identity).list = elemType.list
      exact elemEq.symm ▸ rfl
  | .vec elemType length => by
      have elemEq := Ty.subst_id elemType
      show Ty.vec (elemType.subst Subst.identity) length
         = Ty.vec elemType length
      exact elemEq.symm ▸ rfl
  | .option elemType => by
      have elemEq := Ty.subst_id elemType
      show (elemType.subst Subst.identity).option = elemType.option
      exact elemEq.symm ▸ rfl
  | .either leftType rightType => by
      have leftEq  := Ty.subst_id leftType
      have rightEq := Ty.subst_id rightType
      show (leftType.subst Subst.identity).either
             (rightType.subst Subst.identity)
           = leftType.either rightType
      exact leftEq.symm ▸ rightEq.symm ▸ rfl
  | .id carrier leftEnd rightEnd => by
      have carrierEq := Ty.subst_id carrier
      have leftEq := RawTerm.subst_id leftEnd
      have rightEq := RawTerm.subst_id rightEnd
      show Ty.id (carrier.subst Subst.identity)
                 (leftEnd.subst Subst.identity.forRaw)
                 (rightEnd.subst Subst.identity.forRaw)
         = Ty.id carrier leftEnd rightEnd
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

/-- Substitution commutes with weakening: substituting after
weakening = weakening after substituting (with appropriately lifted
substitution).  Stepping stone for the composition law
`Ty.subst_compose`.

In v1.10, with `Ty.weaken := tyValue.rename Renaming.weaken`, this is
derived from `Ty.rename_subst_commute` and `Ty.subst_rename_commute`
plus the pointwise equivalence
`Subst.precompose Renaming.weaken substitution.lift ≡
 Subst.renameAfter substitution Renaming.weaken`.
The pointwise equivalence is trivial (both forms reduce to
`(substitution position).rename Renaming.weaken` by `Subst.lift`'s
defn at successor positions). -/
theorem Ty.subst_weaken_commute {level source target : Nat}
    (tyValue : Ty level source)
    (substitution : Subst level source target) :
    (tyValue.weaken).subst substitution.lift
      = (tyValue.subst substitution).weaken := by
  show (tyValue.rename Renaming.weaken).subst substitution.lift
     = (tyValue.subst substitution).rename Renaming.weaken
  have substitutionsAgreePointwise :
      Subst.equiv (Subst.precompose Renaming.weaken substitution.lift)
                  (Subst.renameAfter substitution Renaming.weaken) :=
    Subst.precompose_weaken_lift_equiv_renameAfter_weaken substitution
  exact (Ty.rename_subst_commute tyValue Renaming.weaken substitution.lift).trans
          ((Ty.subst_congr substitutionsAgreePointwise tyValue).trans
            (Ty.subst_rename_commute tyValue substitution Renaming.weaken).symm)

/-- Composition of substitutions: apply `firstSubstitution` first, then
`secondSubstitution` to each substituent.  The category-theoretic
composition. -/
def Subst.compose {level source middle target : Nat}
    (firstSubstitution : Subst level source middle)
    (secondSubstitution : Subst level middle target) :
    Subst level source target where
  forTy := fun position =>
    (firstSubstitution position).subst secondSubstitution
  forRaw :=
    RawTermSubst.compose firstSubstitution.forRaw secondSubstitution.forRaw

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
non-trivial `predecessor + 1` case reduces to `Ty.subst_weaken_commute`. -/
theorem Subst.lift_compose_equiv {level source middle target : Nat}
    (firstSubstitution : Subst level source middle)
    (secondSubstitution : Subst level middle target) :
    Subst.equiv (Subst.compose firstSubstitution.lift secondSubstitution.lift)
                ((Subst.compose firstSubstitution secondSubstitution).lift) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      =>
          Ty.subst_weaken_commute
            (firstSubstitution
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            secondSubstitution)
    fun position =>
      (RawTermSubst.lift_compose_equiv
        firstSubstitution.forRaw secondSubstitution.forRaw position).symm

/-- **Composition law for substitution**:
`(tyValue.subst firstSubstitution).subst secondSubstitution
 = tyValue.subst (Subst.compose firstSubstitution secondSubstitution)`.
Together with `Ty.subst_id`, this makes `Subst` a category enriched
over `Ty` and `Ty.subst` its functorial action.  Proven by structural
induction on the type, using `Subst.lift_compose_equiv` +
`Ty.subst_congr` for the binder cases. -/
theorem Ty.subst_compose {level source middle target : Nat} :
    ∀ (tyValue : Ty level source)
      (firstSubstitution : Subst level source middle)
      (secondSubstitution : Subst level middle target),
    (tyValue.subst firstSubstitution).subst secondSubstitution
      = tyValue.subst (Subst.compose firstSubstitution secondSubstitution)
  | .unit, _, _ => rfl
  | .arrow domainType codomainType, firstSubstitution, secondSubstitution => by
      show ((domainType.subst firstSubstitution).subst secondSubstitution).arrow
            ((codomainType.subst firstSubstitution).subst secondSubstitution)
         = (domainType.subst (Subst.compose firstSubstitution secondSubstitution)).arrow
            (codomainType.subst (Subst.compose firstSubstitution secondSubstitution))
      have domainEq :=
        Ty.subst_compose domainType firstSubstitution secondSubstitution
      have codomainEq :=
        Ty.subst_compose codomainType firstSubstitution secondSubstitution
      exact domainEq ▸ codomainEq ▸ rfl
  | .piTy domainType codomainType, firstSubstitution, secondSubstitution => by
      show ((domainType.subst firstSubstitution).subst secondSubstitution).piTy
            ((codomainType.subst firstSubstitution.lift).subst secondSubstitution.lift)
         = (domainType.subst (Subst.compose firstSubstitution secondSubstitution)).piTy
            (codomainType.subst (Subst.compose firstSubstitution secondSubstitution).lift)
      have domainEq :=
        Ty.subst_compose domainType firstSubstitution secondSubstitution
      have codomainEq :=
        Ty.subst_compose codomainType firstSubstitution.lift secondSubstitution.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_compose_equiv firstSubstitution secondSubstitution)
          codomainType
      exact domainEq ▸ codomainEq ▸ liftCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy firstType secondType, firstSubstitution, secondSubstitution => by
      show ((firstType.subst firstSubstitution).subst secondSubstitution).sigmaTy
            ((secondType.subst firstSubstitution.lift).subst secondSubstitution.lift)
         = (firstType.subst (Subst.compose firstSubstitution secondSubstitution)).sigmaTy
            (secondType.subst (Subst.compose firstSubstitution secondSubstitution).lift)
      have firstEq :=
        Ty.subst_compose firstType firstSubstitution secondSubstitution
      have secondEq :=
        Ty.subst_compose secondType firstSubstitution.lift secondSubstitution.lift
      have liftCong :=
        Ty.subst_congr
          (Subst.lift_compose_equiv firstSubstitution secondSubstitution)
          secondType
      exact firstEq ▸ secondEq ▸ liftCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, firstSubstitution, secondSubstitution => by
      show Ty.list ((elemType.subst firstSubstitution).subst secondSubstitution)
         = Ty.list (elemType.subst (Subst.compose firstSubstitution secondSubstitution))
      have elemEq :=
        Ty.subst_compose elemType firstSubstitution secondSubstitution
      exact elemEq ▸ rfl
  | .vec elemType length, firstSubstitution, secondSubstitution => by
      show Ty.vec ((elemType.subst firstSubstitution).subst secondSubstitution) length
         = Ty.vec
             (elemType.subst (Subst.compose firstSubstitution secondSubstitution))
             length
      have elemEq :=
        Ty.subst_compose elemType firstSubstitution secondSubstitution
      exact elemEq ▸ rfl
  | .option elemType, firstSubstitution, secondSubstitution => by
      show Ty.option ((elemType.subst firstSubstitution).subst secondSubstitution)
         = Ty.option (elemType.subst (Subst.compose firstSubstitution secondSubstitution))
      have elemEq :=
        Ty.subst_compose elemType firstSubstitution secondSubstitution
      exact elemEq ▸ rfl
  | .either leftType rightType, firstSubstitution, secondSubstitution => by
      show Ty.either ((leftType.subst firstSubstitution).subst secondSubstitution)
                     ((rightType.subst firstSubstitution).subst secondSubstitution)
         = Ty.either
             (leftType.subst (Subst.compose firstSubstitution secondSubstitution))
             (rightType.subst (Subst.compose firstSubstitution secondSubstitution))
      have leftEq :=
        Ty.subst_compose leftType firstSubstitution secondSubstitution
      have rightEq :=
        Ty.subst_compose rightType firstSubstitution secondSubstitution
      exact leftEq ▸ rightEq ▸ rfl
  | .id carrier leftEnd rightEnd, firstSubstitution, secondSubstitution => by
      show Ty.id ((carrier.subst firstSubstitution).subst secondSubstitution)
                 ((leftEnd.subst firstSubstitution.forRaw).subst secondSubstitution.forRaw)
                 ((rightEnd.subst firstSubstitution.forRaw).subst secondSubstitution.forRaw)
         = Ty.id
             (carrier.subst (Subst.compose firstSubstitution secondSubstitution))
             (leftEnd.subst (Subst.compose firstSubstitution secondSubstitution).forRaw)
             (rightEnd.subst (Subst.compose firstSubstitution secondSubstitution).forRaw)
      have carrierEq :=
        Ty.subst_compose carrier firstSubstitution secondSubstitution
      have leftEq :=
        RawTerm.subst_compose leftEnd
          firstSubstitution.forRaw secondSubstitution.forRaw
      have rightEq :=
        RawTerm.subst_compose rightEnd
          firstSubstitution.forRaw secondSubstitution.forRaw
      exact congrArgThree (function := Ty.id) carrierEq leftEq rightEq

/-! ## Monoid laws for Renaming and Subst.

Composition is associative and unital on both sides.  Stated as
pointwise equivalences to stay funext-free. -/

/-- Pointwise equivalence linking the two singleton-substitution
formulations: substitution-then-rename equals lifted-rename-then-
substitution-with-renamed-substituent.  The auxiliary lemma needed for
the `Ty.subst0_rename_commute` derivation. -/
theorem Subst.singleton_renameAfter_equiv_precompose
    {level scope target : Nat}
    (substituent : Ty level scope)
    (rawRenaming : Renaming scope target) :
    Subst.equiv
      (Subst.renameAfter (Subst.singleton substituent) rawRenaming)
      (Subst.precompose rawRenaming.lift
        (Subst.singleton (substituent.rename rawRenaming))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl

/-- Term-bearing analog of `singleton_renameAfter_equiv_precompose`:
substitution-then-rename equals lifted-rename-then-substitution-with-
renamed-substituent, where both the type substituent and the raw
substituent get renamed by `rawRenaming`.  The forTy side is identical
to the classical singleton case; the forRaw side uses
`RawTermSubst.singleton (rawArg.rename rawRenaming)` after renaming. -/
theorem Subst.termSingleton_renameAfter_equiv_precompose
    {level scope target : Nat}
    (substituent : Ty level scope) (rawArg : RawTerm scope)
    (rawRenaming : Renaming scope target) :
    Subst.equiv
      (Subst.renameAfter (Subst.termSingleton substituent rawArg) rawRenaming)
      (Subst.precompose rawRenaming.lift
        (Subst.termSingleton
          (substituent.rename rawRenaming)
          (rawArg.rename rawRenaming))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl)
    fun position =>
      match position with
      | ⟨0, _⟩          => rfl
      | ⟨_ + 1, _⟩      => rfl

/-- **Single-variable substitution-rename commute** — the practical
specialisation that unblocks `Term.rename`'s `appPi` / `pair` / `snd`
cases.  Substituting the outermost variable then renaming equals
lifted-renaming the codomain then substituting with the renamed
substituent.

Proven by chaining the general lemmas (`subst_rename_commute`,
`rename_subst_commute`) with the singleton-substitution pointwise
equivalence — no fresh structural induction needed.  Showcases how
the v1.7 algebraic structure subsumes ad-hoc lemmas. -/
theorem Ty.subst0_rename_commute {level scope target : Nat}
    (codomain : Ty level (scope + 1))
    (substituent : Ty level scope)
    (rawRenaming : Renaming scope target) :
    (codomain.subst0 substituent).rename rawRenaming
      = (codomain.rename rawRenaming.lift).subst0
          (substituent.rename rawRenaming) := by
  have substThenRename :=
    Ty.subst_rename_commute codomain (Subst.singleton substituent) rawRenaming
  have substitutionsAgreePointwise :=
    Ty.subst_congr
      (Subst.singleton_renameAfter_equiv_precompose substituent rawRenaming)
      codomain
  have renameThenSubst :=
    Ty.rename_subst_commute codomain rawRenaming.lift
      (Subst.singleton (substituent.rename rawRenaming))
  exact substThenRename.trans
          (substitutionsAgreePointwise.trans renameThenSubst.symm)


end LeanFX.Syntax

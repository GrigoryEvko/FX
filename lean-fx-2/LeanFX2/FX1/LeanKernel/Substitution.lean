prelude
import LeanFX2.FX1.LeanKernel.Expr

/-! # FX1/LeanKernel/Substitution

Lean kernel expression renaming and instantiation.

## Deliverable

This module provides the first load-bearing substitution slice for the encoded
Lean expression language:

* scoped renamings;
* single-binder weakening;
* scoped substitutions;
* top-binder instantiation.

It deliberately does not claim the full Lean `abstract` operation yet; that
needs a depth-indexed free-variable abstraction pass to avoid binder capture.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- A scoped expression renaming. -/
@[reducible] def ExprRenaming (_sourceScope _targetScope : Nat) : Type :=
  Nat -> Nat

namespace ExprRenaming

/-- Lift a renaming under one new binder. -/
def lift {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    ExprRenaming (Nat.succ sourceScope) (Nat.succ targetScope) :=
  fun
  | Nat.zero => Nat.zero
  | Nat.succ index => Nat.succ (renamer index)

/-- Weaken all existing bound variables under a fresh newest binder. -/
def weaken {scope : Nat} : ExprRenaming scope (Nat.succ scope) :=
  fun position => Nat.succ position

/-- Lifting maps the newest binder to itself. -/
theorem lift_newest {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    Eq
      (lift renamer Nat.zero)
      Nat.zero :=
  Eq.refl Nat.zero

/-- Lifting maps older variables through the original renaming. -/
theorem lift_succ {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope)
    (position : Nat) :
    Eq
      (lift renamer (Nat.succ position))
      (Nat.succ (renamer position)) :=
  match position with
  | Nat.zero => Eq.refl (Nat.succ (renamer Nat.zero))
  | Nat.succ smallerPosition =>
      Eq.refl (Nat.succ (renamer (Nat.succ smallerPosition)))

end ExprRenaming

namespace Expr

/-- Rename bound variables in an encoded Lean expression. -/
def renameWith {level sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    Expr level sourceScope -> Expr level targetScope :=
  fun
  | Expr.bvar position => Expr.bvar (renamer position)
  | Expr.fvar fvarId => Expr.fvar fvarId
  | Expr.mvar mvarId => Expr.mvar mvarId
  | Expr.sort sortLevel => Expr.sort sortLevel
  | Expr.const constName levels => Expr.const constName levels
  | Expr.app functionExpr argumentExpr =>
      Expr.app (renameWith renamer functionExpr) (renameWith renamer argumentExpr)
  | Expr.lam binderName domainExpr bodyExpr binderInfo =>
      Expr.lam binderName
        (renameWith renamer domainExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        binderInfo
  | Expr.forallE binderName domainExpr bodyExpr binderInfo =>
      Expr.forallE binderName
        (renameWith renamer domainExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        binderInfo
  | Expr.letE declName typeExpr valueExpr bodyExpr nondep =>
      Expr.letE declName
        (renameWith renamer typeExpr)
        (renameWith renamer valueExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        nondep
  | Expr.lit literal => Expr.lit literal
  | Expr.mdata metadata bodyExpr =>
      Expr.mdata metadata (renameWith renamer bodyExpr)
  | Expr.proj structName fieldIndex targetExpr =>
      Expr.proj structName fieldIndex (renameWith renamer targetExpr)

/-- Weaken an expression under a fresh newest binder. -/
def weaken {level scope : Nat} (someExpr : Expr level scope) :
    Expr level (Nat.succ scope) :=
  renameWith ExprRenaming.weaken someExpr

end Expr

/-- A scoped expression substitution. -/
@[reducible] def ExprSubstitution
    (level _sourceScope targetScope : Nat) : Type :=
  Nat -> Expr level targetScope

namespace ExprSubstitution

/-- Lift a substitution under one new binder. -/
def lift {level sourceScope targetScope : Nat}
    (substitution : ExprSubstitution level sourceScope targetScope) :
    ExprSubstitution level (Nat.succ sourceScope) (Nat.succ targetScope) :=
  fun
  | Nat.zero => Expr.bvar Nat.zero
  | Nat.succ index => Expr.weaken (substitution index)

/-- Substitute the newest binder with `valueExpr` and lower older variables. -/
def singleton {level scope : Nat}
    (valueExpr : Expr level scope) :
    ExprSubstitution level (Nat.succ scope) scope :=
  fun
  | Nat.zero => valueExpr
  | Nat.succ index => Expr.bvar index

/-- A singleton substitution maps the newest binder to its value. -/
theorem singleton_newest {level scope : Nat}
    (valueExpr : Expr level scope) :
    Eq
      (singleton valueExpr Nat.zero)
      valueExpr :=
  Eq.refl valueExpr

/-- A singleton substitution lowers older variables by one binder. -/
theorem singleton_succ {level scope : Nat}
    (valueExpr : Expr level scope)
    (position : Nat) :
    Eq (singleton valueExpr (Nat.succ position)) (Expr.bvar position) :=
  match position with
  | Nat.zero => Eq.refl (Expr.bvar Nat.zero)
  | Nat.succ smallerPosition =>
      Eq.refl (Expr.bvar (Nat.succ smallerPosition))

end ExprSubstitution

namespace Expr

/-- Substitute bound variables in an encoded Lean expression. -/
def subst {level sourceScope targetScope : Nat}
    (substitution : ExprSubstitution level sourceScope targetScope) :
    Expr level sourceScope -> Expr level targetScope :=
  fun
  | Expr.bvar position => substitution position
  | Expr.fvar fvarId => Expr.fvar fvarId
  | Expr.mvar mvarId => Expr.mvar mvarId
  | Expr.sort sortLevel => Expr.sort sortLevel
  | Expr.const constName levels => Expr.const constName levels
  | Expr.app functionExpr argumentExpr =>
      Expr.app (subst substitution functionExpr) (subst substitution argumentExpr)
  | Expr.lam binderName domainExpr bodyExpr binderInfo =>
      Expr.lam binderName
        (subst substitution domainExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        binderInfo
  | Expr.forallE binderName domainExpr bodyExpr binderInfo =>
      Expr.forallE binderName
        (subst substitution domainExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        binderInfo
  | Expr.letE declName typeExpr valueExpr bodyExpr nondep =>
      Expr.letE declName
        (subst substitution typeExpr)
        (subst substitution valueExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        nondep
  | Expr.lit literal => Expr.lit literal
  | Expr.mdata metadata bodyExpr => Expr.mdata metadata (subst substitution bodyExpr)
  | Expr.proj structName fieldIndex targetExpr =>
      Expr.proj structName fieldIndex (subst substitution targetExpr)

/-- Instantiate the newest binder in `bodyExpr` with `valueExpr`. -/
def instantiate {level scope : Nat}
    (bodyExpr : Expr level (Nat.succ scope))
    (valueExpr : Expr level scope) : Expr level scope :=
  subst (ExprSubstitution.singleton valueExpr) bodyExpr

/-- Instantiating the newest bound variable returns the substituting value. -/
theorem instantiate_bvar_zero {level scope : Nat}
    (valueExpr : Expr level scope) :
    Eq
      (instantiate
        (Expr.bvar Nat.zero)
        valueExpr)
      valueExpr :=
  Eq.refl valueExpr

/-- Instantiating an older bound variable lowers it by one binder. -/
theorem instantiate_bvar_succ {level scope : Nat}
    (valueExpr : Expr level scope)
    (position : Nat) :
    Eq
      (instantiate (Expr.bvar (Nat.succ position)) valueExpr)
      (Expr.bvar position) :=
  match position with
  | Nat.zero => Eq.refl (Expr.bvar Nat.zero)
  | Nat.succ smallerPosition =>
      Eq.refl (Expr.bvar (Nat.succ smallerPosition))

/-- Weakening maps a bound variable to its successor position. -/
theorem weaken_bvar {level scope : Nat}
    (position : Nat) :
    Eq
      (weaken (level := level) (scope := scope)
        (Expr.bvar (level := level) (scope := scope) position))
      (Expr.bvar (level := level) (scope := Nat.succ scope)
        (Nat.succ position)) :=
  match position with
  | Nat.zero =>
      Eq.refl
        (Expr.bvar (level := level) (scope := Nat.succ scope)
          (Nat.succ Nat.zero))
  | Nat.succ smallerPosition =>
      Eq.refl
        (Expr.bvar (level := level) (scope := Nat.succ scope)
          (Nat.succ (Nat.succ smallerPosition)))

end Expr

end FX1.LeanKernel
end LeanFX2

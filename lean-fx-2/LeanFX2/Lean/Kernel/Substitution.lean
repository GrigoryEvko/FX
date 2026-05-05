import LeanFX2.Lean.Kernel.Expr

/-! # Lean/Kernel/Substitution

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
namespace LeanKernel

/-- A scoped expression renaming. -/
@[reducible] def ExprRenaming (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → Fin targetScope

namespace ExprRenaming

/-- Lift a renaming under one new binder. -/
def lift {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    ExprRenaming (sourceScope + 1) (targetScope + 1) :=
  fun
  | ⟨0, _isLt⟩ => ⟨0, Nat.zero_lt_succ targetScope⟩
  | ⟨index + 1, isLt⟩ =>
      Fin.succ (renamer ⟨index, Nat.lt_of_succ_lt_succ isLt⟩)

/-- Weaken all existing bound variables under a fresh newest binder. -/
def weaken {scope : Nat} : ExprRenaming scope (scope + 1) :=
  fun position => Fin.succ position

/-- Lifting maps the newest binder to itself. -/
theorem lift_newest {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    lift renamer ⟨0, Nat.zero_lt_succ sourceScope⟩ =
      ⟨0, Nat.zero_lt_succ targetScope⟩ := rfl

/-- Lifting maps older variables through the original renaming. -/
theorem lift_succ {sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope)
    (position : Fin sourceScope) :
    lift renamer (Fin.succ position) = Fin.succ (renamer position) := by
  cases position with
  | mk index isLt => rfl

end ExprRenaming

namespace Expr

/-- Rename bound variables in an encoded Lean expression. -/
def renameWith {level sourceScope targetScope : Nat}
    (renamer : ExprRenaming sourceScope targetScope) :
    Expr level sourceScope → Expr level targetScope :=
  fun
  | bvar position => bvar (renamer position)
  | fvar fvarId => fvar fvarId
  | mvar mvarId => mvar mvarId
  | sort sortLevel => sort sortLevel
  | const constName levels => const constName levels
  | app functionExpr argumentExpr =>
      app (renameWith renamer functionExpr) (renameWith renamer argumentExpr)
  | lam binderName domainExpr bodyExpr binderInfo =>
      lam binderName
        (renameWith renamer domainExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        binderInfo
  | forallE binderName domainExpr bodyExpr binderInfo =>
      forallE binderName
        (renameWith renamer domainExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        binderInfo
  | letE declName typeExpr valueExpr bodyExpr nondep =>
      letE declName
        (renameWith renamer typeExpr)
        (renameWith renamer valueExpr)
        (renameWith (ExprRenaming.lift renamer) bodyExpr)
        nondep
  | lit literal => lit literal
  | mdata metadata bodyExpr => mdata metadata (renameWith renamer bodyExpr)
  | proj structName fieldIndex targetExpr =>
      proj structName fieldIndex (renameWith renamer targetExpr)

/-- Weaken an expression under a fresh newest binder. -/
def weaken {level scope : Nat} (someExpr : Expr level scope) :
    Expr level (scope + 1) :=
  renameWith ExprRenaming.weaken someExpr

end Expr

/-- A scoped expression substitution. -/
@[reducible] def ExprSubstitution
    (level sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → Expr level targetScope

namespace ExprSubstitution

/-- Lift a substitution under one new binder. -/
def lift {level sourceScope targetScope : Nat}
    (substitution : ExprSubstitution level sourceScope targetScope) :
    ExprSubstitution level (sourceScope + 1) (targetScope + 1) :=
  fun
  | ⟨0, _isLt⟩ => Expr.bvar ⟨0, Nat.zero_lt_succ targetScope⟩
  | ⟨index + 1, isLt⟩ =>
      Expr.weaken (substitution ⟨index, Nat.lt_of_succ_lt_succ isLt⟩)

/-- Substitute the newest binder with `valueExpr` and lower older variables. -/
def singleton {level scope : Nat}
    (valueExpr : Expr level scope) :
    ExprSubstitution level (scope + 1) scope :=
  fun
  | ⟨0, _isLt⟩ => valueExpr
  | ⟨index + 1, isLt⟩ =>
      Expr.bvar ⟨index, Nat.lt_of_succ_lt_succ isLt⟩

/-- A singleton substitution maps the newest binder to its value. -/
theorem singleton_newest {level scope : Nat}
    (valueExpr : Expr level scope) :
    singleton valueExpr ⟨0, Nat.zero_lt_succ scope⟩ = valueExpr := rfl

/-- A singleton substitution lowers older variables by one binder. -/
theorem singleton_succ {level scope : Nat}
    (valueExpr : Expr level scope)
    (position : Fin scope) :
    singleton valueExpr (Fin.succ position) = Expr.bvar position := by
  cases position with
  | mk index isLt => rfl

end ExprSubstitution

namespace Expr

/-- Substitute bound variables in an encoded Lean expression. -/
def subst {level sourceScope targetScope : Nat}
    (substitution : ExprSubstitution level sourceScope targetScope) :
    Expr level sourceScope → Expr level targetScope :=
  fun
  | bvar position => substitution position
  | fvar fvarId => fvar fvarId
  | mvar mvarId => mvar mvarId
  | sort sortLevel => sort sortLevel
  | const constName levels => const constName levels
  | app functionExpr argumentExpr =>
      app (subst substitution functionExpr) (subst substitution argumentExpr)
  | lam binderName domainExpr bodyExpr binderInfo =>
      lam binderName
        (subst substitution domainExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        binderInfo
  | forallE binderName domainExpr bodyExpr binderInfo =>
      forallE binderName
        (subst substitution domainExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        binderInfo
  | letE declName typeExpr valueExpr bodyExpr nondep =>
      letE declName
        (subst substitution typeExpr)
        (subst substitution valueExpr)
        (subst (ExprSubstitution.lift substitution) bodyExpr)
        nondep
  | lit literal => lit literal
  | mdata metadata bodyExpr => mdata metadata (subst substitution bodyExpr)
  | proj structName fieldIndex targetExpr =>
      proj structName fieldIndex (subst substitution targetExpr)

/-- Instantiate the newest binder in `bodyExpr` with `valueExpr`. -/
def instantiate {level scope : Nat}
    (bodyExpr : Expr level (scope + 1))
    (valueExpr : Expr level scope) : Expr level scope :=
  subst (ExprSubstitution.singleton valueExpr) bodyExpr

/-- Instantiating the newest bound variable returns the substituting value. -/
theorem instantiate_bvar_zero {level scope : Nat}
    (valueExpr : Expr level scope) :
    instantiate
      (bvar ⟨0, Nat.zero_lt_succ scope⟩)
      valueExpr = valueExpr := rfl

/-- Instantiating an older bound variable lowers it by one binder. -/
theorem instantiate_bvar_succ {level scope : Nat}
    (valueExpr : Expr level scope)
    (position : Fin scope) :
    instantiate (bvar (Fin.succ position)) valueExpr =
      bvar position := by
  cases position with
  | mk index isLt => rfl

/-- Weakening maps a bound variable to its successor position. -/
theorem weaken_bvar {level scope : Nat}
    (position : Fin scope) :
    weaken (level := level) (bvar position) =
      bvar (Fin.succ position) := by
  cases position with
  | mk index isLt => rfl

end Expr

end LeanKernel
end LeanFX2

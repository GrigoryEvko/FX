prelude
import LeanFX2.FX1.Core.Expr

/-! # FX1/Core/Substitution

Root status: Root-FX1 metatheory scaffold.

Renaming and substitution for the minimal de Bruijn lambda-Pi core.  This file
contains executable structural operations only; identity, composition,
interaction, and beta-substitution lemmas are the next M2 obligations.
-/

namespace LeanFX2.FX1

/-- De Bruijn variable renaming for FX1 expressions. -/
abbrev Renaming : Type :=
  Nat -> Nat

namespace Renaming

/-- Identity renaming. -/
def identity : Renaming :=
  fun index => index

/-- Weakening renaming that shifts every variable through one new binder. -/
def shift : Renaming :=
  fun index => Nat.succ index

/-- Lift a renaming under one binder. -/
def lift (variableRenaming : Renaming) : Renaming :=
  fun
  | Nat.zero => Nat.zero
  | Nat.succ index => Nat.succ (variableRenaming index)

end Renaming

namespace Expr

/-- Rename de Bruijn variables in an FX1 expression. -/
def rename (variableRenaming : Renaming) : Expr -> Expr :=
  fun
  | Expr.bvar index => Expr.bvar (variableRenaming index)
  | Expr.sort sortLevel => Expr.sort sortLevel
  | Expr.const constName => Expr.const constName
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi
        (Expr.rename variableRenaming domainExpr)
        (Expr.rename (Renaming.lift variableRenaming) bodyExpr)
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam
        (Expr.rename variableRenaming domainExpr)
        (Expr.rename (Renaming.lift variableRenaming) bodyExpr)
  | Expr.app functionExpr argumentExpr =>
      Expr.app
        (Expr.rename variableRenaming functionExpr)
        (Expr.rename variableRenaming argumentExpr)

/-- Weaken an expression through one new surrounding binder. -/
def weaken (expression : Expr) : Expr :=
  Expr.rename Renaming.shift expression

end Expr

/-- De Bruijn substitution for FX1 expressions. -/
abbrev Substitution : Type :=
  Nat -> Expr

namespace Substitution

/-- Identity substitution. -/
def identity : Substitution :=
  fun index => Expr.bvar index

/-- Lift a substitution under one binder. -/
def lift (substitution : Substitution) : Substitution :=
  fun
  | Nat.zero => Expr.bvar Nat.zero
  | Nat.succ index => Expr.weaken (substitution index)

/-- Substitute the newest variable with `replacement`, dropping older indices
through the removed binder. -/
def singleton (replacement : Expr) : Substitution :=
  fun
  | Nat.zero => replacement
  | Nat.succ index => Expr.bvar index

end Substitution

namespace Expr

/-- Substitute de Bruijn variables in an FX1 expression. -/
def subst (substitution : Substitution) : Expr -> Expr :=
  fun
  | Expr.bvar index => substitution index
  | Expr.sort sortLevel => Expr.sort sortLevel
  | Expr.const constName => Expr.const constName
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi
        (Expr.subst substitution domainExpr)
        (Expr.subst (Substitution.lift substitution) bodyExpr)
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam
        (Expr.subst substitution domainExpr)
        (Expr.subst (Substitution.lift substitution) bodyExpr)
  | Expr.app functionExpr argumentExpr =>
      Expr.app
        (Expr.subst substitution functionExpr)
        (Expr.subst substitution argumentExpr)

/-- Substitute the newest variable in an expression. -/
def subst0 (replacement expression : Expr) : Expr :=
  Expr.subst (Substitution.singleton replacement) expression

end Expr

end LeanFX2.FX1

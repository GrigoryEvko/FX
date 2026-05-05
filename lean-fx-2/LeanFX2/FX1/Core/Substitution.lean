prelude
import Init.Prelude
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

/-- Pointwise extensionality for lifted renamings. -/
theorem lift_ext
    {firstRenaming secondRenaming : Renaming}
    (renamingsAgree : forall index : Nat,
      Eq (firstRenaming index) (secondRenaming index))
    (index : Nat) :
    Eq (lift firstRenaming index) (lift secondRenaming index) :=
  match index with
  | Nat.zero => Eq.refl (lift firstRenaming Nat.zero)
  | Nat.succ smallerIndex =>
      congrArg Nat.succ (renamingsAgree smallerIndex)

/-- Lifting the identity renaming is pointwise identity. -/
theorem lift_identity_apply (index : Nat) :
    Eq (lift identity index) (identity index) :=
  match index with
  | Nat.zero => Eq.refl (identity Nat.zero)
  | Nat.succ smallerIndex => Eq.refl (identity (Nat.succ smallerIndex))

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

/-- Congruence for the `pi` expression constructor. -/
theorem pi_congr
    {firstDomain secondDomain firstBody secondBody : Expr}
    (domainEquality : Eq firstDomain secondDomain)
    (bodyEquality : Eq firstBody secondBody) :
    Eq (Expr.pi firstDomain firstBody) (Expr.pi secondDomain secondBody) :=
  Eq.trans
    (congrArg (fun domainExpr => Expr.pi domainExpr firstBody)
      domainEquality)
    (congrArg (fun bodyExpr => Expr.pi secondDomain bodyExpr)
      bodyEquality)

/-- Congruence for the `lam` expression constructor. -/
theorem lam_congr
    {firstDomain secondDomain firstBody secondBody : Expr}
    (domainEquality : Eq firstDomain secondDomain)
    (bodyEquality : Eq firstBody secondBody) :
    Eq (Expr.lam firstDomain firstBody) (Expr.lam secondDomain secondBody) :=
  Eq.trans
    (congrArg (fun domainExpr => Expr.lam domainExpr firstBody)
      domainEquality)
    (congrArg (fun bodyExpr => Expr.lam secondDomain bodyExpr)
      bodyEquality)

/-- Congruence for the `app` expression constructor. -/
theorem app_congr
    {firstFunction secondFunction firstArgument secondArgument : Expr}
    (functionEquality : Eq firstFunction secondFunction)
    (argumentEquality : Eq firstArgument secondArgument) :
    Eq
      (Expr.app firstFunction firstArgument)
      (Expr.app secondFunction secondArgument) :=
  Eq.trans
    (congrArg (fun functionExpr => Expr.app functionExpr firstArgument)
      functionEquality)
    (congrArg (fun argumentExpr => Expr.app secondFunction argumentExpr)
      argumentEquality)

/-- Renaming respects pointwise equality of variable maps. -/
theorem rename_ext
    {firstRenaming secondRenaming : Renaming}
    (renamingsAgree : forall index : Nat,
      Eq (firstRenaming index) (secondRenaming index)) :
    forall expression : Expr,
      Eq (rename firstRenaming expression) (rename secondRenaming expression)
  | Expr.bvar index =>
      congrArg Expr.bvar (renamingsAgree index)
  | Expr.sort sortLevel =>
      Eq.refl (rename firstRenaming (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl (rename firstRenaming (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (rename_ext renamingsAgree domainExpr)
        (rename_ext (Renaming.lift_ext renamingsAgree) bodyExpr)
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (rename_ext renamingsAgree domainExpr)
        (rename_ext (Renaming.lift_ext renamingsAgree) bodyExpr)
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (rename_ext renamingsAgree functionExpr)
        (rename_ext renamingsAgree argumentExpr)

/-- Renaming by identity preserves an expression. -/
theorem rename_identity : forall expression : Expr,
    Eq (rename Renaming.identity expression) expression
  | Expr.bvar index => Eq.refl (Expr.bvar index)
  | Expr.sort sortLevel => Eq.refl (Expr.sort sortLevel)
  | Expr.const constName => Eq.refl (Expr.const constName)
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (rename_identity domainExpr)
        (Eq.trans
          (rename_ext Renaming.lift_identity_apply bodyExpr)
          (rename_identity bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (rename_identity domainExpr)
        (Eq.trans
          (rename_ext Renaming.lift_identity_apply bodyExpr)
          (rename_identity bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (rename_identity functionExpr)
        (rename_identity argumentExpr)

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

/-- Pointwise extensionality for lifted substitutions. -/
theorem lift_ext
    {firstSubstitution secondSubstitution : Substitution}
    (substitutionsAgree : forall index : Nat,
      Eq (firstSubstitution index) (secondSubstitution index))
    (index : Nat) :
    Eq (lift firstSubstitution index) (lift secondSubstitution index) :=
  match index with
  | Nat.zero => Eq.refl (lift firstSubstitution Nat.zero)
  | Nat.succ smallerIndex =>
      congrArg Expr.weaken (substitutionsAgree smallerIndex)

/-- Lifting the identity substitution is pointwise identity. -/
theorem lift_identity_apply (index : Nat) :
    Eq (lift identity index) (identity index) :=
  match index with
  | Nat.zero => Eq.refl (identity Nat.zero)
  | Nat.succ smallerIndex => Eq.refl (identity (Nat.succ smallerIndex))

/-- The singleton substitution maps the newest variable to its replacement. -/
theorem singleton_newest (replacement : Expr) :
    Eq (singleton replacement Nat.zero) replacement :=
  Eq.refl replacement

/-- The singleton substitution drops one binder from older variables. -/
theorem singleton_older (replacement : Expr) (index : Nat) :
    Eq (singleton replacement (Nat.succ index)) (Expr.bvar index) :=
  Eq.refl (Expr.bvar index)

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

/-- Substitution respects pointwise equality of variable substitutions. -/
theorem subst_ext
    {firstSubstitution secondSubstitution : Substitution}
    (substitutionsAgree : forall index : Nat,
      Eq (firstSubstitution index) (secondSubstitution index)) :
    forall expression : Expr,
      Eq
        (subst firstSubstitution expression)
        (subst secondSubstitution expression)
  | Expr.bvar index => substitutionsAgree index
  | Expr.sort sortLevel =>
      Eq.refl (subst firstSubstitution (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl (subst firstSubstitution (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (subst_ext substitutionsAgree domainExpr)
        (subst_ext (Substitution.lift_ext substitutionsAgree) bodyExpr)
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (subst_ext substitutionsAgree domainExpr)
        (subst_ext (Substitution.lift_ext substitutionsAgree) bodyExpr)
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (subst_ext substitutionsAgree functionExpr)
        (subst_ext substitutionsAgree argumentExpr)

/-- Substitution by identity preserves an expression. -/
theorem subst_identity : forall expression : Expr,
    Eq (subst Substitution.identity expression) expression
  | Expr.bvar index => Eq.refl (Expr.bvar index)
  | Expr.sort sortLevel => Eq.refl (Expr.sort sortLevel)
  | Expr.const constName => Eq.refl (Expr.const constName)
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (subst_identity domainExpr)
        (Eq.trans
          (subst_ext Substitution.lift_identity_apply bodyExpr)
          (subst_identity bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (subst_identity domainExpr)
        (Eq.trans
          (subst_ext Substitution.lift_identity_apply bodyExpr)
          (subst_identity bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (subst_identity functionExpr)
        (subst_identity argumentExpr)

/-- `subst0` fires on the newest variable. -/
theorem subst0_bvar_zero (replacement : Expr) :
    Eq (subst0 replacement (Expr.bvar Nat.zero)) replacement :=
  Eq.refl replacement

/-- `subst0` drops one binder from older variables. -/
theorem subst0_bvar_succ (replacement : Expr) (index : Nat) :
    Eq (subst0 replacement (Expr.bvar (Nat.succ index))) (Expr.bvar index) :=
  Eq.refl (Expr.bvar index)

end Expr

end LeanFX2.FX1

prelude
import LeanFX2.FX1.Core.Expr

/-! # FX1/Core/Substitution

Root status: Root-FX1 metatheory scaffold.

Renaming and substitution for the minimal de Bruijn lambda-Pi core.  This file
contains executable structural operations plus the first M2 identity and
composition facts.  Beta-substitution lemmas and preservation-oriented
well-scopedness facts are the remaining M2 obligations.
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

/-- Compose two renamings, applying `innerRenaming` first and then
`outerRenaming`. -/
def compose (outerRenaming innerRenaming : Renaming) : Renaming :=
  fun index => outerRenaming (innerRenaming index)

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

/-- Left identity for renaming composition, pointwise. -/
theorem compose_identity_left_apply
    (variableRenaming : Renaming) (index : Nat) :
    Eq (compose identity variableRenaming index) (variableRenaming index) :=
  Eq.refl (variableRenaming index)

/-- Right identity for renaming composition, pointwise. -/
theorem compose_identity_right_apply
    (variableRenaming : Renaming) (index : Nat) :
    Eq (compose variableRenaming identity index) (variableRenaming index) :=
  Eq.refl (variableRenaming index)

/-- Lifting distributes over renaming composition, pointwise. -/
theorem compose_lift_apply
    (outerRenaming innerRenaming : Renaming) (index : Nat) :
    Eq
      (compose (lift outerRenaming) (lift innerRenaming) index)
      (lift (compose outerRenaming innerRenaming) index) :=
  match index with
  | Nat.zero =>
      Eq.refl
        (lift (compose outerRenaming innerRenaming) Nat.zero)
  | Nat.succ smallerIndex =>
      Eq.refl
        (lift (compose outerRenaming innerRenaming)
          (Nat.succ smallerIndex))

/-- Shifting after a renaming agrees pointwise with lifting that renaming
after shifting. -/
theorem compose_shift_lift_apply
    (variableRenaming : Renaming) (index : Nat) :
    Eq
      (compose shift variableRenaming index)
      (compose (lift variableRenaming) shift index) :=
  Eq.refl (compose shift variableRenaming index)

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

/-- Sequential renaming is equivalent to renaming by the composed variable
map. -/
theorem rename_compose
    (outerRenaming innerRenaming : Renaming) :
    forall expression : Expr,
      Eq
        (rename outerRenaming (rename innerRenaming expression))
        (rename (Renaming.compose outerRenaming innerRenaming) expression)
  | Expr.bvar index =>
      Eq.refl
        (Expr.bvar (Renaming.compose outerRenaming innerRenaming index))
  | Expr.sort sortLevel =>
      Eq.refl
        (rename
          (Renaming.compose outerRenaming innerRenaming)
          (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl
        (rename
          (Renaming.compose outerRenaming innerRenaming)
          (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (rename_compose outerRenaming innerRenaming domainExpr)
        (Eq.trans
          (rename_compose
            (Renaming.lift outerRenaming)
            (Renaming.lift innerRenaming)
            bodyExpr)
          (rename_ext
            (Renaming.compose_lift_apply outerRenaming innerRenaming)
            bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (rename_compose outerRenaming innerRenaming domainExpr)
        (Eq.trans
          (rename_compose
            (Renaming.lift outerRenaming)
            (Renaming.lift innerRenaming)
            bodyExpr)
          (rename_ext
            (Renaming.compose_lift_apply outerRenaming innerRenaming)
            bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (rename_compose outerRenaming innerRenaming functionExpr)
        (rename_compose outerRenaming innerRenaming argumentExpr)

/-- Weakening after a renaming agrees with renaming after weakening by the
lifted variable map. -/
theorem rename_shift_lift_commute
    (variableRenaming : Renaming) :
    forall expression : Expr,
      Eq
        (rename Renaming.shift (rename variableRenaming expression))
        (rename (Renaming.lift variableRenaming)
          (rename Renaming.shift expression)) :=
  fun expression =>
    Eq.trans
      (rename_compose Renaming.shift variableRenaming expression)
      (Eq.trans
        (rename_ext
          (Renaming.compose_shift_lift_apply variableRenaming)
          expression)
        (Eq.symm
          (rename_compose
            (Renaming.lift variableRenaming)
            Renaming.shift
            expression)))

end Expr

/-- De Bruijn substitution for FX1 expressions. -/
abbrev Substitution : Type :=
  Nat -> Expr

namespace Substitution

/-- Identity substitution. -/
def identity : Substitution :=
  fun index => Expr.bvar index

/-- Embed a renaming as a substitution that maps each variable to a variable. -/
def ofRenaming (variableRenaming : Renaming) : Substitution :=
  fun index => Expr.bvar (variableRenaming index)

/-- Post-compose every substituted expression with a renaming. -/
def renameOutput
    (variableRenaming : Renaming) (substitution : Substitution) :
    Substitution :=
  fun index => Expr.rename variableRenaming (substitution index)

/-- Pre-compose a substitution's variable input with a renaming. -/
def renameInput
    (substitution : Substitution) (variableRenaming : Renaming) :
    Substitution :=
  fun index => substitution (variableRenaming index)

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

/-- The identity renaming embeds as the identity substitution, pointwise. -/
theorem ofRenaming_identity_apply (index : Nat) :
    Eq (ofRenaming Renaming.identity index) (identity index) :=
  Eq.refl (identity index)

/-- Lifting an embedded renaming agrees with embedding the lifted renaming,
pointwise. -/
theorem lift_ofRenaming_apply
    (variableRenaming : Renaming) (index : Nat) :
    Eq
      (lift (ofRenaming variableRenaming) index)
      (ofRenaming (Renaming.lift variableRenaming) index) :=
  match index with
  | Nat.zero =>
      Eq.refl (ofRenaming (Renaming.lift variableRenaming) Nat.zero)
  | Nat.succ smallerIndex =>
      Eq.refl
        (ofRenaming
          (Renaming.lift variableRenaming)
          (Nat.succ smallerIndex))

/-- Lifting commutes with post-renaming substituted expressions. -/
theorem lift_renameOutput_apply
    (variableRenaming : Renaming) (substitution : Substitution)
    (index : Nat) :
    Eq
      (lift (renameOutput variableRenaming substitution) index)
      (renameOutput (Renaming.lift variableRenaming)
        (lift substitution) index) :=
  match index with
  | Nat.zero =>
      Eq.refl
        (renameOutput (Renaming.lift variableRenaming)
          (lift substitution) Nat.zero)
  | Nat.succ smallerIndex =>
      Expr.rename_shift_lift_commute
        variableRenaming
        (substitution smallerIndex)

/-- Lifting commutes with pre-renaming substitution inputs. -/
theorem lift_renameInput_apply
    (substitution : Substitution) (variableRenaming : Renaming)
    (index : Nat) :
    Eq
      (lift (renameInput substitution variableRenaming) index)
      (renameInput (lift substitution) (Renaming.lift variableRenaming)
        index) :=
  match index with
  | Nat.zero =>
      Eq.refl
        (renameInput (lift substitution) (Renaming.lift variableRenaming)
          Nat.zero)
  | Nat.succ smallerIndex =>
      Eq.refl
        (renameInput (lift substitution) (Renaming.lift variableRenaming)
          (Nat.succ smallerIndex))

/-- Pre-renaming by shift after lifting agrees with post-renaming outputs by
shift. -/
theorem renameInput_lift_shift_apply
    (substitution : Substitution) (index : Nat) :
    Eq
      (renameInput (lift substitution) Renaming.shift index)
      (renameOutput Renaming.shift substitution index) :=
  Eq.refl (renameOutput Renaming.shift substitution index)

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

end Expr

namespace Substitution

/-- Compose two substitutions, applying `innerSubstitution` first and then
substituting the result through `outerSubstitution`. -/
def compose
    (outerSubstitution innerSubstitution : Substitution) :
    Substitution :=
  fun index => Expr.subst outerSubstitution (innerSubstitution index)

end Substitution

namespace Expr

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

/-- Substitution by the variable embedding of a renaming is exactly renaming. -/
theorem subst_ofRenaming
    (variableRenaming : Renaming) :
    forall expression : Expr,
      Eq
        (subst (Substitution.ofRenaming variableRenaming) expression)
        (rename variableRenaming expression)
  | Expr.bvar index =>
      Eq.refl (rename variableRenaming (Expr.bvar index))
  | Expr.sort sortLevel =>
      Eq.refl (rename variableRenaming (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl (rename variableRenaming (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (subst_ofRenaming variableRenaming domainExpr)
        (Eq.trans
          (subst_ext
            (Substitution.lift_ofRenaming_apply variableRenaming)
            bodyExpr)
          (subst_ofRenaming
            (Renaming.lift variableRenaming)
            bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (subst_ofRenaming variableRenaming domainExpr)
        (Eq.trans
          (subst_ext
            (Substitution.lift_ofRenaming_apply variableRenaming)
            bodyExpr)
          (subst_ofRenaming
            (Renaming.lift variableRenaming)
            bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (subst_ofRenaming variableRenaming functionExpr)
        (subst_ofRenaming variableRenaming argumentExpr)

/-- Renaming after substitution is substitution with post-renamed outputs. -/
theorem rename_subst_commute
    (variableRenaming : Renaming) (substitution : Substitution) :
    forall expression : Expr,
      Eq
        (rename variableRenaming (subst substitution expression))
        (subst (Substitution.renameOutput variableRenaming substitution)
          expression)
  | Expr.bvar index =>
      Eq.refl
        (Substitution.renameOutput variableRenaming substitution index)
  | Expr.sort sortLevel =>
      Eq.refl
        (subst
          (Substitution.renameOutput variableRenaming substitution)
          (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl
        (subst
          (Substitution.renameOutput variableRenaming substitution)
          (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (rename_subst_commute variableRenaming substitution domainExpr)
        (Eq.trans
          (rename_subst_commute
            (Renaming.lift variableRenaming)
            (Substitution.lift substitution)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_renameOutput_apply
                  variableRenaming substitution index))
            bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (rename_subst_commute variableRenaming substitution domainExpr)
        (Eq.trans
          (rename_subst_commute
            (Renaming.lift variableRenaming)
            (Substitution.lift substitution)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_renameOutput_apply
                  variableRenaming substitution index))
            bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (rename_subst_commute variableRenaming substitution functionExpr)
        (rename_subst_commute variableRenaming substitution argumentExpr)

/-- Substitution after renaming is substitution with pre-renamed inputs. -/
theorem subst_rename_commute
    (substitution : Substitution) (variableRenaming : Renaming) :
    forall expression : Expr,
      Eq
        (subst substitution (rename variableRenaming expression))
        (subst (Substitution.renameInput substitution variableRenaming)
          expression)
  | Expr.bvar index =>
      Eq.refl
        (Substitution.renameInput substitution variableRenaming index)
  | Expr.sort sortLevel =>
      Eq.refl
        (subst
          (Substitution.renameInput substitution variableRenaming)
          (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl
        (subst
          (Substitution.renameInput substitution variableRenaming)
          (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (subst_rename_commute substitution variableRenaming domainExpr)
        (Eq.trans
          (subst_rename_commute
            (Substitution.lift substitution)
            (Renaming.lift variableRenaming)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_renameInput_apply
                  substitution variableRenaming index))
            bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (subst_rename_commute substitution variableRenaming domainExpr)
        (Eq.trans
          (subst_rename_commute
            (Substitution.lift substitution)
            (Renaming.lift variableRenaming)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_renameInput_apply
                  substitution variableRenaming index))
            bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (subst_rename_commute substitution variableRenaming functionExpr)
        (subst_rename_commute substitution variableRenaming argumentExpr)

end Expr

namespace Substitution

/-- Lifting distributes over substitution composition, pointwise. -/
theorem lift_compose_apply
    (outerSubstitution innerSubstitution : Substitution)
    (index : Nat) :
    Eq
      (lift (compose outerSubstitution innerSubstitution) index)
      (compose (lift outerSubstitution) (lift innerSubstitution) index) :=
  match index with
  | Nat.zero =>
      show Eq (Expr.bvar Nat.zero) (Expr.bvar Nat.zero) from
        Eq.refl (Expr.bvar Nat.zero)
  | Nat.succ smallerIndex =>
      show
        Eq
          (Expr.rename Renaming.shift
            (Expr.subst outerSubstitution
              (innerSubstitution smallerIndex)))
          (Expr.subst
            (lift outerSubstitution)
            (Expr.rename Renaming.shift
              (innerSubstitution smallerIndex))) from
      let leftToOutputRenamed :
          Eq
            (Expr.rename Renaming.shift
              (Expr.subst outerSubstitution
                (innerSubstitution smallerIndex)))
            (Expr.subst
              (renameOutput Renaming.shift outerSubstitution)
              (innerSubstitution smallerIndex)) :=
        Expr.rename_subst_commute
          Renaming.shift
          outerSubstitution
          (innerSubstitution smallerIndex)
      let rightToInputRenamed :
          Eq
            (Expr.subst
              (lift outerSubstitution)
              (Expr.rename Renaming.shift
                (innerSubstitution smallerIndex)))
            (Expr.subst
              (renameInput (lift outerSubstitution) Renaming.shift)
              (innerSubstitution smallerIndex)) :=
        Expr.subst_rename_commute
          (lift outerSubstitution)
          Renaming.shift
          (innerSubstitution smallerIndex)
      let rightToOutputRenamed :
          Eq
            (Expr.subst
              (lift outerSubstitution)
              (Expr.rename Renaming.shift
                (innerSubstitution smallerIndex)))
            (Expr.subst
              (renameOutput Renaming.shift outerSubstitution)
              (innerSubstitution smallerIndex)) :=
        Eq.trans
          rightToInputRenamed
          (Expr.subst_ext
            (renameInput_lift_shift_apply outerSubstitution)
            (innerSubstitution smallerIndex))
      Eq.trans leftToOutputRenamed (Eq.symm rightToOutputRenamed)

/-- Composing after identity on the left is pointwise identity. -/
theorem compose_identity_left_apply
    (substitution : Substitution) (index : Nat) :
    Eq (compose identity substitution index) (substitution index) :=
  show Eq (Expr.subst identity (substitution index)) (substitution index) from
    Expr.subst_identity (substitution index)

/-- Composing after identity on the right is pointwise identity. -/
theorem compose_identity_right_apply
    (substitution : Substitution) (index : Nat) :
    Eq (compose substitution identity index) (substitution index) :=
  show Eq (Expr.subst substitution (Expr.bvar index)) (substitution index) from
    Eq.refl (substitution index)

end Substitution

namespace Expr

/-- Sequential substitution is equivalent to substitution by the composed
substitution. -/
theorem subst_compose
    (outerSubstitution innerSubstitution : Substitution) :
    forall expression : Expr,
      Eq
        (subst outerSubstitution (subst innerSubstitution expression))
        (subst
          (Substitution.compose outerSubstitution innerSubstitution)
          expression)
  | Expr.bvar index =>
      show
        Eq
          (subst outerSubstitution (innerSubstitution index))
          (subst outerSubstitution (innerSubstitution index)) from
        Eq.refl
          (subst outerSubstitution (innerSubstitution index))
  | Expr.sort sortLevel =>
      Eq.refl
        (subst
          (Substitution.compose outerSubstitution innerSubstitution)
          (Expr.sort sortLevel))
  | Expr.const constName =>
      Eq.refl
        (subst
          (Substitution.compose outerSubstitution innerSubstitution)
          (Expr.const constName))
  | Expr.pi domainExpr bodyExpr =>
      Expr.pi_congr
        (subst_compose outerSubstitution innerSubstitution domainExpr)
        (Eq.trans
          (subst_compose
            (Substitution.lift outerSubstitution)
            (Substitution.lift innerSubstitution)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_compose_apply
                  outerSubstitution innerSubstitution index))
            bodyExpr))
  | Expr.lam domainExpr bodyExpr =>
      Expr.lam_congr
        (subst_compose outerSubstitution innerSubstitution domainExpr)
        (Eq.trans
          (subst_compose
            (Substitution.lift outerSubstitution)
            (Substitution.lift innerSubstitution)
            bodyExpr)
          (subst_ext
            (fun index =>
              Eq.symm
                (Substitution.lift_compose_apply
                  outerSubstitution innerSubstitution index))
            bodyExpr))
  | Expr.app functionExpr argumentExpr =>
      Expr.app_congr
        (subst_compose outerSubstitution innerSubstitution functionExpr)
        (subst_compose outerSubstitution innerSubstitution argumentExpr)

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

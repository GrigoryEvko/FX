import LeanFX2.Tools.StrictHarness.Common

/-! # LeanFX2.Tools.StrictHarness.Census.ModeDiscipline

Constructor-census budget gate for mode-sensitive constructors that
still accept arbitrary `Mode` instead of requiring a strict-fragment
or univalent-fragment equality premise.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Mode-discipline budget check -/

/-- Required mode for constructors that should not be available in every mode. -/
inductive RequiredMode : Type
  /-- Constructor should be restricted to the strict fragment. -/
  | strict : RequiredMode
  /-- Constructor should be restricted to the univalent/cubical fragment. -/
  | univalent : RequiredMode
  deriving Inhabited, Repr

namespace RequiredMode

/-- The concrete `Mode` constructor that witnesses this requirement. -/
def modeConstructorName : RequiredMode → Name
  | .strict => `LeanFX2.Mode.strict
  | .univalent => `LeanFX2.Mode.univalent

/-- Human-readable name for diagnostics. -/
def format : RequiredMode → String
  | .strict => "Mode.strict"
  | .univalent => "Mode.univalent"

end RequiredMode

/-- Whether an expression mentions a specific constant anywhere inside it. -/
partial def doesExprMentionConst (targetName : Name) : Expr → Bool
  | .const constantName _ => constantName == targetName
  | .app functionExpr argumentExpr =>
      doesExprMentionConst targetName functionExpr ||
        doesExprMentionConst targetName argumentExpr
  | .lam _ parameterType bodyType _ =>
      doesExprMentionConst targetName parameterType ||
        doesExprMentionConst targetName bodyType
  | .forallE _ parameterType bodyType _ =>
      doesExprMentionConst targetName parameterType ||
        doesExprMentionConst targetName bodyType
  | .letE _ typeExpr valueExpr bodyExpr _ =>
      doesExprMentionConst targetName typeExpr ||
        doesExprMentionConst targetName valueExpr ||
        doesExprMentionConst targetName bodyExpr
  | .mdata _ bodyExpr => doesExprMentionConst targetName bodyExpr
  | .proj _ _ bodyExpr => doesExprMentionConst targetName bodyExpr
  | _ => false

/-- Whether a parameter type is an equality premise to the required mode. -/
def isModeRequirementEquality
    (requiredMode : RequiredMode) (parameterType : Expr) :
    Bool :=
  match parameterType.getAppFn with
  | .const equalityName _ =>
      equalityName == `Eq &&
        doesExprMentionConst requiredMode.modeConstructorName parameterType
  | _ => false

/-- Detect whether a constructor type already carries the required mode proof. -/
partial def hasRequiredModePremise
    (requiredMode : RequiredMode) (constructorType : Expr) :
    Bool :=
  match constructorType with
  | .forallE _ parameterType bodyType _ =>
      isModeRequirementEquality requiredMode parameterType ||
        hasRequiredModePremise requiredMode bodyType
  | _ => false

/-- Expected mode restriction for the current known mode-sensitive Term ctors. -/
def requiredModeForConstructor? (constructorName : Name) :
    Option RequiredMode :=
  let suffix := Name.lastSegmentString constructorName
  if suffix == "idStrictRefl" ||
      suffix == "idStrictRec" then
    some RequiredMode.strict
  else if suffix == "pathLam" ||
      suffix == "pathApp" ||
      suffix == "glueIntro" ||
      suffix == "glueElim" ||
      suffix == "transp" ||
      suffix == "hcomp" then
    some RequiredMode.univalent
  else
    none

/-- One constructor whose mode-sensitive typing still accepts arbitrary mode. -/
structure ModeDisciplineDebtRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Mode the constructor should require. -/
  requiredMode : RequiredMode
  deriving Inhabited, Repr

/-- Report a mode-sensitive constructor if it lacks the required mode premise. -/
def modeDisciplineDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option ModeDisciplineDebtRecord :=
  match requiredModeForConstructor? constructorName, environment.find? constructorName with
  | some requiredMode, some (.ctorInfo constructorInfo) =>
      if hasRequiredModePremise requiredMode constructorInfo.type then
        none
      else
        some {
          constructorName := constructorName
          requiredMode := requiredMode
        }
  | _, _ => none

/-- Collect mode-discipline debt records for every constructor of an inductive. -/
def modeDisciplineDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array ModeDisciplineDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array ModeDisciplineDebtRecord))
    (fun records constructorName =>
      match modeDisciplineDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for constructors that should be mode-restricted
but currently accept arbitrary mode.  The budget is a ceiling over known debt:
as ctors gain real mode premises the count should fall, and new unrestricted
mode-sensitive ctors must deliberately revise this number. -/
elab "#assert_mode_discipline_budget " inductiveSyntax:ident
    modeDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let modeDebtBudget := modeDebtBudgetSyntax.getNat
  let records := modeDisciplineDebtRecordsForInductive environment inductiveName
  if records.size <= modeDebtBudget then
    let successMessage :=
      s!"mode discipline budget ok: {inductiveName} " ++
      s!"({records.size}/{modeDebtBudget} mode-sensitive ctors lack " ++
      "mode equality premises)"
    logInfo successMessage
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: expected {record.requiredMode.format} equality premise"
    let header :=
      s!"mode discipline budget FAILED for {inductiveName}: " ++
      s!"{records.size} unrestricted mode-sensitive ctors exceed budget " ++
      s!"{modeDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

end LeanFX2.Tools

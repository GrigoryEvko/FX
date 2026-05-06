import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Bool

Root status: Bridge.

Closed Bool bridge fragment.  This file stages the rich Bool type and its two
canonical values as object-level FX1 declarations, then proves that the empty
rich-context true/false terms encode to well-typed FX1 constants.

The staged declarations are `axiomDecl` placeholders, so this is Bridge
evidence only.  It does not claim Bool is a Root-FX1 primitive or that a
general recursive encoder is complete.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged FX1 Bool type name. -/
def boolTypeAtomId : Nat := 3

/-- Native atom id used for the staged FX1 Bool true value name. -/
def boolTrueAtomId : Nat := 4

/-- Native atom id used for the staged FX1 Bool false value name. -/
def boolFalseAtomId : Nat := 5

/-- FX1 name for the rich Bool type constant. -/
def boolTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous boolTypeAtomId

/-- FX1 name for the rich Bool true constant. -/
def boolTrueName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous boolTrueAtomId

/-- FX1 name for the rich Bool false constant. -/
def boolFalseName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous boolFalseAtomId

/-- FX1 expression encoding the rich Bool type. -/
def boolTypeExpr : FX1.Expr :=
  FX1.Expr.const boolTypeName

/-- FX1 expression encoding the rich Bool true value. -/
def boolTrueExpr : FX1.Expr :=
  FX1.Expr.const boolTrueName

/-- FX1 expression encoding the rich Bool false value. -/
def boolFalseExpr : FX1.Expr :=
  FX1.Expr.const boolFalseName

/-- Staged FX1 declaration for the rich Bool type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def boolTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl boolTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the rich Bool true value.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def boolTrueDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl boolTrueName boolTypeExpr

/-- Staged FX1 declaration for the rich Bool false value.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def boolFalseDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl boolFalseName boolTypeExpr

/-- Environment after declaring the rich Bool type constant. -/
def boolTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend FX1.Environment.empty boolTypeDeclaration

/-- Environment after declaring the rich Bool true constant. -/
def boolTrueEnvironment : FX1.Environment :=
  FX1.Environment.extend boolTypeEnvironment boolTrueDeclaration

/-- Staged bridge environment for the Bool fragment. -/
def boolEnvironment : FX1.Environment :=
  FX1.Environment.extend boolTrueEnvironment boolFalseDeclaration

/-- Bool-only type encoder for this bridge fragment. -/
def encodeTy_bool : FX1.Expr :=
  boolTypeExpr

/-- Bool true raw-term encoder for this bridge fragment. -/
def encodeRawTerm_boolTrue : FX1.Expr :=
  boolTrueExpr

/-- Bool false raw-term encoder for this bridge fragment. -/
def encodeRawTerm_boolFalse : FX1.Expr :=
  boolFalseExpr

/-- Bool type encoding computes to the staged FX1 Bool type constant. -/
theorem encodeTy_bool_eq_boolTypeExpr :
    Eq encodeTy_bool boolTypeExpr :=
  Eq.refl boolTypeExpr

/-- Bool true raw-term encoding computes to the staged FX1 true constant. -/
theorem encodeRawTerm_boolTrue_eq_boolTrueExpr :
    Eq encodeRawTerm_boolTrue boolTrueExpr :=
  Eq.refl boolTrueExpr

/-- Bool false raw-term encoding computes to the staged FX1 false constant. -/
theorem encodeRawTerm_boolFalse_eq_boolFalseExpr :
    Eq encodeRawTerm_boolFalse boolFalseExpr :=
  Eq.refl boolFalseExpr

/-- The staged Bool type declaration is well typed in the empty FX1
environment. -/
theorem boolTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      FX1.Environment.empty
      boolTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged Bool true declaration is well typed after the Bool type
constant is available. -/
theorem boolTrueDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      boolTypeEnvironment
      boolTrueDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        boolTypeDeclaration))

/-- The staged Bool false declaration is well typed after Bool and true are
available. -/
theorem boolFalseDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      boolTrueEnvironment
      boolFalseDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.older
        boolTrueDeclaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          boolTypeDeclaration)))

/-- The staged Bool type environment is well formed. -/
theorem boolTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed boolTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    FX1.Environment.WellFormed.empty
    (FX1.Environment.NameFresh.empty boolTypeName)
    boolTypeDeclaration_wellTyped

/-- The staged true name is distinct from the staged Bool type name. -/
theorem boolTrueName_ne_boolTypeName :
    Not (Eq boolTrueName boolTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq boolTrueName) namesEqual
    nomatch boolEquality

/-- The staged false name is distinct from the staged Bool type name. -/
theorem boolFalseName_ne_boolTypeName :
    Not (Eq boolFalseName boolTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq boolFalseName) namesEqual
    nomatch boolEquality

/-- The staged false name is distinct from the staged true name. -/
theorem boolFalseName_ne_boolTrueName :
    Not (Eq boolFalseName boolTrueName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq boolFalseName) namesEqual
    nomatch boolEquality

/-- The staged true value name is fresh after the Bool type declaration. -/
theorem boolTrueName_fresh :
    FX1.Environment.NameFresh boolTypeEnvironment boolTrueName :=
  FX1.Environment.NameFresh.older
    boolTypeDeclaration
    (FX1.Environment.NameFresh.empty boolTrueName)
    boolTrueName_ne_boolTypeName

/-- The staged false value name is fresh after the Bool type and true
declarations. -/
theorem boolFalseName_fresh :
    FX1.Environment.NameFresh boolTrueEnvironment boolFalseName :=
  FX1.Environment.NameFresh.older
    boolTrueDeclaration
    (FX1.Environment.NameFresh.older
      boolTypeDeclaration
      (FX1.Environment.NameFresh.empty boolFalseName)
      boolFalseName_ne_boolTypeName)
    boolFalseName_ne_boolTrueName

/-- The staged Bool true environment is well formed. -/
theorem boolTrueEnvironment_wellFormed :
    FX1.Environment.WellFormed boolTrueEnvironment :=
  FX1.Environment.WellFormed.extend
    boolTypeEnvironment_wellFormed
    boolTrueName_fresh
    boolTrueDeclaration_wellTyped

/-- The staged Bool bridge environment is well formed. -/
theorem boolEnvironment_wellFormed :
    FX1.Environment.WellFormed boolEnvironment :=
  FX1.Environment.WellFormed.extend
    boolTrueEnvironment_wellFormed
    boolFalseName_fresh
    boolFalseDeclaration_wellTyped

/-- The staged Bool type constant has sort zero in the staged Bool
environment. -/
theorem boolTypeExpr_has_sort_in_boolEnvironment :
    FX1.HasType
      boolEnvironment
      FX1.Context.empty
      encodeTy_bool
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      boolFalseDeclaration
      (FX1.Environment.HasDeclaration.older
        boolTrueDeclaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          boolTypeDeclaration)))

/-- The encoded rich true value is well typed in the staged FX1 Bool
environment. -/
theorem encodedBoolTrue_has_type :
    FX1.HasType
      boolEnvironment
      FX1.Context.empty
      boolTrueExpr
      boolTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      boolFalseDeclaration
      (FX1.Environment.HasDeclaration.newest
        boolTypeEnvironment
        boolTrueDeclaration))

/-- The encoded rich false value is well typed in the staged FX1 Bool
environment. -/
theorem encodedBoolFalse_has_type :
    FX1.HasType
      boolEnvironment
      FX1.Context.empty
      boolFalseExpr
      boolTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      boolTrueEnvironment
      boolFalseDeclaration)

/-- Soundness of the empty-context Bool true bridge fragment. -/
theorem encodeTermSound_boolTrue
    {mode : Mode}
    {level : Nat}
    (_trueTerm : Term (Ctx.empty mode level) Ty.bool RawTerm.boolTrue) :
    FX1.HasType
      boolEnvironment
      FX1.Context.empty
      encodeRawTerm_boolTrue
      encodeTy_bool :=
  encodedBoolTrue_has_type

/-- Soundness of the empty-context Bool false bridge fragment. -/
theorem encodeTermSound_boolFalse
    {mode : Mode}
    {level : Nat}
    (_falseTerm : Term (Ctx.empty mode level) Ty.bool RawTerm.boolFalse) :
    FX1.HasType
      boolEnvironment
      FX1.Context.empty
      encodeRawTerm_boolFalse
      encodeTy_bool :=
  encodedBoolFalse_has_type

end FX1Bridge
end LeanFX2

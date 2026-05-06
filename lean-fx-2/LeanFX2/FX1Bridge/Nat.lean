import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Nat

Root status: Bridge.

Closed natural-number zero bridge fragment.  This file stages the rich Nat type
and its zero value as object-level FX1 declarations, then proves that the empty
rich-context `Term.natZero` encodes to a well-typed FX1 constant.

The staged declarations are `axiomDecl` placeholders, so this is Bridge
evidence only.  Successor and eliminator fragments are intentionally left for
later slices because they require function-shaped staged constants and
application-level evidence.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged FX1 Nat type name. -/
def natTypeAtomId : Nat := 6

/-- Native atom id used for the staged FX1 Nat zero value name. -/
def natZeroAtomId : Nat := 7

/-- FX1 name for the rich Nat type constant. -/
def natTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous natTypeAtomId

/-- FX1 name for the rich Nat zero constant. -/
def natZeroName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous natZeroAtomId

/-- FX1 expression encoding the rich Nat type. -/
def natTypeExpr : FX1.Expr :=
  FX1.Expr.const natTypeName

/-- FX1 expression encoding the rich Nat zero value. -/
def natZeroExpr : FX1.Expr :=
  FX1.Expr.const natZeroName

/-- Staged FX1 declaration for the rich Nat type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def natTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl natTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the rich Nat zero value.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def natZeroDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl natZeroName natTypeExpr

/-- Environment after declaring the rich Nat type constant. -/
def natTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend FX1.Environment.empty natTypeDeclaration

/-- Staged bridge environment for the Nat-zero fragment. -/
def natEnvironment : FX1.Environment :=
  FX1.Environment.extend natTypeEnvironment natZeroDeclaration

/-- Nat-only type encoder for this bridge fragment. -/
def encodeTy_nat : FX1.Expr :=
  natTypeExpr

/-- Nat-zero raw-term encoder for this bridge fragment. -/
def encodeRawTerm_natZero : FX1.Expr :=
  natZeroExpr

/-- Nat type encoding computes to the staged FX1 Nat type constant. -/
theorem encodeTy_nat_eq_natTypeExpr :
    Eq encodeTy_nat natTypeExpr :=
  Eq.refl natTypeExpr

/-- Nat-zero raw-term encoding computes to the staged FX1 zero constant. -/
theorem encodeRawTerm_natZero_eq_natZeroExpr :
    Eq encodeRawTerm_natZero natZeroExpr :=
  Eq.refl natZeroExpr

/-- The staged Nat type declaration is well typed in the empty FX1
environment. -/
theorem natTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      FX1.Environment.empty
      natTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged Nat zero declaration is well typed after the Nat type constant
is available. -/
theorem natZeroDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      natTypeEnvironment
      natZeroDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        natTypeDeclaration))

/-- The staged Nat type environment is well formed. -/
theorem natTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed natTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    FX1.Environment.WellFormed.empty
    (FX1.Environment.NameFresh.empty natTypeName)
    natTypeDeclaration_wellTyped

/-- The staged zero name is distinct from the staged Nat type name. -/
theorem natZeroName_ne_natTypeName :
    Not (Eq natZeroName natTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq natZeroName) namesEqual
    nomatch boolEquality

/-- The staged zero value name is fresh after the Nat type declaration. -/
theorem natZeroName_fresh :
    FX1.Environment.NameFresh natTypeEnvironment natZeroName :=
  FX1.Environment.NameFresh.older
    natTypeDeclaration
    (FX1.Environment.NameFresh.empty natZeroName)
    natZeroName_ne_natTypeName

/-- The staged Nat bridge environment is well formed. -/
theorem natEnvironment_wellFormed :
    FX1.Environment.WellFormed natEnvironment :=
  FX1.Environment.WellFormed.extend
    natTypeEnvironment_wellFormed
    natZeroName_fresh
    natZeroDeclaration_wellTyped

/-- The staged Nat type constant has sort zero in the staged Nat environment. -/
theorem natTypeExpr_has_sort_in_natEnvironment :
    FX1.HasType
      natEnvironment
      FX1.Context.empty
      encodeTy_nat
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      natZeroDeclaration
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        natTypeDeclaration))

/-- The encoded rich zero value is well typed in the staged FX1 Nat
environment. -/
theorem encodedNatZero_has_type :
    FX1.HasType
      natEnvironment
      FX1.Context.empty
      natZeroExpr
      natTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      natTypeEnvironment
      natZeroDeclaration)

/-- Soundness of the empty-context Nat-zero bridge fragment. -/
theorem encodeTermSound_natZero
    {mode : Mode}
    {level : Nat}
    (_zeroTerm : Term (Ctx.empty mode level) Ty.nat RawTerm.natZero) :
    FX1.HasType
      natEnvironment
      FX1.Context.empty
      encodeRawTerm_natZero
      encodeTy_nat :=
  encodedNatZero_has_type

end FX1Bridge
end LeanFX2

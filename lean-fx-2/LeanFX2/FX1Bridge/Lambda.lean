import LeanFX2.FX1Bridge.Var

/-! # FX1Bridge/Lambda

Root status: Bridge.

First lambda bridge fragment.  This file deliberately handles only the
canonical unit identity lambda.  It composes the staged unit type bridge with
the newest-variable bridge, without claiming a general recursive encoder for
all rich lambdas.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Rich raw term for the unit identity lambda. -/
def unitIdentityRaw : RawTerm 0 :=
  RawTerm.lam unitVarRaw

/-- Rich type of the unit identity lambda. -/
def unitIdentityType (level : Nat) : Ty level 0 :=
  Ty.arrow Ty.unit Ty.unit

/-- Canonical rich term for the unit identity lambda. -/
def unitIdentityTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (unitIdentityType level)
      unitIdentityRaw :=
  Term.lam unitVarTerm

/-- FX1 encoding of the unit identity lambda's type. -/
def encodeTy_unitIdentity : FX1.Expr :=
  FX1.Expr.pi encodeTy_unit encodeTy_unit

/-- FX1 encoding of the unit identity lambda. -/
def encodeRawTerm_unitIdentity : FX1.Expr :=
  FX1.Expr.lam encodeTy_unit encodeRawTerm_unitVar

/-- The staged unit type constant has sort zero in the one-binder staged unit
context. -/
theorem unitTypeExpr_has_sort_in_encodedUnitVarContext :
    FX1.HasType
      unitEnvironment
      encodeCtx_unitVar
      encodeTy_unit
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      unitValueDeclaration
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        unitTypeDeclaration))

/-- The encoded unit identity type is a well-formed FX1 type in the staged unit
environment. -/
theorem encodedUnitIdentityType_has_sort :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeTy_unitIdentity
      (FX1.Expr.sort (FX1.Level.max FX1.Level.zero FX1.Level.zero)) :=
  FX1.HasType.pi
    unitTypeExpr_has_sort_in_unitEnvironment
    unitTypeExpr_has_sort_in_encodedUnitVarContext

/-- FX1 typing derivation for the encoded unit identity lambda. -/
theorem encodedUnitIdentity_has_type :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdentity
      encodeTy_unitIdentity :=
  FX1.HasType.lam
    unitTypeExpr_has_sort_in_unitEnvironment
    encodedNewestUnitVar_has_type

/-- Soundness of the unit identity-lambda bridge fragment. -/
theorem encodeTermSound_unitIdentity
    {mode : Mode}
    {level : Nat}
    (_identityTerm :
      Term
        (Ctx.empty mode level)
        (unitIdentityType level)
        unitIdentityRaw) :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdentity
      encodeTy_unitIdentity :=
  encodedUnitIdentity_has_type

end FX1Bridge
end LeanFX2

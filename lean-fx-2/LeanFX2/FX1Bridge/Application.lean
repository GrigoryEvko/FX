import LeanFX2.FX1Bridge.Lambda

/-! # FX1Bridge/Application

Root status: Bridge.

First application bridge fragment.  This file handles the canonical application
of the staged unit identity lambda to the staged unit value, and proves both
FX1 typing and the corresponding FX1 beta step for that exact fragment.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Rich raw term for applying the unit identity lambda to unit. -/
def unitIdentityAppRaw : RawTerm 0 :=
  RawTerm.app unitIdentityRaw RawTerm.unit

/-- Canonical rich term for applying the unit identity lambda to unit. -/
def unitIdentityAppTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (Ty.unit : Ty level 0)
      unitIdentityAppRaw :=
  Term.app unitIdentityTerm Term.unit

/-- FX1 encoding of the unit identity application. -/
def encodeRawTerm_unitIdentityApp : FX1.Expr :=
  FX1.Expr.app encodeRawTerm_unitIdentity encodeRawTerm_unit

/-- Fragment decoder for applying the unit identity lambda to unit. -/
def decodeRawTerm_unitIdentityApp : FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app functionExpr argumentExpr =>
      match
        decodeRawTerm_unitIdentity functionExpr,
        decodeRawTerm_unit argumentExpr with
      | Option.some _, Option.some _ => Option.some unitIdentityAppRaw
      | Option.some _, Option.none => Option.none
      | Option.none, Option.some _ => Option.none
      | Option.none, Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none

/-- FX1 typing derivation for the encoded unit identity application. -/
theorem encodedUnitIdentityApp_has_type :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdentityApp
      encodeTy_unit :=
  FX1.HasType.app
    encodedUnitIdentity_has_type
    encodedUnit_has_type

/-- The encoded unit identity application beta-reduces to the staged unit
value. -/
theorem encodedUnitIdentityApp_betaStep :
    FX1.Step
      encodeRawTerm_unitIdentityApp
      encodeRawTerm_unit :=
  FX1.Step.beta_newest_bvar
    encodeTy_unit
    encodeRawTerm_unit

/-- Soundness of the unit identity-application bridge fragment. -/
theorem encodeTermSound_unitIdentityApp
    {mode : Mode}
    {level : Nat}
    (_applicationTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitIdentityAppRaw) :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdentityApp
      encodeTy_unit :=
  encodedUnitIdentityApp_has_type

/-- Exact round-trip evidence for the unit identity-application bridge
fragment. -/
def encodeTermSound_unitIdentityApp_roundTrip
    {mode : Mode}
    {level : Nat}
    (_applicationTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitIdentityAppRaw) :
    BridgeRoundTrip
      encodeTy_unit
      (decodeTy_unit (level := level) (scope := 0))
      (Ty.unit : Ty level 0)
      encodeRawTerm_unitIdentityApp
      decodeRawTerm_unitIdentityApp
      unitIdentityAppRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.unit : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some unitIdentityAppRaw)
  }

end FX1Bridge
end LeanFX2

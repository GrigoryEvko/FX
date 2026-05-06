import LeanFX2.FX1Bridge.Application

/-! # FX1Bridge/Pi

Root status: Bridge.

First dependent-Pi bridge fragment.  This file handles the canonical dependent
unit identity and its application.  The codomain is constant `Unit`, so the FX1
encoding reuses the staged unit type, but the rich witnesses deliberately use
`Term.lamPi` and `Term.appPi`.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Rich raw term for the dependent unit identity lambda. -/
def unitPiIdentityRaw : RawTerm 0 :=
  RawTerm.lam unitVarRaw

/-- Rich dependent-Pi type of the unit identity lambda. -/
def unitPiIdentityType (level : Nat) : Ty level 0 :=
  Ty.piTy Ty.unit (Ty.unit : Ty level 1)

/-- Canonical rich dependent-Pi term for the unit identity lambda. -/
def unitPiIdentityTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (unitPiIdentityType level)
      unitPiIdentityRaw :=
  Term.lamPi unitVarTerm

/-- FX1 encoding of the dependent unit identity type. -/
def encodeTy_unitPiIdentity : FX1.Expr :=
  FX1.Expr.pi encodeTy_unit encodeTy_unit

/-- FX1 encoding of the dependent unit identity lambda. -/
def encodeRawTerm_unitPiIdentity : FX1.Expr :=
  FX1.Expr.lam encodeTy_unit encodeRawTerm_unitVar

/-- Fragment decoder for the dependent unit identity type. -/
def decodeTy_unitPiIdentity {level : Nat} : FX1.Expr ->
    Option (Ty level 0)
  | FX1.Expr.pi domainExpr bodyExpr =>
      match
        decodeTy_unit (level := level) (scope := 0) domainExpr,
        decodeTy_unit (level := level) (scope := 0) bodyExpr with
      | Option.some _, Option.some _ =>
          Option.some (unitPiIdentityType level)
      | Option.some _, Option.none => Option.none
      | Option.none, Option.some _ => Option.none
      | Option.none, Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Fragment decoder for the dependent unit identity lambda. -/
def decodeRawTerm_unitPiIdentity : FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.lam domainExpr bodyExpr =>
      match
        decodeTy_unit (level := 0) (scope := 0) domainExpr,
        decodeRawTerm_unitVar bodyExpr with
      | Option.some _, Option.some _ => Option.some unitPiIdentityRaw
      | Option.some _, Option.none => Option.none
      | Option.none, Option.some _ => Option.none
      | Option.none, Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- The encoded dependent unit identity type is well formed in the staged unit
environment. -/
theorem encodedUnitPiIdentityType_has_sort :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeTy_unitPiIdentity
      (FX1.Expr.sort (FX1.Level.max FX1.Level.zero FX1.Level.zero)) :=
  FX1.HasType.pi
    unitTypeExpr_has_sort_in_unitEnvironment
    unitTypeExpr_has_sort_in_encodedUnitVarContext

/-- FX1 typing derivation for the encoded dependent unit identity lambda. -/
theorem encodedUnitPiIdentity_has_type :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitPiIdentity
      encodeTy_unitPiIdentity :=
  FX1.HasType.lam
    unitTypeExpr_has_sort_in_unitEnvironment
    encodedNewestUnitVar_has_type

/-- Soundness of the dependent unit identity-lambda bridge fragment. -/
theorem encodeTermSound_unitPiIdentity
    {mode : Mode}
    {level : Nat}
    (_identityTerm :
      Term
        (Ctx.empty mode level)
        (unitPiIdentityType level)
        unitPiIdentityRaw) :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitPiIdentity
      encodeTy_unitPiIdentity :=
  encodedUnitPiIdentity_has_type

/-- Exact round-trip evidence for the dependent unit identity-lambda bridge
fragment. -/
def encodeTermSound_unitPiIdentity_roundTrip
    {mode : Mode}
    {level : Nat}
    (_identityTerm :
      Term
        (Ctx.empty mode level)
        (unitPiIdentityType level)
        unitPiIdentityRaw) :
    BridgeRoundTrip
      encodeTy_unitPiIdentity
      (decodeTy_unitPiIdentity (level := level))
      (unitPiIdentityType level)
      encodeRawTerm_unitPiIdentity
      decodeRawTerm_unitPiIdentity
      unitPiIdentityRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (unitPiIdentityType level))
    rawRoundTrip := Eq.refl (Option.some unitPiIdentityRaw)
  }

/-- Rich raw term for applying the dependent unit identity lambda to unit. -/
def unitPiIdentityAppRaw : RawTerm 0 :=
  RawTerm.app unitPiIdentityRaw RawTerm.unit

/-- Canonical rich dependent-Pi application of the unit identity to unit. -/
def unitPiIdentityAppTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (Ty.unit : Ty level 0)
      unitPiIdentityAppRaw :=
  Term.appPi unitPiIdentityTerm Term.unit

/-- FX1 encoding of the dependent unit identity application. -/
def encodeRawTerm_unitPiIdentityApp : FX1.Expr :=
  FX1.Expr.app encodeRawTerm_unitPiIdentity encodeRawTerm_unit

/-- Fragment decoder for applying the dependent unit identity to unit. -/
def decodeRawTerm_unitPiIdentityApp : FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app functionExpr argumentExpr =>
      match
        decodeRawTerm_unitPiIdentity functionExpr,
        decodeRawTerm_unit argumentExpr with
      | Option.some _, Option.some _ => Option.some unitPiIdentityAppRaw
      | Option.some _, Option.none => Option.none
      | Option.none, Option.some _ => Option.none
      | Option.none, Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none

/-- FX1 typing derivation for the encoded dependent unit identity application. -/
theorem encodedUnitPiIdentityApp_has_type :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitPiIdentityApp
      encodeTy_unit :=
  FX1.HasType.app
    encodedUnitPiIdentity_has_type
    encodedUnit_has_type

/-- The encoded dependent unit identity application beta-reduces to the staged
unit value. -/
theorem encodedUnitPiIdentityApp_betaStep :
    FX1.Step
      encodeRawTerm_unitPiIdentityApp
      encodeRawTerm_unit :=
  FX1.Step.beta_newest_bvar
    encodeTy_unit
    encodeRawTerm_unit

/-- Soundness of the dependent unit identity-application bridge fragment. -/
theorem encodeTermSound_unitPiIdentityApp
    {mode : Mode}
    {level : Nat}
    (_applicationTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitPiIdentityAppRaw) :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeRawTerm_unitPiIdentityApp
      encodeTy_unit :=
  encodedUnitPiIdentityApp_has_type

/-- Exact round-trip evidence for the dependent unit identity-application
bridge fragment. -/
def encodeTermSound_unitPiIdentityApp_roundTrip
    {mode : Mode}
    {level : Nat}
    (_applicationTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitPiIdentityAppRaw) :
    BridgeRoundTrip
      encodeTy_unit
      (decodeTy_unit (level := level) (scope := 0))
      (Ty.unit : Ty level 0)
      encodeRawTerm_unitPiIdentityApp
      decodeRawTerm_unitPiIdentityApp
      unitPiIdentityAppRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.unit : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some unitPiIdentityAppRaw)
  }

end FX1Bridge
end LeanFX2

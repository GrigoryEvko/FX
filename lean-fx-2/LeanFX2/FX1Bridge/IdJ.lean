import LeanFX2.FX1Bridge.Id
import LeanFX2.Reduction.Step

/-! # FX1Bridge/IdJ

Root status: Bridge.

Exact Unit identity-eliminator bridge fragment.  FX1/Core does not yet have an
identity eliminator, so this file only bridges the computationally determined
case `J unit (refl unit)`.  The rich source has a typed ι-step to `unit`, and
the FX1 encoding records that exact computed result as the staged unit value.

This is not a general `idJ` encoder and not Root-FX1 identity-eliminator
evidence.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Rich raw term for the exact Unit identity eliminator at reflexivity. -/
def unitIdJRaw : RawTerm 0 :=
  RawTerm.idJ RawTerm.unit unitIdReflRaw

/-- Canonical rich `J unit (refl unit)` term. -/
def unitIdJTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (Ty.unit : Ty level 0)
      unitIdJRaw :=
  Term.idJ Term.unit unitIdReflTerm

/-- The exact rich Unit identity eliminator computes to the Unit base case. -/
theorem unitIdJ_iotaStep {mode : Mode} {level : Nat} :
    Step
      (unitIdJTerm (mode := mode) (level := level))
      (Term.unit :
        Term
          (Ctx.empty mode level)
          (Ty.unit : Ty level 0)
          RawTerm.unit) :=
  Step.iotaIdJRefl Ty.unit RawTerm.unit Term.unit

/-- FX1 encoding of the exact computed Unit identity eliminator. -/
def encodeRawTerm_unitIdJ : FX1.Expr :=
  encodeRawTerm_unit

/-- Fragment decoder for the exact computed Unit identity eliminator. -/
def decodeRawTerm_unitIdJ : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom unitValueAtomId unitIdJRaw

/-- The computed Unit identity eliminator encoding is the staged unit value. -/
theorem encodeRawTerm_unitIdJ_eq_unit :
    Eq encodeRawTerm_unitIdJ encodeRawTerm_unit :=
  Eq.refl encodeRawTerm_unit

/-- The staged unit value remains well typed after the Unit identity
declarations are added. -/
theorem encodedUnit_has_type_in_unitIdEnvironment :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      encodeRawTerm_unit
      encodeTy_unit :=
  FX1.HasType.weaken_environment unitIdReflDeclaration
    (FX1.HasType.weaken_environment unitIdTypeDeclaration
      encodedUnit_has_type)

/-- FX1 typing derivation for the encoded exact Unit identity eliminator. -/
theorem encodedUnitIdJ_has_type :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdJ
      encodeTy_unit :=
  encodedUnit_has_type_in_unitIdEnvironment

/-- Soundness of the exact `J unit (refl unit)` bridge fragment. -/
theorem encodeTermSound_unitIdJ
    {mode : Mode}
    {level : Nat}
    (_idJTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitIdJRaw) :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdJ
      encodeTy_unit :=
  encodedUnitIdJ_has_type

/-- Exact round-trip evidence for the `J unit (refl unit)` bridge fragment. -/
def encodeTermSound_unitIdJ_roundTrip
    {mode : Mode}
    {level : Nat}
    (_idJTerm :
      Term
        (Ctx.empty mode level)
        (Ty.unit : Ty level 0)
        unitIdJRaw) :
    BridgeRoundTrip
      encodeTy_unit
      (decodeTy_unit (level := level) (scope := 0))
      (Ty.unit : Ty level 0)
      encodeRawTerm_unitIdJ
      decodeRawTerm_unitIdJ
      unitIdJRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.unit : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some unitIdJRaw)
  }

end FX1Bridge
end LeanFX2

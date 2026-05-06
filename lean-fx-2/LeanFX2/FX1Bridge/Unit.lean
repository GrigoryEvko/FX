import LeanFX2.FX1Bridge.RoundTrip
import LeanFX2.FX1.Core.WellFormed

/-! # FX1Bridge/Unit

Root status: Bridge.

First explicit LeanFX2-rich to FX1 bridge fragment.

This file does not claim `Ty.unit` is a new FX1 root primitive.  It stages
the rich unit type and its unique value as declared FX1 constants, proves the
staged declarations are well formed, and proves that a rich `Term.unit`
encodes to a well-typed FX1 expression in that staged environment.

The environment intentionally contains object-level `axiomDecl` entries.
That makes this a `Bridge` fragment, not `Root-FX1` release evidence.
Replacing these declarations with real FX1 definitions is a later bridge
strengthening step.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged FX1 unit type name. -/
def unitTypeAtomId : Nat := 1

/-- Native atom id used for the staged FX1 unit value name. -/
def unitValueAtomId : Nat := 2

/-- FX1 name for the rich unit type constant. -/
def unitTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitTypeAtomId

/-- FX1 name for the rich unit value constant. -/
def unitValueName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitValueAtomId

/-- FX1 expression encoding the rich unit type. -/
def unitTypeExpr : FX1.Expr :=
  FX1.Expr.const unitTypeName

/-- FX1 expression encoding the rich unit value. -/
def unitValueExpr : FX1.Expr :=
  FX1.Expr.const unitValueName

/-- Staged FX1 declaration for the rich unit type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the rich unit value.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitValueDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitValueName unitTypeExpr

/-- Environment after declaring the rich unit type constant. -/
def unitTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend FX1.Environment.empty unitTypeDeclaration

/-- Staged bridge environment for the unit fragment. -/
def unitEnvironment : FX1.Environment :=
  FX1.Environment.extend unitTypeEnvironment unitValueDeclaration

/-- The empty rich context encodes to the empty FX1 context. -/
def encodeEmptyCtx {mode : Mode} {level : Nat} :
    Ctx mode level 0 -> FX1.Context
  | Ctx.empty _ _ => FX1.Context.empty

/-- Unit-only type encoder for this first bridge fragment. -/
def encodeTy_unit : FX1.Expr :=
  unitTypeExpr

/-- Unit-only raw-term encoder for this first bridge fragment. -/
def encodeRawTerm_unit : FX1.Expr :=
  unitValueExpr

/-- Fragment decoder for the staged rich unit type. -/
def decodeTy_unit {level scope : Nat} : FX1.Expr -> Option (Ty level scope) :=
  decodeConstByAtom unitTypeAtomId (Ty.unit : Ty level scope)

/-- Fragment decoder for the staged rich unit value. -/
def decodeRawTerm_unit : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom unitValueAtomId RawTerm.unit

/-- Unit type encoding computes to the staged FX1 unit type constant. -/
theorem encodeTy_unit_eq_unitTypeExpr :
    Eq encodeTy_unit unitTypeExpr :=
  Eq.refl unitTypeExpr

/-- Unit raw-term encoding computes to the staged FX1 unit value constant. -/
theorem encodeRawTerm_unit_eq_unitValueExpr :
    Eq encodeRawTerm_unit unitValueExpr :=
  Eq.refl unitValueExpr

/-- The staged unit type declaration is well typed in the empty FX1
environment. -/
theorem unitTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      FX1.Environment.empty
      unitTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged unit value declaration is well typed after the unit type
constant is available. -/
theorem unitValueDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      unitTypeEnvironment
      unitValueDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        unitTypeDeclaration))

/-- The staged unit type environment is well formed. -/
theorem unitTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed unitTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    FX1.Environment.WellFormed.empty
    (FX1.Environment.NameFresh.empty unitTypeName)
    unitTypeDeclaration_wellTyped

/-- The two staged unit names are distinct. -/
theorem unitValueName_ne_unitTypeName :
    Not (Eq unitValueName unitTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitValueName) namesEqual
    nomatch boolEquality

/-- The staged unit value name is fresh after the unit type declaration. -/
theorem unitValueName_fresh :
    FX1.Environment.NameFresh unitTypeEnvironment unitValueName :=
  FX1.Environment.NameFresh.older
    unitTypeDeclaration
    (FX1.Environment.NameFresh.empty unitValueName)
    unitValueName_ne_unitTypeName

/-- The staged unit bridge environment is well formed. -/
theorem unitEnvironment_wellFormed :
    FX1.Environment.WellFormed unitEnvironment :=
  FX1.Environment.WellFormed.extend
    unitTypeEnvironment_wellFormed
    unitValueName_fresh
    unitValueDeclaration_wellTyped

/-- The encoded rich unit value is well typed in the staged FX1 unit
environment. -/
theorem encodedUnit_has_type :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      unitValueExpr
      unitTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      unitTypeEnvironment
      unitValueDeclaration)

/-- Soundness of the unit-only bridge fragment.

Any rich `Term.unit` in an empty rich context encodes to the staged FX1 unit
value, and that value has the encoded unit type. -/
theorem encodeTermSound_unit
    {mode : Mode}
    {level : Nat}
    (_unitTerm : Term (Ctx.empty mode level) Ty.unit RawTerm.unit) :
    FX1.HasType
      unitEnvironment
      (encodeEmptyCtx (Ctx.empty mode level))
      encodeRawTerm_unit
      encodeTy_unit :=
  encodedUnit_has_type

/-- Exact round-trip evidence for the unit bridge fragment. -/
def encodeTermSound_unit_roundTrip
    {mode : Mode}
    {level : Nat}
    (_unitTerm : Term (Ctx.empty mode level) Ty.unit RawTerm.unit) :
    BridgeRoundTrip
      encodeTy_unit
      (decodeTy_unit (level := level) (scope := 0))
      (Ty.unit : Ty level 0)
      encodeRawTerm_unit
      decodeRawTerm_unit
      RawTerm.unit :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.unit : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some RawTerm.unit)
  }

end FX1Bridge
end LeanFX2

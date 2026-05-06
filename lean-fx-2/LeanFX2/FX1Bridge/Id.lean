import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Id

Root status: Bridge.

Exact Unit identity bridge fragment.  FX1/Core does not yet have identity
types, so this file stages the single rich identity type
`Id Unit unit unit` and its canonical reflexivity witness as object-level FX1
declarations.

The staged declarations are `axiomDecl` placeholders.  This is therefore
Bridge evidence only: it proves that the rich Unit-reflexivity fragment has a
well-typed FX1 representation in a staged environment, not that identity is a
new Root-FX1 primitive.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged Unit identity type name. -/
def unitIdTypeAtomId : Nat := 9

/-- Native atom id used for the staged Unit reflexivity witness name. -/
def unitIdReflAtomId : Nat := 10

/-- FX1 name for the exact rich `Id Unit unit unit` type constant. -/
def unitIdTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitIdTypeAtomId

/-- FX1 name for the exact rich `refl unit` value constant. -/
def unitIdReflName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitIdReflAtomId

/-- FX1 expression encoding the exact rich Unit identity type. -/
def unitIdTypeExpr : FX1.Expr :=
  FX1.Expr.const unitIdTypeName

/-- FX1 expression encoding the exact rich Unit reflexivity witness. -/
def unitIdReflExpr : FX1.Expr :=
  FX1.Expr.const unitIdReflName

/-- Staged FX1 declaration for the exact rich Unit identity type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitIdTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitIdTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the exact rich Unit reflexivity witness.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitIdReflDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitIdReflName unitIdTypeExpr

/-- Environment after declaring Unit, unit, and the exact Unit identity type. -/
def unitIdTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend unitEnvironment unitIdTypeDeclaration

/-- Staged bridge environment for the exact Unit identity fragment. -/
def unitIdEnvironment : FX1.Environment :=
  FX1.Environment.extend unitIdTypeEnvironment unitIdReflDeclaration

/-- Rich type of the exact Unit identity fragment. -/
def unitIdType (level : Nat) : Ty level 0 :=
  Ty.id Ty.unit RawTerm.unit RawTerm.unit

/-- Rich raw term for `refl unit`. -/
def unitIdReflRaw : RawTerm 0 :=
  RawTerm.refl RawTerm.unit

/-- Canonical rich term for `refl unit`. -/
def unitIdReflTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (unitIdType level)
      unitIdReflRaw :=
  Term.refl Ty.unit RawTerm.unit

/-- Unit-identity-only type encoder for this bridge fragment. -/
def encodeTy_unitId : FX1.Expr :=
  unitIdTypeExpr

/-- Unit-reflexivity-only raw-term encoder for this bridge fragment. -/
def encodeRawTerm_unitIdRefl : FX1.Expr :=
  unitIdReflExpr

/-- Fragment decoder for the staged exact Unit identity type. -/
def decodeTy_unitId {level : Nat} : FX1.Expr -> Option (Ty level 0) :=
  decodeConstByAtom unitIdTypeAtomId (unitIdType level)

/-- Fragment decoder for the staged exact Unit reflexivity witness. -/
def decodeRawTerm_unitIdRefl : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom unitIdReflAtomId unitIdReflRaw

/-- Unit identity type encoding computes to the staged FX1 type constant. -/
theorem encodeTy_unitId_eq_unitIdTypeExpr :
    Eq encodeTy_unitId unitIdTypeExpr :=
  Eq.refl unitIdTypeExpr

/-- Unit reflexivity encoding computes to the staged FX1 value constant. -/
theorem encodeRawTerm_unitIdRefl_eq_unitIdReflExpr :
    Eq encodeRawTerm_unitIdRefl unitIdReflExpr :=
  Eq.refl unitIdReflExpr

/-- The staged Unit identity type declaration is well typed after Unit and
unit are available. -/
theorem unitIdTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      unitEnvironment
      unitIdTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged Unit reflexivity declaration is well typed after the exact Unit
identity type is available. -/
theorem unitIdReflDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      unitIdTypeEnvironment
      unitIdReflDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        unitEnvironment
        unitIdTypeDeclaration))

/-- The staged Unit identity type name is distinct from the staged Unit type
name. -/
theorem unitIdTypeName_ne_unitTypeName :
    Not (Eq unitIdTypeName unitTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitIdTypeName) namesEqual
    nomatch boolEquality

/-- The staged Unit identity type name is distinct from the staged unit value
name. -/
theorem unitIdTypeName_ne_unitValueName :
    Not (Eq unitIdTypeName unitValueName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitIdTypeName) namesEqual
    nomatch boolEquality

/-- The staged Unit reflexivity name is distinct from the staged Unit type
name. -/
theorem unitIdReflName_ne_unitTypeName :
    Not (Eq unitIdReflName unitTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitIdReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit reflexivity name is distinct from the staged unit value
name. -/
theorem unitIdReflName_ne_unitValueName :
    Not (Eq unitIdReflName unitValueName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitIdReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit reflexivity name is distinct from the staged Unit identity
type name. -/
theorem unitIdReflName_ne_unitIdTypeName :
    Not (Eq unitIdReflName unitIdTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitIdReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit identity type name is fresh after Unit and unit are
available. -/
theorem unitIdTypeName_fresh :
    FX1.Environment.NameFresh unitEnvironment unitIdTypeName :=
  FX1.Environment.NameFresh.older
    unitValueDeclaration
    (FX1.Environment.NameFresh.older
      unitTypeDeclaration
      (FX1.Environment.NameFresh.empty unitIdTypeName)
      unitIdTypeName_ne_unitTypeName)
    unitIdTypeName_ne_unitValueName

/-- The staged Unit reflexivity name is fresh after Unit, unit, and the exact
Unit identity type are available. -/
theorem unitIdReflName_fresh :
    FX1.Environment.NameFresh unitIdTypeEnvironment unitIdReflName :=
  FX1.Environment.NameFresh.older
    unitIdTypeDeclaration
    (FX1.Environment.NameFresh.older
      unitValueDeclaration
      (FX1.Environment.NameFresh.older
        unitTypeDeclaration
        (FX1.Environment.NameFresh.empty unitIdReflName)
        unitIdReflName_ne_unitTypeName)
      unitIdReflName_ne_unitValueName)
    unitIdReflName_ne_unitIdTypeName

/-- The staged Unit identity type environment is well formed. -/
theorem unitIdTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed unitIdTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    unitEnvironment_wellFormed
    unitIdTypeName_fresh
    unitIdTypeDeclaration_wellTyped

/-- The staged Unit identity bridge environment is well formed. -/
theorem unitIdEnvironment_wellFormed :
    FX1.Environment.WellFormed unitIdEnvironment :=
  FX1.Environment.WellFormed.extend
    unitIdTypeEnvironment_wellFormed
    unitIdReflName_fresh
    unitIdReflDeclaration_wellTyped

/-- The encoded exact Unit identity type has sort zero in the staged Unit
identity environment. -/
theorem unitIdTypeExpr_has_sort_in_unitIdEnvironment :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      unitIdTypeExpr
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      unitIdReflDeclaration
      (FX1.Environment.HasDeclaration.newest
        unitEnvironment
        unitIdTypeDeclaration))

/-- The encoded rich `refl unit` witness is well typed in the staged FX1 Unit
identity environment. -/
theorem encodedUnitIdRefl_has_type :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      unitIdReflExpr
      unitIdTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      unitIdTypeEnvironment
      unitIdReflDeclaration)

/-- Soundness of the exact Unit-reflexivity bridge fragment. -/
theorem encodeTermSound_unitIdRefl
    {mode : Mode}
    {level : Nat}
    (_reflTerm :
      Term
        (Ctx.empty mode level)
        (unitIdType level)
        unitIdReflRaw) :
    FX1.HasType
      unitIdEnvironment
      FX1.Context.empty
      encodeRawTerm_unitIdRefl
      encodeTy_unitId :=
  encodedUnitIdRefl_has_type

/-- Exact round-trip evidence for the Unit-reflexivity bridge fragment. -/
def encodeTermSound_unitIdRefl_roundTrip
    {mode : Mode}
    {level : Nat}
    (_reflTerm :
      Term
        (Ctx.empty mode level)
        (unitIdType level)
        unitIdReflRaw) :
    BridgeRoundTrip
      encodeTy_unitId
      (decodeTy_unitId (level := level))
      (unitIdType level)
      encodeRawTerm_unitIdRefl
      decodeRawTerm_unitIdRefl
      unitIdReflRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (unitIdType level))
    rawRoundTrip := Eq.refl (Option.some unitIdReflRaw)
  }

end FX1Bridge
end LeanFX2

import LeanFX2.FX1Bridge.Lambda

/-! # FX1Bridge/Equiv

Root status: Bridge.

Exact Unit equivalence-reflexivity bridge fragment.  FX1/Core does not yet have
an equivalence type former, so this file stages only the single rich type
`Equiv Unit Unit` and the canonical rich identity equivalence as object-level
FX1 declarations.

The staged declarations are `axiomDecl` placeholders.  This proves a
well-typed FX1 representation for the Unit equivalence-reflexivity fragment; it
does not make equivalence a Root-FX1 primitive and does not claim full
univalence.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged Unit equivalence type name. -/
def unitEquivTypeAtomId : Nat := 11

/-- Native atom id used for the staged Unit equivalence-reflexivity name. -/
def unitEquivReflAtomId : Nat := 12

/-- FX1 name for the exact rich `Equiv Unit Unit` type constant. -/
def unitEquivTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitEquivTypeAtomId

/-- FX1 name for the exact rich Unit identity equivalence constant. -/
def unitEquivReflName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous unitEquivReflAtomId

/-- FX1 expression encoding the exact rich `Equiv Unit Unit` type. -/
def unitEquivTypeExpr : FX1.Expr :=
  FX1.Expr.const unitEquivTypeName

/-- FX1 expression encoding the exact rich Unit identity equivalence. -/
def unitEquivReflExpr : FX1.Expr :=
  FX1.Expr.const unitEquivReflName

/-- Staged FX1 declaration for the exact rich `Equiv Unit Unit` type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitEquivTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitEquivTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the exact rich Unit identity equivalence.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def unitEquivReflDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl unitEquivReflName unitEquivTypeExpr

/-- Environment after declaring Unit, unit, and the exact Unit equivalence
type. -/
def unitEquivTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend unitEnvironment unitEquivTypeDeclaration

/-- Staged bridge environment for the exact Unit equivalence fragment. -/
def unitEquivEnvironment : FX1.Environment :=
  FX1.Environment.extend unitEquivTypeEnvironment unitEquivReflDeclaration

/-- Rich type of the exact Unit equivalence fragment. -/
def unitEquivType (level : Nat) : Ty level 0 :=
  Ty.equiv Ty.unit Ty.unit

/-- Rich raw term for the canonical Unit identity equivalence. -/
def unitEquivReflRaw : RawTerm 0 :=
  RawTerm.equivIntro unitIdentityRaw unitIdentityRaw

/-- Canonical rich identity equivalence on Unit. -/
def unitEquivReflTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (unitEquivType level)
      unitEquivReflRaw :=
  Term.equivReflId Ty.unit

/-- Unit-equivalence-only type encoder for this bridge fragment. -/
def encodeTy_unitEquiv : FX1.Expr :=
  unitEquivTypeExpr

/-- Unit-equivalence-reflexivity-only raw-term encoder for this bridge
fragment. -/
def encodeRawTerm_unitEquivRefl : FX1.Expr :=
  unitEquivReflExpr

/-- Unit equivalence type encoding computes to the staged FX1 type constant. -/
theorem encodeTy_unitEquiv_eq_unitEquivTypeExpr :
    Eq encodeTy_unitEquiv unitEquivTypeExpr :=
  Eq.refl unitEquivTypeExpr

/-- Unit equivalence-reflexivity encoding computes to the staged FX1 value
constant. -/
theorem encodeRawTerm_unitEquivRefl_eq_unitEquivReflExpr :
    Eq encodeRawTerm_unitEquivRefl unitEquivReflExpr :=
  Eq.refl unitEquivReflExpr

/-- The staged Unit equivalence type declaration is well typed after Unit and
unit are available. -/
theorem unitEquivTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      unitEnvironment
      unitEquivTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged Unit identity equivalence declaration is well typed after the
exact Unit equivalence type is available. -/
theorem unitEquivReflDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      unitEquivTypeEnvironment
      unitEquivReflDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        unitEnvironment
        unitEquivTypeDeclaration))

/-- The staged Unit equivalence type name is distinct from the staged Unit type
name. -/
theorem unitEquivTypeName_ne_unitTypeName :
    Not (Eq unitEquivTypeName unitTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitEquivTypeName) namesEqual
    nomatch boolEquality

/-- The staged Unit equivalence type name is distinct from the staged unit
value name. -/
theorem unitEquivTypeName_ne_unitValueName :
    Not (Eq unitEquivTypeName unitValueName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitEquivTypeName) namesEqual
    nomatch boolEquality

/-- The staged Unit identity equivalence name is distinct from the staged Unit
type name. -/
theorem unitEquivReflName_ne_unitTypeName :
    Not (Eq unitEquivReflName unitTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitEquivReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit identity equivalence name is distinct from the staged unit
value name. -/
theorem unitEquivReflName_ne_unitValueName :
    Not (Eq unitEquivReflName unitValueName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitEquivReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit identity equivalence name is distinct from the staged Unit
equivalence type name. -/
theorem unitEquivReflName_ne_unitEquivTypeName :
    Not (Eq unitEquivReflName unitEquivTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq unitEquivReflName) namesEqual
    nomatch boolEquality

/-- The staged Unit equivalence type name is fresh after Unit and unit are
available. -/
theorem unitEquivTypeName_fresh :
    FX1.Environment.NameFresh unitEnvironment unitEquivTypeName :=
  FX1.Environment.NameFresh.older
    unitValueDeclaration
    (FX1.Environment.NameFresh.older
      unitTypeDeclaration
      (FX1.Environment.NameFresh.empty unitEquivTypeName)
      unitEquivTypeName_ne_unitTypeName)
    unitEquivTypeName_ne_unitValueName

/-- The staged Unit identity equivalence name is fresh after Unit, unit, and the
exact Unit equivalence type are available. -/
theorem unitEquivReflName_fresh :
    FX1.Environment.NameFresh unitEquivTypeEnvironment unitEquivReflName :=
  FX1.Environment.NameFresh.older
    unitEquivTypeDeclaration
    (FX1.Environment.NameFresh.older
      unitValueDeclaration
      (FX1.Environment.NameFresh.older
        unitTypeDeclaration
        (FX1.Environment.NameFresh.empty unitEquivReflName)
        unitEquivReflName_ne_unitTypeName)
      unitEquivReflName_ne_unitValueName)
    unitEquivReflName_ne_unitEquivTypeName

/-- The staged Unit equivalence type environment is well formed. -/
theorem unitEquivTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed unitEquivTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    unitEnvironment_wellFormed
    unitEquivTypeName_fresh
    unitEquivTypeDeclaration_wellTyped

/-- The staged Unit equivalence bridge environment is well formed. -/
theorem unitEquivEnvironment_wellFormed :
    FX1.Environment.WellFormed unitEquivEnvironment :=
  FX1.Environment.WellFormed.extend
    unitEquivTypeEnvironment_wellFormed
    unitEquivReflName_fresh
    unitEquivReflDeclaration_wellTyped

/-- The encoded exact Unit equivalence type has sort zero in the staged Unit
equivalence environment. -/
theorem unitEquivTypeExpr_has_sort_in_unitEquivEnvironment :
    FX1.HasType
      unitEquivEnvironment
      FX1.Context.empty
      unitEquivTypeExpr
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      unitEquivReflDeclaration
      (FX1.Environment.HasDeclaration.newest
        unitEnvironment
        unitEquivTypeDeclaration))

/-- The encoded rich Unit identity equivalence is well typed in the staged FX1
Unit equivalence environment. -/
theorem encodedUnitEquivRefl_has_type :
    FX1.HasType
      unitEquivEnvironment
      FX1.Context.empty
      unitEquivReflExpr
      unitEquivTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      unitEquivTypeEnvironment
      unitEquivReflDeclaration)

/-- Soundness of the exact Unit identity-equivalence bridge fragment. -/
theorem encodeTermSound_unitEquivRefl
    {mode : Mode}
    {level : Nat}
    (_equivTerm :
      Term
        (Ctx.empty mode level)
        (unitEquivType level)
        unitEquivReflRaw) :
    FX1.HasType
      unitEquivEnvironment
      FX1.Context.empty
      encodeRawTerm_unitEquivRefl
      encodeTy_unitEquiv :=
  encodedUnitEquivRefl_has_type

end FX1Bridge
end LeanFX2

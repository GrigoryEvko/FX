import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Nat

Root status: Bridge.

Closed natural-number bridge fragment.  This file stages the rich Nat type,
zero value, and successor function as object-level FX1 declarations, then
proves that the empty rich-context `Term.natZero` and `Term.natSucc
Term.natZero` encode to well-typed FX1 expressions.

The staged declarations are `axiomDecl` placeholders, so this is Bridge
evidence only.  Eliminator fragments are intentionally left for later slices
because they require motive-shaped staged constants and computation evidence.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged FX1 Nat type name. -/
def natTypeAtomId : Nat := 6

/-- Native atom id used for the staged FX1 Nat zero value name. -/
def natZeroAtomId : Nat := 7

/-- Native atom id used for the staged FX1 Nat successor function name. -/
def natSuccAtomId : Nat := 8

/-- FX1 name for the rich Nat type constant. -/
def natTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous natTypeAtomId

/-- FX1 name for the rich Nat zero constant. -/
def natZeroName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous natZeroAtomId

/-- FX1 name for the rich Nat successor function constant. -/
def natSuccName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous natSuccAtomId

/-- FX1 expression encoding the rich Nat type. -/
def natTypeExpr : FX1.Expr :=
  FX1.Expr.const natTypeName

/-- FX1 expression encoding the rich Nat zero value. -/
def natZeroExpr : FX1.Expr :=
  FX1.Expr.const natZeroName

/-- FX1 expression encoding the rich Nat successor function. -/
def natSuccExpr : FX1.Expr :=
  FX1.Expr.const natSuccName

/-- FX1 expression encoding the rich Nat successor type. -/
def natSuccTypeExpr : FX1.Expr :=
  FX1.Expr.pi natTypeExpr natTypeExpr

/-- Staged FX1 declaration for the rich Nat type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def natTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl natTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the rich Nat zero value.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def natZeroDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl natZeroName natTypeExpr

/-- Staged FX1 declaration for the rich Nat successor function.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def natSuccDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl natSuccName natSuccTypeExpr

/-- Environment after declaring the rich Nat type constant. -/
def natTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend FX1.Environment.empty natTypeDeclaration

/-- Staged bridge environment for the Nat-zero fragment. -/
def natEnvironment : FX1.Environment :=
  FX1.Environment.extend natTypeEnvironment natZeroDeclaration

/-- Staged bridge environment for the Nat successor fragment. -/
def natSuccEnvironment : FX1.Environment :=
  FX1.Environment.extend natEnvironment natSuccDeclaration

/-- Nat-only type encoder for this bridge fragment. -/
def encodeTy_nat : FX1.Expr :=
  natTypeExpr

/-- Nat-zero raw-term encoder for this bridge fragment. -/
def encodeRawTerm_natZero : FX1.Expr :=
  natZeroExpr

/-- Nat-successor raw-term encoder for this bridge fragment. -/
def encodeRawTerm_natSucc : FX1.Expr :=
  natSuccExpr

/-- Rich raw term for applying successor to zero. -/
def natSuccZeroRaw : RawTerm 0 :=
  RawTerm.natSucc RawTerm.natZero

/-- Encoder for the exact rich raw term `succ zero`. -/
def encodeRawTerm_natSuccZero : FX1.Expr :=
  FX1.Expr.app encodeRawTerm_natSucc encodeRawTerm_natZero

/-- Fragment decoder for the staged rich Nat type. -/
def decodeTy_nat {level scope : Nat} : FX1.Expr -> Option (Ty level scope) :=
  decodeConstByAtom natTypeAtomId (Ty.nat : Ty level scope)

/-- Fragment decoder for the staged rich Nat zero value. -/
def decodeRawTerm_natZero : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom natZeroAtomId RawTerm.natZero

/-- Fragment recognizer for the staged rich Nat successor function symbol. -/
def decodeRawTerm_natSuccSymbol : FX1.Expr -> Option Unit :=
  decodeConstByAtom natSuccAtomId ()

/-- Fragment decoder for the exact rich raw term `succ zero`. -/
def decodeRawTerm_natSuccZero : FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app functionExpr argumentExpr =>
      match decodeRawTerm_natSuccSymbol functionExpr with
      | Option.some _ =>
          match decodeRawTerm_natZero argumentExpr with
          | Option.some _ => Option.some natSuccZeroRaw
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none

/-- Nat type encoding computes to the staged FX1 Nat type constant. -/
theorem encodeTy_nat_eq_natTypeExpr :
    Eq encodeTy_nat natTypeExpr :=
  Eq.refl natTypeExpr

/-- Nat-zero raw-term encoding computes to the staged FX1 zero constant. -/
theorem encodeRawTerm_natZero_eq_natZeroExpr :
    Eq encodeRawTerm_natZero natZeroExpr :=
  Eq.refl natZeroExpr

/-- Nat-successor raw-term encoding computes to the staged FX1 successor
constant. -/
theorem encodeRawTerm_natSucc_eq_natSuccExpr :
    Eq encodeRawTerm_natSucc natSuccExpr :=
  Eq.refl natSuccExpr

/-- Exact `succ zero` raw-term encoding computes to successor applied to zero. -/
theorem encodeRawTerm_natSuccZero_eq_app :
    Eq
      encodeRawTerm_natSuccZero
      (FX1.Expr.app natSuccExpr natZeroExpr) :=
  Eq.refl (FX1.Expr.app natSuccExpr natZeroExpr)

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

/-- The staged Nat type constant has sort zero under one Nat binder in the
staged Nat-zero environment. -/
theorem natTypeExpr_has_sort_in_natEnvironment_with_binder :
    FX1.HasType
      natEnvironment
      (FX1.Context.extend FX1.Context.empty natTypeExpr)
      encodeTy_nat
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      natZeroDeclaration
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        natTypeDeclaration))

/-- The staged Nat successor type is well formed in the staged Nat-zero
environment. -/
theorem natSuccTypeExpr_has_sort_in_natEnvironment :
    FX1.HasType
      natEnvironment
      FX1.Context.empty
      natSuccTypeExpr
      (FX1.Expr.sort (FX1.Level.max FX1.Level.zero FX1.Level.zero)) :=
  FX1.HasType.pi
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.older
        natZeroDeclaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          natTypeDeclaration)))
    natTypeExpr_has_sort_in_natEnvironment_with_binder

/-- The staged Nat successor declaration is well typed after Nat and zero are
available. -/
theorem natSuccDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      natEnvironment
      natSuccDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    natSuccTypeExpr_has_sort_in_natEnvironment

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

/-- The staged successor name is distinct from the staged Nat type name. -/
theorem natSuccName_ne_natTypeName :
    Not (Eq natSuccName natTypeName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq natSuccName) namesEqual
    nomatch boolEquality

/-- The staged successor name is distinct from the staged zero name. -/
theorem natSuccName_ne_natZeroName :
    Not (Eq natSuccName natZeroName) :=
  fun namesEqual =>
    let boolEquality := congrArg (FX1.Name.beq natSuccName) namesEqual
    nomatch boolEquality

/-- The staged zero value name is fresh after the Nat type declaration. -/
theorem natZeroName_fresh :
    FX1.Environment.NameFresh natTypeEnvironment natZeroName :=
  FX1.Environment.NameFresh.older
    natTypeDeclaration
    (FX1.Environment.NameFresh.empty natZeroName)
    natZeroName_ne_natTypeName

/-- The staged successor function name is fresh after the Nat type and zero
declarations. -/
theorem natSuccName_fresh :
    FX1.Environment.NameFresh natEnvironment natSuccName :=
  FX1.Environment.NameFresh.older
    natZeroDeclaration
    (FX1.Environment.NameFresh.older
      natTypeDeclaration
      (FX1.Environment.NameFresh.empty natSuccName)
      natSuccName_ne_natTypeName)
    natSuccName_ne_natZeroName

/-- The staged Nat bridge environment is well formed. -/
theorem natEnvironment_wellFormed :
    FX1.Environment.WellFormed natEnvironment :=
  FX1.Environment.WellFormed.extend
    natTypeEnvironment_wellFormed
    natZeroName_fresh
    natZeroDeclaration_wellTyped

/-- The staged Nat-successor bridge environment is well formed. -/
theorem natSuccEnvironment_wellFormed :
    FX1.Environment.WellFormed natSuccEnvironment :=
  FX1.Environment.WellFormed.extend
    natEnvironment_wellFormed
    natSuccName_fresh
    natSuccDeclaration_wellTyped

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

/-- The staged Nat type constant has sort zero in the staged Nat-successor
environment. -/
theorem natTypeExpr_has_sort_in_natSuccEnvironment :
    FX1.HasType
      natSuccEnvironment
      FX1.Context.empty
      encodeTy_nat
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.weaken_environment
    natSuccDeclaration
    natTypeExpr_has_sort_in_natEnvironment

/-- The encoded rich zero value remains well typed in the staged
Nat-successor environment. -/
theorem encodedNatZero_has_type_in_natSuccEnvironment :
    FX1.HasType
      natSuccEnvironment
      FX1.Context.empty
      natZeroExpr
      natTypeExpr :=
  FX1.HasType.weaken_environment
    natSuccDeclaration
    encodedNatZero_has_type

/-- The encoded rich successor function is well typed in the staged FX1 Nat
successor environment. -/
theorem encodedNatSucc_has_type :
    FX1.HasType
      natSuccEnvironment
      FX1.Context.empty
      natSuccExpr
      natSuccTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      natEnvironment
      natSuccDeclaration)

/-- Canonical rich term for `succ zero`. -/
def natSuccZeroTerm {mode : Mode} {level : Nat} :
    Term
      (Ctx.empty mode level)
      (Ty.nat : Ty level 0)
      natSuccZeroRaw :=
  Term.natSucc Term.natZero

/-- FX1 typing derivation for the encoded `succ zero` application. -/
theorem encodedNatSuccZero_has_type :
    FX1.HasType
      natSuccEnvironment
      FX1.Context.empty
      encodeRawTerm_natSuccZero
      encodeTy_nat :=
  FX1.HasType.app
    encodedNatSucc_has_type
    encodedNatZero_has_type_in_natSuccEnvironment

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

/-- Exact round-trip evidence for the Nat-zero bridge fragment. -/
def encodeTermSound_natZero_roundTrip
    {mode : Mode}
    {level : Nat}
    (_zeroTerm : Term (Ctx.empty mode level) Ty.nat RawTerm.natZero) :
    BridgeRoundTrip
      encodeTy_nat
      (decodeTy_nat (level := level) (scope := 0))
      (Ty.nat : Ty level 0)
      encodeRawTerm_natZero
      decodeRawTerm_natZero
      RawTerm.natZero :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.nat : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some RawTerm.natZero)
  }

/-- Soundness of the empty-context `succ zero` bridge fragment. -/
theorem encodeTermSound_natSuccZero
    {mode : Mode}
    {level : Nat}
    (_succZeroTerm :
      Term
        (Ctx.empty mode level)
        (Ty.nat : Ty level 0)
        natSuccZeroRaw) :
    FX1.HasType
      natSuccEnvironment
      FX1.Context.empty
      encodeRawTerm_natSuccZero
      encodeTy_nat :=
  encodedNatSuccZero_has_type

/-- Exact round-trip evidence for the `succ zero` bridge fragment. -/
def encodeTermSound_natSuccZero_roundTrip
    {mode : Mode}
    {level : Nat}
    (_succZeroTerm :
      Term
        (Ctx.empty mode level)
        (Ty.nat : Ty level 0)
        natSuccZeroRaw) :
    BridgeRoundTrip
      encodeTy_nat
      (decodeTy_nat (level := level) (scope := 0))
      (Ty.nat : Ty level 0)
      encodeRawTerm_natSuccZero
      decodeRawTerm_natSuccZero
      natSuccZeroRaw :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.nat : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some natSuccZeroRaw)
  }

end FX1Bridge
end LeanFX2

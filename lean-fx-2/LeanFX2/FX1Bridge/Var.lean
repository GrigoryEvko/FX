import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Var

Root status: Bridge.

First variable bridge fragment.  This does not claim a general context encoder
yet.  It handles the canonical newest variable in a one-binder rich context
whose binder type is unit, using the staged unit environment from
`FX1Bridge.Unit`.
-/

namespace LeanFX2
namespace FX1Bridge

/-- The only position in a one-binder rich context. -/
def unitVarPosition : Fin 1 :=
  ⟨0, Nat.zero_lt_succ 0⟩

/-- Rich raw term for the newest variable in the one-binder context. -/
def unitVarRaw : RawTerm 1 :=
  RawTerm.var unitVarPosition

/-- One-binder rich context whose newest variable has unit type. -/
def unitVarContext (mode : Mode) (level : Nat) : Ctx mode level 1 :=
  Ctx.cons (Ctx.empty mode level) (Ty.unit : Ty level 0)

/-- FX1 encoding of the one-binder unit context. -/
def encodeCtx_unitVar : FX1.Context :=
  FX1.Context.extend FX1.Context.empty encodeTy_unit

/-- FX1 encoding of the newest de Bruijn variable. -/
def encodeRawTerm_unitVar : FX1.Expr :=
  FX1.Expr.bvar Nat.zero

/-- The rich newest variable lookup in the unit context computes to unit. -/
theorem unitVarType_eq_unit {mode : Mode} {level : Nat} :
    Eq
      (varType (unitVarContext mode level) unitVarPosition)
      (Ty.unit : Ty level 1) :=
  Eq.refl (Ty.unit : Ty level 1)

/-- Canonical rich term for the newest unit variable. -/
def unitVarTerm {mode : Mode} {level : Nat} :
    Term
      (unitVarContext mode level)
      (Ty.unit : Ty level 1)
      unitVarRaw :=
  Term.var unitVarPosition

/-- The staged unit type constant has sort zero in the staged unit
environment. -/
theorem unitTypeExpr_has_sort_in_unitEnvironment :
    FX1.HasType
      unitEnvironment
      FX1.Context.empty
      encodeTy_unit
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      unitValueDeclaration
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        unitTypeDeclaration))

/-- The encoded one-binder unit context is well formed in the staged unit
environment. -/
theorem encodedUnitVarContext_wellFormed :
    FX1.Context.WellFormed unitEnvironment encodeCtx_unitVar :=
  FX1.Context.WellFormed.extend
    FX1.Context.WellFormed.empty
    unitTypeExpr_has_sort_in_unitEnvironment

/-- FX1 typing derivation for the encoded newest unit variable. -/
theorem encodedNewestUnitVar_has_type :
    FX1.HasType
      unitEnvironment
      encodeCtx_unitVar
      encodeRawTerm_unitVar
      encodeTy_unit :=
  FX1.HasType.var
    (FX1.Context.HasTypeAt.newest
      FX1.Context.empty
      encodeTy_unit)

/-- Soundness of the newest unit-variable bridge fragment. -/
theorem encodeTermSound_newestUnitVar
    {mode : Mode}
    {level : Nat}
    (_variableTerm :
      Term
        (unitVarContext mode level)
        (Ty.unit : Ty level 1)
        unitVarRaw) :
    FX1.HasType
      unitEnvironment
      encodeCtx_unitVar
      encodeRawTerm_unitVar
      encodeTy_unit :=
  encodedNewestUnitVar_has_type

end FX1Bridge
end LeanFX2

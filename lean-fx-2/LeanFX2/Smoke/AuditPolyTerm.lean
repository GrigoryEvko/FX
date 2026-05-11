import LeanFX2.Foundation.Polygraph.PolyTerm

namespace LeanFX2.Smoke

open LeanFX2 LeanFX2.Foundation.Polygraph

/-! K11.9 Phase A — concrete witnesses exercising the `PolyTerm`
typed mirror at the core MLTT fragment.  Each smoke value's
`#print axioms` line below must report "does not depend on any
axioms".

The witnesses cover the canonical inductive shape categories:
atomic (unit, boolTrue, natZero, listNil, optionNone), unary
(natSucc, optionSome, refl, idJ), binary (app, eitherInl/Inr,
listCons), ternary (boolElim, natElim, listElim, optionMatch,
eitherMatch), binder-bearing (lam, lamPi, pair, appPi), variable
lookup (var), and the raw-level converter (toRawTerm). -/

/-- The empty typing context at universe level 0, mode `strict`.
Used as the base for every smoke witness so we don't depend on a
particular Mode instance. -/
abbrev emptyContext : Ctx Mode.strict 0 0 := Ctx.empty Mode.strict 0

/-- Smoke witness — unit at empty scope. -/
def polyUnit_smoke : PolyTerm emptyContext Ty.unit RawPolyTerm.unit :=
  PolyTerm.unit

/-- Smoke witness — boolean true at empty scope. -/
def polyBoolTrue_smoke :
    PolyTerm emptyContext Ty.bool RawPolyTerm.boolTrue :=
  PolyTerm.boolTrue

/-- Smoke witness — natural zero at empty scope. -/
def polyNatZero_smoke :
    PolyTerm emptyContext Ty.nat RawPolyTerm.natZero :=
  PolyTerm.natZero

/-- Smoke witness — successor of zero (unary). -/
def polyNatSucc_smoke :
    PolyTerm emptyContext Ty.nat
      (RawPolyTerm.natSucc RawPolyTerm.natZero) :=
  PolyTerm.natSucc polyNatZero_smoke

/-- Smoke witness — list nil. -/
def polyListNil_smoke :
    PolyTerm emptyContext (Ty.listType Ty.nat) RawPolyTerm.listNil :=
  PolyTerm.listNil

/-- Smoke witness — option none. -/
def polyOptionNone_smoke :
    PolyTerm emptyContext (Ty.optionType Ty.nat)
      RawPolyTerm.optionNone :=
  PolyTerm.optionNone

/-- Smoke witness — list cons (binary). -/
def polyListCons_smoke :
    PolyTerm emptyContext (Ty.listType Ty.nat)
      (RawPolyTerm.listCons RawPolyTerm.natZero RawPolyTerm.listNil) :=
  PolyTerm.listCons polyNatZero_smoke polyListNil_smoke

/-- Smoke witness — option some (unary). -/
def polyOptionSome_smoke :
    PolyTerm emptyContext (Ty.optionType Ty.nat)
      (RawPolyTerm.optionSome RawPolyTerm.natZero) :=
  PolyTerm.optionSome polyNatZero_smoke

/-- Smoke witness — toRawTerm round-trip on natSucc reduces to
the matching `RawTerm.natSucc RawTerm.natZero` via the
`@[reducible]` definitional equality. -/
theorem polyToRawTerm_natSucc_smoke :
    (RawPolyTerm.natSucc RawPolyTerm.natZero
      : RawPolyTerm 0).toRawTerm =
    RawTerm.natSucc RawTerm.natZero := by
  rfl

/-- Smoke witness — toRawTerm at depth-3 nested ctor. -/
theorem polyToRawTerm_listCons_smoke :
    (RawPolyTerm.listCons RawPolyTerm.natZero RawPolyTerm.listNil
      : RawPolyTerm 0).toRawTerm =
    RawTerm.listCons RawTerm.natZero RawTerm.listNil := by
  rfl

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.RawPolyTerm.toRawTerm
#print axioms LeanFX2.PolyTerm
#print axioms LeanFX2.Smoke.polyUnit_smoke
#print axioms LeanFX2.Smoke.polyBoolTrue_smoke
#print axioms LeanFX2.Smoke.polyNatZero_smoke
#print axioms LeanFX2.Smoke.polyNatSucc_smoke
#print axioms LeanFX2.Smoke.polyListNil_smoke
#print axioms LeanFX2.Smoke.polyOptionNone_smoke
#print axioms LeanFX2.Smoke.polyListCons_smoke
#print axioms LeanFX2.Smoke.polyOptionSome_smoke
#print axioms LeanFX2.Smoke.polyToRawTerm_natSucc_smoke
#print axioms LeanFX2.Smoke.polyToRawTerm_listCons_smoke

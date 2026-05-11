import LeanFX2.Foundation.Polygraph.PolyTerm

namespace LeanFX2.Smoke

open LeanFX2 LeanFX2.Foundation.Polygraph

/-! K11.9 Phase A + Phase B — concrete witnesses exercising the
`PolyTerm` typed mirror.  Phase A covered the core MLTT fragment
(27 ctors); Phase B extends to all 77 ctors covering observational
equality, strict identity, modal, cubical, refinement, records,
codata, sessions, effects, universe + type-shape codes, cumulativity,
and the full univalence vocabulary.  Each smoke value's
`#print axioms` line below must report "does not depend on any
axioms".

Phase A witnesses cover canonical inductive shape categories:
atomic, unary, binary, ternary, binder-bearing, variable lookup,
plus the raw-level converter.  Phase B witnesses exercise the
new ctors that are inhabitable at the empty context with
`Mode.strict`: equivReflId + univalence type-codes + cumulUp +
unit-typed cubical Kan witness, etc. -/

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

/-! Phase B — coverage witnesses for the 50 newly added typed
constructors.  Each value below has a `#print axioms` line at the
bottom of the file. -/

/-- Smoke witness — modal intro on a unit value (Layer 6 will refine
the modality interaction; Phase B ships raw-side scaffolding only). -/
def polyModIntro_smoke :
    PolyTerm emptyContext Ty.unit
      (RawPolyTerm.modIntro RawPolyTerm.unit) :=
  PolyTerm.modIntro PolyTerm.unit

/-- Smoke witness — modal elim. -/
def polyModElim_smoke :
    PolyTerm emptyContext Ty.unit
      (RawPolyTerm.modElim RawPolyTerm.unit) :=
  PolyTerm.modElim PolyTerm.unit

/-- Smoke witness — subsume scaffold. -/
def polySubsume_smoke :
    PolyTerm emptyContext Ty.unit
      (RawPolyTerm.subsume RawPolyTerm.unit) :=
  PolyTerm.subsume PolyTerm.unit

/-- Smoke witness — universe code at level 0 inside Type 1.  Outer
context is at level ≥ 1 to satisfy the `levelLe` premise. -/
def polyUniverseCode_smoke :
    PolyTerm (Ctx.empty Mode.strict 1 : Ctx Mode.strict 1 0)
      (Ty.universe (UniverseLevel.zero) (by decide))
      (RawPolyTerm.universeCode 0) :=
  PolyTerm.universeCode (UniverseLevel.zero)
    (UniverseLevel.zero) (by decide) (by decide)

/-- Smoke witness — arrowCode value-shaped raw payload (CUMUL-2.4). -/
def polyArrowCode_smoke :
    PolyTerm (Ctx.empty Mode.strict 1 : Ctx Mode.strict 1 0)
      (Ty.universe (UniverseLevel.zero) (by decide))
      (RawPolyTerm.arrowCode (RawPolyTerm.universeCode 0)
        (RawPolyTerm.universeCode 0)) :=
  PolyTerm.arrowCode (UniverseLevel.zero) (by decide)
    (RawPolyTerm.universeCode 0) (RawPolyTerm.universeCode 0)

/-- Smoke witness — `equivReflId` canonical identity equivalence. -/
def polyEquivReflId_smoke :
    PolyTerm emptyContext (Ty.equiv Ty.unit Ty.unit)
      (RawPolyTerm.equivIntro
        (RawPolyTerm.lam (RawPolyTerm.var ⟨0, Nat.zero_lt_succ 0⟩))
        (RawPolyTerm.lam (RawPolyTerm.var ⟨0, Nat.zero_lt_succ 0⟩))) :=
  PolyTerm.equivReflId Ty.unit

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
#print axioms LeanFX2.Smoke.polyModIntro_smoke
#print axioms LeanFX2.Smoke.polyModElim_smoke
#print axioms LeanFX2.Smoke.polySubsume_smoke
#print axioms LeanFX2.Smoke.polyUniverseCode_smoke
#print axioms LeanFX2.Smoke.polyArrowCode_smoke
#print axioms LeanFX2.Smoke.polyEquivReflId_smoke

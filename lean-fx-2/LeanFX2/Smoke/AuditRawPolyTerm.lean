import LeanFX2.Foundation.Polygraph.RawPolyTerm

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-! K11.8 — concrete witnesses exercising the `RawPolyTerm` inductive
across atomic, unary, binary, ternary, and binder-bearing
constructors.  Each smoke value's `#print axioms` line below must
report "does not depend on any axioms". -/

/-- Smoke witness — atomic dim-0 ctor at empty scope. -/
def rawPolyUnit_smoke : RawPolyTerm 0 := RawPolyTerm.unit

/-- Smoke witness — variable at de-Bruijn position zero. -/
def rawPolyVar_smoke : RawPolyTerm 1 :=
  RawPolyTerm.var ⟨0, by decide⟩

/-- Smoke witness — boolean true atom. -/
def rawPolyBoolTrue_smoke : RawPolyTerm 0 := RawPolyTerm.boolTrue

/-- Smoke witness — natural-zero atom. -/
def rawPolyNatZero_smoke : RawPolyTerm 0 := RawPolyTerm.natZero

/-- Smoke witness — successor (unary). -/
def rawPolyNatSucc_smoke : RawPolyTerm 0 :=
  RawPolyTerm.natSucc rawPolyNatZero_smoke

/-- Smoke witness — pair (binary). -/
def rawPolyPair_smoke : RawPolyTerm 0 :=
  RawPolyTerm.pair rawPolyNatZero_smoke rawPolyBoolTrue_smoke

/-- Smoke witness — function intro (binder-bearing). -/
def rawPolyLam_smoke : RawPolyTerm 0 :=
  RawPolyTerm.lam (RawPolyTerm.var ⟨0, by decide⟩)

/-- Smoke witness — function elimination (binary). -/
def rawPolyApp_smoke : RawPolyTerm 0 :=
  RawPolyTerm.app rawPolyLam_smoke rawPolyNatZero_smoke

/-- Smoke witness — eliminator (ternary). -/
def rawPolyNatElim_smoke : RawPolyTerm 0 :=
  RawPolyTerm.natElim rawPolyNatZero_smoke rawPolyBoolTrue_smoke
    rawPolyBoolTrue_smoke

/-- Smoke witness — cubical path binder. -/
def rawPolyPathLam_smoke : RawPolyTerm 0 :=
  RawPolyTerm.pathLam (RawPolyTerm.var ⟨0, by decide⟩)

/-- Smoke witness — Pi-type code (binder-bearing). -/
def rawPolyPiTyCode_smoke : RawPolyTerm 0 :=
  RawPolyTerm.piTyCode (RawPolyTerm.universeCode 0)
    (RawPolyTerm.universeCode 0)

/-- Smoke witness — equivalence composition (D3.6-S5). -/
def rawPolyEquivCompose_smoke : RawPolyTerm 0 :=
  RawPolyTerm.equivCompose
    (RawPolyTerm.equivIntro rawPolyLam_smoke rawPolyLam_smoke)
    (RawPolyTerm.equivIntro rawPolyLam_smoke rawPolyLam_smoke)

/-- Smoke witness — observational-equality refl. -/
def rawPolyOeqRefl_smoke : RawPolyTerm 0 :=
  RawPolyTerm.oeqRefl rawPolyNatZero_smoke

/-- Smoke witness — decidable equality fires zero-axiom on equal
witnesses.  Exercises the `deriving DecidableEq` instance through
the most-recursive case (`equivCompose` ctor at depth 4). -/
theorem rawPolyDecEqRefl_smoke :
    (decide (rawPolyEquivCompose_smoke = rawPolyEquivCompose_smoke)) =
    true := by
  decide

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.RawPolyTerm
#print axioms LeanFX2.Foundation.Polygraph.instDecidableEqRawPolyTerm
#print axioms LeanFX2.Smoke.rawPolyUnit_smoke
#print axioms LeanFX2.Smoke.rawPolyVar_smoke
#print axioms LeanFX2.Smoke.rawPolyBoolTrue_smoke
#print axioms LeanFX2.Smoke.rawPolyNatZero_smoke
#print axioms LeanFX2.Smoke.rawPolyNatSucc_smoke
#print axioms LeanFX2.Smoke.rawPolyPair_smoke
#print axioms LeanFX2.Smoke.rawPolyLam_smoke
#print axioms LeanFX2.Smoke.rawPolyApp_smoke
#print axioms LeanFX2.Smoke.rawPolyNatElim_smoke
#print axioms LeanFX2.Smoke.rawPolyPathLam_smoke
#print axioms LeanFX2.Smoke.rawPolyPiTyCode_smoke
#print axioms LeanFX2.Smoke.rawPolyEquivCompose_smoke
#print axioms LeanFX2.Smoke.rawPolyOeqRefl_smoke
#print axioms LeanFX2.Smoke.rawPolyDecEqRefl_smoke
